import data.real.basic
import data.set.intervals.basic
import data.complex.exponential
import data.matrix.basic
import analysis.convex.basic


noncomputable theory
open_locale classical
open_locale convex
open_locale matrix


open set
open metric.metric_space

namespace fuzzy

-- Tactic example
example (A B C : Type) (h1: A → B) (h2 : B → C) : A → C :=
begin
  intro a,
  exact h2 (h1 a),
end

-- Fuzzy sets basic definitions
@[simp]
def fuzzy_set (u : Type) := u → Icc (0 : ℝ) 1

@[simp]
def mem {u : Type} (X : fuzzy_set u) (x : u) : ℝ := (X x).val

variable {u : Type}
variables (X Y : fuzzy_set u)

lemma mem_def_val : ∀ x, (X x).val = mem X x := 
begin
  intro x,
  dsimp,
  refl,
end

@[simp]
lemma mem_def : ∀ x, mem X x ∈ Icc (0:ℝ) 1 := λ x, (X x).2


lemma mem_pos : ∀ x, 0 ≤ mem X x := λ x, (X x).2.1
lemma mem_le_one : ∀ x, mem X x ≤ 1 := λ x, (X x).2.2

@[simp]
def support (X : fuzzy_set u) : set u := {x : u | (mem X x) > 0}
def support' : fuzzy_set u → set u := λ X,  {x : u | (mem X x) > 0}


def is_classical (X : fuzzy_set u) := ∀x,((mem X x)=0 ∨ (mem X x)=1)

@[simp]
def classical_to_fuzzy (X : set u) : fuzzy_set u := λ x, ite (x ∈ X) ⟨1,by simp⟩ ⟨0,by simp⟩
@[simp]
def fuzzy_to_classical (X : fuzzy_set u) /-(h : is_classical X)-/: set u := {x:u | (mem X x) = 1 }


def is_empty (X : fuzzy_set u) := ∀x, (mem X x)=0

example (X: fuzzy_set u) ( x : u) (h: is_empty X) : (mem X x)=0 :=
begin
  unfold is_empty at h,
  specialize h x,
  exact h,
end

lemma empty_is_classical (X : fuzzy_set u) : is_empty X → (is_classical X):=
begin
  intros emp x,
  left,
  specialize emp x,
  exact emp,
end





lemma fuzzy_nat_subset_is_cl (X: fuzzy_set ℕ ) (h1: ∀n, n ≤ 3 → (mem X n)=1) (h2 : ∀n, n > 3 → (mem X n)=0) : is_classical X :=
begin
  unfold is_classical,
  intros nn,
  specialize h1 nn,
  specialize h2 nn,
  cases le_or_lt nn 3 with hl3 hg3,
  right,
  apply h1,
  exact hl3,
  left,
  apply h2,
  exact hg3,
end

lemma fuzzy_natural_subset (X: fuzzy_set ℕ ) (h1: ∀n, n ≤ 3 → (mem X n)=1) (h2 : ∀n, n > 3 → (mem X n)=0) : fuzzy_to_classical X = {n : ℕ | n≤ 3}:=
begin
  unfold fuzzy_to_classical,
  ext,
  split,
  intro h,
  specialize h2 x,
  have H : mem X x = 1 → x ≤ 3,
  {contrapose!,
  intro Mem,
  --push_neg at Mem,
  have C:= h2 Mem,
  linarith,},
  rw mem_set_of_eq,
  rw mem_set_of_eq at h,
  apply H,
  exact h,

  intro h, 
  rw mem_set_of_eq,
  rw mem_set_of_eq at h,
  specialize h1 x,
  apply h1,
  exact h,
end

-- Instances for notation and definition of lattice structure
-- We define here the inclusion, union, intersection and complement of fuzzy sets
instance {α : Type*} : has_subset (fuzzy_set α) := {subset := λ A B, (∀ x, A x ≤ B x) }
#check X⊆Y

@[simp]
instance {α : Type*} : has_sup (fuzzy_set α) := { sup := λ A B, (λ x, max (A x) (B x)) }
@[simp]
instance {α : Type*} : has_inf (fuzzy_set α) := { inf := λ A B, (λ x, min (A x) (B x)) }
@[simp]
instance {α : Type*} : has_compl (fuzzy_set α) := {compl := λ A, (λ x,⟨ 1 - (A x), by 
begin
  split,
  rw sub_nonneg,
  have h1: (A x).val ≤ 1,{have := mem_def A x, cases this with f0 f1,exact f1,},
  exact h1,
  rw sub_le_self_iff,
  have h2: 0 ≤ (A x).val,{have := mem_pos A x, unfold mem at this, exact this,},
  exact h2,
end ⟩
)}
#check Xᶜ

instance is_lattice {α : Type*}: lattice (fuzzy_set α) := 
begin
apply lattice.mk',
{ intros a b, unfold has_sup.sup, simp [max_comm],},
{ intros a b c, unfold has_sup.sup, simp [max_assoc],},
{ intros a b, unfold has_inf.inf, simp [min_comm],},
{ intros a b c, unfold has_inf.inf, simp [min_assoc],},
{ intros a b, unfold has_sup.sup,  unfold has_inf.inf, ext,
  rw ←subtype.ext_iff, apply max_eq_left, apply min_le_left,},
{ intros a b, unfold has_sup.sup, unfold has_inf.inf, ext,
  rw ←subtype.ext_iff, apply min_eq_left, apply le_max_left,},
end

-- Structure extension so we have distributive property
instance is_distrib_lattice {α : Type*}: distrib_lattice (fuzzy_set α) := 
{ le_sup_inf := 
begin
  intros x y z,
  have h1: (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ∧ (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ z,
  {split,
  exact inf_le_left,
  exact inf_le_right,},
  have h2 : y = y ⊓ z ∨  z = y ⊓ z,
  {by_cases h : y ≤ z,
  left,
  exact left_eq_inf.mpr h,
  right,
  have h' : z ≤ y, sorry,
  exact right_eq_inf.mpr h',},
  cases h2 with hy hz,
  calc (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y : by {exact inf_le_left}
  ... = x ⊔ y ⊓ z :  by {exact congr_arg (has_sup.sup x) hy},
  calc (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ z : by {exact inf_le_right}
  ... = x ⊔ y ⊓ z :  by {exact congr_arg (has_sup.sup x) hz},
end
..fuzzy.is_lattice}




-- Alernative definitions for intersection and union
def intersection (X Y : fuzzy_set u) : fuzzy_set u := λ x, ⟨ min (X x).val (Y x).val, by
begin
  split,
  have h1: (X x).val ≥ 0,{have := mem_def X x, cases this with f0 f1,exact f0,},
  have h2: (Y x).val ≥ 0,{have := mem_def Y x, cases this with f0 f1,exact f0,},
  exact le_min h1 h2,
  have h1: (X x).val ≤ 1,{have := mem_def X x, cases this with f0 f1,exact f1,},
  have h2: (Y x).val ≤ 1,{have := mem_def Y x, cases this with f0 f1,exact f1,},
  exact min_le_of_left_le h1,
end⟩


example (X Y : fuzzy_set u) (x : u) (h1 : mem X x ≤ 1/2) : mem (X ⊓ Y) x ≤ 1/2:=
begin
  calc mem (X ⊓ Y) x = (min (X x) (Y x)).val : by {simp[has_inf.inf]}
  ... ≤ mem X x : by simp
  ... ≤ 1/2 : by {exact h1},
end

example (X Y : fuzzy_set u) (Z = intersection X Y) (x : u) (h1 : mem X x ≤ 1/2) : mem Z x ≤ 1/2:=
begin
  have h2 : mem Z x = (min (X x) (Y x)),
 {rw H,
  simp only [intersection],
  unfold_coes,
  ring,},
  have : mem Z x ≤ mem X x,
  {rw h2,
  exact min_le_left ↑(X x) ↑(Y x)},
  calc mem Z x ≤ mem X x : by {exact this}
  ...≤ 1/2 : by linarith,
end
 

def equivalence (X Y : fuzzy_set u) := ∀x, (mem X x = mem Y x)
instance {α : Type*} : has_equiv (fuzzy_set α) := {equiv := λ A B, (∀ x, A x = B x) }


-- Some results from the operations of fuzzy sets
open fuzzy

lemma max_min (x y : ℝ ): 1 - max x y = min (1-x) (1-y):=
begin
  by_cases h : x ≤ y,
  simp[h],
  {have h' : y ≤  x, by linarith [h],
  simp [h']},
end

lemma min_max (x y : ℝ ): 1 - min x y = max (1-x) (1-y):=
begin
  by_cases h: x ≤ y,
  {simp [h]},
  {have h' : y ≤  x, by linarith [h],
  simp [h']},
end

@[simp]
lemma max_val_comm {u : Type}(A B : fuzzy_set u) (x : u) :  (max (A x) (B x)).val = max ↑(A x) ↑(B x) :=
begin
    by_cases h : A x ≤ B x,
  {
    simp [h],
  },
  {
    replace h : B x ≤ A x,
    {
      unfold has_le.le,
      unfold_coes,
      
      push_neg at h,
      unfold has_lt.lt at h,
      unfold_coes at h,
sorry,
      --nlinarith [h],
    },
    simp [h],
  }
end



theorem first_Morgan_law (A B : fuzzy_set u) :  (A ⊔ B)ᶜ = Aᶜ ⊓ Bᶜ  :=
begin
  ext,
  calc mem (A ⊔ B)ᶜ x = 1 - mem (A ⊔ B) x: by simp[has_compl.compl]
  ... = 1 - (max (A x) (B x)).val : by simp[has_sup.sup]
  ... = 1 - max ((A x)) (B x) : by {simp}
  ... = min (1 - A x) (1 - B x) : by {rw max_min}
  ... = min (Aᶜ x) (Bᶜ x) : by simp[has_compl.compl]
  ... = mem (Aᶜ ⊓ Bᶜ) x : by {simp[has_inf.inf],sorry},

end


theorem second_Morgan_law (A B : fuzzy_set u) : (A ⊓ B)ᶜ = Aᶜ ⊔ Bᶜ   :=
begin
  ext,
  calc mem (A ⊓ B)ᶜ x = 1 - mem (A ⊓ B) x : by simp[has_compl.compl]
  ... = 1 - min (A x) (B x) : by {simp[has_inf.inf],/-rw mem_def-/sorry}
  ... = max (1 - A x) (1 - B x) : by {rw min_max}
  ... = max (Aᶜ x) (Bᶜ x) : by simp[has_compl.compl]
  ... = mem (Aᶜ ⊔ Bᶜ) x : by {sorry},
end


theorem distr_int (A B C : fuzzy_set u) : C ⊔ (A ⊓ B) = (C ⊔ A) ⊓ (C ⊔ B):=
begin
  exact sup_inf_left,
 end

theorem distr_uni (A B C : fuzzy_set u) : C ⊓ (A ⊔ B) = (C ⊓ A) ⊔ (C ⊓ B):=
begin
  exact inf_sup_left,
end

theorem int_big (A B C: fuzzy_set u) (h1 : C ⊆ A) (h2 : C ⊆ B) : C ⊆ (A ⊓ B):=
begin
  intro x,
  calc mem C x ≤ (min (A x) (B x)).val : by {simp, split, exact h1 x,exact h2 x}
  ... = mem (A ⊓ B) x : by simp[has_inf.inf],

end

theorem uni_small (A B C: fuzzy_set u) (h1 : A ⊆ C) (h2 : B ⊆ C) : (A ⊔ B) ⊆ C:=
begin
  intro x,
  calc mem (A ⊔ B) x = (max (A x) (B x)).val : by simp[has_sup.sup]
  ... ≤ mem C x : by {simp,split,exact h1 x, exact h2 x},
end


-- ℱ

-- Fuzzy sets defined in ℝⁿ

variables {n : ℕ}
local notation `E` := fin n → ℝ -- definition of Rⁿ in Lean 
#check (univ : set E)
#check (fin n)


example (X : fin 4 → ℝ ) (h2: (X 0) = 3) (h3: X 1 = 4) : X 0 + X 1 = 7:=
begin
  rw h2,rw h3,
  linarith,
end


def test3 : fuzzy_set (fin 3 → ℝ )  := λ x, ⟨ ((real.sin(x 0))^2+(real.sin(x 1))^2)/2 , by
begin
  split,
  nlinarith,
  have h1: ((real.sin(x 0))^2) ≤ 1,
  exact real.sin_sq_le_one (x 0),
  have h2: ((real.sin(x 1))^2) ≤ 1,
  exact real.sin_sq_le_one (x 1),
  calc (real.sin (x 0) ^ 2 + real.sin (x 1) ^ 2) / 2 ≤ (real.sin (x 0) ^ 2)/2 + (real.sin (x 1) ^ 2 )/2 : by linarith
  ...≤ 1/2 + 1/2 : by linarith[h1, h2]
  ... ≤ 1 : by linarith,
  --repeat {linarith},
end
⟩ 


example : has_dist.dist (1:ℝ) 2 = 1 :=
begin
  unfold dist,
  rw [show (1:ℝ)-2= - 1, by ring],
  simp,
end


example /-(𝕜 : Type)-/  : convex ℝ (Icc (0 : ℝ ) 1 : set ℝ )  :=
begin
  unfold convex,
  intros x y hx hy a b ha hb hab,
  cases hx,
  cases hy,
  split;
  {simp,
  nlinarith [ha, hb, hab],},
end

example {a b : ℝ} (x : Icc a b) : (x : ℝ) ≤ b :=
begin
rcases x with ⟨xv, ⟨x1, x2⟩⟩,
norm_num,
assumption,
end

example :  metric.bounded (Icc (0 : ℝ ) 1 : set ℝ )  :=
begin
  unfold metric.bounded,
  use 2,
  intros x hx y hy,
  unfold dist,
  unfold abs,
  simp,
  split;
  {linarith[hx.2,hx.1,hy.1,hy.2]},
end


-- Fuzzy convex and bounded sets, and separation theorems
@[simp]
def cla (X: fuzzy_set u) (α : ℝ) : set u := {x:u | (mem X x) > α }

@[simp]
def fuzzy_convex (A : fuzzy_set E) := ∀α, convex ℝ  (cla A α : set E)
@[simp]
def fuzzy_bounded (A : fuzzy_set E) := ∀α, metric.bounded (cla A α : set E)


#check (⬝ᵥ) --dot product
@[simp]
def hyperplane (v : E) (c : ℝ) : set E := { x : E | (x ⬝ᵥ v) = c}
def pos_hyperplane (v : E) (c : ℝ) : set E := { x : E | (x ⬝ᵥ v) ≥ c}
def neg_hyperplane (v : E) (c : ℝ) : set E := { x : E | (x ⬝ᵥ v) ≤ c}

theorem hyperplane_sep_classic (A B : set E) (h1: convex ℝ (A : set E) ∧ convex ℝ (B : set E) ) 
(h2: disjoint A B) : ∃ (v : E) (c :ℝ ), ∀ a ∈ A, ∀ b∈ B,  (a ⬝ᵥ v) ≥ c ∧ (b ⬝ᵥ v) ≤  c:=
begin
  sorry,
end

-- Supremum of the image of a fuzzy set
def fuzzy_sup (A : fuzzy_set u) := (Sup (range (mem A)) : ℝ )


theorem hyperplane_sep_fuzzy (A B : fuzzy_set E) (h1 : fuzzy_convex A ∧ fuzzy_convex B)
(h2 : fuzzy_bounded A ∧ fuzzy_bounded B) :  
(∃ (v : E) (c :ℝ ),  fuzzy_sup (A⊓B) = max (fuzzy_sup (A ⊓ (classical_to_fuzzy (pos_hyperplane v c))))
 (fuzzy_sup (B⊓(classical_to_fuzzy (neg_hyperplane v c))))) ∧ 
(∀ (v : E) (c :ℝ ), fuzzy_sup (A⊓B) ≤ max (fuzzy_sup (A ⊓ (classical_to_fuzzy (pos_hyperplane v c))))
 (fuzzy_sup (B⊓(classical_to_fuzzy (neg_hyperplane v c))))):=
begin
  sorry,
end



end fuzzy
