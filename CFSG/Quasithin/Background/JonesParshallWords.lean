module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.Quasithin.JonesParshall

open Matrix

section Words

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] {k : ℕ}

@[expose] def wordEval (gens : Fin k → G) : List (Fin k) → G
  | [] => 1
  | i :: w => gens i * wordEval gens w

@[expose] def foxEval (μ : G →* AddMonoid.End M) (gens : Fin k → G) (vals : Fin k → M) :
    List (Fin k) → M
  | [] => 0
  | i :: w => vals i + μ (gens i) (foxEval μ gens vals w)

theorem Z1A_wordEval {μ : G →* AddMonoid.End M} {f : G → M} (hf : f ∈ Z1A μ)
    (gens : Fin k → G) (w : List (Fin k)) :
    f (wordEval gens w) = foxEval μ gens (fun i => f (gens i)) w := by
  induction w with
  | nil => exact Z1A_one hf
  | cons i w ih =>
    change f (gens i * wordEval gens w) = f (gens i) + μ (gens i) (foxEval μ gens _ w)
    rw [hf, ih]

@[expose] def vanishSubgroup {μ : G →* AddMonoid.End M} {f : G → M} (hf : f ∈ Z1A μ) :
    Subgroup G where
  carrier := {g | f g = 0}
  mul_mem' {g h} hg hh := by
    change f (g * h) = 0
    rw [hf, show f g = 0 from hg, show f h = 0 from hh, map_zero, add_zero]
  one_mem' := Z1A_one hf
  inv_mem' {g} hg := by
    change f g⁻¹ = 0
    have h := hf g⁻¹ g
    rw [inv_mul_cancel, Z1A_one hf, show f g = 0 from hg, map_zero, add_zero] at h
    exact h.symm

theorem eq_zero_of_vanish_closure {μ : G →* AddMonoid.End M} {f : G → M} (hf : f ∈ Z1A μ)
    {S : Set G} (hS : Subgroup.closure S = ⊤) (h : ∀ s ∈ S, f s = 0) : f = 0 := by
  have hle : Subgroup.closure S ≤ vanishSubgroup hf := (Subgroup.closure_le _).mpr h
  rw [hS] at hle
  funext g
  exact hle (Subgroup.mem_top g)

theorem mem_Z1A_of_gens [Finite G] {μ : G →* AddMonoid.End M} {S : Set G}
    (hS : Subgroup.closure S = ⊤) {f : G → M} (h1 : f 1 = 0)
    (h : ∀ s ∈ S, ∀ g, f (s * g) = f s + μ s (f g)) : f ∈ Z1A μ := by
  let C : Submonoid G :=
    { carrier := {x | ∀ g, f (x * g) = f x + μ x (f g)}
      mul_mem' := fun {x y} hx hy g => by
        rw [mul_assoc, hx, hy, map_add, ← add_assoc, ← hx y, map_mul]
        rfl
      one_mem' := fun g => by rw [one_mul, h1, map_one, zero_add]; rfl }
  have hinv : ∀ x ∈ C, x⁻¹ ∈ C := fun x hx => by
    have hpos : 0 < orderOf x := orderOf_pos x
    have h' : x ^ (orderOf x - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [← eq_inv_of_mul_eq_one_left h']
    exact C.pow_mem hx _
  let C' : Subgroup G := { C with inv_mem' := fun {x} hx => hinv x hx }
  have hle : Subgroup.closure S ≤ C' := (Subgroup.closure_le _).mpr fun s hs => h s hs
  rw [hS] at hle
  intro g g'
  exact hle (Subgroup.mem_top g) g'

end Words

section Matrices

variable {n k : ℕ} {R : Type*} [CommRing R]

@[expose] def wordEvalM (mats : Fin k → Matrix (Fin n) (Fin n) R) : List (Fin k) →
    Matrix (Fin n) (Fin n) R
  | [] => 1
  | i :: w => mats i * wordEvalM mats w

@[expose] def foxEvalM (mats : Fin k → Matrix (Fin n) (Fin n) R) (vals : Fin k → Fin n → R) :
    List (Fin k) → Fin n → R
  | [] => 0
  | i :: w => vals i + mats i *ᵥ foxEvalM mats vals w

theorem coe_wordEval (gens : Fin k → SpecialLinearGroup (Fin n) R) (w : List (Fin k)) :
    ((wordEval gens w : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      wordEvalM (fun i => (gens i : Matrix (Fin n) (Fin n) R)) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change ((gens i : Matrix (Fin n) (Fin n) R) *
      ((wordEval gens w : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)) = _
    rw [ih]
    rfl

theorem foxEval_SL (gens : Fin k → SpecialLinearGroup (Fin n) R) (vals : Fin k → Fin n → R)
    (w : List (Fin k)) :
    foxEval (DistribMulAction.toAddMonoidEnd _ _) gens vals w =
      foxEvalM (fun i => (gens i : Matrix (Fin n) (Fin n) R)) vals w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change vals i + gens i • foxEval _ gens vals w = _
    rw [ih]
    rfl

end Matrices

theorem closure_eq_top_of_transvection {n : ℕ}
    {S : Set (SpecialLinearGroup (Fin n) (ZMod 2))}
    (h : ∀ t : TransvectionStruct (Fin n) (ZMod 2),
      t.toSpecialLinearGroup ∈ Subgroup.closure S) :
    Subgroup.closure S = ⊤ := by
  refine eq_top_iff.mpr fun M _ => ?_
  obtain ⟨L, L', D, hD, hM⟩ :=
    SpecialLinearGroup.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hD1 : (⟨diagonal D, hD⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) =
      (1 : SpecialLinearGroup (Fin n) (ZMod 2)) := by
    have hprod : ∏ i, D i = 1 := by rwa [det_diagonal] at hD
    have hDi : ∀ i, D i = 1 := fun i => by
      have hne : D i ≠ 0 := fun h0 => by
        rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at hprod
        exact zero_ne_one hprod
      have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact this _ hne
    ext i j
    change diagonal D i j = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j
    rw [show D = fun _ => 1 from funext hDi, diagonal_one]
  rw [hM, hD1, mul_one]
  refine Subgroup.mul_mem _ (Subgroup.list_prod_mem _ fun x hx => ?_)
    (Subgroup.list_prod_mem _ fun x hx => ?_)
  · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact h t
  · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact h t

end CFSG.Quasithin.JonesParshall
