module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LieType.RootSystem.Form
public import CFSG.LieType.RootSystem.Positivity
public import CFSG.LinearAlgebra.IntegralCongruenceTorsionFree

public section

namespace CFSG.StandardType

open Module CFSG.LieType.RootSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem coxeterMatrix_eq_of_ggIntCartan {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ} (hFT : TauCeti.IsFiniteType C)
    (hC : GGIntCartan M C) : coxeterMatrix hFT = M := by
  ext i j
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  by_cases hij : i = j
  · subst hij
    rw [hC.1 i, M.diagonal i]
    norm_num
  · rcases hC.2 i j hij with ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, h1, -, -⟩ | ⟨hm, h1, -, -⟩
    · rw [hm, h1, h2]
      simp
    · rw [hm, h1, h2]
      norm_num
    · rw [hm, h1]
      simp
    · rw [hm, h1]
      simp

section Coord

variable {p : ℕ} {Γ : Type} [Fintype Γ] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

variable (p) in
noncomputable def ggCoord (h : Γ → V) (v : Γ → ℤ) : V :=
  ∑ j, ((v j : ℤ) : ZMod p) • h j

theorem ggCoord_sub (h : Γ → V) (v w : Γ → ℤ) :
    ggCoord p h (v - w) = ggCoord p h v - ggCoord p h w := by
  simp only [ggCoord, Pi.sub_apply, Int.cast_sub, sub_smul, Finset.sum_sub_distrib]

theorem ggCoord_reflection [DecidableEq Γ] {C : Matrix Γ Γ ℤ} {h : Γ → V}
    {α : Γ → Module.Dual (ZMod p) V} (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p)) (i : Γ) (v : Γ → ℤ) :
    ggCoord p h (CFSG.LieType.RootSystem.reflection C i v) =
      Module.reflection (hα i) (ggCoord p h v) := by
  rw [CFSG.LieType.RootSystem.reflection_apply, Module.reflection_apply, ggCoord_sub]
  have hsum : α i (ggCoord p h v) = ((∑ j, C i j * v j : ℤ) : ZMod p) := by
    simp only [ggCoord, map_sum, map_smul, smul_eq_mul, hP]
    push_cast
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hsum]
  congr 1
  simp only [ggCoord, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

end Coord

section Faithful

variable {p : ℕ} {Γ : Type} [Fintype Γ] [DecidableEq Γ] {C : Matrix Γ Γ ℤ}
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {h : Γ → V} {α : Γ → Module.Dual (ZMod p) V} (hα : ∀ i, α i (h i) = 2)
  (hP : ∀ i j, α i (h j) = (C i j : ZMod p))

include hP in
theorem ggCoord_weylAction (hFT : TauCeti.IsFiniteType C)
    (hL : (coxeterMatrix hFT).IsLiftable fun i => Module.reflection (hα i))
    (w : (coxeterMatrix hFT).Group) (v : Γ → ℤ) :
    ggCoord p h (weylAction hFT w v) =
      (coxeterMatrix hFT).toCoxeterSystem.lift ⟨fun i => Module.reflection (hα i), hL⟩ w
        (ggCoord p h v) := by
  induction w using (coxeterMatrix hFT).toCoxeterSystem.simple_induction_left generalizing v with
  | one => simp
  | mul_simple_left w i ih =>
    rw [weylAction_mul_apply, weylAction_simple, ggCoord_reflection hα hP, ih, map_mul,
      CoxeterSystem.lift_apply_simple, LinearEquiv.mul_apply]

theorem ggCartanFaithful_of_isFiniteType [Fact p.Prime] (hp2 : p ≠ 2) {M : CoxeterMatrix Γ}
    (hFT : TauCeti.IsFiniteType C) (hC : GGIntCartan M C) (hind : LinearIndependent (ZMod p) h) :
    Function.Injective (M.toCoxeterSystem.lift
      ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩) := by
  have hM : coxeterMatrix hFT = M := coxeterMatrix_eq_of_ggIntCartan hFT hC
  subst hM
  have : Finite (coxeterMatrix hFT).Group := finite_group hFT
  rw [injective_iff_map_eq_one]
  intro w hw
  apply weylAction_injective hFT
  rw [map_one]
  set X := LinearMap.toMatrixAlgEquiv' (weylAction hFT w) with hXdef
  have hk : orderOf w ≠ 0 := (orderOf_pos w).ne'
  have hX : X ^ orderOf w = 1 := by
    rw [hXdef, ← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
  have hmod : ∀ i j, (p : ℤ) ∣ (X - 1) i j := by
    intro i j
    have h0 : ggCoord p h (weylAction hFT w (Pi.single j 1) - Pi.single j 1) = 0 := by
      rw [ggCoord_sub,
        ggCoord_weylAction hα hP hFT (isLiftable_reflection_of_intCartan hC h α hα hP), hw]
      simp
    have hz := (Fintype.linearIndependent_iff.mp hind)
      (fun k => (((weylAction hFT w (Pi.single j 1) - Pi.single j 1 : Γ → ℤ) k : ℤ) : ZMod p))
      h0 i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    rw [Matrix.sub_apply, hXdef, LinearMap.toMatrixAlgEquiv'_apply, Matrix.one_apply]
    convert hz using 2
    simp [Pi.single_apply]
  have hX1 := int_matrix_eq_one_of_pow_eq_one hp2 hk hX hmod
  exact (LinearMap.toMatrixAlgEquiv').injective (by rw [← hXdef, hX1, map_one])

end Faithful

end CFSG.StandardType
