module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived
public import CFSG.LocalAnalysis.StandardType.ZS.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol
public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarConnGen
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarLinData
public import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import CFSG.LocalAnalysis.StandardType.ZS.OrthOrderBound


attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.QTwo

open TauCeti QuadraticMap
open scoped commutatorElement

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W]

theorem qTwoGlobIdx_two_mul_card_le_card_of_ne {G : Type} [Group G] [Finite G]
    {H A : Subgroup G} (hHA : H ≤ A) (hne : A ≠ H) :
    2 * Nat.card H ≤ Nat.card A := by
  have hcard : H.relIndex A * Nat.card H = Nat.card A := by
    simpa only [inf_of_le_left hHA] using Subgroup.relIndex_mul_card H A
  have h1 : H.relIndex A ≠ 1 := by
    intro h
    exact hne (le_antisymm ((Subgroup.relIndex_eq_one).mp h) hHA)
  have h0 : H.relIndex A ≠ 0 := by
    haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
    haveI : H.IsFiniteRelIndex A := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  have h2 : 2 ≤ H.relIndex A := by omega
  calc 2 * Nat.card H ≤ H.relIndex A * Nat.card H := Nat.mul_le_mul_right _ h2
    _ = Nat.card A := hcard

theorem qTwoGlobIdx_refl_notMem_commutator {Q : QuadraticForm (ZMod 3) W}
    [FiniteDimensional (ZMod 3) W] {t : W ≃ₗ[ZMod 3] W} (ht : ZS.IsRefl 3 t) :
    t ∉ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  intro hmem
  have hker : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      (LinearEquiv.det : (W ≃ₗ[ZMod 3] W) →* (ZMod 3)ˣ).ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have h1 : LinearEquiv.det t = 1 := MonoidHom.mem_ker.mp (hker hmem)
  have h2 : LinearEquiv.det t = -1 := ZS.det_eq_neg_one_of_isRefl (p := 3) (by norm_num) ht
  rw [h2] at h1
  exact (by decide : (-1 : (ZMod 3)ˣ) ≠ 1) h1

theorem qTwoGlobIdx_four_mul_card {Q : QuadraticForm (ZMod 3) W}
    [FiniteDimensional (ZMod 3) W] (hQ : (qTwoPolar Q).Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) W) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) ≤
      4 * Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  classical
  let O : Subgroup (W ≃ₗ[ZMod 3] W) := TauCeti.QuadraticMap.orthogonalGroup Q
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have hidx : (commutator O).index ≤ 4 :=
    CFSG.OddStandard.SmallF3.Omega.index_commutator_le_four (V := W) (Q := Q) hQ' h2
  have hcard : Nat.card ↥O = (commutator O).index * Nat.card ↥(commutator O) :=
    (Subgroup.index_mul_card (commutator O)).symm
  have hmap : ⁅O, O⁆ = (commutator O).map O.subtype :=
    (Subgroup.map_subtype_commutator O).symm
  calc Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = Nat.card ↥O := rfl
    _ = (commutator O).index * Nat.card ↥(commutator O) := hcard
    _ ≤ 4 * Nat.card ↥(commutator O) := Nat.mul_le_mul_right _ hidx
    _ = 4 * Nat.card ↥⁅O, O⁆ := by
        rw [hmap, Subgroup.card_map_of_injective O.subtype_injective]

theorem qTwoGlobIdx_orthogonal_le_two_mul_card {Q : QuadraticForm (ZMod 3) W}
    [FiniteDimensional (ZMod 3) W] (hQ : (qTwoPolar Q).Nondegenerate)
    (hdim : 5 ≤ Module.finrank (ZMod 3) W)
    (A : Subgroup (W ≃ₗ[ZMod 3] W))
    (hA : ∀ g h : W ≃ₗ[ZMod 3] W, (∀ w, Q (g w) = Q w) → (∀ w, Q (h w) = Q w) →
      g * h * g⁻¹ * h⁻¹ ∈ A)
    (hrefl : ∃ t ∈ A, ZS.IsRefl 3 t) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ 2 * Nat.card A := by
  classical
  let O : Subgroup (W ≃ₗ[ZMod 3] W) := TauCeti.QuadraticMap.orthogonalGroup Q
  haveI : Finite W := Module.finite_of_finite (ZMod 3)
  haveI : Finite (W ≃ₗ[ZMod 3] W) :=
    Finite.of_injective (fun g : W ≃ₗ[ZMod 3] W => (g : W → W))
      (fun g h hgh => LinearEquiv.ext (congrFun hgh))
  have hΩA : ⁅O, O⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    exact hA g h (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg)
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hh)
  have hne : A ≠ ⁅O, O⁆ := by
    obtain ⟨t, htA, ht⟩ := hrefl
    intro hEq
    exact qTwoGlobIdx_refl_notMem_commutator (Q := Q) ht (hEq ▸ htA)
  have hstep : 2 * Nat.card ↥⁅O, O⁆ ≤ Nat.card ↥A :=
    qTwoGlobIdx_two_mul_card_le_card_of_ne hΩA hne
  calc Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ 4 * Nat.card ↥⁅O, O⁆ :=
        qTwoGlobIdx_four_mul_card hQ (by omega)
    _ = 2 * (2 * Nat.card ↥⁅O, O⁆) := by ring
    _ ≤ 2 * Nat.card ↥A := Nat.mul_le_mul_left 2 hstep

theorem qTwoGlobIdx_degSix_card_ge {Q : QuadraticForm (ZMod 3) W}
    [FiniteDimensional (ZMod 3) W] (hQ : (qTwoPolar Q).Nondegenerate)
    (h6 : Module.finrank (ZMod 3) W = 6) :
    24261120 ≤ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hdim : Module.finrank (ZMod 3) W = 2 * (2 + 1) := by omega
  by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType Q
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3)
        (V := W) hQ (m := 2) hdim (ε := 1) (Or.inl ⟨rfl, hp⟩)
    have hv : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 24261120 := by
      rw [h]
      norm_num [Nat.card_zmod, Finset.prod_Icc_succ_top]
    have h2 : (24261120 : ℤ) ≤ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) := by
      rw [hv]
    exact_mod_cast h2
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3)
        (V := W) hQ (m := 2) hdim (ε := -1) (Or.inr ⟨rfl, hp⟩)
    have hv : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 26127360 := by
      rw [h]
      norm_num [Nat.card_zmod, Finset.prod_Icc_succ_top]
    have h2 : (24261120 : ℤ) ≤ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) := by
      rw [hv]; norm_num
    exact_mod_cast h2

theorem qTwoGlobIdx_degSix_false {Q : QuadraticForm (ZMod 3) W}
    [FiniteDimensional (ZMod 3) W] (hQ : (qTwoPolar Q).Nondegenerate)
    (h6 : Module.finrank (ZMod 3) W = 6)
    (A : Subgroup (W ≃ₗ[ZMod 3] W))
    (hA : ∀ g h : W ≃ₗ[ZMod 3] W, (∀ w, Q (g w) = Q w) → (∀ w, Q (h w) = Q w) →
      g * h * g⁻¹ * h⁻¹ ∈ A)
    (hrefl : ∃ t ∈ A, ZS.IsRefl 3 t)
    (hbound : Nat.card A ≤ 3 ^ 6 * (2 * Nat.factorial 7)) : False := by
  have hle := qTwoGlobIdx_orthogonal_le_two_mul_card hQ (by omega) A hA hrefl
  have hge := qTwoGlobIdx_degSix_card_ge hQ h6
  have hb : 3 ^ 6 * (2 * Nat.factorial 7) = 7348320 := by norm_num
  rw [hb] at hbound
  omega

end CFSG.StandardType.QTwo

attribute [instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end
