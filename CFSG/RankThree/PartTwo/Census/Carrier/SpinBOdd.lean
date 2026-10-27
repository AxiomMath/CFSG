module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOrth
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
import all TauCeti.Algebra.CharP.Frobenius.Fixed

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinB

open TauCeti CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.RankThree.PartTwo.Census.Carrier.SpinD (dcqEquivOfCentralKernel)

theorem two_ne_zero_frobeniusFixedSubfield {A : Type} [Field A] {p : ℕ} [Fact p.Prime]
    [CharP A p] (hp : p ≠ 2) (k : ℕ) : (2 : ↥(frobeniusFixedSubfield A p k)) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ↥(frobeniusFixedSubfield A p k)) = 0 := by rwa [Nat.cast_ofNat]
  rw [CharP.cast_eq_zero_iff _ p] at h'
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

def typeBGroupEquivStatedProj_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hp : q.p ≠ 2) (hr : 3 ≤ r) :
    ValidLieTypeIndex.Group ⟨.B r q, hv⟩ ≃*
      StatedProj (StatedOmega
        (StatedQuadOdd r ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩))) := by
  cases r with
  | zero => exact absurd hr (by omega)
  | succ m =>
    have h2 := two_ne_zero_frobeniusFixedSubfield
      (A := ValidLieTypeIndex.Closure ⟨.B (m + 1) q, hv⟩)
      (fun h => hp ((show ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩ = q.p from
        LieTypeIndex.characteristic_B (m + 1) q).symm.trans h))
      (ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩)
    have hperf := isPerfect_statedOmega_quadOdd (n := m + 1) h2 hr
    have hperf' : ⁅StatedOmega (StatedQuadOdd (m + 1) ↥(frobeniusFixedSubfield
          (ValidLieTypeIndex.Closure ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩))),
        StatedOmega (StatedQuadOdd (m + 1) ↥(frobeniusFixedSubfield
          (ValidLieTypeIndex.Closure ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩)))⁆ =
        StatedOmega (StatedQuadOdd (m + 1) ↥(frobeniusFixedSubfield
          (ValidLieTypeIndex.Closure ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩))) := by
      rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, Subgroup.map_top,
        Subgroup.range_subtype]
    let e1 : ValidLieTypeIndex.Group ⟨.B (m + 1) q, hv⟩ ≃* DerivedCentralQuotient
        ↥(TypeBSpinCarrier.points m ↥(frobeniusFixedSubring
          (ValidLieTypeIndex.Closure ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩))) :=
      DerivedCentralQuotient.congr (TypeBSpinCarrier.pointsMulEquivFixedSubgroupFrobenius m
        (ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩)
        (ValidLieTypeIndex.Closure ⟨.B (m + 1) q, hv⟩)).symm
    let e2 := dcqEquivOfCentralKernel (orthPointsB m _) (orthPointsB_ker_le_center m)
      (commutator_rangeB m h2 (by omega)) hperf'
    let e3 := QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadOdd (K := ↥(
      frobeniusFixedSubfield (ValidLieTypeIndex.Closure ⟨.B (m + 1) q, hv⟩)
        (ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩))) (n := m + 1) h2 hr)
    exact e1.trans (e2.trans e3)

end CFSG.RankThree.PartTwo.Census.Carrier.SpinB

namespace CFSG.RankThree.PartTwo.Census

open TauCeti CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_typeB_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hp : q.p ≠ 2) (hr : 3 ≤ r) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :
    StatedClassicalModel G .POmegaOdd r q.p q.exponent := by
  refine ⟨⟨q.prime_p, q.exponent_pos, hr, hp⟩,
    ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩), inferInstance,
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, ?_,
    ⟨e.trans (Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hp hr)⟩⟩
  rw [ValidLieTypeIndex.card_fixedField]
  simp [ValidLieTypeIndex.fieldOrder]

theorem catalogBridgeFor_B_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hr : 3 ≤ r) (hp : q.p ≠ 2) :
    CFSG.QuasithinUnique.B1.CatalogBridgeFor (.lie ⟨.B r q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, statedClassicalModel_typeB_odd r q hv hp hr e⟩))

theorem catalogBridgeFor_B (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hr : 3 ≤ r) : CFSG.QuasithinUnique.B1.CatalogBridgeFor (.lie ⟨.B r q, hv⟩) := by
  by_cases hp : q.p = 2
  · exact catalogBridgeFor_B_even r q hv hr hp
  · exact catalogBridgeFor_B_odd r q hv hr hp

end CFSG.RankThree.PartTwo.Census
