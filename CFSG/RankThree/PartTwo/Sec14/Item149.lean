module

public import CFSG.RankThree.PartTwo.Sec14.Item14Statements
public import CFSG.RankThree.PartTwo.Sec14.Item145
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.Transfer.Yoshida
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.GH74.GLS

variable {G : Type*} [Group G]

theorem mem_oResidual_two_of_pow_three {D : Subgroup G} {x : G} (hx : x ∈ D) {k : ℕ}
    (hk : x ^ 3 ^ k = 1) : x ∈ inSubgroup (oResidual 2) D := by
  rw [inSubgroup_oResidual_eq_closure]
  refine Subgroup.subset_closure ⟨hx, ?_⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  rw [hj]
  exact Nat.Coprime.pow_left j (by norm_num)

variable [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem rank3II_14_9_of (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) (hnat : IsNaturalFamily A LB)
    (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥) (h147 : Item147 A LB)
    (h148 : Item148Normal A LB) : Item149 A LB := by
  intro Y hY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hdelta, -, hnorm⟩ := rank3II_14_5 hA hnat hbot hY.2
  set D := deltaZero A LB Y with hD
  set Δ := delta A LB Y with hΔ
  set C' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hC'
  set R := pPrimeCoreOf 3 Y with hR
  set X := inSubgroup (oResidual 2) D with hX
  have hDY : D ≤ Y := deltaZero_le Y
  have hXD : X ≤ D := inSubgroup_oResidual_le_self 2 D
  have hXY : X ≤ Y := hXD.trans hDY
  have hRY : R ≤ Y := pPrimeCoreOf_le 3 Y
  have hC'N : C' ≤ Subgroup.normalizer (D : Set G) :=
    (le_sup_right.trans hdelta.symm.le).trans hnorm
  have hcopC' : Nat.Coprime 3 (Nat.card C') :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 _)
  have h3Δ : ∀ x ∈ Δ, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ D := fun x hx k hk =>
    mem_left_of_pow_prime_pow Nat.prime_three hC'N hcopC' (hdelta ▸ hx) hk
  have e1 : oPrimeResidualOf 3 D = oPrimeResidualOf 3 Δ :=
    oPrimeResidualOf_eq_of_le (deltaZero_le_delta Y) h3Δ
  have e2 : oPrimeResidualOf 3 X = oPrimeResidualOf 3 D :=
    oPrimeResidualOf_eq_of_le hXD fun x hx k hk => mem_oResidual_two_of_pow_three hx hk
  have h7 : ⁅D, R⁆ ≤ Δ :=
    (h147 Y hY).trans (sSup_le fun _ hQ => le_delta hQ.1 (hQ.2.trans hRY))
  have hN'Δ : D ⊔ ⁅D, R⁆ ≤ Δ := sup_le (deltaZero_le_delta Y) h7
  have hRN' : R ≤ Subgroup.normalizer ((D ⊔ ⁅D, R⁆ : Subgroup G) : Set G) :=
    le_normalizer_sup_commutator D R
  have h3DR : ∀ x ∈ D ⊔ R, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ D := by
    intro x hx k hk
    have hx' : x ∈ (D ⊔ ⁅D, R⁆) ⊔ R := (sup_le_sup_right le_sup_left R) hx
    exact h3Δ x (hN'Δ (mem_left_of_pow_prime_pow Nat.prime_three hRN'
      (coprime_card_pPrimeCoreOf 3 Y) hx' hk)) k hk
  have e3 : oPrimeResidualOf 3 D = oPrimeResidualOf 3 (D ⊔ R) :=
    oPrimeResidualOf_eq_of_le le_sup_left h3DR
  have hYDR : Y ≤ Subgroup.normalizer ((D ⊔ R : Subgroup G) : Set G) :=
    (map_mk_normal_iff hDY).mp (h148 Y hY)
  have hYO : Y ≤ Subgroup.normalizer (oPrimeResidualOf 3 X : Set G) := by
    rw [e2, e3]
    exact le_normalizer_oPrimeResidualOf hYDR
  have hOY : oPrimeResidualOf 3 X ≤ Y := (oPrimeResidualOf_le_self 3 X).trans hXY
  set P := CFSG.Open.pCoreOf 2 Y with hP
  have hPY : P ≤ Y := Subgroup.map_subtype_le _
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hPR : P ≤ R := by
    refine le_pPrimeCoreOf hPY hYP ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hC2P : ⁅D, P⁆ ≤ P := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hDY.trans hYP)
  have hC2Δ : ⁅D, P⁆ ≤ Δ := (Subgroup.commutator_mono le_rfl hPR).trans h7
  have hC2N : ⁅D, P⁆ ≤ Subgroup.normalizer (D : Set G) := hC2Δ.trans hnorm
  have h2N'' : ∀ x ∈ D ⊔ ⁅D, P⁆, Nat.Coprime (orderOf x) 2 → x ∈ D := fun x hx hc =>
    mem_left_of_coprime_of_isPGroup Nat.prime_two hC2N (hP2.to_le hC2P) hx hc
  have e4 : X = inSubgroup (oResidual 2) (D ⊔ ⁅D, P⁆) :=
    inSubgroup_oResidual_eq_of_le le_sup_left h2N''
  have hPX : P ≤ Subgroup.normalizer (X : Set G) := by
    rw [e4]
    exact le_normalizer_inSubgroup_oResidual (le_normalizer_sup_commutator D P)
  have hPXn : (X.subgroupOf (P ⊔ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hPX Subgroup.le_normalizer)
  refine ⟨e1.symm.trans e2.symm, (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).mpr hYO,
    hPXn, fun hF => ?_⟩
  have hYc : IsCharacteristicP 2 ↥Y :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mpr hF
  have hPXY : P ⊔ X ≤ Y := sup_le hPY hXY
  have hPX2 : IsCharacteristicP 2 ↥((P ⊔ X).subgroupOf Y) := by
    refine isCharacteristicP_of_pCore_le _ hYc ?_
    intro y hy
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left ?_)
    rw [hP, CFSG.Open.pCoreOf]
    exact ⟨y, hy, rfl⟩
  have hPX2' : IsCharacteristicP 2 ↥(P ⊔ X) :=
    isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hPXY) hPX2
  have hX2 : IsCharacteristicP 2 ↥X :=
    isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe le_sup_right)
      (isCharacteristicP_of_normal (X.subgroupOf (P ⊔ X)) hPX2')
  have hXsub : X.subgroupOf D = oResidual 2 ↥D :=
    Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
  have hD2 : IsCharacteristicP 2 ↥D := by
    have hq : IsPGroup 2 (↥D ⧸ oResidual 2 ↥D) :=
      CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le (oResidual 2 ↥D) le_rfl
    have : (oResidual 2 ↥D).Normal := by
      rw [← hXsub]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXD).mpr
        (le_normalizer_inSubgroup_oResidual Subgroup.le_normalizer)
    refine isCharacteristicP_of_isPGroup_quotient (oResidual 2 ↥D) hq ?_
    rw [← hXsub]
    exact isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hXD).symm hX2
  exact ⟨(isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp hX2,
    (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp hD2⟩

end CFSG.RankThree.PartTwo.Sec14
