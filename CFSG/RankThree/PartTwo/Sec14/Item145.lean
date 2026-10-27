module

public import CFSG.RankThree.PartTwo.Sec14.Closure
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree.PartTwo CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

omit [Finite G] in
theorem centralizer_le_normalizer_pPrimeCoreOf {B : Subgroup G} (hBA : B ≤ A) :
    Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) : Set G) :=
  (Subgroup.centralizer_le hBA).trans (le_normalizer_pPrimeCoreOf 3 _)

theorem le_pPrimeCoreOf_centralizer (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥)
    {Q : Subgroup G} (hQ : Q ∈ scriptQ A LB) (hQA : Q ≤ Subgroup.centralizer (A : Set G)) :
    Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B, hB, hLB⟩ := hbot
  set OB := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hOB
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOA
  have hCAB : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le hB.1
  have hQB : Q ≤ OB ⊔ OA := by
    have h := hQ.2 B hB
    rw [qBound, hLB, sup_bot_eq, inf_eq_left.mpr (hQA.trans hCAB)] at h
    exact h
  have hOAN : OA ≤ Subgroup.normalizer (OB : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hB.1)
  have hK : OB ⊓ Subgroup.centralizer (A : Set G) ≤ OA := by
    refine le_pPrimeCoreOf inf_le_right ?_ ?_
    · exact CFSG.RankThree.PartTwo.Late.le_normalizer_inf
        (centralizer_le_normalizer_pPrimeCoreOf hB.1) Subgroup.le_normalizer
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 _)
  intro x hx
  have hx' : x ∈ ((OB : Set G) * (OA : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left OB OA hOAN]
    exact hQB hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  have hzA : z ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hz
  have hyA : y ∈ Subgroup.centralizer (A : Set G) := by
    have h := mul_mem (hQA hx) (inv_mem hzA)
    rwa [mul_inv_cancel_right] at h
  exact mul_mem (hK ⟨hy, hyA⟩) hz

theorem pPrimeCoreOf_centralizer_inf_mem_scriptQ (hA : IsMulCommutative A) {Y : Subgroup G}
    (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y ∈ scriptQ A LB := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA
  refine mem_scriptQ_iff.mpr ⟨?_, ?_, fun B _ => ?_⟩
  · refine (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr fun h => ?_
    have h3 := h.trans (Subgroup.card_dvd_of_le inf_le_left)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) h3
  · exact CFSG.RankThree.PartTwo.Late.le_normalizer_inf
      (hAC.trans (le_normalizer_pPrimeCoreOf 3 _)) hY
  · exact inf_le_left.trans (inf_le_left.trans (le_sup_right.trans le_sup_left))

theorem delta_inf_centralizer (hA : IsMulCommutative A) (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥)
    {Y : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    delta A LB (Y ⊓ Subgroup.centralizer (A : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y := by
  refine le_antisymm (sSup_le fun Q hQ => le_inf ?_ (hQ.2.trans inf_le_left)) ?_
  · exact le_pPrimeCoreOf_centralizer hbot hQ.1 (hQ.2.trans inf_le_right)
  · refine le_delta (pPrimeCoreOf_centralizer_inf_mem_scriptQ hA hY) (le_inf inf_le_right ?_)
    exact inf_le_left.trans (pPrimeCoreOf_le 3 _)

theorem rank3II_14_5 (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) (hnat : IsNaturalFamily A LB)
    (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥) {Y : Subgroup G}
    (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    delta A LB Y = deltaZero A LB Y ⊔ (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y) ∧
      deltaZero A LB Y = ⁅delta A LB Y, A⁆ ∧
      delta A LB Y ≤ Subgroup.normalizer (deltaZero A LB Y : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hAab : IsMulCommutative A := hA.1.1
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab
  set C' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hC'
  have hC'q : C' ∈ scriptQ A LB := pPrimeCoreOf_centralizer_inf_mem_scriptQ hAab hY
  have hC'N : C' ≤ Subgroup.normalizer (deltaZero A LB Y : Set G) := fun w hw =>
    mem_normalizer_deltaZero hnat
      (Subgroup.centralizer_le_normalizer _ (pPrimeCoreOf_le 3 _ (Subgroup.mem_inf.mp hw).1))
      (Subgroup.le_normalizer (Subgroup.mem_inf.mp hw).2)
  have hAN : A ≤ Subgroup.normalizer (deltaZero A LB Y : Set G) := fun a ha =>
    mem_normalizer_deltaZero hnat (Subgroup.le_normalizer ha) (hY ha)
  have hdelta : delta A LB Y = deltaZero A LB Y ⊔ C' := by
    refine le_antisymm (sSup_le fun Q hQ => ?_)
      (sup_le (deltaZero_le_delta Y) (le_delta hC'q inf_le_right))
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
    have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.1.1.2.2
    have hfac :=
      CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
        3 Nat.prime_three A Q hA3 hQ3 hAQ
    have hcommQ : ⁅Q, A⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp hAQ
    have hAcomm : A ≤ Subgroup.normalizer ((⁅Q, A⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.normalizer_commutator_ge_left A Q
    have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent
      3 Nat.prime_three A Q hA3 hQ3 hAQ
    have h0 : ⁅Q, A⁆ ∈ scriptQZero A LB := ⟨mem_scriptQ_of_le hQ.1 hcommQ hAcomm, hidem.symm⟩
    have hQA : Q ⊓ Subgroup.centralizer (A : Set G) ∈ scriptQ A LB :=
      mem_scriptQ_of_le hQ.1 inf_le_left
        (CFSG.RankThree.PartTwo.Late.le_normalizer_inf hAQ (hAC.trans Subgroup.le_normalizer))
    rw [hfac]
    exact sup_le_sup (le_deltaZero h0 (hcommQ.trans hQ.2))
      (le_inf (le_pPrimeCoreOf_centralizer hbot hQA inf_le_right) (inf_le_left.trans hQ.2))
  refine ⟨hdelta, le_antisymm (sSup_le fun Q hQ => ?_) ?_, ?_⟩
  · calc Q = ⁅Q, A⁆ := hQ.1.2
      _ ≤ ⁅delta A LB Y, A⁆ := Subgroup.commutator_mono (le_delta hQ.1.1 hQ.2) le_rfl
  · rw [hdelta, Subgroup.commutator_le]
    intro h hh a ha
    have hh' : h ∈ ((deltaZero A LB Y : Set G) * (C' : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hC'N]
      exact hh
    obtain ⟨d, hd, c, hc, rfl⟩ := hh'
    have hcA : c ∈ Subgroup.centralizer (A : Set G) :=
      pPrimeCoreOf_le 3 _ (Subgroup.mem_inf.mp hc).1
    have hca : c * a = a * c := (Subgroup.mem_centralizer_iff.mp hcA a ha).symm
    have hkey : ⁅d * c, a⁆ = d * (a * d⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      calc d * c * a * (d * c)⁻¹ * a⁻¹ = d * (c * a) * c⁻¹ * d⁻¹ * a⁻¹ := by group
        _ = d * (a * c) * c⁻¹ * d⁻¹ * a⁻¹ := by rw [hca]
        _ = d * (a * d⁻¹ * a⁻¹) := by group
    rw [hkey]
    exact mul_mem hd ((Subgroup.mem_normalizer_iff.mp (hAN ha) d⁻¹).mp (inv_mem hd))
  · rw [hdelta]
    exact sup_le Subgroup.le_normalizer hC'N

end CFSG.RankThree.PartTwo.Sec14
