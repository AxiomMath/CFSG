module

public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools
public import CFSG.RankThree.PartTwo.Sec15.Item1423ProofLocal
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec6 CFSG.RankThree.PartTwo.Sec15
open scoped commutatorElement

@[expose] def Step143BalanceSz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ B : Subgroup G, IsHyperplane A B → a ∈ B →
        ∀ J ∈ thetaComponentsIn (pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))),
          ¬ A ≤ thetaQuotCentralizer J →
            J ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_centralizer_of_isHyperplane {A B : Subgroup G} (hAab : IsMulCommutative A)
    (hB : IsHyperplane A B) : A ≤ Subgroup.centralizer (B : Set G) :=
  (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab).trans (Subgroup.centralizer_le hB.1)

theorem commutator_le_of_balanceSz (h45 : Sec4.Item4_5)
    (hKPSz : KFacts.KPSz) (hSz : Step143BalanceSz) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hΩ : Subgroup.zpowers a ∉ omegaA A) {B : Subgroup G} (hB : IsHyperplane A B) (haB : a ∈ B)
    (hM1 : pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ≠ ⊥) :
    ⁅pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)), A⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have hD := h.toSec13Data
  have hA := h.isE27'
  have hAab : IsMulCommutative A := hA.1.1
  set M := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hM
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  set θM := inSubgroup (aschbacherSolvableCore 3) M with hθM
  set θB := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)) with hθB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM3 : ¬ 3 ∣ Nat.card M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (coprime_card_pPrimeCoreOf 3 _)
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := le_centralizer_of_isHyperplane hAab hB
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := hAB.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hCBa : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := hAB.trans hCBa
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := (pPrimeCoreOf_le 3 _).trans hCBa
  have hON : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hA3 : ∀ α ∈ A, α ^ 3 = 1 := fun α hα => hD.isElemAbelian.2 α hα
  have hMA : M ⊔ A ≠ ⊤ := by
    have : IsSimpleGroup G := h.isSimpleGroup
    intro htop
    have hMn : M.Normal := Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (htop ▸ sup_le Subgroup.le_normalizer hAM))
    rcases hMn.eq_bot_or_eq_top with hb | ht
    · exact hM1 hb
    · apply hM3
      rw [ht, Subgroup.card_top]
      exact (show 3 ∣ 27 by norm_num).trans (hD.card_eq ▸ Subgroup.card_subgroup_dvd_card A)
  have hM4 : SectionFourHyp ↥(M ⊔ A) := h.toTheoremFourHyp.sectionFourHyp hMA
  have hMnorm : (M.subgroupOf (M ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hAM)
  have hAJ : ∀ J ∈ thetaComponentsIn M, A ≤ Subgroup.normalizer (J : Set G) := fun J hJ =>
    le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hM4 le_sup_right hD.isElemAbelian
      ⟨3, le_rfl, by rw [hD.card_eq]; norm_num⟩ J
      (Proof1423.mem_thetaComponentsIn_of_isSubnormal hJ le_sup_left hMnorm.isSubnormal)
  have hout : ∀ J ∈ thetaComponentsIn M,
      commutator (MulAut (J ⧸ aschbacherSolvableCore 3 J)) ≤
        (MulAut.conj : (J ⧸ aschbacherSolvableCore 3 J) →* _).range := fun J hJ => by
    obtain ⟨f, hf⟩ := Proof1423.suzukiModel_thetaQuot hKPSz hM4 le_sup_left hM3 hJ
    exact KFacts.commutator_le_inner_of_suzukiModel hf
  have hcomm := BalTools.commutator_le_sup_theta hM3 hAM hA3 hAJ hout
  have hstar := starConditionAt_of_not_mem_omegaA hA.1 ha ha1 hΩ
  have hθBO : ⁅θB, A⁆ ≤ O :=
    (commutator_theta_le_of_starConditionAt hA ha ha1 hstar hB haB).trans
      (inSubgroup_theta_le_pPrimeCoreOf _)
  have hθMB : θM ≤ θB := by
    have hθMM : θM ≤ M := Subgroup.map_subtype_le _
    refine le_theta_of_normal (hθMM.trans (pPrimeCoreOf_le 3 _)) ?_
      (theta_solvable_and_not_dvd M).1 (theta_solvable_and_not_dvd M).2
    exact (le_normalizer_pPrimeCoreOf 3 _).trans (normalizer_le_normalizer_theta M)
  have hθMO : ⁅θM, A⁆ ≤ O := (Subgroup.commutator_mono hθMB le_rfl).trans hθBO
  have hJO : ∀ J ∈ thetaComponentsIn M, ⁅J, A⁆ ≤ O := by
    intro J hJ
    by_cases hJC : A ≤ thetaQuotCentralizer J
    · have hJθ : ⁅J, A⁆ ≤ inSubgroup (aschbacherSolvableCore 3) J :=
        (commutator_le_theta_iff (hAJ J hJ)).mpr hJC
      have hθJ : inSubgroup (aschbacherSolvableCore 3) J ≤ θM := by
        rw [theta_eq_inf_of_mem_thetaComponentsIn hJ]
        exact inf_le_right
      have hJ3 : ¬ 3 ∣ Nat.card J := fun h3 =>
        hM3 (h3.trans (Subgroup.card_dvd_of_le (le_of_mem_thetaComponentsIn hJ)))
      rw [← CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
        Nat.prime_three A J hA.isPGroup hJ3 (hAJ J hJ)]
      exact (Subgroup.commutator_mono (hJθ.trans hθJ) le_rfl).trans hθMO
    · have hJa := hSz G A c L h a ha ha1 hΩ B hB haB J hJ hJC
      exact (Subgroup.commutator_mono hJa le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hAa.trans hON))
  have hgen : ∀ X : Subgroup G, X ≤ M → ⁅X, A⁆ ≤ O → X ≤ commutatorInSubgroup A O := by
    intro X hXM hXA x hx
    refine mem_commutatorInSubgroup.mpr ⟨hON (hMa (hXM hx)), fun α hα => ?_⟩
    rw [← commutatorElement_inv]
    exact inv_mem (hXA (Subgroup.commutator_mem_commutator hx hα))
  have hXle : (⨆ J ∈ thetaComponentsIn M, J) ⊔ θM ≤ commutatorInSubgroup A O := by
    refine sup_le (iSup₂_le fun J hJ => hgen J (le_of_mem_thetaComponentsIn hJ) (hJO J hJ)) ?_
    exact hgen θM (Subgroup.map_subtype_le _) hθMO
  have hXO : ⁅(⨆ J ∈ thetaComponentsIn M, J) ⊔ θM, A⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro x hx α hα
    rw [← commutatorElement_inv]
    exact inv_mem ((mem_commutatorInSubgroup.mp (hXle hx)).2 α hα)
  rw [← CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three A M hA.isPGroup hM3 hAM]
  exact (Subgroup.commutator_mono hcomm le_rfl).trans hXO

theorem step143Balance_of (h45 : Sec4.Item4_5)
    (hKPSz : KFacts.KPSz) (hSz : Step143BalanceSz) : Step143Balance := by
  intro G _ _ A c L h a ha ha1 hΩ B hB haB hns
  refine commutator_le_of_balanceSz h45 hKPSz hSz h ha ha1 hΩ hB haB fun hbot => hns ?_
  rw [hbot]
  infer_instance

end CFSG.RankThree.PartTwo.Sec14
