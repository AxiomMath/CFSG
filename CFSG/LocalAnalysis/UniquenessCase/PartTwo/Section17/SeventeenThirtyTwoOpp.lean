module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySevenE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SylowCentralOuter
public import CFSG.GroupTheory.PRankCommutingSup
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma5_2
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.ClassicalInvolution.Q3.Q3SSylow
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DExt
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.GroupTheory.SylowNormalizedByPGroup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12b
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22x
public import CFSG.Quasithin.Background.B69E22Pre
public import CFSG.Quasithin.Background.B69Final
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.Quasithin.Background.B69Lift
public import CFSG.Quasithin.Background.B69Mod
public import CFSG.Quasithin.Background.B69Simple
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15Proof
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpTrans
public import CFSG.RankThree.PartOne.N1322.Statements
public import CFSG.RankThree.PartOne.S11d.ThreeCompEasy
public import CFSG.RankThree.PartOne.S12.Sec1322Inputs
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
public import CFSG.RankThree.ThinCatalog.OuterThreeFree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_opp_of_is3D4 {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) (hsimple : IsSimpleGroup (Bar2 L)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hout : ¬ r ∣ Nat.card (Outer (Bar2 L)))
    {R : Subgroup G} (hRL : R ≤ L) (hRel : IsElemAbelian r R) (hRcard : Nat.card R = r ^ 2)
    (hrM : CFSG.Open.pRank r D.M ≤ 2) : L = Opp r D.M := by
  classical
  let C : Subgroup G := F08.CentOverO2 D.M L
  let Q : Subgroup G := pCoreOf 2 L
  have hLM : L ≤ D.M := hL.1.le
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hr1 : 1 < r := hr.one_lt
  have hRpg : IsPGroup r R := hRel.isPGroup
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hQL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hQnormM : D.M ≤ Subgroup.normalizer (Q : Set G) :=
    hMN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hnotrQ : ¬ r ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    intro hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.center_eq_bot_of_quasisimple_simple
      hL.2.2 hsimple
  have hC_le_M : C ≤ D.M := fun x hx => (mem_centOverO2_iff.mp hx).1
  have hCr : ¬ r ∣ Nat.card C := by
    intro hdvd
    obtain ⟨z, hzord⟩ := @exists_prime_orderOf_dvd_card' ↥C _ _ r ⟨hr⟩ hdvd
    have hzC : (z : G) ∈ C := z.2
    have hzM : (z : G) ∈ D.M := hC_le_M hzC
    have hzordG : orderOf (z : G) = r := (Subgroup.orderOf_coe z).trans hzord
    have hcentz : ∀ l ∈ L, (z : G) * l * (z : G)⁻¹ * l⁻¹ ∈ Q :=
      (mem_centOverO2_iff.mp hzC).2
    have hBL : Subgroup.zpowers (z : G) ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyz : y ∈ Subgroup.zpowers (z : G) := hy.1
      have hyL : y ∈ L := hy.2
      have hyC : y ∈ C := (Subgroup.zpowers_le.mpr hzC) hyz
      have hcenty : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Q := (mem_centOverO2_iff.mp hyC).2
      have hyQ : y ∈ Q := mem_pCoreOf_of_centralizesBar hyL hcenty hZ
      obtain ⟨k, hk⟩ := hQ2.exists_card_eq
      have hdvd_r : orderOf y ∣ r := by
        rw [← hzordG]
        exact orderOf_dvd_of_mem_zpowers hyz
      have hdvd_2 : orderOf y ∣ 2 ^ k := by
        have h := Subgroup.orderOf_dvd_natCard Q hyQ
        rwa [hk] at h
      have hnot2 : ¬ r ∣ 2 ^ k := hk ▸ hnotrQ
      have hcop : Nat.Coprime (2 ^ k) r := (hr.coprime_iff_not_dvd.mpr hnot2).symm
      have h1 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd_2 hdvd_r
      rw [Subgroup.mem_bot]
      exact orderOf_eq_one_iff.mp h1
    have hcomm : ⁅R, Subgroup.zpowers (z : G)⁆ ≤ Q := by
      refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem ?_ ?_
      · exact hQnormM hzM
      · intro a ha
        have hza : (z : G) * a * (z : G)⁻¹ * a⁻¹ ∈ Q := hcentz a (hRL ha)
        rw [show ⁅a, (z : G)⁆ = ((z : G) * a * (z : G)⁻¹ * a⁻¹)⁻¹ from by
          rw [commutatorElement_def]
          group]
        exact Q.inv_mem hza
    have hRN : R ≤ Subgroup.normalizer (Q : Set G) :=
      hRL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    have hBN : Subgroup.zpowers (z : G) ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.zpowers_le.mpr (hQnormM hzM)
    have hBelab : IsElemAbelian r (Subgroup.zpowers (z : G)) :=
      isElemAbelian_zpowers (p := r) (by rw [← hzordG]; exact pow_orderOf_eq_one (z : G))
    have hBpg : IsPGroup r (Subgroup.zpowers (z : G)) := hBelab.isPGroup
    obtain ⟨n, hnQ, hFn⟩ :=
      @CFSG.GroupTheory.exists_map_conj_le_centralizer_of_commutator_le G _ _ r r ⟨hr⟩ ⟨hr⟩
        Q R (Subgroup.zpowers (z : G)) hRN hBN hRpg hBpg hnotrQ hnotrQ hcomm
    let F : Subgroup G := R.map (MulAut.conj n).toMonoidHom
    have hFcent : F ≤ Subgroup.centralizer (Subgroup.zpowers (z : G) : Set G) := hFn
    have hFL : F ≤ L := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      change MulAut.conj n a ∈ L
      rw [MulAut.conj_apply]
      exact L.mul_mem (L.mul_mem (hQL hnQ) (hRL ha)) (L.inv_mem (hQL hnQ))
    have hFcard : Nat.card F = r ^ 2 := by
      show Nat.card (R.map (MulAut.conj n).toMonoidHom) = r ^ 2
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hRcard]
    have hFelab : IsElemAbelian r F := hRel.map (MulAut.conj n).toMonoidHom
    have hBcard : Nat.card (Subgroup.zpowers (z : G)) = r := by
      rw [Nat.card_zpowers, hzordG]
    have hpF : CFSG.Open.pRank r F = 2 := by
      have h := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hFelab
      exact Nat.pow_right_injective hr.one_lt (h.symm.trans hFcard)
    have hpB : CFSG.Open.pRank r (Subgroup.zpowers (z : G)) = 1 := by
      have h := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hBelab
      rw [hBcard] at h
      have h' : r ^ CFSG.Open.pRank r (Subgroup.zpowers (z : G)) = r ^ 1 := by
        rw [pow_one]
        exact h.symm
      exact Nat.pow_right_injective hr.one_lt h'
    have hFB : F ⊓ Subgroup.zpowers (z : G) = (⊥ : Subgroup G) := by
      have hle : F ⊓ Subgroup.zpowers (z : G) ≤ L ⊓ Subgroup.zpowers (z : G) :=
        inf_le_inf_right _ hFL
      rw [inf_comm L, hBL] at hle
      exact le_antisymm hle bot_le
    have hnotdvd : ¬ r ∣ Nat.card ↥(F ⊓ Subgroup.zpowers (z : G)) := by
      have hcard : Nat.card ↥(F ⊓ Subgroup.zpowers (z : G)) = 1 :=
        (Subgroup.eq_bot_iff_card (F ⊓ Subgroup.zpowers (z : G))).mp hFB
      rw [hcard]
      exact hr.not_dvd_one
    have hsum : CFSG.Open.pRank r (F ⊔ Subgroup.zpowers (z : G)) =
        CFSG.Open.pRank r F + CFSG.Open.pRank r (Subgroup.zpowers (z : G)) :=
      CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd hr hFcent hnotdvd
    have hmono : CFSG.Open.pRank r (F ⊔ Subgroup.zpowers (z : G)) ≤
        CFSG.Open.pRank r D.M :=
      CFSG.SectionRank.pRank_mono hr.one_lt
        (sup_le (hFL.trans hLM) (Subgroup.zpowers_le.mpr hzM))
    have h3 : CFSG.Open.pRank r (F ⊔ Subgroup.zpowers (z : G)) = 3 := by
      rw [hsum, hpF, hpB]
    omega
  have hHC : L ≤ Subgroup.normalizer (C : Set G) := by
    have hMC : D.M ≤ Subgroup.normalizer (C : Set G) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact ⟨fun hx => mem_centOverO2_conj hMN hm hx, fun hx => by
        have h := mem_centOverO2_conj hMN (D.M.inv_mem hm) hx
        have heq : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x := by group
        rwa [heq] at h⟩
    exact hLM.trans hMC
  have hrelOut : ¬ r ∣ (L ⊔ C).relIndex D.M := by
    intro hd
    exact hout (hd.trans (relIndex_centOverO2_dvd_card_outer hLM hMN))
  have hsup : L.relIndex (L ⊔ C) ∣ Nat.card C := by
    have hEq := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := L) (K := C) hHC).1
    rw [hEq]
    exact Subgroup.relIndex_dvd_card _ _
  have hsupNot : ¬ r ∣ L.relIndex (L ⊔ C) := fun hd => hCr (hd.trans hsup)
  have hnotrel : ¬ r ∣ L.relIndex D.M := by
    have hmul := Subgroup.relIndex_mul_relIndex L (L ⊔ C) D.M le_sup_left
      (sup_le hLM hC_le_M)
    intro hd
    rw [← hmul] at hd
    rcases hr.dvd_mul.mp hd with h | h
    · exact hsupNot h
    · exact hrelOut h
  have hOpp_le : Opp r D.M ≤ L := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    refine (Subgroup.closure_le L).2 ?_
    rintro x ⟨hxM, k, hk⟩
    exact CFSG.ClassicalInvolution.Q3.mem_of_normal_of_not_dvd_relIndex
      (N := L) (M := D.M) (p := r) (k := k) hN hr hnotrel hxM
      (by rw [← hk]; exact pow_orderOf_eq_one x)
  have hdvdBar : r ∣ Nat.card (Bar2 L) := by
    let O : Subgroup ↥L := CFSG.pCore 2 ↥L
    let R' : Subgroup ↥L := R.subgroupOf L
    have hR'pg : IsPGroup r R' :=
      hRpg.of_equiv (Subgroup.subgroupOfEquivOfLe hRL).symm
    have hnotO : ¬ r ∣ Nat.card O := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
      rw [hk]
      intro hd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
    have hinj : Function.Injective ((QuotientGroup.mk' O).comp R'.subtype) :=
      @CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype ↥L _ r ⟨hr⟩ O _
        hnotO R' hR'pg
    have hR'card : Nat.card R' = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
    have hcardImage : Nat.card ((⊤ : Subgroup ↥R').map
        ((QuotientGroup.mk' O).comp R'.subtype)) = r ^ 2 := by
      rw [Subgroup.card_map_of_injective hinj, Subgroup.card_top, hR'card, hRcard]
    have hdvd2 : r ^ 2 ∣ Nat.card (Bar2 L) := by
      rw [← hcardImage]
      exact Subgroup.card_subgroup_dvd_card _
    exact (show r ∣ r ^ 2 from by rw [pow_two]; exact dvd_mul_right r r).trans hdvd2
  have hOppL : Opp r L = L := opp_eq_self_of_calC hL hsimple hr hr2 hdvdBar
  have hL_le : L ≤ Opp r D.M := by
    rw [← hOppL]
    exact s13_Thirteen2_pElementSubgroup_mono hLM
  exact le_antisymm hL_le hOpp_le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
