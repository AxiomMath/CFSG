module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xDefs
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroup
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PBasic
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PImg
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PSolv
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PCases
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PTheta
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PMax
import CFSG.RankThree.PartTwo.Sec15.ThmDLemma10
import CFSG.RankThree.PartTwo.Sec15.Item153Push2Proof
import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofA6
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProofChar

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof155P

theorem step155W315P_of
    (hSz : KFacts.KPSz)
    {A L : Subgroup G} {c : G} (h142 : Concl142 A (lB A)) (h143 : Concl143 A (lB A))
    (h146 : Item146 A (lB A)) (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A))
    (hQ : ∀ Y ∈ scriptY0 A (lB A), CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A))
    (hY0 : ∀ M ∈ scriptY2 A, generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        J ∈ scriptY0 A (lB A)) :
    Step155W315P A c L := by
  intro h X K Y M T P hC _ _ hE hRP hWO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Proof155Wx.Facts155W A X Y M P := Proof155Wx.facts155W_of h h148 h149 hC hE hRP
  letI : (ker148 A M).Normal := ker148_normal hf.mem_m2.1.2
  have hX : X ∈ thetaComponentsIn M := hE.mem_x
  obtain ⟨d, hdA, hd1, hdW, h5X, htype⟩ := cases148_of_not_le h h148 h149 hf hX hWO
  set W := w155 A M X with hWdef
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  have hWΔ : W ≤ delta A (lB A) M := hf.w_le_i0.trans (Sec14.oPrimeResidualOf_le_self 3 _)
  have hWM : W ≤ M := hWΔ.trans (delta_le M)
  have hWp : Group.IsPerfect ↥W := Proof155Wx.isPerfect_w155 A M X
  have hK : CFSG.IsKGroup ↥M := (h.toTheoremFourHyp.sectionFourHyp hf.mem_m2.1.1).kGroup
  obtain ⟨hNn, hN3, hNeq⟩ := inf_pPrimeCoreOf_facts hWM
  have hθO : inSubgroup (aschbacherSolvableCore 3) W ≤ pPrimeCoreOf 3 M :=
    inSubgroup_theta_le_pPrimeCoreOf hf.subnormal_w_m
  have h5 : 5 ∣ ((W ⊓ pPrimeCoreOf 3 M).subgroupOf W).index := by
    rw [hNeq, ← card_img148_eq_index (A := A) hWM]
    exact (type155_facts htype).2.2.1
  have hsol : IsSolvable ↥(W ⊓ pPrimeCoreOf 3 M) :=
    isSolvable_of_pRank_five_le_one hSz hK hWM hWp inf_le_left hNn hN3
      (le_inf (Subgroup.map_subtype_le _) hθO) h5 (pRank_five_w155_le_one h hf hX h5X)
  obtain ⟨hθ, hWc⟩ := theta_w155_eq_and_mem_comp3In hWM hf.subnormal_w_m hWΔ
    hf.subnormal_w_delta hWp hsol htype
  have hW0 : W ∈ scriptY0 A (lB A) := hY0 M hf.mem_m2 hf.fit_m W hWc hf.a_le_normalizer_w
  have hWeq : W = delta A (lB A) W := hW0.1.2.2.1
  obtain ⟨hWO2, hWtype⟩ := w155_quot_facts hWM hWp hθ hW0.1.2.2.2 htype
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcen : ∀ y ∈ W, ⁅y, d⁆ ∈ CFSG.Open.pCoreOf 2 W := by
    intro y hy
    have hdN : d ∈ Subgroup.normalizer (W : Set G) := hf.a_le_normalizer_w hdA
    have h1 : d * y⁻¹ * d⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hdN y⁻¹).mp (W.inv_mem hy)
    have hyd : ⁅y, d⁆ ∈ W := by
      rw [commutatorElement_def]
      simpa [mul_assoc] using W.mul_mem hy h1
    exact hWO2 ⟨hyd, hdW y hy⟩
  have hQ2 : ∀ V ≤ W, IsPGroup 2 V → A ≤ Subgroup.normalizer (V : Set G) →
      V ∈ scriptQ A (lB A) := by
    intro V hVW hV2 hAV
    have hV3 : ¬ 3 ∣ Nat.card V := by
      obtain ⟨k, hk⟩ := hV2.exists_card_eq
      rw [hk]
      intro h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at this
    exact ThmD.mem_scriptQ_of_centralizes hA h142 h143 h146 hWeq hf.a_le_normalizer_w
      (hQ W hW0) hdA hd1 hcen hVW hV3 hAV
  have hO : CFSG.Open.pCoreOf 2 (W ⊔ R) ≤ R := pCoreOf_sup_le_of_scriptQ hA h146 hE hf hQ2
  refine ⟨hWeq, ?_⟩
  by_cases hch : CharNormal153 W R
  · obtain ⟨C, hC1, hCR, hCchar, hCN⟩ := hch
    exact Or.inr (Or.inr ⟨C, hC1, hCR, hCchar, le_sup_left.trans hCN⟩)
  · refine Or.inr (Or.inl ?_)
    have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
    have hRW : R ≤ Subgroup.normalizer (W : Set G) := hRP.trans hf.p_le_normalizer_w
    have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
      rw [hRdef, hE.eq_rq]
      exact (Sec14.le_normalizer_sup (mem_scriptQ_iff.mp hf.mem_p).2.1 hf.mem_x4.1.2).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    have hAF : A ∈ partTwoF G := h.toSec13Data.mem_partTwoF
    have hW2 : CFSG.Open.pCoreOf 2 W ≠ ⊥ := hW0.2.2
    have hW3 : W = oPrimeResidualOf 3 W := hW0.1.2.1
    have hinv : InvA315 (W ⊔ R) R := by
      rcases hWtype with ⟨⟨φ⟩⟩ | ⟨hT, hq⟩
      · exact Push153B.invA315_of_alt (n := 5) (by norm_num) (by norm_num)
          (fun P _ _ h2 hle hne hn1 hn2 => Push153B.le_of_sylow_five P h2 hle hne hn1 hn2)
          Push153B.sylow_five_comm Push153B.sylow_five_pow hAF hf.a_le_normalizer_w hAR hR2 hRW
          hO hW2 hch φ
      · exact Push153B.invA315_of_a6 hAF hf.a_le_normalizer_w hAR hR2 hRW hO hW2 hch hq hT
    have hT : Listed315 (↥W ⧸ CFSG.pCore 2 ↥W) := by
      rcases hWtype with ⟨⟨φ⟩⟩ | ⟨hT, -⟩
      · obtain ⟨κ⟩ := nonempty_projSL_two_two_mulEquiv_alt5
        exact Or.inl ⟨2, by norm_num, even_two, ⟨φ.trans κ.symm⟩⟩
      · exact Or.inr (Or.inl hT)
    obtain ⟨e⟩ := Push153.nonempty_oResidual_quotient_equiv hR2 hRW hW3
    rw [sup_comm]
    exact ⟨le_sup_right, Push153.generalizedFitting_sup_eq hf.fit_w hR2 hRW,
      Push153.listed315_of_mulEquiv e hT, hinv⟩

end Proof155P

end CFSG.RankThree.PartTwo.Sec15
