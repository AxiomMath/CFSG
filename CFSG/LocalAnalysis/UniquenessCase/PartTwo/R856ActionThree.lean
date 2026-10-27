module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R856G2Three
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBR865Types
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCStarSigmaStd
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TwistedF4InnerChoiceX
import CFSG.LocalAnalysis.UniquenessCase.UC22R856TrialityAction
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCSylowHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCOutHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R69CenterApps
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Pair
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65WeakClosureBar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2CharThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65AssemblyGeneric
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65O3PrimeRankTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarCyclic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarKernel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62CenterOfNormal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarX108
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.RankThree
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixThirtyEight
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixNine
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecomp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.UniquenessCase.UC22.R856NormalFour
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Fusion


theorem fusion_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P : Subgroup G} (hc : Cex856 (dataOfSetup hS S) L Q P) :
    List857 (Bar2 L) ∧ ¬ List857Clause1 (Bar2 L) ∧
      ControlsFusionIn S.M P ∧
      (∀ A : Subgroup G, A ≤ P → normalizer (A : Set G) ≤ S.M →
        A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet S.M) := by
  obtain ⟨hlist, hno, -, -⟩ := UC22.R856Normal.fusion_of_cex856 (UC6S846.sigmaStd_dataOfSetup hS S)
    (UC6G.uc_theorem_6_14_three hS hUC hC (UCK.k36_of_eqlStar
        (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
            UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S)
    (r6_3_dataOfSetup hS hUC hC S) hc
  exact ⟨hlist, hno, r862_dataOfSetup hS hUC hC S L Q P hc⟩

theorem le_centralizer_of_abelian_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G} (hX : ChoiceX (dataOfSetup hS S) L Q P X)
    (hML : S.M ≤ normalizer (L : Set G))
    {A : Subgroup G} (hAM : A ≤ S.M) (hA : IsPGroup 3 A)
    (hAb : IsMulCommutative A) (hXA : X ≤ normalizer (A : Set G)) :
    X ≤ centralizer (A : Set G) := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have hc := hX.cex
  obtain ⟨hlist, hno, -, -⟩ := fusion_dataOfSetup hS hUC hC S hc
  have h61 := h61_of_list857
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.outerFixedE9_holds
    hc.mem hc.rank hlist hno hc.sylowQ hc.sylowP hc.le
    (hc.sylowP.le.trans hML) X hX.le hX.card hX.not_le_sylowQ
  obtain ⟨E, hE, hEel, hEc, hGamma, hEX⟩ := hasGammaE9_of_pRank hc h61
  exact le_centralizer_of_abelian_of_R6_9
    (r6_9_dataOfSetup hS hUC hC (UCK.k36_of_eqlStar
        (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
            UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S)
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hc.mem))
    hE hEel hEc hGamma (hX.le.trans hc.sylowP.le) hX.card hEX
    (fun hN => hX.notLe ((centralizer_le_normalizer _).trans hN)) hAM hA hAb hXA

theorem le_centralizer_sylow_of_normal_inner_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G}
    (h : ChoiceX (dataOfSetup hS S) L Q P X)
    (hLM : S.M ≤ normalizer (L : Set G)) (hZ : center (Bar2 L) = ⊥)
    (hInner : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ pCoreOf 2 L) : X ≤ centralizer (Q : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := h.cex
  have hQL := hc.sylowQ.le
  have hQP := hc.le
  have hPL : P ≤ normalizer (L : Set G) := hc.sylowP.le.trans hLM
  have hQeq : Q = P ⊓ L :=
    (hc.sylowQ.eq_of_le (le_inf hQP hQL) inf_le_right
      (hc.sylowP.isPGroup.to_le inf_le_left)).symm
  have hQn : (Q.subgroupOf P).Normal :=
    normal_subgroupOf_of_isSylowOf_of_le_normalizer hc.sylowQ hQP hc.sylowP.isPGroup hPL
  have hXC : X ≤ Q ⊔ centralizerBar P L :=
    le_sup_centralizerBar_of_inner hQP hQL hQeq hQn hc.sylowQ hc.sylowP.isPGroup hPL h.le hInner
  have hcap : Q ⊓ centralizerBar P L = ⊥ :=
    inf_centralizerBar_eq_bot_of_ker hQL hc.inf_pCore_eq_bot
      (inf_centralizerBar_le_pCore_of_center_bar2 hZ)
  have hQc : ∀ q ∈ Q, ∀ c ∈ centralizerBar P L, q * c = c * q :=
    fun q hq c hcc => commute_of_mem_centralizerBar Nat.prime_three (by norm_num)
      hc.sylowP.isPGroup hQL hQP hq hcc
  have hQr : CFSG.Open.pRank 3 Q = 2 := by
    obtain ⟨Qs, hQs⟩ := hc.sylowQ.exists_sylow_eq_subgroupOf
    have hr := (CFSG.SectionRank.pRank_sylow Qs).1
    rw [hQs, pRank_subgroupOf_eq Nat.prime_three hQL,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hr
    exact hr.trans hc.rank
  have hPr : CFSG.Open.pRank 3 P ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hc.sylowP.le).trans
      (CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3.pRank_three_le_three_of_not_sp
        (UC6S846.sigmaStd_dataOfSetup hS S) hc.notStrong hc.mem)
  have hCr : CFSG.Open.pRank 3 (centralizerBar P L) ≤ 1 := by
    have ha := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
      Nat.prime_three hQc hcap
    have hr := (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt
      (sup_le hQP (centralizerBar_le P L))).trans hPr
    omega
  have hCcyc : IsCyclic (centralizerBar P L) :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
      Nat.prime_three (by norm_num) (hc.sylowP.isPGroup.to_le (centralizerBar_le P L))
      (by rwa [CFSG.SectionRank.pRank_coe_eq_openPRank])
  have hCc : IsMulCommutative (centralizerBar P L) := hCcyc.isMulCommutative
  let W : Subgroup G := Q ⊔ X
  have hWP : W ≤ P := sup_le hQP h.le
  have hW3 : IsPGroup 3 W := hc.sylowP.isPGroup.to_le hWP
  have hQW : Q ≤ W := le_sup_left
  have hXW : X ≤ W := le_sup_right
  let C : Subgroup G := centralizerBar P L ⊓ W
  have hCW : C ≤ W := inf_le_right
  have hXCW : X ≤ Q ⊔ C := by
    intro x hx
    obtain ⟨q, hq, c, hcc, hxc⟩ := exists_mul_mem_sup_of_commute
      (fun c hcc q hq => (hQc q hq c hcc).symm) (hXC hx)
    have hcW : c ∈ W := by
      have h1 : c = q⁻¹ * x := by rw [hxc]; group
      rw [h1]
      exact W.mul_mem (W.inv_mem (hQW hq)) (hXW hx)
    rw [hxc]
    exact mul_mem_sup hq ⟨hcc, hcW⟩
  have hdecompW : X.subgroupOf W ≤ Q.subgroupOf W ⊔ C.subgroupOf W := by
    rw [← subgroupOf_sup hQW hCW]
    exact subgroupOf_mono W hXCW
  have hsup : Q.subgroupOf W ⊔ X.subgroupOf W = ⊤ :=
    codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup Q X)
  have hcent : ∀ A : Subgroup W, A ≤ Q.subgroupOf W → IsMulCommutative A →
      X.subgroupOf W ≤ normalizer (A : Set W) → X.subgroupOf W ≤ centralizer (A : Set W) := by
    intro A hAQ hAb hXA
    let Ag : Subgroup G := A.map W.subtype
    have hAgQ : Ag ≤ Q := map_le_iff_le_comap.mpr hAQ
    have hAgc : IsMulCommutative Ag := by
      refine ⟨⟨fun a b => ?_⟩⟩
      apply Subtype.ext
      change (a : G) * (b : G) = (b : G) * (a : G)
      obtain ⟨aa, haa, ha⟩ := a.2
      obtain ⟨bb, hbb, hb⟩ := b.2
      rw [← ha, ← hb]
      exact congrArg (fun z : W => (z : G))
        (congrArg Subtype.val (hAb.is_comm.comm (⟨aa, haa⟩ : A) ⟨bb, hbb⟩))
    have hXAg : X ≤ normalizer (Ag : Set G) := by
      intro x hx
      exact Subgroup.le_normalizer_map W.subtype
        (mem_map.mpr ⟨⟨x, hXW hx⟩, hXA (show (⟨x, hXW hx⟩ : W) ∈ X.subgroupOf W from hx), rfl⟩)
    have hh := le_centralizer_of_abelian_dataOfSetup hS hUC hC S h hLM
      (hAgQ.trans (hQL.trans hc.mem.1.le))
      (hc.sylowQ.isPGroup.to_le hAgQ) hAgc hXAg
    intro x hx
    rw [mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (mem_centralizer_iff.mp (hh hx) (a : G) (mem_map.mpr ⟨a, ha, rfl⟩))
  obtain ⟨hlist, hno, -, -⟩ := fusion_dataOfSetup hS hUC hC S hc
  have h61 := h61_of_list857
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.outerFixedE9_holds
    hc.mem hc.rank hlist hno hc.sylowQ hc.sylowP hc.le hPL X h.le h.card h.not_le_sylowQ
  obtain ⟨E, hE, hEel, hEc, hGamma, hEX⟩ := hasGammaE9_of_pRank hc h61
  have hpush : X.subgroupOf W ≤ Subgroup.upperCentralSeries W 2 → X.subgroupOf W ≤ center W := by
    intro h2 x hx
    have hz := X_le_center_sup_of_R6_9
      (r6_9_dataOfSetup hS hUC hC (UCK.k36_of_eqlStar
          (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
              UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds)
          UCK.l34OuterFree) S)
      (UC6S846.sig_subset_sig1 (UC6S846.sigmaStd_dataOfSetup hS S)
        (UC6S846.not_solvable_of_mem_calC hc.mem))
      hE hEel hEc hGamma (h.le.trans hc.sylowP.le) h.card hEX
      (fun hn => h.notLe ((centralizer_le_normalizer _).trans hn))
      (hWP.trans hc.sylowP.le) hW3 hXW
      (fun y hy => mem_map.mpr ⟨⟨y, hXW hy⟩, h2 hy, rfl⟩)
    obtain ⟨z, hz, heq⟩ := hz hx
    have he : z = x := Subtype.ext heq
    rwa [he] at hz
  have hXcenter : X.subgroupOf W ≤ center W :=
    le_center_of_inner_of_rank_le_two (Q := Q.subgroupOf W) (X := X.subgroupOf W)
      (C := C.subgroupOf W) hW3
      (by rw [pRank_subgroupOf_eq Nat.prime_three hQW]; exact hQr.le)
      hsup
      (fun x hx => by
        apply Subtype.ext
        change (x : G) ^ 3 = 1
        have hp := pow_card_eq_one' (G := X) (x := ⟨(x : G), hx⟩)
        rw [h.card] at hp
        exact congrArg (fun y : X => (y : G)) hp)
      (fun q hq c hcc => Subtype.ext (hQc q hq c hcc.1))
      (fun c hcc d hdc => by
        apply Subtype.ext
        change (c : G) * (d : G) = (d : G) * (c : G)
        exact congrArg (fun z : centralizerBar P L => (z : G))
          (hCc.is_comm.comm ⟨(c : G), hcc.1⟩ ⟨(d : G), hdc.1⟩))
      (by
        rw [eq_bot_iff]
        intro x hx
        apply Subtype.ext
        exact mem_bot.mp (hcap ▸ (show (x : G) ∈ Q ⊓ centralizerBar P L from ⟨hx.1, hx.2.1⟩)))
      hdecompW hcent hpush
  have hXCQ : X ≤ centralizer (Q : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val
      (mem_center_iff.mp (hXcenter (show (⟨x, hXW hx⟩ : W) ∈ X.subgroupOf W from hx))
        ⟨q, hQW hq⟩)
  exact hXCQ

theorem le_center_sylow_of_normal_inner_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G}
    (h : ChoiceX (dataOfSetup hS S) L Q P X)
    (hLM : S.M ≤ normalizer (L : Set G)) (hZ : center (Bar2 L) = ⊥)
    (hInner : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ pCoreOf 2 L) :
    X ≤ (center P).map P.subtype := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := h.cex
  have hQL := hc.sylowQ.le
  have hQP := hc.le
  have hPL : P ≤ normalizer (L : Set G) := hc.sylowP.le.trans hLM
  have hQeq : Q = P ⊓ L :=
    (hc.sylowQ.eq_of_le (le_inf hQP hQL) inf_le_right
      (hc.sylowP.isPGroup.to_le inf_le_left)).symm
  have hQn : (Q.subgroupOf P).Normal :=
    normal_subgroupOf_of_isSylowOf_of_le_normalizer hc.sylowQ hQP hc.sylowP.isPGroup hPL
  have hQnP : P ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQP).mp hQn
  have hcap : Q ⊓ centralizerBar P L = ⊥ :=
    inf_centralizerBar_eq_bot_of_ker hQL hc.inf_pCore_eq_bot
      (inf_centralizerBar_le_pCore_of_center_bar2 hZ)
  have hQc : ∀ q ∈ Q, ∀ c ∈ centralizerBar P L, q * c = c * q :=
    fun q hq c hcc => commute_of_mem_centralizerBar Nat.prime_three (by norm_num)
      hc.sylowP.isPGroup hQL hQP hq hcc
  have hQr : CFSG.Open.pRank 3 Q = 2 := by
    obtain ⟨Qs, hQs⟩ := hc.sylowQ.exists_sylow_eq_subgroupOf
    have hr := (CFSG.SectionRank.pRank_sylow Qs).1
    rw [hQs, pRank_subgroupOf_eq Nat.prime_three hQL,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hr
    exact hr.trans hc.rank
  have hPr : CFSG.Open.pRank 3 P ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hc.sylowP.le).trans
      (CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3.pRank_three_le_three_of_not_sp
        (UC6S846.sigmaStd_dataOfSetup hS S) hc.notStrong hc.mem)
  have hCr : CFSG.Open.pRank 3 (centralizerBar P L) ≤ 1 := by
    have ha := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
      Nat.prime_three hQc hcap
    have hr := (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt
      (sup_le hQP (centralizerBar_le P L))).trans hPr
    omega
  have hCcyc : IsCyclic (centralizerBar P L) :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
      Nat.prime_three (by norm_num) (hc.sylowP.isPGroup.to_le (centralizerBar_le P L))
      (by rwa [CFSG.SectionRank.pRank_coe_eq_openPRank])
  have hXC : X ≤ Q ⊔ centralizerBar P L :=
    le_sup_centralizerBar_of_inner hQP hQL hQeq hQn hc.sylowQ hc.sylowP.isPGroup hPL h.le hInner
  have hXCQ := le_centralizer_sylow_of_normal_inner_dataOfSetup hS hUC hC S h hLM hZ hInner
  have hXCQP : X.subgroupOf P ≤ centralizer (Q.subgroupOf P : Set P) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro q hq
    exact Subtype.ext (mem_centralizer_iff.mp (hXCQ hx) q hq)
  have hCcycP : IsCyclic ((centralizerBar P L).subgroupOf P) :=
    isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe (centralizerBar_le P L)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (centralizerBar_le P L)).injective
  have hXZ2 : X ≤ (Subgroup.upperCentralSeries P 2).map P.subtype := by
    have h2 := le_upperCentralSeries_two_of_centralizes_rank_two
      (Q := Q.subgroupOf P) (C := (centralizerBar P L).subgroupOf P) (X := X.subgroupOf P)
      hc.sylowP.isPGroup hQn (centralizerBar_normal hPL)
      (by rw [pRank_subgroupOf_eq Nat.prime_three hQP]; exact hQr.le) hCcycP
      (fun q hq c hcc => Subtype.ext (hQc q hq c hcc))
      (by rw [eq_bot_iff]; intro x hx; apply Subtype.ext;
          exact mem_bot.mp (hcap ▸ (show (x : G) ∈ Q ⊓ centralizerBar P L from hx)))
      (by rw [← subgroupOf_sup hQP (centralizerBar_le P L)]; exact subgroupOf_mono P hXC)
      hXCQP (fun x hx => by
        apply Subtype.ext
        change (x : G) ^ 3 = 1
        have hp := pow_card_eq_one' (G := X) (x := ⟨(x : G), hx⟩)
        rw [h.card] at hp
        exact congrArg (fun y : X => (y : G)) hp)
    exact fun x hx => mem_map.mpr ⟨⟨x, h.le hx⟩, h2 hx, rfl⟩
  obtain ⟨hlist, hno, -, -⟩ := fusion_dataOfSetup hS hUC hC S hc
  have h61 := h61_of_list857
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.outerFixedE9_holds
    hc.mem hc.rank hlist hno hc.sylowQ hc.sylowP hc.le hPL X h.le h.card h.not_le_sylowQ
  obtain ⟨E, hE, hEel, hEc, hGamma, hEX⟩ := hasGammaE9_of_pRank hc h61
  exact X_le_center_sup_of_R6_9 (r6_9_dataOfSetup hS hUC hC (UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S)
    (UC6S846.sig_subset_sig1 (UC6S846.sigmaStd_dataOfSetup hS S)
      (UC6S846.not_solvable_of_mem_calC hc.mem)) hE hEel hEc hGamma
    (h.le.trans hc.sylowP.le) h.card hEX
    (fun hn => h.notLe ((centralizer_le_normalizer _).trans hn))
    hc.sylowP.le hc.sylowP.isPGroup h.le hXZ2

theorem fixes_abelian_bar_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G}
    (hX : ChoiceX (dataOfSetup hS S) L Q P X)
    (hML : S.M ≤ normalizer (L : Set G)) {x : G} (hx : x ∈ X) (hXgen : X = zpowers x)
    {Ab : Subgroup (Bar2 L)} (hAb : IsPGroup 3 Ab) (hcomm : IsMulCommutative Ab)
    (hAbx : ∀ a ∈ Ab, barConjAut (L := L) x a ∈ Ab) :
    ∀ a ∈ Ab, barConjAut (L := L) x a = a := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxN : x ∈ normalizer (L : Set G) := (hX.le.trans (hX.cex.sylowP.le.trans hML)) hx
  have hx3 : x ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := X) (x := ⟨x, hx⟩)
    rw [hX.card] at h
    exact congrArg Subtype.val h
  obtain ⟨A, hAL, hA3, hXA, hmap⟩ := exists_stable_three_lift hxN hx3 hAb hAbx
  let ψ : A →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 L)).comp (Subgroup.inclusion hAL)
  have hAker : A ⊓ pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) A (pCoreOf 2 L) hA3
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)).eq_bot
  have hψinj : Function.Injective ψ := injective_comp_subgroupOf_mk' hAL hAker
  have hrange : ψ.range = Ab := (range_comp_subgroupOf_mk' hAL).trans hmap
  have hAcomm : IsMulCommutative A := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply hψinj
    rw [map_mul, map_mul]
    have ha : ψ a ∈ Ab := hrange ▸ MonoidHom.mem_range.mpr ⟨a, rfl⟩
    have hb : ψ b ∈ Ab := hrange ▸ MonoidHom.mem_range.mpr ⟨b, rfl⟩
    exact congrArg Subtype.val (hcomm.is_comm.comm (⟨ψ a, ha⟩ : Ab) ⟨ψ b, hb⟩)
  have hXC : X ≤ centralizer (A : Set G) := le_centralizer_of_abelian_dataOfSetup
    hS hUC hC S hX hML (hAL.trans hX.cex.mem.1.le) hA3 hAcomm (hXgen ▸ hXA)
  intro a ha
  have hmem : a ∈ ψ.range := hrange.symm ▸ ha
  obtain ⟨b, rfl⟩ := hmem
  let bL : L := ⟨b, hAL b.2⟩
  have hbX : x * (b : G) = (b : G) * x := (mem_centralizer_iff.mp (hXC hx) b b.2).symm
  have hφfix : (normalizerMonoidHom L) ⟨x, hxN⟩ bL = bL := by
    apply Subtype.ext
    exact mul_inv_eq_of_eq_mul hbX
  change barConjAut (L := L) x ((QuotientGroup.mk' (CFSG.pCore 2 L)) bL) = _
  change barConjAut (L := L) x (QuotientGroup.mk bL) = QuotientGroup.mk bL
  rw [barConjAut_of_mem hxN, barAction_mk L ⟨x, hxN⟩ bL, hφfix]

theorem false_of_moved_abelian_bar_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G}
    (hX : ChoiceX (dataOfSetup hS S) L Q P X)
    (hML : S.M ≤ normalizer (L : Set G)) {x : G} (hx : x ∈ X) (hXgen : X = zpowers x)
    (hMoved : ∃ Ab : Subgroup (Bar2 L), IsPGroup 3 Ab ∧ IsMulCommutative Ab ∧
      (∀ a ∈ Ab, barConjAut (L := L) x a ∈ Ab) ∧
      ∃ a ∈ Ab, barConjAut (L := L) x a ≠ a) : False := by
  obtain ⟨Ab, hAb, hc, hInv, a, ha, hne⟩ := hMoved
  exact hne (fixes_abelian_bar_dataOfSetup hS hUC hC S hX hML hx hXgen hAb hc hInv a ha)

theorem false_of_normal_twistedF4_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G} (hX : ChoiceX (dataOfSetup hS S) L Q P X)
    (hML : S.M ≤ normalizer (L : Set G)) {f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .twistedF4 0 2 f)
    (hNontrivial : ¬ ⁅L, X⁆ ≤ pCoreOf 2 L)
    (hInner : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ pCoreOf 2 L) : False :=
  PartOne.Section8.false_of_inner_twistedF4_of_choiceX (UC6S846.sigmaStd_dataOfSetup hS S)
    (UC6G.uc_theorem_6_14_three hS hUC hC (UCK.k36_of_eqlStar
        (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
            UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S)
    (r6_3_dataOfSetup hS hUC hC S)
    (r6_9_dataOfSetup hS hUC hC (UCK.k36_of_eqlStar
        (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
            UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S)
    hX hML hmodel hNontrivial hInner

theorem false_of_normal_trialityD4_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G} (hX : ChoiceX (dataOfSetup hS S) L Q P X)
    (hML : S.M ≤ normalizer (L : Set G)) {p f : ℕ} (hp3 : p ≠ 3)
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .trialityD4 0 p f)
    (hNontrivial : ¬ ⁅L, X⁆ ≤ pCoreOf 2 L) : False := by
  obtain ⟨x, hx, hgen, -, -, hAut3, hAut1⟩ :=
    UC22.R856NormalFour.exists_generator_of_commutator_not_le hX.le
      (hX.cex.sylowP.le.trans hML) hX.card hNontrivial
  exact UC22.false_of_trialityD4_three_action hmodel hp3 (barConjAut (L := L) x) hAut3 hAut1
    (fun A hA hAc hAα => fixes_abelian_bar_dataOfSetup hS hUC hC S hX hML hx hgen hA hAc hAα)

end Fusion

section StarInputs


theorem star_inputs_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G) :
    UC6S846.SigmaStd (dataOfSetup hS S) ∧ UC6.R6_14 (dataOfSetup hS S) ∧
      UC6.R6_38 (dataOfSetup hS S) ∧ R858 (dataOfSetup hS S) ∧ F07.R72 (dataOfSetup hS S) ∧
      F07.R76Sig (dataOfSetup hS S) := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have h614 := UC6G.uc_theorem_6_14_three hS hUC hC (UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S
  have hG3 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  exact ⟨hSg, h614, r6_38_dataOfSetup hS S,
    r858_of_r857 hSg (UC22.R856Normal.r857_of_data hSg h614),
    PartOne.Section7.R72.r72_dataOfSetup hS hUC hC S,
    r76Sig_dataOfSetup PartOne.Section7.SEFive.stronglyEmbeddedFive_holds hSE3 hS S⟩

end StarInputs

section NormalG2Center


theorem commutator_le_of_normal_g2_center_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G}
    (h : ChoiceX (dataOfSetup hS S) L Q P X)
    (hLM : S.M ≤ normalizer (L : Set G)) {p f : ℕ} (hp3 : p ≠ 3)
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .G2 0 p f)
    (hXZ : X ≤ (center P).map P.subtype) : ⁅L, X⁆ ≤ pCoreOf 2 L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := h.cex
  have hm := hmodel.chevalleyExceptionalModel (by decide)
  have hp := hm.1.1
  have hpf : p = 2 → 2 ≤ f := by
    intro heq
    have hq := hm.1.2.2.2
    rw [heq] at hq
    by_contra hf
    have ht := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : f ≤ 1)
    norm_num at ht
    omega
  have hQZ : Nat.card ((center Q).map Q.subtype) = 3 :=
    card_center_map_sylow_eq_three_of_g2 hc.sylowQ hp hp3 hpf hmodel
  let Z : Subgroup G := (center Q).map Q.subtype
  have hZQ : Z ≤ Q := map_subtype_le _
  have hZcQ : Z ≤ centralizer (Q : Set G) := by
    rintro z ⟨zq, hzq, rfl⟩
    rw [mem_centralizer_iff]
    exact fun q hq => congrArg Subtype.val (mem_center_iff.mp hzq ⟨q, hq⟩)
  obtain ⟨-, -, -, hUQ⟩ := fusion_dataOfSetup hS hUC hC S hc
  have hNZ : normalizer (Z : Set G) ≤ S.M :=
    normalizer_le_of_card_three_of_gamma hc.gamma hZQ hQZ
  have hZU := hUQ Z (hZQ.trans hc.le) hNZ
  have hnormL : (L.subgroupOf S.M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hc.mem.1.le).mpr hLM
  have hrk := CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3.pRank_three_le_three_of_not_sp
    (UC6S846.sigmaStd_dataOfSetup hS S) hc.notStrong hc.mem
  have hXcq : Q ≤ centralizer (X : Set G) := by
    intro q hq
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨xx, hxx, heq⟩ := hXZ hx
    have hh := congrArg Subtype.val (mem_center_iff.mp hxx ⟨q, hc.le hq⟩)
    have hh' : q * (xx : G) = (xx : G) * q := hh
    have heq' : (xx : G) = x := heq
    rw [heq'] at hh'
    exact hh'.symm
  have hW : ∀ m ∈ S.M, CFSG.conjugate Z m ≤ normalizer (Z : Set G) → CFSG.conjugate Z m = Z :=
    fun m hm hmn => conjugate_eq_of_sylowCenterWeaklyClosed_bar
      (g2SylowCenterWeakClosure_holds _ p f hp3 hmodel) hc.mem.1.le hnormL hZQ hZcQ hQZ
      hc.sylowQ.le hc.sylowQ.exists_sylow_eq_subgroupOf hc.inf_pCore_eq_bot hQZ hm hmn
  have hN : ¬ normalizer (X : Set G) ≤ S.M := fun hn =>
    h.notLe ((centralizer_le_normalizer _).trans hn)
  obtain ⟨hJ2, hU33, hG2⟩ := sylowCenterInverted_inputs g2CharThreeInversion_holds
  obtain ⟨t, htX, htZ⟩ := exists_inverting_of_K332
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.k332Z3_holds
    hJ2 hU33 hG2 hrk hZU h.card hXcq hZQ hQZ hW
    (fun O hQO hO => le_of_two_le_pRank_of_gamma hc.gamma hQO hO hc.pRank_sylowQ_eq_two.ge)
    hN
  by_contra hnot
  have h64 : List864 L X P := Or.inr (Or.inr (Or.inr
    ⟨Or.inr (Or.inr ⟨p, f, hmodel⟩), hnot, hXZ⟩))
  exact eight65_pointwise_false_of_lieModel_g2_of_cq
    g2AutSylowCentralizer_of_isInner
    hp hp3 hpf hZU hc.gamma hc.sylowP.le hc.mem.1.le hnormL hc.le hZQ hZcQ hQZ
    hc.sylowQ.le hc.sylowQ.exists_sylow_eq_subgroupOf hc.inf_pCore_eq_bot hQZ h.le h.card
    h64 hN (center_eq_bot_of_lieModel_g2 hmodel) hmodel htX htZ hnot

end NormalG2Center

section NormalG2Inner


theorem false_of_normal_g2_inner_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G} (hX : ChoiceX (dataOfSetup hS S) L Q P X)
    (hML : S.M ≤ normalizer (L : Set G)) {p f : ℕ} (hp3 : p ≠ 3)
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .G2 0 p f)
    (hInner : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ pCoreOf 2 L) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSimple : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hmodel
  have hcent : center (Bar2 L) = ⊥ :=
    @P22w.center_eq_bot_of_isSimpleGroup (Bar2 L) _ hSimple hX.cex.mem.2.2
  have hXZ := le_center_sylow_of_normal_inner_dataOfSetup hS hUC hC S hX hML hcent hInner
  have hLX := commutator_le_of_normal_g2_center_dataOfSetup hS hUC hC S hX hML hp3 hmodel hXZ
  obtain ⟨hSg, h614, h638, h858, h72, h76⟩ := star_inputs_dataOfSetup hS hUC hC S
  have hlist := list863_of_lieModel_g2_of_choiceX_of_sigmaStd hSg h614 h638 h858 h72 h76
    kStrongEmbedded72_holds hX hLX hmodel
  exact false_of_normal_g2_of_outer_prime_dataOfSetup hS hUC hC S hX hML hp3 hmodel
    (not_three_dvd_card_outer_of_list863 hlist)

end NormalG2Inner

section NormalLieCommutator


theorem false_of_normal_d4_f4_of_commutator_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G} (hX : ChoiceX (dataOfSetup hS S) L Q P X)
    (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L)
    (hmodel : (∃ p f : ℕ, CFSG.Blueprint.LieModel (Bar2 L) .trialityD4 0 p f) ∨
      ∃ f : ℕ, CFSG.Blueprint.LieModel (Bar2 L) .twistedF4 0 2 f) : False := by
  obtain ⟨hSg, h614, h638, h858, h72, h76⟩ := star_inputs_dataOfSetup hS hUC hC S
  have hSimple : IsSimpleGroup (Bar2 L) := by
    rcases hmodel with ⟨p, f, h⟩ | ⟨f, h⟩ <;> exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
  apply false_of_lie_families_of_choiceX_of_sigmaStd g2NonsplitSylowInput_holds
    trialityTorusSylowInput_holds lieOutCyclicInput_holds hSg h614 h638 h858 h72 h76
    kStrongEmbedded72_holds hX hLX hSimple
  rcases hmodel with ⟨p, f, h⟩ | ⟨f, h⟩
  · exact Or.inr (Or.inl ⟨p, f, h, h.admissible.1, h.admissible.2.1⟩)
  · have ho := h.admissible
    have pars : Nat.Prime 2 ∧ 1 ≤ f ∧ Odd f ∧ 3 ≤ f := by
      simpa [CFSG.Open.StatedLieAdmissible] using ho
    exact Or.inr (Or.inr ⟨f, h, pars.2.2.2, pars.2.2.1⟩)

end NormalLieCommutator

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
