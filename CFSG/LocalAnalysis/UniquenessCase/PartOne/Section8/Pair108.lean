module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Pair108Setup
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qv
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SylowNormalizer859
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R69Corollaries
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62UniqueMaxInU
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.NormalizerSylow108
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAIndex
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normalizer_zpowers_le_of_mem_planes {D : Data G} (h69 : UC6.R6_9 D)
    (hsub : D.sig ⊆ D.sig1) {P W B Z₀ : Subgroup G} (hPM : P ≤ D.M) (hP : IsPGroup 3 P)
    (hWel : IsElemAbelian 3 W) (hWc : Nat.card W = 9) (hWB : W ≤ B) (hBP : B ≤ P)
    (hBel : IsElemAbelian 3 B)
    (hBZ2 : B ≤ (Subgroup.upperCentralSeries ↥P 2).map P.subtype) (hZ₀W : Z₀ ≤ W)
    (hBZ : ∀ b ∈ B, b ∈ (center ↥P).map P.subtype → b ∈ Z₀)
    (hΓW : rankThreeGamma 1 3 W ≤ D.M) {y : G} (hyB : y ∈ B) (hy1 : y ≠ 1) :
    normalizer ((zpowers y : Subgroup G) : Set G) ≤ D.M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hXc : Nat.card (zpowers y) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  by_cases hyW : y ∈ W
  · refine (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (zpowers_le.mpr hyW)
      ?_).trans hΓW
    exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl (isElemAbelian_zpowers hy3) (k := 1)
      (by rw [hXc]; norm_num)
  · by_contra hnot
    have hyP : zpowers y ≤ P := (zpowers_le.mpr hyB).trans hBP
    have hWN : W ≤ normalizer ((zpowers y : Subgroup G) : Set G) := fun w hw =>
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
        hBel.comm ((zpowers_le.mpr hyB) hx) (hWB hw))
    have hXZ := le_center_of_le_upperCentral_two_of_R6_9 h69 hsub Nat.prime_three (by norm_num)
      (hWB.trans (hBP.trans hPM)) hWel (by rw [hWc]; norm_num) hΓW Nat.prime_three
      (hyP.trans hPM) hXc hWN hnot hPM hP hyP ((zpowers_le.mpr hyB).trans hBZ2)
    exact hyW (hZ₀W (hBZ y hyB (hXZ (mem_zpowers y))))

theorem rankThreeGamma_le_of_inU_of_normalizer_zpowers_le {M W B : Subgroup G}
    (hNM : normalizer (M : Set G) = M) (hU : UC6.InU M W) (hWB : W ≤ B)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hN : ∀ y ∈ B, y ≠ 1 → normalizer ((zpowers y : Subgroup G) : Set G) ≤ M) :
    rankThreeGamma 1 3 B ≤ M := by
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall (p := 3) (k := 1) (P := B)
    (M := M) ?_
  intro Y hYB hY
  obtain ⟨y, hyY, hy1⟩ :=
    Y.bot_or_exists_ne_one.resolve_left (uc22p22qv_ne_bot_of_pRank Nat.prime_three hY)
  intro g hg
  have hgy : g * y * g⁻¹ ∈ Y := (mem_normalizer_iff.mp hg y).mp hyY
  have hle : W ≤ M.map (MulAut.conj g).toMonoidHom := by
    intro w hw
    have h1 := hBc w (hWB hw) (g * y * g⁻¹) (hYB hgy)
    have hc : g⁻¹ * w * g ∈ centralizer ((zpowers y : Subgroup G) : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
      calc g⁻¹ * w * g * y = g⁻¹ * (w * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * w) * g := by rw [h1]
        _ = y * (g⁻¹ * w * g) := by group
    refine ⟨g⁻¹ * w * g, hN y (hYB hyY) hy1 (centralizer_le_normalizer _ hc), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hconj : CFSG.Open.uniqueFourConj g⁻¹ M = M.map (MulAut.conj g).toMonoidHom := by
    rw [CFSG.Open.uniqueFourConj, inv_inv]
  have hMg := hU.2 g⁻¹ (hconj ▸ hle)
  rw [hconj] at hMg
  rw [← hNM]
  exact mem_normalizer_iff_map_conj_eq.mpr hMg

theorem centralizer_le_of_inf_planes_eq_bot {D : Data G} (h69 : UC6.R6_9 D)
    (hsub : D.sig ⊆ D.sig1) {P B Z₀ : Subgroup G} (hPM : P ≤ D.M) (hP : IsPGroup 3 P)
    (hBP : B ≤ P) (hBel : IsElemAbelian 3 B) (hBc : Nat.card B = 27)
    (hPB : P ≤ normalizer (B : Set G))
    (hBZ2 : B ≤ (Subgroup.upperCentralSeries ↥P 2).map P.subtype) (hZ₀B : Z₀ ≤ B)
    (hZ₀c : Nat.card Z₀ = 3) (hBZ : ∀ b ∈ B, b ∈ (center ↥P).map P.subtype → b ∈ Z₀)
    (hΓB : rankThreeGamma 1 3 B ≤ D.M) (hm3 : CFSG.Open.pRank 3 D.M ≤ 3) {A : Subgroup G}
    (hAP : A ≤ P) (hAc : Nat.card A = 3) (hAB : A ⊓ B = ⊥) :
    centralizer (A : Set G) ≤ D.M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hnot
  obtain ⟨a, haA, ha1⟩ := A.bot_or_exists_ne_one.resolve_left fun h => by
    rw [h, card_bot] at hAc
    norm_num at hAc
  have haP : a ∈ P := hAP haA
  have hcomZ : ∀ b ∈ B, b * a * b⁻¹ * a⁻¹ ∈ Z₀ := by
    intro b hb
    have h1 : a * b⁻¹ * a⁻¹ ∈ B := (mem_normalizer_iff.mp (hPB haP) b⁻¹).mp (B.inv_mem hb)
    have hmem : b * a * b⁻¹ * a⁻¹ ∈ B := by
      rw [show b * a * b⁻¹ * a⁻¹ = b * (a * b⁻¹ * a⁻¹) by group]
      exact B.mul_mem hb h1
    refine hBZ _ hmem ?_
    obtain ⟨b', hb', rfl⟩ := hBZ2 hb
    have hb'' : b' ∈ Subgroup.upperCentralSeries ↥P (1 + 1) := hb'
    rw [Subgroup.mem_upperCentralSeries_succ_iff, Subgroup.upperCentralSeries_one] at hb''
    exact ⟨_, hb'' ⟨a, haP⟩, rfl⟩
  have hidx := CFSG.Quasithin.Stroth.caseA_relIndex_centralizer_le_card_of_comm_mem
    (fun z hz b hb => hBel.comm (hZ₀B hz) hb) hcomZ
  rw [hZ₀c] at hidx
  have hmul := relIndex_mul_card (H := B ⊓ centralizer ({a} : Set G)) (K := B)
  rw [inf_eq_left.mpr inf_le_left, hBc] at hmul
  have hK9 : 3 ^ 2 ≤ Nat.card ↥(B ⊓ centralizer ({a} : Set G)) := by
    by_contra h
    have h8 : Nat.card ↥(B ⊓ centralizer ({a} : Set G)) ≤ 8 := by omega
    have := Nat.mul_le_mul hidx h8
    omega
  obtain ⟨E, hEK, hEel, hEc⟩ := UC6S846.exists_card_p_sq Nat.prime_three (hBel.mono inf_le_left) hK9
  have hEM : E ≤ D.M := (hEK.trans inf_le_left).trans (hBP.trans hPM)
  have hΓE : rankThreeGamma 1 3 E ≤ D.M :=
    (CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := 3) (k := 1)
      (hEK.trans inf_le_left)).trans hΓB
  have ha3 : a ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥A) (x := ⟨a, haA⟩)
    simpa [hAc] using congrArg Subtype.val h
  have hAeq : zpowers a = A := eq_of_le_of_card_ge (zpowers_le.mpr haA)
    (by rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1, hAc])
  have hEN : E ≤ normalizer (A : Set G) := by
    rw [← hAeq]
    intro e he
    apply centralizer_le_normalizer
    rw [zpowers_eq_closure, centralizer_closure]
    exact (hEK he).2
  have hnotN : ¬ normalizer (A : Set G) ≤ D.M := fun h =>
    hnot ((centralizer_le_normalizer _).trans h)
  have hAB' : ∀ x ∈ A, ∀ b ∈ B, x * b = b * x := fun x hx b hb =>
    commute_of_mem_upperCentral_two_of_R6_9 h69 hsub Nat.prime_three (by norm_num) hEM hEel hEc
      hΓE Nat.prime_three (hAP.trans hPM) hAc hEN hnotN hPM hP hAP (hBZ2 hb) hx
  have hel := (CFSG.GroupTheory.isElemAbelian_of_card_prime hAc).sup_of_commute hBel hAB'
  have hcard := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute hAB'
  rw [hAB, card_bot, mul_one, hAc, hBc] at hcard
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.SectionRank.le_pRank (by norm_num) (sup_le (hAP.trans hPM) (hBP.trans hPM)) hel (k := 4)
      (by rw [hcard]; norm_num)
  omega

theorem isStronglyPEmbedded_three_of_not_le_normalizer {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h63 : UC6.R6_3 D) (h69 : UC6.R6_9 D) (h76 : F07.R76Sig D)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : ¬ D.M ≤ normalizer (L : Set G))
    (hr : CFSG.Open.pRank 3 L ≤ 2) (hZ : Nat.card (center (Bar2 L)) ≤ 3)
    (hZS : ∀ S : Sylow 3 (Bar2 L), Nat.card (center (S : Subgroup (Bar2 L))) = 3)
    (hAut : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 1)
    (hm3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L))) :
    IsStronglyPEmbedded 3 D.M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hns3
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hsub : D.sig ⊆ D.sig1 := UC6S846.sig_subset_sig1 hSg hns
  have h3σ : 3 ∉ D.sig := fun h => hns3 (UC6S846.sp_of_mem_sig hSg hns h)
  have hm3M : CFSG.Open.pRank 3 D.M ≤ 3 := by
    by_contra h
    exact h3σ (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega))
  have hLM : L ≤ D.M := hL.1.le
  have hrL : CFSG.Open.pRank 3 L = 2 := by
    have h := pRank_bar2_eq_of_odd (Y := L) Nat.prime_three (by norm_num)
    omega
  have h2 : (conjSetOf D.M L).ncard ≤ 2 :=
    ncard_conjSetOf_le_two_of_three_conj_rank (fun L₁ h₁ L₂ h₂ L₃ h₃ h12 h13 h23 =>
      four_le_pRank_three_of_three_conj_of_center hL h₁ h₂ h₃ h12 h13 h23 hrL hZ) hm3M
  obtain ⟨g, hgM, hgN⟩ : ∃ g ∈ D.M, g ∉ normalizer (L : Set G) := by
    by_contra hc
    push Not at hc
    exact hN hc
  set L' : Subgroup G := L.map (MulAut.conj g).toMonoidHom with hL'def
  have hL'mem : L' ∈ conjSetOf D.M L := ⟨g, hgM, rfl⟩
  have hne : L ≠ L' := fun he => hgN (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hL' : L' ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hL hL'mem
  have hL'M : L' ≤ D.M := hL'.1.le
  have h2' : (conjSetOf D.M L').ncard ≤ 2 := by rw [uc22p2214_conjSetOf_eq hL'mem]; exact h2
  obtain ⟨eL⟩ : Nonempty (Bar2 L ≃* Bar2 L') := uc22p20d_bar2_conj g L
  have hrL' : CFSG.Open.pRank 3 L' = 2 := by
    rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num),
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eL,
      pRank_bar2_eq_of_odd Nat.prime_three (by norm_num), hrL]
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  have hPM : P ≤ D.M := hP.le
  have hPp : IsPGroup 3 P := hP.isPGroup
  have hR : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn hP hLM
      hL.1.subgroupOf
  have hR' : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L') L' :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn hP hL'M
      hL'.1.subgroupOf
  have hPR : P ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_normalizer (sylow_le_normalizer_of_ncard_conjSetOf_le_two hP hL h2)).trans
      inf_normalizer_le_normalizer_inf
  have hPR' : P ≤ normalizer ((P ⊓ L' : Subgroup G) : Set G) :=
    (le_inf le_normalizer (sylow_le_normalizer_of_ncard_conjSetOf_le_two hP hL' h2')).trans
      inf_normalizer_le_normalizer_inf
  have hdisj : Disjoint P (pCoreOf 2 D.M) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hPp (UC6S846.isPGroup_pCoreOf D.M)
  have hcomm : ∀ r ∈ P ⊓ L, ∀ r' ∈ P ⊓ L', r * r' = r' * r := by
    intro r hr r' hr'
    have hc : ⁅r, r'⁆ ∈ pCoreOf 2 D.M :=
      PartTwo.commutator_mem_pCoreOf_of_ne hL hL' hne hr.2 hr'.2
    have hcP : ⁅r, r'⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hr.1 hr'.1) (P.inv_mem hr.1)) (P.inv_mem hr'.1)
    exact commutatorElement_eq_one_iff_mul_comm.mp (disjoint_def.mp hdisj hcP hc)
  have hRrk : 2 ≤ CFSG.Open.pRank 3 (P ⊓ L) := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_isSylowOf3 Nat.prime_three hR, hrL]
  have hR'rk : 2 ≤ CFSG.Open.pRank 3 (P ⊓ L') := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_isSylowOf3 Nat.prime_three hR', hrL']
  obtain ⟨W, B, Z₀, hWR, hWel, hWc, hWB, hBP, hBel, hBc, hPB, hBZ2, hZ₀W, hZ₀c, hBZ⟩ :=
    exists_planes_of_commute hPp inf_le_left inf_le_left hPR hPR' hcomm
      (card_center_of_isSylowOf_of_bar2 hR hZS)
      (card_center_of_isSylowOf_of_bar2 hR' (card_center_sylow_eq_of_mulEquiv eL hZS))
      (CFSG.Goldschmidt.Sec82.not_isCyclic_of_two_le_pRank Nat.prime_three hRrk)
      (CFSG.Goldschmidt.Sec82.not_isCyclic_of_two_le_pRank Nat.prime_three hR'rk)
      ((CFSG.SectionRank.pRank_mono (by norm_num) hPM).trans hm3M)
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpσ
  have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hpσ)
  have : Fact p.Prime := ⟨hpp⟩
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hpσ
  obtain ⟨Bp, hBpM, hBpel, hBpc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := D.M) hpp (k := 3) (hSg.three_le p hpσ)
  have hBpN : Bp ≤ normalizer (L : Set G) := fun x hx =>
    mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order h2 (hBpM hx)
      ((hpp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one (hBpel.2 x hx)))
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut_le hLM hpp hp2 (k := 1)
    (hAut p hpp hp2 hp3) hBpM hBpN hBpel hBpc Nat.prime_three (by norm_num) inf_le_right
    hR.isPGroup
  have hΓR : rankThreeGamma 1 3 (P ⊓ L) ≤ D.M :=
    Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp (h76 p hpσ hp2 hsp)
      (inf_le_right.trans hLM) hR.isPGroup hRrk hF
  have hWL : W ≤ L := hWR.trans inf_le_right
  have hU : UC6.InU D.M W :=
    inU_of_isElemAbelian_card_nine_le_of_isSylowOf h63 hLM hR hΓR hWL hWel hWc
  have hΓW : rankThreeGamma 1 3 W ≤ D.M :=
    gamma_le_of_isElemAbelian_le_of_isSylowOf hLM hR hΓR hWL hWel
  have hΓB : rankThreeGamma 1 3 B ≤ D.M :=
    rankThreeGamma_le_of_inU_of_normalizer_zpowers_le
      (UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal) hU hWB
      (fun a ha b hb => hBel.comm ha hb) fun y hy hy1 =>
        normalizer_zpowers_le_of_mem_planes h69 hsub hPM hPp hWel hWc hWB hBP hBel hBZ2 hZ₀W
          hBZ hΓW hy hy1
  have hBrk : CFSG.Open.pRank 3 B = 3 :=
    le_antisymm ((CFSG.SectionRank.pRank_mono (by norm_num) (hBP.trans hPM)).trans hm3M)
      (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hBel (k := 3) (by rw [hBc]; norm_num))
  have hNP : normalizer (P : Set G) ≤ D.M :=
    normalizer_le_of_gammaQ (hBP.trans hPM) hBel.isPGroup hBrk hBP hP hm3M hΓB
  have hC : ∀ x ∈ P, orderOf x = 3 → centralizer ({x} : Set G) ≤ D.M := fun x hx hxo =>
    centralizer_le_of_mem_of_gamma hΓB (fun A hAP hAc hAB =>
      centralizer_le_of_inf_planes_eq_bot h69 hsub hPM hPp hBP hBel hBc hPB hBZ2
        (hZ₀W.trans hWB) hZ₀c hBZ hΓB hm3M hAP hAc hAB) hx hxo
  have : IsSimpleGroup G := D.standing.simple
  have hMtop : D.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
  have hP1 : P ≠ ⊥ := by
    intro h
    have h1 : Nat.card B ≤ Nat.card (⊥ : Subgroup G) := card_le_of_le (h ▸ hBP)
    rw [card_bot, hBc] at h1
    omega
  exact hns3 (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le hMtop hP hP1
    hNP hC)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
