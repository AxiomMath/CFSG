module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
import CFSG.Adapters.GeneralizedFitting
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.CGT.PushingUpLit.T2KSW.FieldAutWeakClosure
import CFSG.CGT.PushingUp.BenderBridge
import CFSG.CGT.PushingUp.BlockOrder
import CFSG.CGT.PushingUpLit.BHS7.BlockComm
import CFSG.CGT.PushingUpLit.BHS7.SevenThree
import CFSG.CGT.PushingUpLit.BHS7.VFacts
import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

namespace TwelveEight

theorem fstar_eq_pCoreOf_of_mem_hSet {T M H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet T M) : Fstar H = pCoreOf 2 H := by
  have hc : CFSG.IsCharacteristicP 2 ↥H := by
    intro x hx
    have hx' : (x : G) ∈ H ⊓ centralizer (pCoreOf 2 H : Set G) := by
      refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨y', hy', rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx y' hy')
    obtain ⟨y, hy, hxy⟩ := hH.2.2 hx'
    have : y = x := Subtype.ext hxy
    rw [← this]
    exact hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥H 2).1 hc
  unfold Fstar pCoreOf
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, h]

theorem f12Hyp124_of_mem_hSet (D : Data G) {H₀ : Subgroup G}
    (hH : H₀ ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M)
    (h : CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M H₀) : F12.Hyp124 D H₀ := by
  refine ⟨hH.1, hH.2.1, fstar_eq_pCoreOf_of_mem_hSet hH, ?_, ?_⟩
  · rintro ⟨n, hn, h1, L, _, hL, hP⟩
    refine h.1 ⟨L, inferInstance, hL, n, hn, h1, ?_⟩
    rcases hP with hP | hP | hP
    · exact Or.inl hP
    · exact Or.inr (Or.inr hP)
    · exact Or.inr (Or.inl hP)
  · intro hs ⟨L, _, hL, hP⟩
    refine h.2 hs ⟨L, inferInstance, hL, ?_⟩
    rcases hP with ⟨n, hn, t, m, hP⟩ | hP | hP | hP | hP | hP | hP
    · exact Or.inl ⟨t, m, n, hn, hP⟩
    · exact Or.inr (Or.inl hP)
    · exact Or.inr (Or.inr (Or.inl hP))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hP)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hP)))))

theorem pRankMod_centralizer_eq {M V : Subgroup G} (hMV : M ≤ normalizer (V : Set G)) (p : ℕ) :
    F12.pRankMod p M (centralizer (V : Set G)) = CFSG.pRank p (MBar M V) := by
  haveI hn : (kerAct M V).Normal := kerAct_normal M V hMV
  have hn' : ((centralizer (V : Set G)).subgroupOf M).Normal := hn
  unfold F12.pRankMod
  rw [dif_pos hn', ← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.pRank_congr_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.normalCore_eq_self (kerAct M V)).symm) p

theorem mem_of_le_map_conj (D : Data G) {g : G}
    (hg : D.T ≤ D.M.map (MulAut.conj g).toMonoidHom) : g ∈ D.M := by
  exact CFSG.CGT.PushingUpLit.T2KSW.WeakCl.mem_of_le_map_conj D.sylowM D.normalizer_le le_rfl
    (fun X h1 h2 => le_antisymm h2 h1 ▸ Subgroup.le_normalizer)
    (fun X h1 h2 => le_antisymm h2 h1 ▸ D.normalizer_le) hg

theorem isTI_U (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (hW : ∀ W : Subgroup G, ¬ InCalW D.M D.T W) : IsTI D.U := by
  by_contra hU
  exact hW _ (uc22p22o_inCalW_U_of_not_isTI D hx h61 hU)

theorem centralizersUnique (D : Data G) (hU : IsTI D.U) : CentralizersUnique D.M D.T := by
  intro z hzT hzc hz1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUV := uc22p22e_inCalV_U D
  have hzle : Subgroup.zpowers z ≤ D.T := (Subgroup.zpowers_le).2 hzT
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := D.sylowM.isPGroup.to_le hzle
  have hcard : 2 ∣ Nat.card (Subgroup.zpowers z) := by
    rcases hzp.card_eq_or_dvd with h | h
    · exfalso
      apply hz1
      have hb : Subgroup.zpowers z = ⊥ := Subgroup.card_eq_one.1 h
      have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
      rw [hb] at this
      exact Subgroup.mem_bot.1 this
    · exact h
  obtain ⟨⟨y, hy⟩, hyo⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  have hyo' : orderOf y = 2 := by rw [← Subgroup.orderOf_mk y hy]; exact hyo
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hyT : z ^ j ∈ D.T := hzle hy
  have hy2 : (z ^ j) ^ 2 = 1 := by rw [← hyo']; exact pow_orderOf_eq_one _
  have hy1 : z ^ j ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyo'
    exact absurd hyo' (by norm_num)
  have hyZ : z ^ j ∈ D.Z := by
    refine CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.2 ⟨hyT, fun k hk => ?_, hy2⟩
    exact ((Commute.zpow_left (hzc k hk) j)).symm.eq
  have hyU : z ^ j ∈ D.U := by
    have : D.Z ≤ D.U := by
      intro w hw
      refine (le_iSup (fun m : D.M => (CFSG.RankThree.PartOne.omegaOneCenterIn D.T).map
        (MulAut.conj (m : G)).toMonoidHom) 1) ?_
      exact ⟨w, hw, by simp⟩
    exact this hyZ
  have hCy : centralizer ({z ^ j} : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.centralizer_le_of_isTI D.maxLocal hUV.1
      (uc22p22e_isPGroup_of_elem hUV.2.2.2) hUV.2.2.1 hU hyU hy1
  refine ⟨fun g hg => hCy ?_, fun g hg hle => hg (mem_of_le_map_conj D (le_trans ?_ hle))⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact ((Commute.zpow_right hg j)).eq
  · intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hzc t ht).symm

theorem not_twoReduced (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (hW : ∀ W : Subgroup G, ¬ InCalW D.M D.T W) {V : Subgroup G} (hV : InCalV D.M V)
    (hTI : ¬ IsTI V) : ¬ TwoReduced D.M V := by
  exact fun h2 => hW V ⟨uc22p22n_inCalV1_of_not_isTI D hx h61 hV hTI,
    uc22p22n_eight_le_card D hx h61 hV hTI, h2⟩

theorem exists_inCalV_lt (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (hW : ∀ W : Subgroup G, ¬ InCalW D.M D.T W) {V : Subgroup G} (hV : InCalV D.M V)
    (hTI : ¬ IsTI V) : ∃ V₀ : Subgroup G, InCalV D.M V₀ ∧ V₀ < V := by
  by_contra hno
  apply not_twoReduced D hx h61 hW hV hTI
  refine uc22p22na_twoReduced_of_irr D hV fun X hXV hMX => ?_
  by_cases hX : X = ⊥
  · exact Or.inl hX
  · refine Or.inr ?_
    by_contra hXne
    exact hno ⟨X, ⟨hX, hXV.trans hV.2.1, hMX, uc22p22n_isElemAbelian_of_le hXV hV.2.2.2⟩,
      lt_of_le_of_ne hXV hXne⟩

theorem closure_conj_eq (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h1214 : F12.R1214 D)
    (h124 : ∃ H₀ ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M,
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M H₀)
    {V₀ V : Subgroup G} (hV : InCalV D.M V) (hTI : ¬ IsTI V)
    (hmin : ∀ X : Subgroup G, InCalV D.M X → X < V → IsTI X)
    (hV₀ : InCalV D.M V₀) (hV₀V : V₀ < V)
    (hmax : ∀ X : Subgroup G, InCalV D.M X → X < V → V₀ ≤ X → X = V₀)
    {v : G} (hv : v ∈ V) (hv₀ : v ∉ V₀) :
    closure {x : G | ∃ m ∈ D.M, x = m * v * m⁻¹} = V := by
  set W := closure {x : G | ∃ m ∈ D.M, x = m * v * m⁻¹} with hWdef
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hWV : W ≤ V := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨m, hm, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hvW : v ∈ W := Subgroup.subset_closure ⟨1, D.M.one_mem, by simp⟩
  have hconj : ∀ m ∈ D.M, W.map (MulAut.conj m).toMonoidHom = W := by
    have key : ∀ m ∈ D.M, W.map (MulAut.conj m).toMonoidHom ≤ W := by
      intro m hm
      rw [hWdef, MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨x, ⟨m', hm', rfl⟩, rfl⟩
      exact ⟨m * m', D.M.mul_mem hm hm', by simp [MulAut.conj_apply, mul_assoc]⟩
    intro m hm
    refine le_antisymm (key m hm) ?_
    intro w hw
    refine ⟨m⁻¹ * w * m, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := key m⁻¹ (D.M.inv_mem hm) ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hMW : D.M ≤ normalizer (W : Set G) := fun m hm =>
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hconj m hm)
  have hv1 : v ≠ 1 := fun h => hv₀ (h ▸ V₀.one_mem)
  have hWin : InCalV D.M W := ⟨fun h => hv1 (by rw [h] at hvW; exact Subgroup.mem_bot.1 hvW),
    hWV.trans hV.2.1, hMW, uc22p22n_isElemAbelian_of_le hWV hV.2.2.2⟩
  by_contra hne
  have hWlt : W < V := lt_of_le_of_ne hWV hne
  have hsupV : V₀ ⊔ W = V := by
    have hsup_le : V₀ ⊔ W ≤ V := sup_le hV₀V.le hWV
    have hMsup : D.M ≤ normalizer ((V₀ ⊔ W : Subgroup G) : Set G) := by
      intro m hm
      have h1 : W.map (MulAut.conj m).toMonoidHom = W := hconj m hm
      have h2 : V₀.map (MulAut.conj m).toMonoidHom = V₀ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (hV₀.2.2.1 hm)
      refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
      have h3 := Subgroup.map_sup V₀ W (MulAut.conj m).toMonoidHom
      rw [h1, h2] at h3
      exact h3
    have hsupIn : InCalV D.M (V₀ ⊔ W) := ⟨fun h => hV₀.1 (le_bot_iff.1 (h ▸ le_sup_left)),
      hsup_le.trans hV.2.1, hMsup, uc22p22n_isElemAbelian_of_le hsup_le hV.2.2.2⟩
    by_contra hsne
    have h0 := hmax _ hsupIn (lt_of_le_of_ne hsup_le hsne) le_sup_left
    exact hv₀ (h0 ▸ (le_sup_right : W ≤ V₀ ⊔ W) hvW)
  obtain ⟨H₀, hH₀, h₀⟩ := h124
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hrank : 1 < F12.pRankMod p D.M (centralizer (V : Set G)) := by
    rw [pRankMod_centralizer_eq hMV]
    exact uc22p22n_one_lt_pRank_mbar D hx h61 hV hTI p hp
  rcases h1214 ⟨H₀, f12Hyp124_of_mem_hSet D hH₀ h₀⟩ V V₀ W V₀ hV hV₀ hWin hV₀ hsupV.symm
      hV₀V.ne' hWlt.ne' hV₀V.ne' p hp hrank with h | h
  · exact h (hmin V₀ hV₀ hV₀V)
  · exact h (hmin W hWin hWlt)

theorem exists_inCalV0 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h1214 : F12.R1214 D)
    (h124 : ∃ H₀ ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M,
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M H₀)
    (hne : ∃ V : Subgroup G, InCalV D.M V ∧ ¬ IsTI V)
    (hW : ∀ W : Subgroup G, ¬ InCalW D.M D.T W) :
    ∃ V₀ V : Subgroup G, InCalV0 D.M V₀ V := by
  obtain ⟨V, hVmin⟩ :=
    (Set.toFinite {V : Subgroup G | InCalV D.M V ∧ ¬ IsTI V}).exists_minimal hne
  obtain ⟨hV, hTI⟩ := hVmin.1
  have hmin : ∀ X : Subgroup G, InCalV D.M X → X < V → IsTI X := fun X hX hXV => by
    by_contra hXTI
    exact hXV.ne (hVmin.eq_of_le ⟨hX, hXTI⟩ hXV.le)
  obtain ⟨V₁, hV₁⟩ := exists_inCalV_lt D hx h61 hW hV hTI
  obtain ⟨V₀, hV₀max⟩ := (Set.toFinite {X : Subgroup G | InCalV D.M X ∧ X < V}).exists_maximal
    ⟨V₁, hV₁⟩
  obtain ⟨hV₀, hV₀V⟩ := hV₀max.1
  refine ⟨V₀, V, hV₀, hV, hV₀V.le, hmin V₀ hV₀ hV₀V, hTI, fun v hv hv₀ => ?_,
    not_twoReduced D hx h61 hW hV hTI⟩
  exact closure_conj_eq D hx h61 h1214 h124 hV hTI hmin hV₀ hV₀V
    (fun X hX hXV h0X => hV₀max.eq_of_ge ⟨hX, hXV⟩ h0X) hv hv₀

theorem exists_inCalWStar {M T : Subgroup G} (h : ∃ W : Subgroup G, InCalW M T W) :
    ∃ V : Subgroup G, InCalWStar M T V := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨V, hV⟩ := (Set.toFinite {W : Subgroup G | InCalW M T W}).exists_minimal ⟨W, hW⟩
  exact ⟨V, hV.1, fun W hW hWV => hV.eq_of_le hW hWV⟩

end TwelveEight

theorem twelve_eight_of_exists_not_isTI (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h1214 : F12.R1214 D) (hne : ∃ V : Subgroup G, InCalV D.M V ∧ ¬ IsTI V)
    (h124 : ∃ H₀ ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M,
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M H₀) :
    ∃ V₀ V : Subgroup G, Hyp125 D V₀ V := by
  by_cases hW : ∃ W : Subgroup G, InCalW D.M D.T W
  · obtain ⟨V, hV⟩ := TwelveEight.exists_inCalWStar hW
    exact ⟨⊥, V, Or.inl ⟨hV, rfl⟩, h124⟩
  · have hW' : ∀ W : Subgroup G, ¬ InCalW D.M D.T W := fun W hW'' => hW ⟨W, hW''⟩
    obtain ⟨V₀, V, h0⟩ := TwelveEight.exists_inCalV0 D hx h61 h1214 h124 hne hW'
    exact ⟨V₀, V, Or.inr ⟨h0, TwelveEight.centralizersUnique D (TwelveEight.isTI_U D hx h61 hW'),
      hW'⟩, h124⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

