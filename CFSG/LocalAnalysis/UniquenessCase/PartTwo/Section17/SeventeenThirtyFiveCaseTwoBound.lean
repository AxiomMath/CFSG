module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34NatModuleIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isIrrOn_top_bot_of_rankThree {W : Type} [CommGroup W] [Nontrivial W]
    {X Y : Subgroup (MulAut W)} (h : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn X)
    (hXY : X ≤ Y) : IsIrrOn Y ⊤ ⊥ := by
  have hbot : (⊥ : Subgroup W) < ⊤ := by
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    refine lt_of_le_of_ne bot_le ?_
    intro h
    have hmem : w ∈ (⊤ : Subgroup W) := Subgroup.mem_top w
    rw [← h] at hmem
    exact hw (Subgroup.mem_bot.mp hmem)
  refine ⟨hbot, ?_, ?_, ?_⟩
  · intro y _ u _
    exact Subgroup.mem_top _
  · intro y _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro J hJ _ _
    exact CFSG.GroupTheory.isIrrOn_mono h hXY J hJ

theorem caseTwo_three_six
    {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {K : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hK : K = barSub V₀ V h.isElemAbelian L)
    {Z : Subgroup (Vtil V₀ V h.isElemAbelian)}
    (hZ : Z = fixSupConjSet K (Mbar D.M V₀ V h.isElemAbelian))
    (hsum : IsDirSumOver (conjSet K (Mbar D.M V₀ V h.isElemAbelian))
      (fun X => commV (autQuot X Z)))
    {I : Subgroup (Vtil V₀ V h.isElemAbelian)} (hI : I ∈ irrSet K)
    (hmn : (E3.mParam (autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian) Z)
        (I.map (QuotientGroup.mk' Z))) : ℚ) *
      ((rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥(I.map (QuotientGroup.mk' Z)) : ℚ)) ≤
      mBar D.M V₀ V h.isElemAbelian)
    {n : ℕ} (hshape : IsSU3 (Bar2 L) n) (hn2 : 2 ≤ n)
    (hmle : mBar D.M V₀ V h.isElemAbelian ≤ n + 2)
    (h36 : W4Lem3_6) :
    n = 2 ∧ mBar D.M V₀ V h.isElemAbelian = 4 ∧
      I.map (QuotientGroup.mk' Z) = commV (autQuot K Z) ∧
      NatSUn (autQuot (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z)))
        (fixV (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))))) ⊤ ⊥ 3 2 := by
  subst hK
  subst hZ
  classical
  let K := barSub V₀ V h.isElemAbelian L
  let Mbar := Mbar D.M V₀ V h.isElemAbelian
  let H : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) := ⨆ X ∈ conjSet K Mbar, X
  let Z : Subgroup (Vtil V₀ V h.isElemAbelian) := fixV H
  let Istar : Subgroup (Vtil V₀ V h.isElemAbelian ⧸ Z) := I.map (QuotientGroup.mk' Z)
  let Lstar : Subgroup (MulAut ↥Istar) := autSub (autQuot K Z) Istar
  let G1 : Subgroup (MulAut ↥Istar) := autSub (autQuot Mbar Z) Istar
  let C : Subgroup ↥Istar := fixV Lstar
  let Wq := ↥Istar ⧸ C
  let X : Subgroup (MulAut Wq) := autQuot Lstar C
  let G1q : Subgroup (MulAut Wq) := autQuot G1 C
  have hKcomp : K ∈ compBar D.M V₀ V h.isElemAbelian :=
    barSub_mem_compBar_of_ne_bot h hL hne
  have hKleM : K ≤ Mbar := hKcomp.1
  have hKmem : K ∈ conjSet K Mbar := ⟨1, Mbar.one_mem, by ext x; simp [MulAut.conj_apply]⟩
  have hKleH : K ≤ H := le_iSup₂_of_le (f := fun X (_ : X ∈ conjSet K Mbar) => X) K hKmem le_rfl
  have hKZ : K ≤ stabSub Z := hKleH.trans (CFSG.Quasithin.RonanF918.le_stabSub_fixV H)
  have hZK : Z ≤ fixV K := fixV_anti hKleH
  have hnotI : ¬ I ≤ Z := by
    intro hle
    exact CFSG.LocalAnalysis.WeakClosure81.not_le_fixV_of_mem_irrSet (X := K) (I := I) hI
      (hle.trans hZK)
  have hIstarNe : Istar ≠ ⊥ := by
    intro hbot
    have hle : I ≤ Z := by
      rw [Subgroup.map_eq_bot_iff] at hbot
      rwa [QuotientGroup.ker_mk'] at hbot
    exact hnotI hle
  have hKq : CFSG.IsQuasisimple K := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hKcomp.2.2
  have hLstarq : CFSG.Open.IsQuasisimple ↥Lstar :=
    caseTwo_Lstar_quasisimple hKq hKZ hZK hI hnotI
  have hLstarqC : CFSG.IsQuasisimple ↥Lstar :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hLstarq
  have hLstarNe : Lstar ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot Lstar).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hLstarqC)
  have hLC : Lstar ≤ stabSub C := CFSG.Quasithin.RonanF918.le_stabSub_fixV Lstar
  have hLG1 : Lstar ≤ G1 := autSub_mono (autQuot_mono hKleM Z) Istar
  have hLnorm : (Lstar.subgroupOf G1).Normal :=
    autSub_autQuot_subgroupOf_normal_of_isDirSumOver (W := Vtil V₀ V h.isElemAbelian)
      hKZ hZK hI hsum hKleM
  have hG1norm : G1 ≤ Subgroup.normalizer (Lstar : Set (MulAut ↥Istar)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG1).mp hLnorm
  have hG1C : G1 ≤ stabSub C :=
    CFSG.Quasithin.B1.le_stabSub_of_invariant (fun g hg w hw =>
      CFSG.Quasithin.RonanF918.apply_mem_fixV_of_mem_normalizer (hG1norm hg) hw)
  have hcommW : commSub Istar (autQuot K Z) = Istar := by
    have h1 := map_commSub_eq_commSub_autQuot (K := K) (Z := Z) (I := I) hKZ
    rw [hI.1] at h1
    exact h1.symm
  have hcommIstar : commSub (⊤ : Subgroup ↥Istar) Lstar = ⊤ :=
    commSub_top_autSub_eq_top (X := autQuot K Z) (U := Istar)
      (autQuot_le_stabSub_map hI.2.2.1) hcommW
  have hCneTop : C ≠ ⊤ := by
    intro htop
    have hLbot : Lstar = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      apply MulEquiv.ext
      intro u
      have hu : u ∈ C := htop ▸ Subgroup.mem_top u
      simpa using (mem_fixV.mp hu) l hl
    exact hLstarNe hLbot
  have htopStab : G1 ≤ stabSub (⊤ : Subgroup ↥Istar) := by
    intro g _
    rw [mem_stabSub]
    intro u
    exact ⟨fun _ => Subgroup.mem_top _, fun _ => Subgroup.mem_top _⟩
  have hVexp : ∀ v : Vtil V₀ V h.isElemAbelian ⧸ Z, v ^ 2 = 1 := by
    intro v
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    show (QuotientGroup.mk' Z u) ^ 2 = 1
    rw [← map_pow]
    have h1 : u ^ 2 = 1 := by
      induction u using QuotientGroup.induction_on with
      | H y => rw [← QuotientGroup.mk_pow, IntMod.sq_eq_one, QuotientGroup.mk_one]
    rw [h1, map_one]
  have hWexp : ∀ w : ↥Istar, w ^ 2 = 1 := by
    intro w
    exact Subtype.ext (by simpa using hVexp (w : Vtil V₀ V h.isElemAbelian ⧸ Z))
  have hWq : ∀ w : Wq, w ^ 2 = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, hWexp x, QuotientGroup.mk_one]
  have hWq' : ∀ w : Wq, w * w = 1 := fun w => by rw [← pow_two]; exact hWq w
  let π : ↥Lstar →* X := CFSG.Quasithin.D37Lift.toQuot C Lstar hLC
  have hπsurj : Function.Surjective π :=
    CFSG.Quasithin.D37Lift.toQuot_surjective C Lstar hLC
  have hfaith : ∀ (s : MulAut ↥Istar) (hs : s ∈ stabSub C), s ∈ G1 →
      quotHom C ⟨s, hs⟩ = 1 → s = 1 := by
    intro s hs hsG1 hq
    have hsU : ∀ u ∈ (⊤ : Subgroup ↥Istar), s u * u⁻¹ ∈ C := by
      intro u _
      have h1 : (QuotientGroup.mk (s u) : Wq) = QuotientGroup.mk u := by
        have hthis := congrArg (fun f : MulAut Wq => f (QuotientGroup.mk u)) hq
        rw [quotHom_mk] at hthis
        simpa using hthis
      exact (CFSG.Quasithin.mk_eq_mk_iff (s u) u).1 h1
    have hfix := CFSG.Quasithin.d3q_faithful hLstarqC (le_rfl : C ≤ fixV Lstar)
      hLG1 hG1norm hG1C htopStab hcommIstar
      (fun hle => hCneTop (top_le_iff.mp hle)) hsG1 hsU
    exact MulEquiv.ext fun u => hfix u (Subgroup.mem_top u)
  have hXne : X ≠ ⊥ := by
    intro hbot
    obtain ⟨l, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hLstarNe
    have hq : quotHom C ⟨(l : MulAut ↥Istar), hLC l.2⟩ = 1 := by
      have hmem : quotHom C ⟨(l : MulAut ↥Istar), hLC l.2⟩ ∈ X :=
        mem_autQuot.mpr ⟨⟨(l : MulAut ↥Istar), hLC l.2⟩, l.2, rfl⟩
      rw [hbot] at hmem
      simpa using hmem
    have hq' : quotHom C ⟨(l : MulAut ↥Istar), hG1C (hLG1 l.2)⟩ = 1 := by
      simpa using hq
    have h1 : (l : MulAut ↥Istar) = 1 := hfaith _ _ (hLG1 l.2) hq'
    exact hl1 (Subtype.ext h1)
  have hXnt : ∃ l, π l ≠ 1 := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
    obtain ⟨l, rfl⟩ := hπsurj x
    exact ⟨l, by simpa using hx⟩
  have hπker : π.ker ≤ Subgroup.center ↥Lstar :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLstarqC hXnt
  have hXq : CFSG.IsQuasisimple ↥X := by
    have hmap : (Lstar.subgroupOf (stabSub C)).map (quotHom C) = X := rfl
    rw [← hmap]
    exact isQuasisimple_map_subgroupOf_of_ne_bot hLC hLstarqC (quotHom C) (by rwa [hmap])
  have hXqopen : CFSG.Open.IsQuasisimple ↥X :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hXq
  have hoddX : Odd (Nat.card (Subgroup.center ↥X)) := by
    have hcenter : Subgroup.center ↥X = (Subgroup.center ↥Lstar).map π :=
      CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hLstarqC hπsurj hπker
    rw [hcenter]
    exact Odd.of_dvd_nat
      (caseTwo_Lstar_odd_center hKq hKZ hZK hI hnotI (odd_center_barSub h hL hne))
      (Subgroup.card_map_dvd (H := Subgroup.center ↥Lstar) (f := π))
  have hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn X :=
    isIrrOn_autQuot_fixV_autSub hKZ hZK hI
  have eX : (X ⧸ Subgroup.center X) ≃* BarInf L := by
    have e1 : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* (X ⧸ Subgroup.center X) :=
      CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple (φ := π) hLstarqC hπsurj hπker
    let eBar : BarInf L ≃* K ⧸ Subgroup.center K :=
      Classical.choice (barSub_centerQuot_equiv_barInf (V₀ := V₀) (V := V) h hL hne)
    have e0 : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* BarInf L :=
      Classical.choice (caseTwo_Lstar_centerQuot_equiv_barInf hKq hKZ hZK hI hnotI
        (B := BarInf L) eBar)
    exact e1.symm.trans e0
  have hXle : X ≤ G1q := autQuot_mono hLG1 C
  have hG1qnorm : G1q ≤ Subgroup.normalizer (X : Set (MulAut Wq)) :=
    CFSG.Quasithin.d3q_autQuot_le_normalizer hLG1 hG1C hG1norm
  have hIle : Istar ≤ commV (autQuot K Z) := by
    have h1 : I ≤ commV K := by
      rw [CFSG.Quasithin.commV_eq_commSub]
      calc I = commSub I K := hI.1.symm
        _ ≤ commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian)) K := commSub_mono le_top le_rfl
    calc Istar = I.map (QuotientGroup.mk' Z) := rfl
      _ ≤ (commV K).map (QuotientGroup.mk' Z) := Subgroup.map_mono h1
      _ = commV (autQuot K Z) := map_commV_eq_commV_autQuot K Z hKZ
  have hIstarPos : 0 < rk ↥Istar :=
    Nat.pos_of_ne_zero fun h0 =>
      hIstarNe ((rk_eq_zero_iff (V := Vtil V₀ V h.isElemAbelian ⧸ Z) hVexp (H := Istar)).1 h0)
  have hcast : (rk ↥Istar : ℚ) ≤ (rk ↥(commV (autQuot K Z)) : ℚ) := by
    exact_mod_cast rk_mono hIle
  have hn1 : (1 : ℚ) ≤ (rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ) := by
    rw [le_div_iff₀ (by exact_mod_cast hIstarPos)]
    simpa using hcast
  have hmleN : (E3.mParam G1 : ℚ) ≤ (mBar D.M V₀ V h.isElemAbelian : ℚ) := by
    calc (E3.mParam G1 : ℚ) = (E3.mParam G1 : ℚ) * 1 := by ring
      _ ≤ (E3.mParam G1 : ℚ) *
          ((rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ)) :=
          mul_le_mul_of_nonneg_left hn1 (by exact_mod_cast Nat.zero_le _)
      _ ≤ (mBar D.M V₀ V h.isElemAbelian : ℚ) := hmn
  have hmleN' : E3.mParam G1 ≤ mBar D.M V₀ V h.isElemAbelian := by
    exact_mod_cast hmleN
  have hevenL : Even (Nat.card ↥Lstar) :=
    CFSG.ComponentClassification.Burgoyne.even_card_of_isQuasisimple hLstarqC
  have hevenG1 : Even (Nat.card ↥G1) := by
    have h2 : 2 ∣ Nat.card ↥G1 :=
      (even_iff_two_dvd.mp hevenL).trans (Subgroup.card_dvd_of_le hLG1)
    exact even_iff_two_dvd.mpr h2
  obtain ⟨s₀, hs₀G1, hs₀ord, hs₀rk⟩ :=
    CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam G1 hevenG1
  have hs₀C : s₀ ∈ stabSub C := hG1C hs₀G1
  have hs₀sq : s₀ * s₀ = 1 := by
    have h1 : s₀ ^ 2 = 1 := by rw [← hs₀ord]; exact pow_orderOf_eq_one s₀
    simpa [pow_two] using h1
  have hs₀ne : s₀ ≠ 1 := by
    intro h0
    rw [h0] at hs₀ord
    simp at hs₀ord
  let s0q : MulAut Wq := quotHom C ⟨s₀, hs₀C⟩
  have hs0qsq : s0q * s0q = 1 := by
    rw [show s0q * s0q = quotHom C (⟨s₀, hs₀C⟩ * ⟨s₀, hs₀C⟩) from (map_mul _ _ _).symm]
    have h1 : (⟨s₀, hs₀C⟩ * ⟨s₀, hs₀C⟩ : stabSub C) = 1 := by
      refine Subtype.ext ?_
      simpa [pow_two] using hs₀sq
    rw [h1, map_one]
  have hs0qne : s0q ≠ 1 := by
    intro hq
    exact hs₀ne (hfaith s₀ hs₀C hs₀G1 hq)
  have hs0qord : orderOf s0q = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hs0qsq) hs0qne
  let Y : Subgroup (MulAut Wq) := X ⊔ Subgroup.zpowers s0q
  have hXY : X ≤ Y := le_sup_left
  have hs0qY : s0q ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hs0qG1q : s0q ∈ G1q :=
    mem_autQuot.mpr ⟨⟨s₀, hs₀C⟩, hs₀G1, rfl⟩
  have hYle : Y ≤ G1q := sup_le hXle (Subgroup.zpowers_le.mpr hs0qG1q)
  have hXN : (X.subgroupOf Y).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hYle.trans hG1qnorm)
  have hNtriv : Nontrivial Wq := QuotientGroup.nontrivial_iff.mpr hCneTop
  have hF : Fstar Y = X :=
    fstar_eq_of_generalizedFitting_eq hXY
      (@CFSG.GroupTheory.fstar_sup_zpowers_eq_of_quasisimple_normal Wq _ _ hNtriv hWq'
        X Y hXY hXq hirr hXN s0q hs0qY hs0qsq hs0qne)
  have hYirr : IsIrrOn Y ⊤ ⊥ :=
    @isIrrOn_top_bot_of_rankThree Wq _ hNtriv X Y hirr hXY
  have hmY : E3.mParam Y ≤ rkIdx (fixV (Subgroup.zpowers s0q)) :=
    CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two hs0qY hs0qord
  have hrk : rkIdx (fixV (Subgroup.zpowers s0q)) ≤ rkIdx (fixV (Subgroup.zpowers s₀)) :=
    CFSG.Quasithin.f918v6f_rkIdx_le hs₀C
  have hchain : E3.mParam Y ≤ mBar D.M V₀ V h.isElemAbelian := by
    calc E3.mParam Y ≤ rkIdx (fixV (Subgroup.zpowers s0q)) := hmY
      _ ≤ rkIdx (fixV (Subgroup.zpowers s₀)) := hrk
      _ = E3.mParam G1 := hs₀rk
      _ ≤ mBar D.M V₀ V h.isElemAbelian := hmleN'
  have hU3 : LieModel (BarInf L) .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (Classical.choice
        (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL)).symm
      hshape.2
  have hXSU : IsSU3 ↥X n := ⟨hXqopen, CFSG.Blueprint.LieModel.of_mulEquiv eX.symm hU3⟩
  by_cases hn : n = 2
  ·
    have hmY6 : E3.mParam Y ≤ 2 * 2 := by
      calc E3.mParam Y ≤ mBar D.M V₀ V h.isElemAbelian := hchain
        _ ≤ n + 2 := hmle
        _ = 2 * 2 := by rw [hn]
    have hXSU2 : IsSU3 ↥X 2 := hn ▸ hXSU
    obtain ⟨hnatX, hmY4⟩ :=
      u34NatModule_of_rankThreeIrr hWq hXY hXN hXSU2 hirr hmY6
    have hmY4' : E3.mParam Y = 4 := by simpa using hmY4
    have hmbar4 : mBar D.M V₀ V h.isElemAbelian = 4 := by
      refine le_antisymm ?_ ?_
      · calc mBar D.M V₀ V h.isElemAbelian ≤ n + 2 := hmle
          _ = 4 := by rw [hn]
      · calc 4 = E3.mParam Y := hmY4'.symm
          _ ≤ mBar D.M V₀ V h.isElemAbelian := hchain
    have hmG14 : E3.mParam G1 = 4 := by
      refine le_antisymm ?_ ?_
      · calc E3.mParam G1 ≤ mBar D.M V₀ V h.isElemAbelian := hmleN'
          _ = 4 := hmbar4
      · calc 4 = E3.mParam Y := hmY4'.symm
          _ ≤ rkIdx (fixV (Subgroup.zpowers s0q)) := hmY
          _ ≤ rkIdx (fixV (Subgroup.zpowers s₀)) := hrk
          _ = E3.mParam G1 := hs₀rk
    have h4mul : (4 : ℚ) * ((rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ)) ≤ 4 := by
      have hq := hmn
      rw [hmG14, hmbar4] at hq
      norm_num at hq
      linarith
    have hratio_le : (rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ) ≤ 1 := by
      linarith
    have hratio_eq : (rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ) = 1 :=
      le_antisymm hratio_le hn1
    have hqeq : (rk ↥(commV (autQuot K Z)) : ℚ) = (rk ↥Istar : ℚ) := by
      have hpos : (rk ↥Istar : ℚ) ≠ 0 := by exact_mod_cast hIstarPos.ne'
      simpa using (div_eq_iff hpos).mp hratio_eq
    have hrkeq : rk ↥(commV (autQuot K Z)) = rk ↥Istar := by exact_mod_cast hqeq
    have hIeq : Istar = commV (autQuot K Z) :=
      CFSG.Quasithin.eq_of_le_of_rk_le hVexp hIle (le_of_eq hrkeq)
    refine ⟨hn, hmbar4, hIeq, ?_⟩
    simpa only [X, Lstar, Istar, C] using hnatX
  ·
    have hn2' : 2 < n := lt_of_le_of_ne hn2 (Ne.symm hn)
    have hmY6 : E3.mParam Y ≤ 2 * n + 2 := by
      calc E3.mParam Y ≤ mBar D.M V₀ V h.isElemAbelian := hchain
        _ ≤ n + 2 := hmle
        _ ≤ 2 * n + 2 := by omega
    obtain ⟨-, hmYeq⟩ :=
      h36 Wq hWq Y X n hXY hXN hF hXSU hn2' hYirr hmY6
    exfalso
    have hle : 2 * n ≤ n + 2 := by
      calc 2 * n = E3.mParam Y := hmYeq.symm
        _ ≤ mBar D.M V₀ V h.isElemAbelian := hchain
        _ ≤ n + 2 := hmle
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
