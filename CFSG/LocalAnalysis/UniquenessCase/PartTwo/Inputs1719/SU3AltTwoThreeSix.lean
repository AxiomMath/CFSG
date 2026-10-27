module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveCaseTwoBound
public import CFSG.Quasithin.Background.SmithB51LnSub

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem altTwo_three_six (hW : ∀ w : W, w ^ 2 = 1) {Y K : Subgroup (MulAut W)} {n : ℕ}
    (hKY : K ≤ Y) (hKcomp : CFSG.Open.IsComponentOf K Y) (hSU : IsSU3 ↥K n) (hn3 : 3 ≤ n)
    (hsum : IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X (⊥ : Subgroup W))))
    {I : Subgroup W} (hI : I ∈ irrSet K)
    (hmn : (E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) : ℚ) *
        ((rk ↥(commV (autQuot K (⊥ : Subgroup W))) : ℚ) /
          (rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) : ℚ)) ≤ E3.mParam Y)
    (hmY : E3.mParam Y ≤ 2 * n + 2) (h36 : W4Lem3_6) :
    NatSUn (autQuot (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W))))
        (fixV (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))))) ⊤ ⊥ 3 n ∧
      2 * n ≤ E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) ∧ 2 * n ≤ E3.mParam Y := by
  classical
  let Z : Subgroup W := ⊥
  let Istar : Subgroup (W ⧸ Z) := I.map (QuotientGroup.mk' Z)
  let Lstar : Subgroup (MulAut ↥Istar) := autSub (autQuot K Z) Istar
  let G1 : Subgroup (MulAut ↥Istar) := autSub (autQuot Y Z) Istar
  let C : Subgroup ↥Istar := fixV Lstar
  let Wq := ↥Istar ⧸ C
  let X : Subgroup (MulAut Wq) := autQuot Lstar C
  let G1q : Subgroup (MulAut Wq) := autQuot G1 C
  have hKZ : K ≤ stabSub Z := CFSG.Quasithin.B5.Ln.stabSub_bot_le K
  have hZK : Z ≤ fixV K := bot_le
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
    S17.caseTwo_Lstar_quasisimple hKq hKZ hZK hI hnotI
  have hLstarqC : CFSG.IsQuasisimple ↥Lstar :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hLstarq
  have hLstarNe : Lstar ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot Lstar).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hLstarqC)
  have hLC : Lstar ≤ stabSub C := CFSG.Quasithin.RonanF918.le_stabSub_fixV Lstar
  have hLG1 : Lstar ≤ G1 := autSub_mono (autQuot_mono hKY Z) Istar
  have hLnorm : (Lstar.subgroupOf G1).Normal :=
    autSub_autQuot_subgroupOf_normal_of_isDirSumOver (W := W) hKZ hZK hI hsum hKY
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
  have hVexp : ∀ v : W ⧸ Z, v ^ 2 = 1 := by
    intro v
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_pow, hW u, QuotientGroup.mk_one]
  have hWexp : ∀ w : ↥Istar, w ^ 2 = 1 := by
    intro w
    exact Subtype.ext (by simpa using hVexp (w : W ⧸ Z))
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
  have hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn X :=
    isIrrOn_autQuot_fixV_autSub hKZ hZK hI
  have eX : (X ⧸ Subgroup.center X) ≃* (↥K ⧸ Subgroup.center ↥K) := by
    have e1 : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* (X ⧸ Subgroup.center X) :=
      CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple (φ := π) hLstarqC hπsurj hπker
    have e0 : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* (↥K ⧸ Subgroup.center ↥K) :=
      Classical.choice (S17.caseTwo_Lstar_centerQuot_equiv_barInf hKq hKZ hZK hI hnotI
        (B := ↥K ⧸ Subgroup.center ↥K) (MulEquiv.refl _))
    exact e1.symm.trans e0
  have hXle : X ≤ G1q := autQuot_mono hLG1 C
  have hG1qnorm : G1q ≤ Subgroup.normalizer (X : Set (MulAut Wq)) :=
    CFSG.Quasithin.d3q_autQuot_le_normalizer hLG1 hG1C hG1norm
  have hIle : Istar ≤ commV (autQuot K Z) := by
    have h1 : I ≤ commV K := by
      rw [CFSG.Quasithin.commV_eq_commSub]
      calc I = commSub I K := hI.1.symm
        _ ≤ commSub (⊤ : Subgroup W) K := commSub_mono le_top le_rfl
    calc Istar = I.map (QuotientGroup.mk' Z) := rfl
      _ ≤ (commV K).map (QuotientGroup.mk' Z) := Subgroup.map_mono h1
      _ = commV (autQuot K Z) := map_commV_eq_commV_autQuot K Z hKZ
  have hIstarPos : 0 < rk ↥Istar :=
    Nat.pos_of_ne_zero fun h0 =>
      hIstarNe ((rk_eq_zero_iff (V := W ⧸ Z) hVexp (H := Istar)).1 h0)
  have hcast : (rk ↥Istar : ℚ) ≤ (rk ↥(commV (autQuot K Z)) : ℚ) := by
    exact_mod_cast rk_mono hIle
  have hn1 : (1 : ℚ) ≤ (rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ) := by
    rw [le_div_iff₀ (by exact_mod_cast hIstarPos)]
    simpa using hcast
  have hmleN : (E3.mParam G1 : ℚ) ≤ (E3.mParam Y : ℚ) := by
    calc (E3.mParam G1 : ℚ) = (E3.mParam G1 : ℚ) * 1 := by ring
      _ ≤ (E3.mParam G1 : ℚ) *
          ((rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ)) :=
          mul_le_mul_of_nonneg_left hn1 (by exact_mod_cast Nat.zero_le _)
      _ ≤ (E3.mParam Y : ℚ) := hmn
  have hmleN' : E3.mParam G1 ≤ E3.mParam Y := by exact_mod_cast hmleN
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
  let Y' : Subgroup (MulAut Wq) := X ⊔ Subgroup.zpowers s0q
  have hXY : X ≤ Y' := le_sup_left
  have hs0qY : s0q ∈ Y' := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hs0qG1q : s0q ∈ G1q :=
    mem_autQuot.mpr ⟨⟨s₀, hs₀C⟩, hs₀G1, rfl⟩
  have hYle : Y' ≤ G1q := sup_le hXle (Subgroup.zpowers_le.mpr hs0qG1q)
  have hXN : (X.subgroupOf Y').Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hYle.trans hG1qnorm)
  have hNtriv : Nontrivial Wq := QuotientGroup.nontrivial_iff.mpr hCneTop
  have hF : Fstar Y' = X :=
    fstar_eq_of_generalizedFitting_eq hXY
      (@CFSG.GroupTheory.fstar_sup_zpowers_eq_of_quasisimple_normal Wq _ _ hNtriv hWq'
        X Y' hXY hXq hirr hXN s0q hs0qY hs0qsq hs0qne)
  have hYirr : IsIrrOn Y' ⊤ ⊥ :=
    @S17.isIrrOn_top_bot_of_rankThree Wq _ hNtriv X Y' hirr hXY
  have hmY' : E3.mParam Y' ≤ rkIdx (fixV (Subgroup.zpowers s0q)) :=
    CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two hs0qY hs0qord
  have hrk : rkIdx (fixV (Subgroup.zpowers s0q)) ≤ rkIdx (fixV (Subgroup.zpowers s₀)) :=
    CFSG.Quasithin.f918v6f_rkIdx_le hs₀C
  have hchain : E3.mParam Y' ≤ E3.mParam G1 := by
    calc E3.mParam Y' ≤ rkIdx (fixV (Subgroup.zpowers s0q)) := hmY'
      _ ≤ rkIdx (fixV (Subgroup.zpowers s₀)) := hrk
      _ = E3.mParam G1 := hs₀rk
  have hXSU : IsSU3 ↥X n := ⟨hXqopen, CFSG.Blueprint.LieModel.of_mulEquiv eX.symm hSU.2⟩
  have hmY6 : E3.mParam Y' ≤ 2 * n + 2 := hchain.trans (hmleN'.trans hmY)
  obtain ⟨hnatX, hmYeq⟩ := h36 Wq hWq Y' X n hXY hXN hF hXSU (by omega) hYirr hmY6
  have h2nG : 2 * n ≤ E3.mParam G1 := hmYeq ▸ hchain
  exact ⟨hnatX, h2nG, h2nG.trans hmleN'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
