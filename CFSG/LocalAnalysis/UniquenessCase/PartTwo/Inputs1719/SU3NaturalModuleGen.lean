module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleAltTwoHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem altTwo_su3_of_mParam_autSub_lt
    (hW : ∀ w : W, w ^ 2 = 1) {Y K : Subgroup (MulAut W)}
    (hKY : K ≤ Y) (hKcomp : CFSG.Open.IsComponentOf K Y) {n : ℕ} (hn : 2 ≤ n)
    (hSU : IsSU3 ↥K n)
    (hsum : IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X (⊥ : Subgroup W))))
    {I : Subgroup W} (hI : I ∈ irrSet K)
    (hmI : E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
      (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) < 3 * n) :
    NatSUn (autQuot (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W))))
        (fixV (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))))) ⊤ ⊥ 3 n ∧
      2 * n ≤ E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) := by
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
  have hmY' : E3.mParam Y' ≤ rkIdx (fixV (Subgroup.zpowers s0q)) :=
    CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two hs0qY hs0qord
  have hrk : rkIdx (fixV (Subgroup.zpowers s0q)) ≤ rkIdx (fixV (Subgroup.zpowers s₀)) :=
    CFSG.Quasithin.f918v6f_rkIdx_le hs₀C
  have hchain : E3.mParam Y' ≤ E3.mParam G1 := by
    calc E3.mParam Y' ≤ rkIdx (fixV (Subgroup.zpowers s0q)) := hmY'
      _ ≤ rkIdx (fixV (Subgroup.zpowers s₀)) := hrk
      _ = E3.mParam G1 := hs₀rk
  have hXSU : IsSU3 ↥X n := ⟨hXqopen, CFSG.Blueprint.LieModel.of_mulEquiv eX.symm hSU.2⟩
  have hmY'lt : E3.mParam Y' < 3 * n := lt_of_le_of_lt hchain hmI
  obtain ⟨hnatX, hmYeq⟩ := su3NatModule_of_irr hWq hXY hXN hn hXSU hirr hmY'lt
  have h2nG : 2 * n ≤ E3.mParam G1 := hmYeq ▸ hchain
  exact ⟨hnatX, h2nG⟩

theorem altTwo_su3
    (hW : ∀ w : W, w ^ 2 = 1) {Y K : Subgroup (MulAut W)}
    (hKY : K ≤ Y) (hKcomp : CFSG.Open.IsComponentOf K Y) {n : ℕ} (hn : 2 ≤ n)
    (hSU : IsSU3 ↥K n)
    (hsum : IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X (⊥ : Subgroup W))))
    {I : Subgroup W} (hI : I ∈ irrSet K)
    (hmn : (E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) : ℚ) *
        ((rk ↥(commV (autQuot K (⊥ : Subgroup W))) : ℚ) /
          (rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) : ℚ)) ≤ E3.mParam Y)
    (hmY : E3.mParam Y < 3 * n) :
    NatSUn (autQuot (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W))))
        (fixV (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))))) ⊤ ⊥ 3 n ∧
      2 * n ≤ E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) ∧ 2 * n ≤ E3.mParam Y := by
  classical
  have hKZ : K ≤ stabSub (⊥ : Subgroup W) := CFSG.Quasithin.B5.Ln.stabSub_bot_le K
  have hnotI : ¬ I ≤ (⊥ : Subgroup W) := by
    intro hle
    exact CFSG.LocalAnalysis.WeakClosure81.not_le_fixV_of_mem_irrSet (X := K) (I := I) hI
      (hle.trans (bot_le : (⊥ : Subgroup W) ≤ fixV K))
  have hIstarNe : I.map (QuotientGroup.mk' (⊥ : Subgroup W)) ≠ ⊥ := by
    intro hbot
    have hle : I ≤ (⊥ : Subgroup W) := by
      rw [Subgroup.map_eq_bot_iff] at hbot
      rwa [QuotientGroup.ker_mk'] at hbot
    exact hnotI hle
  have hVexp : ∀ v : W ⧸ (⊥ : Subgroup W), v ^ 2 = 1 := by
    intro v
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_pow, hW u, QuotientGroup.mk_one]
  have hIstarPos : 0 < rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) :=
    Nat.pos_of_ne_zero fun h0 =>
      hIstarNe ((rk_eq_zero_iff (V := W ⧸ (⊥ : Subgroup W)) hVexp
        (H := I.map (QuotientGroup.mk' (⊥ : Subgroup W)))).1 h0)
  have hIle : I.map (QuotientGroup.mk' (⊥ : Subgroup W)) ≤
      commV (autQuot K (⊥ : Subgroup W)) := by
    have h1 : I ≤ commV K := by
      rw [CFSG.Quasithin.commV_eq_commSub]
      calc I = commSub I K := hI.1.symm
        _ ≤ commSub (⊤ : Subgroup W) K := commSub_mono le_top le_rfl
    rw [← map_commV_eq_commV_autQuot K (⊥ : Subgroup W) hKZ]
    exact Subgroup.map_mono h1
  have hcast : (rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) : ℚ) ≤
      (rk ↥(commV (autQuot K (⊥ : Subgroup W))) : ℚ) := by
    exact_mod_cast rk_mono hIle
  have hn1 : (1 : ℚ) ≤
      (rk ↥(commV (autQuot K (⊥ : Subgroup W))) : ℚ) /
        (rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) : ℚ) := by
    rw [le_div_iff₀ (by exact_mod_cast hIstarPos)]
    simpa using hcast
  have hmleN : (E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) : ℚ) ≤ (E3.mParam Y : ℚ) := by
    calc (E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) : ℚ)
        = (E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
            (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) : ℚ) * 1 := by ring
      _ ≤ (E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
            (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) : ℚ) *
          ((rk ↥(commV (autQuot K (⊥ : Subgroup W))) : ℚ) /
            (rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) : ℚ)) :=
          mul_le_mul_of_nonneg_left hn1 (by exact_mod_cast Nat.zero_le _)
      _ ≤ (E3.mParam Y : ℚ) := hmn
  have hmleN' : E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) ≤ E3.mParam Y := by
    exact_mod_cast hmleN
  have hmI : E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) < 3 * n :=
    lt_of_le_of_lt hmleN' hmY
  obtain ⟨hnatX, h2nG⟩ :=
    altTwo_su3_of_mParam_autSub_lt hW hKY hKcomp hn hSU hsum hI hmI
  exact ⟨hnatX, h2nG, h2nG.trans hmleN'⟩

theorem su3NaturalModule_altTwo
    (hW : ∀ w : W, w ^ 2 = 1) {Y K : Subgroup (MulAut W)}
    (hKY : K ≤ Y) (hKcomp : CFSG.Open.IsComponentOf K Y) {n : ℕ} (hn : 2 ≤ n)
    (hSU : IsSU3 ↥K n)
    (hfix : fixV (⨆ X ∈ conjSet K Y, X) = ⊥) (hmY : E3.mParam Y < 3 * n)
    (Z : Subgroup W) (hZ : Z = ⊥)
    (hsum : IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X Z)))
    (I : Subgroup W) (hI : I ∈ irrSet K)
    (hmn : (E3.mParam (autSub (autQuot Y Z) (I.map (QuotientGroup.mk' Z))) : ℚ) *
        ((rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥(I.map (QuotientGroup.mk' Z)) : ℚ)) ≤
        E3.mParam Y) :
    S17.CNatModSU3Sub W (CFSG.Quasithin.commSub (⊤ : Subgroup W) K) K n ∧
      E3.mParam Y = 2 * n ∧
        CFSG.Quasithin.commSub (⊤ : Subgroup W) K ∈ irrSet K := by
  subst hZ
  classical
  have : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  have hsupV := commV_sup_fixV_eq_top_of_isDirSumOver hKcomp hsum
  have hinfV := commV_inf_fixV_eq_bot_of_isDirSumOver hKcomp hfix hsum
  have hsup : commSub (⊤ : Subgroup W) K ⊔ fixV K = ⊤ := by
    rwa [← CFSG.Quasithin.commV_eq_commSub]
  have hC := fixV_autSub_autQuot_bot_eq_bot hI hinfV
  obtain ⟨hnat, h2nG, h2nY⟩ := altTwo_su3 hW hKY hKcomp hn hSU hsum hI hmn hmY
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup W)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  have hrkI : rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) = rk ↥I := by
    unfold rk
    rw [Subgroup.card_map_of_injective hinj]
  have hrkK : rk ↥(commV (autQuot K (⊥ : Subgroup W))) = rk ↥(commV K) := by
    rw [← map_commV_eq_commV_autQuot K ⊥ (CFSG.Quasithin.B5.Ln.stabSub_bot_le K)]
    unfold rk
    rw [Subgroup.card_map_of_injective hinj]
  have hrk6 : rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) = 6 * n := by
    have hcardWq := S17.card_of_cNatModSU3Sub (S17.cNatModStructSU3Sub_of_natSUn hnat rfl)
    rw [Subgroup.card_top] at hcardWq
    have hC1 : Nat.card ↥(fixV (autSub (autQuot K (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W))))) = 1 := by
      rw [hC]
      exact Subgroup.card_bot
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (fixV (autSub (autQuot K (⊥ : Subgroup W)) (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))))
    rw [hC1, mul_one, hcardWq] at hc
    unfold rk
    rw [hc, padicValNat.prime_pow]
  have hI6 : rk ↥I = 6 * n := hrkI ▸ hrk6
  have he : rk ↥(commV K) ≤ 9 * n - 3 := by
    rw [hrkK, hrk6] at hmn
    have hpos : (0 : ℚ) < ((6 * n : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 6 * n)
    rw [mul_div_assoc', div_le_iff₀ hpos] at hmn
    have h2 : E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) * rk ↥(commV K) ≤
        E3.mParam Y * (6 * n) := by exact_mod_cast hmn
    have h5 : 2 * n * rk ↥(commV K) ≤ 2 * n * (9 * n - 3) := by
      calc 2 * n * rk ↥(commV K) ≤ E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
            (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) * rk ↥(commV K) :=
            Nat.mul_le_mul_right _ h2nG
        _ ≤ E3.mParam Y * (6 * n) := h2
        _ ≤ (3 * n - 1) * (6 * n) := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * n * (9 * n - 3) := by
            rw [Nat.sub_mul, Nat.mul_sub]
            congr 1
            · ring
            · ring
    exact Nat.le_of_mul_le_mul_left h5 (by omega)
  have hdK : 6 * n ≤ dMinDeg ↥K := k_SU3MinDegree_holds ↥K n hSU hn
  have hIle : I ≤ commSub (⊤ : Subgroup W) K := by
    calc I = commSub I K := hI.1.symm
      _ ≤ commSub (⊤ : Subgroup W) K := commSub_mono le_top le_rfl
  have hSK : StableUnder K (commSub (⊤ : Subgroup W) K) :=
    fun x hx u hu => CFSG.Quasithin.Asc81c.commSub_stable' hx hu
  have hle : commSub (commSub (⊤ : Subgroup W) K) K ≤ I :=
    commSub_le_of_rk_lt_dMinDeg hW hIle hSK hI.2.2.1 (by
      rw [← CFSG.Quasithin.commV_eq_commSub]
      omega)
  have hperfS := CFSG.Quasithin.RonanF918.commSub_commSub_eq_of_perfect (L := K)
    (S := (⊤ : Subgroup W)) (fun _ _ _ _ => Subgroup.mem_top _)
  rw [hperfS] at hle
  have hIK : I = commSub (⊤ : Subgroup W) K := le_antisymm hIle hle
  obtain ⟨hCN, hmle⟩ := altTwo_transport hKY hn hI hIK hsup hC hnat
  exact ⟨hCN, le_antisymm hmle h2nY, hIK ▸ hI⟩

theorem su3NaturalModule_of_w4
    (h128 : W4Lem12_8) (hW : ∀ w : W, w ^ 2 = 1) {Y K : Subgroup (MulAut W)} {n : ℕ}
    (hKY : K ≤ Y) (hKcomp : CFSG.Open.IsComponentOf K Y) (hSU : IsSU3 ↥K n) (hn : 2 ≤ n)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hbasic : IsBasicModule Y) (hfix : fixV (⨆ X ∈ conjSet K Y, X) = ⊥)
    (hmY : E3.mParam Y < 3 * n) :
    S17.CNatModSU3Sub W (CFSG.Quasithin.commSub (⊤ : Subgroup W) K) K n ∧
      E3.mParam Y = 2 * n ∧
        CFSG.Quasithin.commSub (⊤ : Subgroup W) K ∈ irrSet K := by
  let H : Subgroup (MulAut W) := ⨆ X ∈ conjSet K Y, X
  rcases h128 W hW Y hO2 hbasic K hKcomp H rfl with h1 | h2 | h3
  · have hd : 6 * n ≤ dMinDeg ↥K := k_SU3MinDegree_holds ↥K n hSU hn
    omega
  · obtain ⟨hsum, I, hI, hratio⟩ := h2
    exact su3NaturalModule_altTwo hW hKY hKcomp hn hSU hfix hmY (fixV H) hfix hsum I hI hratio
  · obtain ⟨R, e, -, -, -, -, hmE, hde⟩ := h3
    have hd : 6 * n ≤ dMinDeg ↥K := k_SU3MinDegree_holds ↥K n hSU hn
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
