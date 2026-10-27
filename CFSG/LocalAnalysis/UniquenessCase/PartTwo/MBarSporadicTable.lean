module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveCaseTwoBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)
open Matrix
open CFSG.Quasithin.H13
open CFSG.Quasithin.H13.H9Coord

@[expose] def MRowBound (B : Type) [Group B] (c : ℕ) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      CFSG.Open.IsQuasisimple ↥L → O2Trivial L →
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* B) → c ≤ E3.mParam Y

theorem MRowBound.of_rowM {s : TauCeti.SporadicName} (hrow : W4Thm11_1RowM s)
    {B : Type} [Group B] (hs : IsSpor B s) : MRowBound B (tableM s) := by
  intro W _ _ hw Y L h1 h2 h3 h4 h5 ⟨e⟩
  obtain ⟨f⟩ := hs
  exact hrow W hw Y L h1 h2 h3 ((CFSG.Quasithin.A3.isQuasisimple_iff_open).2 h4) h5 ⟨e.trans f⟩

theorem MRowBound.of_row {s : TauCeti.SporadicName} (hrow : W4Thm11_1Row s)
    {B : Type} [Group B] (hs : IsSpor B s) : MRowBound B (tableM s) :=
  MRowBound.of_rowM hrow.rowM hs

theorem caseOne_le_mBar {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hKle : dMinDeg ↥(barSub V₀ V h.isElemAbelian L) ≤ mBar D.M V₀ V h.isElemAbelian)
    {c : ℕ} (hrow : MRowBound (BarInf L) c) : c ≤ mBar D.M V₀ V h.isElemAbelian := by
  classical
  let K := barSub V₀ V h.isElemAbelian L
  have hKcomp : K ∈ compBar D.M V₀ V h.isElemAbelian := barSub_mem_compBar_of_ne_bot h hL hne
  have hKne : K ≠ ⊥ := ne_bot_of_mem_compBar hKcomp
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  let d := dMinDeg ↥K
  obtain ⟨f₀, hf₀⟩ := exists_nontrivial_repr_dMinDeg ↥K
  let k : ↥K →* MulAut (Vec d) := (vecEquiv (n := d)).toMonoidHom.comp f₀
  let Y : Subgroup (MulAut (Vec d)) := k.range
  have hknt : ∃ x, k x ≠ 1 := by
    by_contra hcontra
    push Not at hcontra
    refine hf₀ (MonoidHom.ext fun x => ?_)
    have h1 : (vecEquiv (n := d)) (f₀ x) = 1 := hcontra x
    exact (vecEquiv (n := d)).injective (by simpa using h1)
  have hKqOpen : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKq : CFSG.IsQuasisimple ↥K := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hKqOpen
  have hker : k.ker ≤ Subgroup.center ↥K :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hKq hknt
  have hQsY : CFSG.IsQuasisimple ↥Y :=
    CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center hKq k hker
  have hQsYopen : CFSG.Open.IsQuasisimple ↥Y :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hQsY
  have hFY : Fstar Y = Y := fstar_eq_self_of_isQuasisimple hQsYopen
  have hoddK : Odd (Nat.card (Subgroup.center ↥K)) := odd_center_barSub h hL hne
  have hoddY : Odd (Nat.card (Subgroup.center ↥Y)) := by
    have hks : Function.Surjective k.rangeRestrict := MonoidHom.rangeRestrict_surjective k
    have hker' : k.rangeRestrict.ker ≤ Subgroup.center ↥K := by
      rwa [MonoidHom.ker_rangeRestrict]
    have hcY : Subgroup.center ↥Y = (Subgroup.center ↥K).map k.rangeRestrict :=
      CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hKq hks hker'
    rw [hcY]
    exact Odd.of_dvd_nat hoddK
      (Subgroup.card_map_dvd (H := Subgroup.center ↥K) (f := k.rangeRestrict))
  have hO2 : O2Trivial Y := o2Trivial_of_isQuasisimple_of_odd_center hQsYopen hoddY
  have e2 : ↥K ⧸ Subgroup.center ↥K ≃* ↥Y ⧸ Subgroup.center ↥Y :=
    CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hKq
      (φ := k.rangeRestrict) (MonoidHom.rangeRestrict_surjective k) (by
        rwa [MonoidHom.ker_rangeRestrict])
  obtain ⟨e1⟩ : Nonempty (BarInf L ≃* ↥K ⧸ Subgroup.center ↥K) :=
    barSub_centerQuot_equiv_barInf h hL hne
  have e : ↥Y ⧸ Subgroup.center ↥Y ≃* BarInf L := e2.symm.trans e1.symm
  have hmle : E3.mParam Y ≤ d := by
    calc E3.mParam Y ≤ rk (Vec d) := E3.mParam_le_rk Y
      _ = d := by rw [rk, H9Coord.card_vec, padicValNat.prime_pow]
  have hWexp : ∀ w : Vec d, w ^ 2 = 1 := by
    intro w
    rw [pow_two]
    change Multiplicative.ofAdd (Multiplicative.toAdd w + Multiplicative.toAdd w) = 1
    have hzero : Multiplicative.toAdd w + Multiplicative.toAdd w = 0 := by
      ext i
      have h2 : ∀ x : ZMod 2, x + x = 0 := fun x => by revert x; decide
      exact h2 _
    rw [hzero, ofAdd_zero]
  have hLN : (Y.subgroupOf Y).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact le_trans (hrow (Vec d) hWexp Y Y le_rfl hLN hFY hQsYopen hO2 ⟨e⟩) (hmle.trans hKle)

theorem lieModel_psl_two_of_isNaturalO4Plus {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {Y : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))} {e : ℕ}
    (hsn : CFSG.Open.IsSubnormal (barSub V₀ V h.isElemAbelian L) Y)
    (hnat : IsNaturalO4Plus Y e) : LieModel (BarInf L) .PSL 2 2 e := by
  classical
  let Kc := barSub V₀ V h.isElemAbelian L
  have hKcomp : Kc ∈ compBar D.M V₀ V h.isElemAbelian :=
    barSub_mem_compBar_of_ne_bot h hL hne
  have hKq : CFSG.Open.IsQuasisimple Kc := hKcomp.2.2
  obtain ⟨K, hKfield, hKfinite, hKcard, hK4, ⟨eK⟩⟩ :=
    exists_mulEquiv_sl2_of_isSubnormal_isNaturalO4Plus hKq hsn hnat
  letI : Field K := hKfield
  have : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := by
    have h1 : Fintype.card K = 2 ^ e := by
      rw [← Nat.card_eq_fintype_card]
      exact hKcard
    exact charP_of_card_eq_prime_pow (f := e) h1
  have hZ : Subgroup.center Kc = ⊥ :=
    CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv eK
      (CFSG.Timmesfeld.RankOne.center_SL2_eq_bot (K := K))
  obtain ⟨eBar⟩ := barSub_centerQuot_equiv_barInf (V₀ := V₀) (V := V) h hL hne
  let eBar2 : BarInf L ≃* Kc :=
    eBar.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have hBarKc : BarInf L ≃* Matrix.SpecialLinearGroup (Fin 2) K := eBar2.trans eK
  have hBarSL : BarInf L ≃* CFSG.Open.StatedSL 2 K :=
    hBarKc.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
  have hperf : Group.IsPerfect (BarInf L) := by
    have : Group.IsPerfect ↥L :=
      CFSG.Quasithin.Vol2.Ch10.SecB.KRT.isPerfect_of_commutator_eq hL.2.1
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.solvableRadical ↥L))
      (QuotientGroup.mk'_surjective _)
  have : Nontrivial Kc := (Subgroup.nontrivial_iff_ne_bot Kc).mpr (ne_bot_of_mem_compBar hKcomp)
  have : Nontrivial (BarInf L) := eBar2.toEquiv.nontrivial
  have hmSL : LieModel (BarInf L) .PSL 2 2 e :=
    CFSG.Quasithin.H13.lieModel_psl_two_of_mulEquiv (n := e) hperf hKcard hBarSL
  exact hmSL

theorem caseTwo_package {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
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
      mBar D.M V₀ V h.isElemAbelian) :
    Even (Nat.card ↥(autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian) Z)
        (I.map (QuotientGroup.mk' Z)))) ∧
    E3.mParam (autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian) Z)
        (I.map (QuotientGroup.mk' Z))) ≤ mBar D.M V₀ V h.isElemAbelian ∧
    ∀ s ∈ autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian) Z) (I.map (QuotientGroup.mk' Z)),
      orderOf s = 2 →
      ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (Y X : Subgroup (MulAut W)),
        (∀ w : W, w ^ 2 = 1) ∧ X ≤ Y ∧ (X.subgroupOf Y).Normal ∧ Fstar Y = X ∧
        CFSG.Open.IsQuasisimple ↥X ∧ O2Trivial X ∧ Odd (Nat.card (Subgroup.center ↥X)) ∧
        Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* BarInf L) ∧ IsIrrOn X ⊤ ⊥ ∧
        E3.mParam Y ≤ rkIdx (fixV (Subgroup.zpowers s)) ∧
        (fixV K = ⊥ → rk W = rk ↥(I.map (QuotientGroup.mk' Z))) := by
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
  have hLstarNe : Lstar ≠ ⊥ := by
    have : Nontrivial ↥Lstar := CFSG.LocalCores.isQuasisimple_nontrivial hLstarqC
    exact (Subgroup.nontrivial_iff_ne_bot Lstar).mp inferInstance
  have hPerfL : Group.IsPerfect ↥Lstar := hLstarqC.1
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
  have ho2X : O2Trivial X := o2Trivial_of_isQuasisimple_of_odd_center hXqopen hoddX
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
  refine ⟨?_, ?_, ?_⟩
  · exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp
      (CFSG.ComponentClassification.Burgoyne.even_card_of_isQuasisimple hLstarqC)).trans
      (Subgroup.card_dvd_of_le hLG1))
  · have hIle : Istar ≤ commV (autQuot K Z) := by
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
    have hmle : (E3.mParam G1 : ℚ) ≤ (mBar D.M V₀ V h.isElemAbelian : ℚ) := by
      calc (E3.mParam G1 : ℚ) = (E3.mParam G1 : ℚ) * 1 := by ring
        _ ≤ (E3.mParam G1 : ℚ) *
            ((rk ↥(commV (autQuot K Z)) : ℚ) / (rk ↥Istar : ℚ)) :=
            mul_le_mul_of_nonneg_left hn1 (by exact_mod_cast Nat.zero_le _)
        _ ≤ (mBar D.M V₀ V h.isElemAbelian : ℚ) := hmn
    have hmleN : E3.mParam G1 ≤ mBar D.M V₀ V h.isElemAbelian := by
      exact_mod_cast hmle
    exact hmleN
  · intro s hsG1 hso
    have hs2 : s * s = 1 := by
      have h1 : s ^ 2 = 1 := by rw [← hso]; exact pow_orderOf_eq_one s
      simpa [pow_two] using h1
    have hs1 : s ≠ 1 := by intro h; rw [h] at hso; simp at hso
    have hsC : s ∈ stabSub C := hG1C hsG1
    have hs12 : quotHom C ⟨s, hsC⟩ ≠ 1 := fun hq =>
      hs1 (hfaith s hsC hsG1 hq)
    have hs2q : quotHom C ⟨s, hsC⟩ * quotHom C ⟨s, hsC⟩ = 1 := by
      rw [← map_mul]
      have h1 : (⟨s, hsC⟩ * ⟨s, hsC⟩ : stabSub C) = 1 := by
        refine Subtype.ext ?_
        simpa [pow_two] using hs2
      rw [h1, map_one]
    have hsord : orderOf (quotHom C ⟨s, hsC⟩) = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using hs2q) hs12
    let Y : Subgroup (MulAut Wq) := X ⊔ Subgroup.zpowers (quotHom C ⟨s, hsC⟩)
    have hXY : X ≤ Y := le_sup_left
    have hsY : quotHom C ⟨s, hsC⟩ ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hsG1q : quotHom C ⟨s, hsC⟩ ∈ G1q :=
      mem_autQuot.mpr ⟨⟨s, hsC⟩, hsG1, rfl⟩
    have hYle : Y ≤ G1q := sup_le hXle (Subgroup.zpowers_le.mpr hsG1q)
    have hXN : (X.subgroupOf Y).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hYle.trans hG1qnorm)
    have : Nontrivial Wq := QuotientGroup.nontrivial_iff.mpr hCneTop
    have hF : CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar Y = X :=
      fstar_eq_of_generalizedFitting_eq hXY
        (CFSG.GroupTheory.fstar_sup_zpowers_eq_of_quasisimple_normal hWq' hXY hXq hirr hXN
          hsY hs2q hs12)
    have hmY : E3.mParam Y ≤ rkIdx (fixV (Subgroup.zpowers (quotHom C ⟨s, hsC⟩))) :=
      CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two hsY hsord
    have hrk : rkIdx (fixV (Subgroup.zpowers (quotHom C ⟨s, hsC⟩))) ≤
        rkIdx (fixV (Subgroup.zpowers s)) :=
      CFSG.Quasithin.f918v6f_rkIdx_le hsC
    refine ⟨Wq, inferInstance, inferInstance, Y, X, hWq, hXY, hXN, hF, hXqopen, ho2X, hoddX,
      ⟨eX⟩, isIrrOn_top_bot_of_rankThree hirr le_rfl, le_trans hmY hrk, ?_⟩
    intro hfixK
    have hfixK' : fixV K = ⊥ := hfixK
    have hC : C = ⊥ := by
      have h2 : (fixV Lstar).map Istar.subtype = ⊥ := by
        refine (map_subtype_fixV_autSub_autQuot hKZ hZK hI).trans ?_
        rw [hfixK', inf_bot_eq, Subgroup.map_bot]
      exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective Istar)).1 h2
    show rk (↥Istar ⧸ C) = rk ↥Istar
    unfold rk
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hC).trans
      QuotientGroup.quotientBot).toEquiv]

theorem caseTwo_le_mParam {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
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
    {c : ℕ} (hrow : MRowBound (BarInf L) c) :
    c ≤ E3.mParam (autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian) Z)
      (I.map (QuotientGroup.mk' Z))) := by
  obtain ⟨heven, -, hwit⟩ := caseTwo_package h hL hne hK hZ hsum hI hmn
  have key : ∀ s : MulAut ↥(I.map (QuotientGroup.mk' Z)),
      s ∈ autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian) Z) (I.map (QuotientGroup.mk' Z)) →
      orderOf s = 2 → c ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
    intro s hs hso
    obtain ⟨W, _, _, Y, X, hW, hXY, hXN, hF, hXq, hO2, -, he, -, hmY, -⟩ := hwit s hs hso
    exact le_trans (hrow W hW Y X hXY hXN hF hXq hO2 he) hmY
  obtain ⟨t₀, ht₀, ht₀o, -⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam _ heven
  have hcrk : c ≤ rk ↥(I.map (QuotientGroup.mk' Z)) :=
    le_trans (key t₀ ht₀ ht₀o)
      (CFSG.Quasithin.padicValNat_two_le_of_dvd Nat.card_pos.ne'
        (Subgroup.index_dvd_card (H := fixV (Subgroup.zpowers t₀))))
  exact CFSG.Quasithin.H.Mathieu.le_mParam_of hcrk key

theorem caseTwo_le_mBar {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hsum : IsDirSumOver (conjSet (barSub V₀ V h.isElemAbelian L)
      (Mbar D.M V₀ V h.isElemAbelian))
      (fun X => commV (autQuot X (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
        (Mbar D.M V₀ V h.isElemAbelian)))))
    {I : Subgroup (Vtil V₀ V h.isElemAbelian)}
    (hI : I ∈ irrSet (barSub V₀ V h.isElemAbelian L))
    (hmn : (E3.mParam (autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian)
        (fixSupConjSet (barSub V₀ V h.isElemAbelian L) (Mbar D.M V₀ V h.isElemAbelian)))
        (I.map (QuotientGroup.mk' (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
          (Mbar D.M V₀ V h.isElemAbelian))))) : ℚ) *
      ((rk ↥(commV (autQuot (barSub V₀ V h.isElemAbelian L)
        (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
          (Mbar D.M V₀ V h.isElemAbelian)))) : ℚ) /
        (rk ↥(I.map (QuotientGroup.mk' (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
          (Mbar D.M V₀ V h.isElemAbelian)))) : ℚ)) ≤
      mBar D.M V₀ V h.isElemAbelian)
    {c : ℕ} (hrow : MRowBound (BarInf L) c) : c ≤ mBar D.M V₀ V h.isElemAbelian :=
  (caseTwo_le_mParam h hL hne rfl rfl hsum hI hmn hrow).trans
    (caseTwo_package h hL hne rfl rfl hsum hI hmn).2.1

theorem le_mBar_of_mRowBound (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h4128 : W4Lem12_8) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {c : ℕ} (hrow : MRowBound (BarInf L) c)
    (hnL2 : ∀ e : ℕ, ¬ LieModel (BarInf L) .PSL 2 2 e) :
    c ≤ mBar D.M V₀ V h.isElemAbelian := by
  have hKcomp : barSub V₀ V h.isElemAbelian L ∈ compBar D.M V₀ V h.isElemAbelian :=
    barSub_mem_compBar_of_ne_bot h hL hne
  rcases twelve_twentyFour D hx h61 h127 h1214 h4128 h hKcomp rfl with
    h1 | ⟨hsum, I, hI, hmn⟩ | ⟨Y, e, -, -, hsn, hnat, -⟩
  · exact caseOne_le_mBar h hL hne h1 hrow
  · exact caseTwo_le_mBar h hL hne hsum hI hmn hrow
  · exact (hnL2 e (lieModel_psl_two_of_isNaturalO4Plus h hL hne hsn hnat)).elim

theorem tableM_le_mBar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h4128 : W4Lem12_8) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {s : TauCeti.SporadicName} (hrow : W4Thm11_1RowM s) (hs : IsSpor (BarInf L) s)
    (hnL2 : ∀ e : ℕ, ¬ LieModel (BarInf L) .PSL 2 2 e) :
    tableM s ≤ mBar D.M V₀ V h.isElemAbelian :=
  le_mBar_of_mRowBound D hx h61 h127 h1214 h4128 h hL hne (MRowBound.of_rowM hrow hs) hnL2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
