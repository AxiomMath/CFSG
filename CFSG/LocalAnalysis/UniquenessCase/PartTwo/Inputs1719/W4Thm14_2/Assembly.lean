module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.Statement
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.MinDegree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.CentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallApply
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.Swap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveApply
public import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KO4PlusSwap.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FixVQuot.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem map_conj_eq_of_mem_of_normal {A : Type*} [Group A] {L Y : Subgroup A}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) {g : A} (hg : g ∈ Y) :
    L.map (MulAut.conj g).toMonoidHom = L := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff hLY).mp hLn y g hy hg
  · intro x hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · simpa using (Subgroup.normal_subgroupOf_iff hLY).mp hLn x g⁻¹ hx (Y.inv_mem hg)
    · simp [MulAut.conj_apply, mul_assoc]

theorem conjSet_eq_singleton_of_normal {A : Type*} [Group A] {L Y : Subgroup A}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y = {L} := by
  ext X
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Set.mem_singleton_iff.mpr (map_conj_eq_of_mem_of_normal hLY hLn hg)
  · intro hX
    refine ⟨1, Y.one_mem, ?_⟩
    rw [Set.mem_singleton_iff] at hX
    rw [hX]
    ext x
    simp

theorem isSL3_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 X n) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 Y n :=
  ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm h.1,
    CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) h.2⟩

theorem w4Thm14_2_caseTwo (hSmall2 : K14_2Small)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hs : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 4)
    (hTY : T ≤ Y) (hT : IsSylowIn 2 T Y) (hsw : S17.SwapsParabolics T L)
    (hm : E3.mParam Y = 4)
    (hdir : IsDirSumOver (conjSet L Y) (fun X => commV (autQuot X (fixV L))))
    (I : Subgroup W) (hI : I ∈ irrSet L)
    (hineq : ((E3.mParam (autSub (autQuot Y (fixV L)) (I.map (QuotientGroup.mk' (fixV L)))) : ℚ) *
      ((rk ↥(commV (autQuot L (fixV L))) : ℚ) /
        (rk ↥(I.map (QuotientGroup.mk' (fixV L))) : ℚ)) ≤ (E3.mParam Y : ℚ))) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 ∧ Subgroup.center ↥L ≠ ⊥ ∧
      Odd (Nat.card (Subgroup.center ↥L)) ∧ fixV L = ⊥ ∧ commV L = ⊤ ∧
      rk ↥(⊤ : Subgroup W) ≤ 12 := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hqL : CFSG.Open.IsQuasisimple ↥L := hs.elim (fun h => h.1) (fun h => h.1)
  have hcomp : IsComponentOf L Y :=
    ⟨hLY, IsSubnormal.step hLY hLn (IsSubnormal.refl Y), hqL⟩
  have hH : L = ⨆ X ∈ conjSet L Y, X := (FixVQuot.iSup_conjSet_eq_self_of_normal hLY hLn).symm
  have hO : O2Trivial Y := hO2
  set C : Subgroup W := fixV L with hC
  set Lq : Subgroup (MulAut (W ⧸ C)) := autQuot L C with hLq
  set Yq : Subgroup (MulAut (W ⧸ C)) := autQuot Y C with hYq
  set Iq : Subgroup (W ⧸ C) := I.map (QuotientGroup.mk' C) with hIq
  have hWq : ∀ w : W ⧸ C, w ^ 2 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_pow, hW x, QuotientGroup.mk_one]
  have hLqYq : Lq ≤ Yq := autQuot_mono hLY C
  have hcompq : IsComponentOf Lq Yq :=
    FixVQuot.isComponentOf_autQuot hW hO hB hcomp hLn
  have hLnq : (Lq.subgroupOf Yq).Normal :=
    FixVQuot.autQuot_subgroupOf_normal hW hO hB hcomp hLn
  have hnormLq : Yq ≤ Subgroup.normalizer (Lq : Set (MulAut (W ⧸ C))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLqYq).mp hLnq
  have hqLq : CFSG.Open.IsQuasisimple ↥Lq := hcompq.2.2
  have hquotL : ↥L ≃* ↥Lq := FixVQuot.autQuotEquiv hW hO hB hcomp hLn hLY
  have hquotY : ↥Y ≃* ↥Yq := FixVQuot.autQuotEquiv hW hO hB hcomp hLn le_rfl
  have hIq_data := FixVQuot.map_mem_irrSet_autQuot hW hO hB hcomp hLn hI
  have hIqmem : Iq ∈ irrSet Lq := hIq_data.1
  have hIqfix : Iq ⊓ fixV Lq = ⊥ := hIq_data.2
  have hIqne : Iq ≠ ⊥ := ne_bot_of_mem_irrSet hIqmem
  have hLIq : Lq ≤ stabSub Iq := Thm14_5.le_stabSub_of_mem_irrSet hIqmem
  have hneIq : ¬ Lq ≤ centSub Iq := Thm14_5.not_le_centSub_of_mem_irrSet hIqmem hIqfix
  have hnormIq : ∀ y ∈ Yq, y ∈ stabSub Iq →
      y ∈ Subgroup.normalizer (Lq : Set (MulAut (W ⧸ C))) := fun y hy _ => hnormLq hy
  have hfixLq : fixV Lq = ⊥ := by
    rw [hLq]
    exact fixV_autQuot_eq_bot hcomp hH
  have hconjset : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y = {L} :=
    conjSet_eq_singleton_of_normal hLY hLn
  have htopq : commV Lq = ⊤ := by
    rw [eq_top_iff, ← hdir.2]
    refine iSup_le fun X => ?_
    have hX : (X : Subgroup (MulAut W)) = L := by
      obtain ⟨g, hg, hgX⟩ := X.2
      rw [hgX]
      exact map_conj_eq_of_mem_of_normal hLY hLn hg
    rw [hX]
  set u : ℕ := E3.mParam (autSub Yq Iq) with hu_def
  set r : ℕ := rk ↥Iq with hr_def
  set Rr : ℕ := rk ↥(commV Lq) with hRr_def
  have hrpos : 0 < r := by
    rw [Nat.pos_iff_ne_zero, Ne, rk_eq_zero_iff hWq]
    exact hIqne
  have hIc : Iq ≤ commV Lq := by
    rw [commV_eq_commSub, ← hIqmem.1]
    exact commSub_mono le_top le_rfl
  have hrR : r ≤ Rr := by
    rw [hRr_def]
    exact rk_mono hIc
  have hineq' : (u : ℚ) * ((Rr : ℚ) / (r : ℚ)) ≤ (E3.mParam Y : ℚ) := by
    simpa [hu_def, hr_def, hRr_def, hIq, hLq, hC] using hineq
  have hQ13' : commV Lq = Iq ∨ 2 * r ≤ Rr := by
    rcases FixVQuot.commV_eq_or_two_mul_rk_le hW hO2 hB hcomp hLn hI with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hmain : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 ∧
      Subgroup.center ↥L ≠ ⊥ ∧ u = 2 ∧ r = 6 := by
    rcases hQ13' with hIqtop | h2r
    · exfalso
      have htopI : Iq = ⊤ := by rw [← hIqtop, htopq]
      have hu4 : u ≤ 4 := by
        have hrq : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hrpos
        have hRr_eq : Rr = r := by
          rw [hRr_def, hr_def, htopI, htopq]
        have h1 := hineq'
        rw [hm, hRr_eq, div_self (ne_of_gt hrq), mul_one] at h1
        exact_mod_cast h1
      have hIrrLq : IsIrrOn Lq ⊤ ⊥ := by
        simpa [htopI, hfixLq] using hIqmem.2
      have hLq3 : UC22.IsSL3 ↥Lq 2 ∨ UC22.IsSL3 ↥Lq 4 :=
        hs.imp (isSL3_of_mulEquiv hquotL) (isSL3_of_mulEquiv hquotL)
      have hu4' : E3.mParam (autSub Yq ⊤) ≤ 4 := by
        rw [hu_def] at hu4
        rwa [htopI] at hu4
      have hmq : E3.mParam Yq ≤ 4 := by
        have h := hu4'
        rw [CFSG.Quasithin.H13.autSub_top_eq_map] at h
        rwa [CFSG.Quasithin.H.mParam_map_congrHom (Subgroup.topEquiv (G := W ⧸ C)).symm
          Yq] at h
      let hYstab : Y ≤ stabSub C := FixVQuot.le_stabSub_fixV_of_subgroupOf_normal hLY hLn
      let g : ↥Y →* MulAut (W ⧸ C) := (quotHom C).comp (Subgroup.inclusion hYstab)
      have hg_inj : Function.Injective g := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        have hquot : quotHom C (Subgroup.inclusion hYstab x) = 1 := hx
        have hx1 : (x : MulAut W) = 1 := by
          refine eq_one_of_mem_fixV_quot hW hO hB hcomp hH x.2 fun w => ?_
          have h := congrArg (fun φ : MulAut (W ⧸ C) => φ (QuotientGroup.mk w)) hquot
          simp only [quotHom_mk, MulAut.one_apply] at h
          exact hC ▸ (mk_eq_mk_iff (U := C) ((x : MulAut W) w) w).mp h
        exact Subgroup.mem_bot.mpr (Subtype.ext hx1)
      have hg_surj : ∀ φ : MulAut (W ⧸ C), φ ∈ Yq → ∃ y : ↥Y, g y = φ := by
        intro φ hφ
        obtain ⟨g', hg'Y, hg'⟩ := mem_autQuot.mp hφ
        refine ⟨⟨(g' : MulAut W), hg'Y⟩, ?_⟩
        show quotHom C (Subgroup.inclusion hYstab ⟨(g' : MulAut W), hg'Y⟩) = φ
        rw [show Subgroup.inclusion hYstab ⟨(g' : MulAut W), hg'Y⟩ = g' from Subtype.ext rfl]
        exact hg'
      have hYmap : (⊤ : Subgroup ↥Y).map g = Yq := by
        ext φ
        constructor
        · rintro ⟨y, -, rfl⟩
          exact mem_autQuot.mpr ⟨Subgroup.inclusion hYstab y, y.2, rfl⟩
        · intro hφ
          obtain ⟨y, hy⟩ := hg_surj φ hφ
          exact ⟨y, Subgroup.mem_top y, hy⟩
      have hLmap : (L.subgroupOf Y).map g = Lq := by
        ext φ
        rw [Subgroup.mem_map, mem_autQuot]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨Subgroup.inclusion hYstab y, hy, rfl⟩
        · rintro ⟨g', hg'L, hg'⟩
          refine ⟨⟨(g' : MulAut W), hLY hg'L⟩, hg'L, ?_⟩
          show quotHom C (Subgroup.inclusion hYstab ⟨(g' : MulAut W), hLY hg'L⟩) = φ
          rw [show Subgroup.inclusion hYstab ⟨(g' : MulAut W), hLY hg'L⟩ = g' from
            Subtype.ext rfl]
          exact hg'
      have hTsylTop : IsSylowIn 2 (T.subgroupOf Y) (⊤ : Subgroup ↥Y) := by
        rw [← CFSG.Quasithin.E1.isSylowIn_map_of_injective Y.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hTY, Subgroup.map_top, Subgroup.range_subtype]
        exact hT
      have hTmapSyl : IsSylowIn 2 ((T.subgroupOf Y).map g) Yq := by
        rw [← hYmap]
        exact (CFSG.Quasithin.E1.isSylowIn_map_of_injective hg_inj).mpr hTsylTop
      obtain ⟨x, hxT, P, hPmax, hPmove⟩ := swapsParabolics_map_of_le g hg_inj hTY hLY hsw
      have hxYq : x ∈ Yq := by
        rw [← hYmap]
        exact Subgroup.map_mono le_top hxT
      have hxnormL : x ∈ Subgroup.normalizer (Lq : Set (MulAut (W ⧸ C))) := hnormLq hxYq
      have hPmax' : S17.IsMaxParabolicOver Lq ((T.subgroupOf Y).map g ⊓ Lq) P := by
        rwa [hLmap] at hPmax
      have hSsyl : IsSylowIn 2 ((T.subgroupOf Y).map g ⊓ Lq) Lq :=
        IsSylowIn.inf_normal hTmapSyl hLqYq hLnq
      let Sq : Subgroup (MulAut (W ⧸ C)) := (T.subgroupOf Y).map g ⊓ Lq
      have hSsyl' : IsSylowIn 2 Sq Lq := hSsyl
      have hxnormS : x ∈ Subgroup.normalizer (Sq : Set (MulAut (W ⧸ C))) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨hyT, hyL⟩
          exact ⟨(T.subgroupOf Y).map g |>.mul_mem
              ((T.subgroupOf Y).map g |>.mul_mem hxT hyT)
              ((T.subgroupOf Y).map g |>.inv_mem hxT),
            (Subgroup.mem_normalizer_iff.mp hxnormL y).mp hyL⟩
        · rintro ⟨hyT, hyL⟩
          have hyT' : y ∈ (T.subgroupOf Y).map g := by
            have h : x⁻¹ * (x * y * x⁻¹) * x ∈ (T.subgroupOf Y).map g :=
              (T.subgroupOf Y).map g |>.mul_mem
                ((T.subgroupOf Y).map g |>.mul_mem ((T.subgroupOf Y).map g |>.inv_mem hxT)
                  hyT) hxT
            simpa [mul_assoc] using h
          exact ⟨hyT', (Subgroup.mem_normalizer_iff.mp hxnormL y).mpr hyL⟩
      exact hPmove ((hSmall2 (W ⧸ C) hWq Yq Lq hLqYq hLnq hIrrLq hLq3 hmq).1
        Sq x hSsyl' hxnormL hxnormS P hPmax')

    · have hu2 : u ≤ 2 := by
        have hrq : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hrpos
        have hnu : (2 : ℚ) ≤ (Rr : ℚ) / (r : ℚ) := by
          rw [le_div_iff₀ hrq]
          exact_mod_cast h2r
        have h1 := hineq'
        rw [hm] at h1
        have h2 : (u : ℚ) * 2 ≤ 4 := by
          have := mul_le_mul_of_nonneg_left hnu (Nat.cast_nonneg u)
          linarith
        have h3 : (u : ℚ) ≤ 2 := by nlinarith
        exact_mod_cast h3
      have hWiq : ∀ w : ↥Iq, w ^ 2 = 1 := fun w => Subtype.ext (by
        simpa using hWq (w : W ⧸ C))
      have hleI : autSub Lq Iq ≤ autSub Yq Iq := autSub_mono hLqYq Iq
      have hnormSub : ((autSub Lq Iq).subgroupOf (autSub Yq Iq)).Normal :=
        Thm14_5.normal_autSub_of_normalizes hnormIq
      have hirrIq : IsIrrOn (autSub Lq Iq) ⊤ ⊥ :=
        Thm14_5.isIrrOn_autSub_of_mem_irrSet hIqmem hIqfix
      have hSL3any : IsSL3 ↥(autSub Lq Iq) 2 ∨ IsSL3 ↥(autSub Lq Iq) 4 := by
        have hsurj := Thm14_5.resTo_surjective hLIq
        have hker := Thm14_5.ker_resTo_le_center hqLq hLIq hneIq
        have hnt := Thm14_5.nontrivial_autSub hLIq hneIq
        rcases hs with h2 | h4
        · exact Or.inl (isSL3_of_surjective_central (isSL3_of_mulEquiv hquotL h2)
            (Thm14_5.resTo hLIq) hsurj hker hnt)
        · exact Or.inr (isSL3_of_surjective_central (isSL3_of_mulEquiv hquotL h4)
            (Thm14_5.resTo hLIq) hsurj hker hnt)
      have hsmall := hSmall2 ↥Iq hWiq (autSub Yq Iq) (autSub Lq Iq) hleI hnormSub hirrIq
        hSL3any (by omega)
      obtain ⟨hSL3I, hZneI, hrkTop, huI, _⟩ := hsmall.2 (by simpa [hu_def] using hu2)
      have hrkI6 : r = 6 := by
        rw [hr_def]
        rw [rk_top] at hrkTop
        exact hrkTop
      have hu2eq : u = 2 := by
        rw [hu_def]
        exact huI
      have hqLq' : CFSG.IsQuasisimple ↥Lq :=
        (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥Lq).2.2.1.mpr hqLq
      have hSL3Lq2 : IsSL3 ↥Lq 2 := by
        have hsurj := Thm14_5.resTo_surjective hLIq
        have hker := Thm14_5.ker_resTo_le_center hqLq hLIq hneIq
        let e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hqLq' hsurj hker
        exact ⟨hqLq, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hSL3I.2⟩
      have hZneLq : Subgroup.center ↥Lq ≠ ⊥ := by
        intro hbot
        apply hZneI
        have hcen := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple
          (K := ↥Lq) (G := ↥(autSub Lq Iq)) (φ := Thm14_5.resTo hLIq) hqLq'
          (Thm14_5.resTo_surjective hLIq) (Thm14_5.ker_resTo_le_center hqLq hLIq hneIq)
        rw [hcen, hbot]
        simp
      have hSL3L2 : IsSL3 ↥L 2 := isSL3_of_mulEquiv hquotL.symm hSL3Lq2
      have hZneL : Subgroup.center ↥L ≠ ⊥ := by
        intro hbot
        apply hZneLq
        have hcard := Nat.card_congr (Subgroup.centerCongr hquotL).toEquiv
        rw [hbot] at hcard
        exact Subgroup.card_eq_one.mp (by simpa using hcard.symm)
      exact ⟨hSL3L2, hZneL, hu2eq, hrkI6⟩
  obtain ⟨hSL3L2, hZneL, hu2eq, hrkI⟩ := hmain
  have hoddZ : Odd (Nat.card (Subgroup.center ↥L)) :=
    W4Row.odd_card_center_of_o2Trivial (CFSG.GroupTheory.o2Trivial_of_normal hO2 hLY hLn)
  have hfixL : fixV L = ⊥ := fixV_eq_bot_of_center hW hB hLY hLn hZneL hoddZ
  have hcommL : commV L = ⊤ := commV_eq_top hW hO hB hcomp hH
  refine ⟨hSL3L2, hZneL, hoddZ, hfixL, hcommL, ?_⟩
  have hCbot : C = ⊥ := by rw [hC]; exact hfixL
  have hcardW : Nat.card W = Nat.card (W ⧸ C) := by
    rw [hCbot]
    exact (Nat.card_congr (QuotientGroup.quotientBot (G := W)).toEquiv).symm
  have hrkW : rk W = rk (W ⧸ C) := by
    unfold rk
    rw [hcardW]
  have hRrW : Rr = rk (W ⧸ C) := by
    rw [hRr_def, htopq, rk_top]
  have hRr12 : Rr ≤ 12 := by
    have hrq : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hrpos
    have h1 := hineq'
    rw [hm] at h1
    rw [hu2eq, mul_div_assoc', div_le_iff₀ hrq] at h1
    have h1n : 2 * Rr ≤ 4 * r := by exact_mod_cast h1
    omega
  rw [rk_top, hrkW, ← hRrW]
  exact hRr12

theorem w4Thm14_2_sl3Four (hSmall2 : K14_2Small)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hs : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 4)
    (hTY : T ≤ Y) (hT : IsSylowIn 2 T Y) (hsw : S17.SwapsParabolics T L)
    (hm : E3.mParam Y = 4) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 ∧ Subgroup.center ↥L ≠ ⊥ ∧
      Odd (Nat.card (Subgroup.center ↥L)) ∧ fixV L = ⊥ ∧ commV L = ⊤ ∧
      rk ↥(⊤ : Subgroup W) ≤ 12 := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hqL : CFSG.Open.IsQuasisimple ↥L := hs.elim (fun h => h.1) (fun h => h.1)
  have hcomp : IsComponentOf L Y :=
    ⟨hLY, IsSubnormal.step hLY hLn (IsSubnormal.refl Y), hqL⟩
  have hH : L = ⨆ X ∈ conjSet L Y, X := (FixVQuot.iSup_conjSet_eq_self_of_normal hLY hLn).symm
  rcases w4Lem12_8_holds W hW Y hO2 hB L hcomp L hH with h1 | ⟨hdir, I, hI, hineq⟩ |
    ⟨R, e, hRY, -, hLR, hnatR, -, -⟩
  · exact absurd (hm ▸ h1) (by have := k_SL3MinDegree_holds ↥L hs; omega)
  · exact w4Thm14_2_caseTwo hSmall2 hW hO2 hB hLY hLn hs hTY hT hsw hm hdir I hI hineq
  · obtain ⟨S, hS⟩ := CFSG.Quasithin.E1.exists_isSylowIn_two R
    have hSle : S ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
      (hS.le.trans hRY).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn)
    exact absurd hSle (kO4PlusSwap_holds W R L S e hnatR hqL hLR hS)

theorem w4Thm14_2Used_of (hSmall2 : K14_2Small)
    (hCent : K14_2Cent) : W4Thm14_2Used := by
  intro W _ _ hW Y L _ hO2 hB hLY hLn hs hT hm p hp hp3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTY, hTsyl, hsw⟩ := hT
  obtain ⟨hSL3, hZne, hZodd, hfix, hcomm, hrk⟩ :=
    w4Thm14_2_sl3Four hSmall2 hW hO2 hB hLY hLn hs hTY hTsyl hsw hm
  obtain ⟨t, htT, P, hPmax, hPmove⟩ := hsw
  have hYnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have htL : t ∈ Subgroup.normalizer (L : Set (MulAut W)) := hYnorm (hTY htT)
  have hSyl : IsSylowIn 2 (T ⊓ L) L := hTsyl.inf_normal hLY hLn
  have htT' : t ∈ Subgroup.normalizer (T : Set (MulAut W)) := Subgroup.le_normalizer htT
  have htS : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff] at htT' htL ⊢
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, htT' x, htL x]
  have hc : ∀ c : MulAut W, (∀ l ∈ L, c * l = l * c) → c ^ 6 = 1 :=
    hCent W hW L hSL3 hZne hZodd hrk hfix hcomm
      ⟨t, htL, T ⊓ L, hSyl, htS, P, hPmax, hPmove⟩
  exact pRank_le_one_of_centralizer_pow_six hLY hLn hSL3 hc p hp hp3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
