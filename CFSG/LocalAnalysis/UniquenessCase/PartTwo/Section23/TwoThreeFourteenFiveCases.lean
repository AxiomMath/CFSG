module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveApply
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KO4PlusSwap.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.IrrSetQuotient
public import CFSG.Quasithin.Vol2.Ch10SecCWF
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FM
public import CFSG.Foundations.SteinbergCADefinitionNodesII
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isDirSumOver_of_map_injective {W W' : Type} [CommGroup W] [CommGroup W']
    {ι : Type*} {S : Set ι} {U : ι → Subgroup W} (f : W →* W') (hf : Function.Injective f)
    (h : IsDirSumOver S (fun X => (U X).map f)) : IsDirSumOver S U := by
  classical
  constructor
  · refine iSupIndep_def.mpr fun i => ?_
    rw [disjoint_iff]
    have hind := iSupIndep_def.mp h.1 i
    have hmap : (⨆ j : {X // X ∈ S}, ⨆ (_ : j ≠ i), U j).map f =
        ⨆ j : {X // X ∈ S}, ⨆ (_ : j ≠ i), (U j).map f := by
      rw [Subgroup.map_iSup]
      congr 1
      funext j
      rw [Subgroup.map_iSup]
    have hle : (U i ⊓ ⨆ j : {X // X ∈ S}, ⨆ (_ : j ≠ i), U j).map f ≤
        (U i).map f ⊓ (⨆ j : {X // X ∈ S}, ⨆ (_ : j ≠ i), U j).map f :=
      le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
    have hbot : (U i ⊓ ⨆ j : {X // X ∈ S}, ⨆ (_ : j ≠ i), U j).map f = ⊥ := by
      rw [hmap] at hle
      exact le_bot_iff.mp (hle.trans (le_of_eq (disjoint_iff.mp hind)))
    exact (Subgroup.map_eq_bot_iff_of_injective
      (U i ⊓ ⨆ j : {X // X ∈ S}, ⨆ (_ : j ≠ i), U j) hf).mp hbot
  · rw [eq_top_iff]
    have htop : (⨆ X : S, U X).map f = ⊤ := by
      rw [Subgroup.map_iSup]
      exact h.2
    have htop' : (⊤ : Subgroup W).map f = ⊤ := by
      refine top_le_iff.mp ?_
      calc ⊤ = (⨆ X : S, U X).map f := htop.symm
        _ ≤ (⊤ : Subgroup W).map f := Subgroup.map_mono le_top
    exact (Subgroup.map_injective (f := f) hf (htop.trans htop'.symm)).ge

theorem isDirSumOver_congr {W : Type} [CommGroup W] {ι : Type*} {S : Set ι}
    {U V : ι → Subgroup W} (h : ∀ X ∈ S, U X = V X) (hU : IsDirSumOver S U) :
    IsDirSumOver S V := by
  have hfun : (fun X : S => U X) = (fun X : S => V X) :=
    funext fun X => h X X.2
  unfold IsDirSumOver at hU ⊢
  rw [hfun] at hU
  exact hU

theorem not_dMinDeg_le_mBar {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) (h1A : S23_1A D Ch) (hDeg : KMinDegLow)
    {A K P : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L) (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hn : NParam (Hinf P) c.n) (hn2 : 2 < c.n) (hshape : S20_7Shape (Bar2 c.L)) :
    ¬ dMinDeg ↥(barSub ⊥ A hA K) ≤ mBar c.N ⊥ A hA := by
  intro hle
  have hKN : K ≤ c.N := (CFSG.Quasithin.A3.subnormal_le hK.1).trans (Ctx23L.L_le_N c)
  have hNbot : c.N ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  have hKstab : K ≤ stabTil ⊥ A := hKN.trans (le_inf hAN hNbot)
  have h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥ :=
    barSub_pCoreOf_eq_bot_of_isComponentOf c h208 h1930 hA hAV hK
  have hcomp : IsComponentOf (barSub ⊥ A hA K) (Mbar c.N ⊥ A hA) :=
    isComponentOf_barSub_of_sup_conj c h208 h1930 hA hAV hAN hAne hK hgen
  haveI : Nontrivial ↥(barSub ⊥ A hA K) :=
    CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2)
  have hsurj : Function.Surjective (barSubBar2Hom (V₀ := ⊥) hA hKstab h2) :=
    barSubBar2Hom_surjective hA hKstab h2
  have hd1 : dMinDeg (Bar2 K) ≤ dMinDeg ↥(barSub ⊥ A hA K) :=
    dMinDeg_le_of_surjective (barSubBar2Hom (V₀ := ⊥) hA hKstab h2) hsurj
  have hd2 : c.n + 1 < dMinDeg (Bar2 K) :=
    hDeg c.L K P c.n hshape hK hP.1.1 hn hn2
  obtain ⟨hW, hm, ha⟩ :=
    aBar_bound_of_S23_1A c h1A h1930 hA hAV hAne hAN hmin
  have hmle : mBar c.N ⊥ A hA ≤ c.n + 1 :=
    le_trans hm (Nat.add_le_add_right ha 1)
  exact (not_le_of_gt hd2) (le_trans hd1 (le_trans hle hmle))

theorem false_of_isDirSumOver_case_two {W : Type} [CommGroup W] [Finite W]
    {Y L H : Subgroup (MulAut W)} (hcomp : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) (hHfix : fixV H = ⊥) (hLfix : fixV L = ⊥)
    (hfaith : ∀ y ∈ Y, (∀ w : W, y w = w) → y = 1) (hHne : H ≠ L)
    (hsum : IsDirSumOver (conjSet L Y) (fun X => commV (autQuot X (fixV H)))) : False := by
  classical
  have hstab : ∀ X ∈ conjSet L Y, X ≤ stabSub (fixV H) := by
    intro X hX
    have hXH : X ≤ H := by
      rw [hH]
      exact le_iSup₂_of_le X hX le_rfl
    exact hXH.trans (CFSG.Quasithin.Vol2.Ch10.G16.le_stabSub_fixV H)
  have hsum' : IsDirSumOver (conjSet L Y)
      (fun X => (commV X).map (QuotientGroup.mk' (fixV H))) :=
    isDirSumOver_congr
      (fun X hX => (map_commV_eq_commV_autQuot X (fixV H) (hstab X hX)).symm) hsum
  have hker : (QuotientGroup.mk' (fixV H)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hHfix]
  have hf : Function.Injective (QuotientGroup.mk' (fixV H)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hsumW : IsDirSumOver (conjSet L Y) (fun X => commV X) :=
    isDirSumOver_of_map_injective _ hf hsum'
  exact false_of_case_one_of_fixV_eq_bot hcomp hH hLfix hfaith hHne hsumW

private theorem le_normalizer_of_iSupIndep_commV {W : Type} [CommGroup W]
    {Y T K R : Subgroup (MulAut W)}
    (hT : T ≤ Y) (hsum : IsDirSumOver (conjSet R Y) commV)
    (hRY : R ≤ Y) (hKsub : CFSG.Open.IsSubnormal K R) (hKne : K ≠ ⊥)
    (hTK : T ≤ Subgroup.normalizer (K : Set (MulAut W))) :
    T ≤ Subgroup.normalizer (R : Set (MulAut W)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  let R' : {X // X ∈ conjSet R Y} := ⟨R, s15_T7_mem_conjSet_self R Y⟩
  let Rt' : {X // X ∈ conjSet R Y} := ⟨R.map (MulAut.conj t).toMonoidHom, ⟨t, hT ht, rfl⟩⟩
  have hne' : Rt' ≠ R' := fun h => hne (congrArg Subtype.val h)
  have hind := (iSupIndep_def.mp hsum.1) R'
  have hle : commV (R.map (MulAut.conj t).toMonoidHom) ≤
      ⨆ j : {X // X ∈ conjSet R Y}, ⨆ (_ : j ≠ R'), commV j :=
    le_iSup_of_le Rt' (le_iSup_of_le hne' le_rfl)
  have hdisj : Disjoint (commV R) (commV (R.map (MulAut.conj t).toMonoidHom)) :=
    hind.mono_right hle
  have hKleR : K ≤ R := CFSG.Quasithin.A3.subnormal_le hKsub
  have hcommKleR : commV K ≤ commV R :=
    CFSG.Quasithin.H13.commV_mono_ch615 hKleR
  have hKmap : K.map (MulAut.conj t).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTK ht)
  have hEq : (commV K).map t.toMonoidHom = commV K := by
    rw [← CFSG.Quasithin.commV_map_conj_eq K t, hKmap]
  have hKt : commV K ≤ commV (R.map (MulAut.conj t).toMonoidHom) := by
    rw [CFSG.Quasithin.commV_map_conj_eq]
    calc commV K = (commV K).map t.toMonoidHom := hEq.symm
      _ ≤ (commV R).map t.toMonoidHom := Subgroup.map_mono hcommKleR
  have hbot : commV K = ⊥ := by
    have hleinf : commV K ≤ commV R ⊓ commV (R.map (MulAut.conj t).toMonoidHom) :=
      le_inf hcommKleR hKt
    rw [disjoint_iff.mp hdisj] at hleinf
    exact le_bot_iff.mp hleinf
  have hKleY : K ≤ Y := hKleR.trans hRY
  have hfaith : ∀ y ∈ Y, (∀ w : W, y w = w) → y = 1 :=
    fun y _ hy => MulEquiv.ext fun w => hy w
  exact commV_ne_bot_of_faithful hfaith hKne hKleY hbot

theorem false_of_isDirSumOver_isNaturalO4Plus {W : Type} [CommGroup W] [Finite W]
    {Y T K R : Subgroup (MulAut W)} {e : ℕ}
    (hT : IsSylowIn 2 T Y) (hsum : IsDirSumOver (conjSet R Y) commV)
    (hRY : R ≤ Y) (hKsub : CFSG.Open.IsSubnormal K R)
    (hKq : CFSG.Open.IsQuasisimple K)
    (hTK : T ≤ Subgroup.normalizer (K : Set (MulAut W)))
    (hnat : IsNaturalO4Plus R e) (hKne : K ≠ ⊥) : False := by
  classical
  have hTR : T ≤ Subgroup.normalizer (R : Set (MulAut W)) :=
    le_normalizer_of_iSupIndep_commV hT.le hsum hRY hKsub hKne hTK
  let S : Subgroup (MulAut W) := T ⊓ R
  have hSyl : IsSylowIn 2 S R := by
    refine ⟨inf_le_right, hT.isPGroup.to_le inf_le_left, ?_⟩
    have hodd : Odd (T.relIndex Y) := by
      rw [← Nat.not_even_iff_odd]
      simpa [Nat.even_iff] using hT.not_dvd_relIndex
    have hrel := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := T) (K := R) hTR).1
    have hmul := Subgroup.relIndex_mul_relIndex (H := T) (K := T ⊔ R) (L := Y)
      le_sup_left (sup_le hT.le hRY)
    have hdvd : (T ⊓ R).relIndex R ∣ T.relIndex Y := by
      refine ⟨(T ⊔ R).relIndex Y, ?_⟩
      rw [← hrel]
      exact hmul.symm
    have hoddS : Odd ((T ⊓ R).relIndex R) := Odd.of_dvd_nat hodd hdvd
    simpa [Nat.even_iff] using (Nat.not_even_iff_odd.mpr hoddS)
  have hleS : S ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    inf_le_left.trans hTK
  exact (kO4PlusSwap_holds W (R := R) (K := K) (S := S) (e := e) hnat hKq hKsub hSyl) hleS

private theorem iSup_conjSet_ne_self_of_not_normal {W : Type} [CommGroup W]
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hnot : ¬ (L.subgroupOf Y).Normal) : (⨆ X ∈ conjSet L Y, X) ≠ L := by
  intro hHK
  apply hnot
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLY]
  intro y hy
  have hle_y : L.map (MulAut.conj y).toMonoidHom ≤ L := by
    have hmem : L.map (MulAut.conj y).toMonoidHom ≤ ⨆ X ∈ conjSet L Y, X :=
      le_iSup₂_of_le _ ⟨y, hy, rfl⟩ le_rfl
    simpa [hHK] using hmem
  have hle_yinv : L.map (MulAut.conj y⁻¹).toMonoidHom ≤ L := by
    have hmem : L.map (MulAut.conj y⁻¹).toMonoidHom ≤ ⨆ X ∈ conjSet L Y, X :=
      le_iSup₂_of_le _ ⟨y⁻¹, Y.inv_mem hy, rfl⟩ le_rfl
    simpa [hHK] using hmem
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmem := hle_y (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hx)
    simpa [MulAut.conj_apply] using hmem
  · intro hx
    have hx' : MulAut.conj y x ∈ L := by simpa [MulAut.conj_apply] using hx
    have hmem := hle_yinv (Subgroup.mem_map_of_mem (MulAut.conj y⁻¹).toMonoidHom hx')
    simpa [MulAut.conj_apply, mul_assoc] using hmem

theorem normal_of_higher_rank {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) (h1A : S23_1A D Ch)
    (h128 : W4Lem12_8) (hDeg : KMinDegLow)
    {A K P : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L) (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hn : NParam (Hinf P) c.n) (hn2 : 2 < c.n) (hshape : S20_7Shape (Bar2 c.L))
    (hLAeq : barSub ⊥ A hA c.L = barSub ⊥ A hA K)
    (hfixH : fixV (⨆ X ∈ conjSet (barSub ⊥ A hA K) (Mbar c.N ⊥ A hA), X) = ⊥)
    (hTK : barSub ⊥ A hA D.T ≤
      Subgroup.normalizer (barSub ⊥ A hA K : Set (MulAut (Vtil ⊥ A hA))))
    (hTsyl : IsSylowIn 2 (barSub ⊥ A hA D.T) (Mbar c.N ⊥ A hA)) :
    ((barSub ⊥ A hA K).subgroupOf (Mbar c.N ⊥ A hA)).Normal := by
  classical
  set Y : Subgroup (MulAut (Vtil ⊥ A hA)) := Mbar c.N ⊥ A hA with hY
  set KA : Subgroup (MulAut (Vtil ⊥ A hA)) := barSub ⊥ A hA K with hKA
  set H : Subgroup (MulAut (Vtil ⊥ A hA)) := ⨆ X ∈ conjSet KA Y, X with hH
  have hcomp : IsComponentOf KA Y := by
    simpa [Y, KA] using
      isComponentOf_barSub_of_sup_conj c h208 h1930 hA hAV hAN hAne hK hgen
  have hbasic : O2Trivial Y ∧ IsIrrOn Y ⊤ ⊥ ∧ IsIndivisible Y ∧ IsBasicModule Y := by
    simpa [Y] using Ctx23L.isBasic_barSub c hA hAV hAN hAne hmin
  have hKne : KA ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot KA).mp (CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2))
  have hfixKA : fixV KA = ⊥ := by
    rw [← hLAeq]
    exact fixV_barSub_eq_bot c hA hAV hAN
  have hfaith : ∀ y ∈ Y, (∀ w : Vtil ⊥ A hA, y w = w) → y = 1 :=
    fun y _ hy => MulEquiv.ext fun w => hy w
  by_contra hnot
  have hHne : H ≠ KA := by
    have h := iSup_conjSet_ne_self_of_not_normal hcomp.1 hnot
    simpa [H, KA] using h
  have htrich := h128 (Vtil ⊥ A hA) (s15_Infra_vtil_sq_eq_one ⊥ A hA) Y
    (by simpa [O2Trivial, Y] using hbasic.1) (by simpa [Y] using hbasic.2.2.2)
    KA hcomp H hH.symm
  have hne1 : ¬ dMinDeg ↥KA ≤ E3.mParam Y := by
    simpa [Y, KA, mBar] using
      not_dMinDeg_le_mBar c h208 h1930 h1A hDeg hA hAV hAne hAN hmin hK hgen hP hL0P hn hn2
        hshape
  rcases htrich with h1 | ⟨h2sum, -⟩ | ⟨R, e, hRY, hsumR, hKsubR, hnatR, -, -⟩
  · exact hne1 (by simpa [Y, KA] using h1)
  · exact false_of_isDirSumOver_case_two hcomp hH (by simpa [H, Y, KA] using hfixH) hfixKA
      hfaith hHne h2sum
  · exact false_of_isDirSumOver_isNaturalO4Plus (T := barSub ⊥ A hA D.T) hTsyl hsumR hRY
      hKsubR hcomp.2.2 hTK hnatR hKne

theorem eq_of_isQuasisimple_of_isComponentOf {W : Type} [CommGroup W] [Finite W]
    {H L : Subgroup (MulAut W)} (hH : CFSG.Open.IsQuasisimple ↥H) (hLH : L ≤ H)
    (hL : IsComponentOf L H) : L = H := by
  have hqSub : CFSG.Open.IsQuasisimple ↥(L.subgroupOf H) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH) hL.2.2
  have hsubSub : CFSG.Open.IsSubnormal (L.subgroupOf H) ⊤ := by
    have h := CFSG.Open.IsSubnormal.comap (f := H.subtype) hL.2.1
    simpa [Subgroup.subgroupOf_self] using h
  have hsubSubM : (L.subgroupOf H).IsSubnormal :=
    (CFSG.Quasithin.A3.subnormal_top_iff).mp hsubSub
  have hcompSub : CFSG.IsComponent (L.subgroupOf H) :=
    (CFSG.Foundations.SteinbergCA.component_iff _).mpr
      ⟨(CFSG.Quasithin.A3.isQuasisimple_iff_open).mpr hqSub, hsubSubM⟩
  have hqL : CFSG.IsQuasisimple L :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).mpr hL.2.2
  have hHnative : CFSG.IsQuasisimple ↥H :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).mpr hH
  rcases CFSG.Quasithin.A3.eq_top_or_le_center_of_subnormal hHnative hcompSub.2 with
    htop | hcen
  · have hHL : H ≤ L := by
      intro x hx
      have hx' : (⟨x, hx⟩ : H) ∈ L.subgroupOf H := htop ▸ Subgroup.mem_top _
      exact hx'
    exact le_antisymm hLH hHL
  · exfalso
    have hcomm : ∀ a b : ↥(L.subgroupOf H), a * b = b * a := by
      intro a b
      apply Subtype.ext
      simpa using (Subgroup.mem_center_iff.mp (hcen a.2) (b : H)).symm
    have hsolvSub : Group.IsSolvable ↥(L.subgroupOf H) := Group.isSolvable_of_comm hcomm
    haveI : Group.IsPerfect ↥(L.subgroupOf H) := (Group.isPerfect_def).mpr hqSub.1
    haveI : Nontrivial ↥(L.subgroupOf H) :=
      CFSG.LocalCores.isQuasisimple_nontrivial
        ((CFSG.Quasithin.A3.isQuasisimple_iff_open).mpr hqSub)
    exact Group.IsPerfect.not_isSolvable ↥(L.subgroupOf H) hsolvSub

private theorem le_of_eq_iSup_conjSet {W : Type} [CommGroup W]
    {Y L H : Subgroup (MulAut W)} (hLY : L ≤ Y) (hH : H = ⨆ X ∈ conjSet L Y, X) :
    H ≤ Y := by
  rw [hH]
  refine iSup₂_le fun X hX => ?_
  obtain ⟨m, hm, rfl⟩ := hX
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
  simpa [MulAut.conj_apply] using Y.mul_mem (Y.mul_mem hm (hLY hl)) (Y.inv_mem hm)

theorem natural_of_case_two_three {W : Type} [CommGroup W] [Finite W]
    {Y L LA H : Subgroup (MulAut W)} {n : ℕ}
    (hcomp : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    (hYH : Y ≤ Subgroup.normalizer (H : Set (MulAut W))) (hLA : LA = H)
    (hcase : IsNaturalClassicalModule H n ∨
      (Even n ∧ IsOmegaMinus ↥H 4 (n / 2) ∧ NatOmegaMinus H ⊤ ⊥ 4 (n / 2))) :
    ∃ k, IsNaturalClassicalModule LA k ∧
      (k = n ∨ (2 * k = n ∧ IsOmegaMinus ↥LA 4 k)) ∧ (LA.subgroupOf Y).Normal := by
  classical
  have hHY : H ≤ Y := le_of_eq_iSup_conjSet hcomp.1 hH
  have hLAleY : LA ≤ Y := hLA ▸ hHY
  have hnorm : (LA.subgroupOf Y).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hLAleY).mpr ?_
    rwa [hLA]
  have hnormH : (H.subgroupOf Y).Normal := by simpa [hLA] using hnorm
  rcases hcase with hnat | ⟨heven, hom, hnatom⟩
  · refine ⟨n, ?_, Or.inl rfl, ?_⟩
    · rw [hLA]
      exact hnat
    · rw [hLA]
      exact hnormH
  · have htwo : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
    have hnat' : IsNaturalClassicalModule H (n / 2) :=
      Or.inr (Or.inl ⟨hom, hnatom⟩)
    refine ⟨n / 2, ?_, Or.inr ⟨htwo, ?_⟩, ?_⟩
    · rw [hLA]
      exact hnat'
    · rw [hLA]
      exact hom
    · rw [hLA]
      exact hnormH

theorem natural_of_case_two_three_barSub {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hK : K ∈ calC c.L) {H : Subgroup (MulAut (Vtil ⊥ A hA))}
    (hH : H = ⨆ X ∈ conjSet (barSub ⊥ A hA K) (Mbar c.N ⊥ A hA), X)
    (hLA : barSub ⊥ A hA c.L = H)
    (hYH : Mbar c.N ⊥ A hA ≤ Subgroup.normalizer (H : Set (MulAut (Vtil ⊥ A hA))))
    (hcase : IsNaturalClassicalModule H c.n ∨
      (Even c.n ∧ IsOmegaMinus ↥H 4 (c.n / 2) ∧ NatOmegaMinus H ⊤ ⊥ 4 (c.n / 2)))
    (hcomp : IsComponentOf (barSub ⊥ A hA K) (Mbar c.N ⊥ A hA)) :
    ∃ k, IsNaturalClassicalModule (barSub ⊥ A hA c.L) k ∧
      (k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k)) ∧
      ((barSub ⊥ A hA c.L).subgroupOf (Mbar c.N ⊥ A hA)).Normal := by
  exact natural_of_case_two_three hcomp hH hYH hLA hcase

end CFSG.LocalAnalysis.UniquenessCase.UC22
