module

public import CFSG.GroupTheory.ComponentImageUniqueness
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCoverSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barSub_eq_map_barImage
    {V₀ V Y K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hYs : Y ≤ stabTil V₀ V)
    (psi : Bar2 Y →* MulAut (Vtil V₀ V hV))
    (hpsi : ∀ y : Y,
      psi (QuotientGroup.mk y) = actTil V₀ V hV ⟨y, hYs y.2⟩)
    (hKY : K ≤ Y) :
    barSub V₀ V hV K = (UC22.barImage Y K).map psi := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hgK, rfl⟩ := (mem_barSub V₀ V hV K φ).1 hφ
    refine Subgroup.mem_map.2
      ⟨QuotientGroup.mk ⟨(g : G), hKY hgK⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.2
        ⟨⟨(g : G), hKY hgK⟩, (Subgroup.mem_subgroupOf).2 hgK, rfl⟩
    · rw [hpsi ⟨(g : G), hKY hgK⟩]
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hc
    have hyK : (y : G) ∈ K := (Subgroup.mem_subgroupOf).1 hy
    refine (mem_barSub V₀ V hV K (psi c)).2 ⟨⟨(y : G), hYs y.2⟩, hyK, ?_⟩
    rw [← hyc]
    change actTil V₀ V hV ⟨(y : G), hYs y.2⟩ = psi (QuotientGroup.mk y)
    rw [hpsi y]

private theorem exists_calC_cover_of_component_aux
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) (h127 : R127 D) (h119 : F11.R119 D)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : CFSG.Open.IsComponentOf H (Mbar D.M V₀ V hV)) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧ barSub V₀ V hV K = H ∧
      (Subgroup.center ↥H = ⊥ →
        Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* ↥H)) := by
  classical
  have hms : D.M ≤ stabTil V₀ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  haveI hCT : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal hV hms
  set X : Subgroup G := preBarSub D.M V₀ V hV H with hXdef
  have hXM : X ≤ D.M := by rw [hXdef]; exact inf_le_left
  have hCX : F11.CTilde D.M V₀ V ≤ X := by
    rw [hXdef, cTilde_eq_preBarSub_bot hV h125.pairFacts.le_normalizer]
    exact s15_Seven_preBarSub_mono hV bot_le
  have hbarX : barSub V₀ V hV X = H := by
    rw [hXdef, barSub_preBarSub]
    exact inf_eq_left.2 hcomp.1
  have hpre : X = (H.comap (barHom V₀ V hV hms)).map D.M.subtype := by
    rw [hXdef]
    ext g
    rw [mem_preBarSub, Subgroup.mem_map]
    constructor
    · rintro ⟨hgM, hst, hact⟩
      refine ⟨⟨g, hgM⟩, ?_, rfl⟩
      change actTil V₀ V hV ((Subgroup.inclusion hms) ⟨g, hgM⟩) ∈ H
      rw [show ((Subgroup.inclusion hms) ⟨g, hgM⟩ : ↥(stabTil V₀ V)) = ⟨g, hst⟩ from
        Subtype.ext rfl]
      exact hact
    · rintro ⟨m, hm, rfl⟩
      refine ⟨m.2, hms m.2, ?_⟩
      change actTil V₀ V hV ((Subgroup.inclusion hms) m) ∈ H
      exact hm
  have htop : (Mbar D.M V₀ V hV).comap (barHom V₀ V hV hms) = ⊤ := by
    rw [eq_top_iff]
    intro m _
    rw [Subgroup.mem_comap]
    change (barHom V₀ V hV hms) m ∈ barSub V₀ V hV D.M
    exact (range_barHom V₀ V hV hms) ▸ MonoidHom.mem_range.mpr ⟨m, rfl⟩
  have hXMsub : CFSG.Open.IsSubnormal X D.M := by
    have hcomap : CFSG.Open.IsSubnormal (H.comap (barHom V₀ V hV hms))
        ((Mbar D.M V₀ V hV).comap (barHom V₀ V hV hms)) :=
      CFSG.Open.IsSubnormal.comap (barHom V₀ V hV hms) hcomp.2.1
    rw [htop] at hcomap
    have hmap := CFSG.Open.IsSubnormal.map D.M.subtype hcomap
    rw [Subgroup.map_top, Subgroup.range_subtype, ← hpre] at hmap
    exact hmap
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hms
  have hqX : CFSG.Open.IsQuasisimple ↥(F11.barImage11 D.M V₀ V X) := by
    have hmap : (F11.barImage11 D.M V₀ V X).map e.toMonoidHom =
        H.subgroupOf (Mbar D.M V₀ V hV) := by
      rw [he X hXM, hbarX]
    let eB : ↥(F11.barImage11 D.M V₀ V X) ≃* ↥H :=
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).trans (Subgroup.subgroupOfEquivOfLe hcomp.1)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv eB hcomp.2.2
  have hlayerX : rankThreeLayer (F11.barImage11 D.M V₀ V X) =
      F11.barImage11 D.M V₀ V X := by
    set B : Subgroup (F11.MBar11 D.M V₀ V) := F11.barImage11 D.M V₀ V X with hBdef
    have hqB : CFSG.Open.IsQuasisimple ↥B := hqX
    exact le_antisymm (sSup_le fun _ hK => hK.1)
      (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl B, hqB⟩)
  obtain ⟨Y, hY, -⟩ := h119 V₀ V (Hyp125.hyp11 h127 h125) X hCX hXM hlayerX
  have hYX : Y ≤ X := hY.1
  have hYperf : ⁅Y, Y⁆ = Y := hY.2.1
  have hYE : F11.O2E Y = Y := hY.2.2.1
  have hYN : X ≤ normalizer (Y : Set G) := hY.2.2.2.1
  have hYC : Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y := hY.2.2.2.2.1
  have hYbar : F11.barImage11 D.M V₀ V Y = F11.barImage11 D.M V₀ V X := hY.2.2.2.2.2
  have hY_le : Y ≤ D.M := hYX.trans hXM
  have hYXsub : CFSG.Open.IsSubnormal Y X :=
    A3.subnormal_of_normal hYX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hYN)
  have hYMsub : CFSG.Open.IsSubnormal Y D.M := A3.subnormal_trans hYXsub hXMsub
  have hbarY : barSub V₀ V hV Y = H := by
    have hsub : (barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV) =
        (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he Y hY_le, ← he X hXM, hYbar]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hY_le),
      inf_eq_left.2 (barSub_mono V₀ V hV hXM), hbarX] at h2
    exact h2
  have hYs : Y ≤ stabTil V₀ V := hY_le.trans hms
  have h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hYMsub
      (barSub_pCoreOf_eq_bot_of_hyp125 h125)
  obtain ⟨psi, hpsi⟩ := s1715six_barLift_exists hV hYs h2
  have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hYmap : (⊤ : Subgroup (Bar2 Y)).map psi = H := by
    have h := s1715six_barSub_comap_map hV hYs psi hpsi ⊤
    rw [Subgroup.comap_top, hTop] at h
    rw [← hbarY]
    exact h.symm
  have hlayer_top : rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ :=
    s1715six_layer_top_of_O2E_eq hYE
  have hsup : H = ⨆ C ∈ {C : Subgroup (Bar2 Y) | CFSG.Open.IsComponentOf C ⊤},
      C.map psi := by
    rw [← hYmap]
    conv_lhs => rw [← hlayer_top]
    rw [CFSG.Open.rankThreeLayer, sSup_eq_iSup]
    simp only [Subgroup.map_iSup]
  have hex : ∃ C : Subgroup (Bar2 Y), CFSG.Open.IsComponentOf C ⊤ ∧ C.map psi = H := by
    by_contra hcon
    push Not at hcon
    have hbot : ∀ C : Subgroup (Bar2 Y),
        CFSG.Open.IsComponentOf C ⊤ → C.map psi = ⊥ := by
      intro C hC
      by_cases hker : C ≤ psi.ker
      · exact (Subgroup.map_eq_bot_iff _).mpr hker
      · have hcomp' := CFSG.Quasithin.B15P4.isComponentOf_map_hom psi hC hker
        rw [hYmap] at hcomp'
        haveI : Group.IsPerfect ↥(C.map psi) := ⟨hcomp'.2.2.1⟩
        have hsub : CFSG.Open.IsSubnormal ((C.map psi).subgroupOf H) ⊤ :=
          A3.subnormal_top_iff.mpr hcomp'.2.1.subgroupOf
        haveI : Group.IsPerfect ↥((C.map psi).subgroupOf H) :=
          Group.IsPerfect.ofSurjective
            (f := (Subgroup.subgroupOfEquivOfLe hcomp'.1).symm.toMonoidHom)
            (Subgroup.subgroupOfEquivOfLe hcomp'.1).symm.surjective
        rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
          hcomp.2.2 ((C.map psi).subgroupOf H) hsub with h0 | htop
        · exact (Subgroup.subgroupOf_eq_bot.1 h0).eq_bot_of_le hcomp'.1
        · exact absurd (le_antisymm hcomp'.1 (Subgroup.subgroupOf_eq_top.1 htop)) (hcon C hC)
    have hHbot : H = ⊥ := by
      rw [hsup]
      refine le_bot_iff.1 (iSup_le fun C => iSup_le fun hC => ?_)
      rw [hbot C hC]
    exact (Subgroup.nontrivial_iff_ne_bot H).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial (A3.isQuasisimple_iff_open.mpr hcomp.2.2))
      hHbot
  obtain ⟨C, hC, hCmap⟩ := hex
  obtain ⟨K, hKY, hKs, hKperf, hKq, -, hKmap⟩ := s15_Three_core_of_component hC
  have hbarImage : UC22.barImage Y K = C := by
    unfold UC22.barImage
    exact hKmap
  have hbarK : barSub V₀ V hV K = H := by
    rw [barSub_eq_map_barImage hV hYs psi hpsi hKY, hbarImage, hCmap]
  have hKMsub : CFSG.Open.IsSubnormal K D.M := A3.subnormal_trans hKs hYMsub
  have hKmem : K ∈ calC D.M := ⟨hKMsub, hKperf, hKq⟩
  refine ⟨K, hKmem, hbarK, fun hZH => ?_⟩
  have hT : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV K) := by
    rw [hbarK]
    exact hcomp.2.2
  have hZ : Subgroup.center ↥(barSub V₀ V hV K) = ⊥ := by
    rw [hbarK]
    exact hZH
  obtain ⟨eK⟩ :=
    s15_Three_cover_iso (K₀ := K) hV hms hKY hKs hYC hYMsub.le h2 hKq hT hZ rfl
  exact ⟨eK.trans (MulEquiv.subgroupCongr hbarK)⟩

theorem exists_calC_cover_of_component
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) (h127 : R127 D) (h119 : F11.R119 D)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : CFSG.Open.IsComponentOf H (Mbar D.M V₀ V hV)) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧ barSub V₀ V hV K = H := by
  obtain ⟨K, hK, hbar, -⟩ := exists_calC_cover_of_component_aux h125 h127 h119 hcomp
  exact ⟨K, hK, hbar⟩

theorem exists_calC_cover_of_simple_component
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) (h127 : R127 D) (h119 : F11.R119 D)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : CFSG.Open.IsComponentOf H (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥H) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧
      barSub V₀ V hV K = H ∧
      Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* ↥H) := by
  haveI := hsimple
  have hZH : Subgroup.center ↥H = ⊥ := by
    haveI : Group.IsPerfect ↥H := ⟨hcomp.2.2.1⟩
    exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative (G := ↥H))
  obtain ⟨K, hK, hbar, hiso⟩ :=
    exists_calC_cover_of_component_aux h125 h127 h119 hcomp
  exact ⟨K, hK, hbar, hiso hZH⟩

theorem exists_barLift_of_hyp125
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) :
    ∃ ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV),
      ∀ m : D.M, ψ (QuotientGroup.mk m) =
        actTil V₀ V hV ⟨m, le_stabTil h125.pairFacts.le_normalizer
          h125.pairFacts.le_normalizer₀ m.2⟩ :=
  s1715six_barLift_exists hV
    (le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀)
    (barSub_pCoreOf_eq_bot_of_hyp125 h125)

theorem barImage_map_eq_of_mem_calC
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hbarK : barSub V₀ V hV K = H)
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil h125.pairFacts.le_normalizer
        h125.pairFacts.le_normalizer₀ m.2⟩) :
    (UC22.barImage D.M K).map ψ = H := by
  have hms : D.M ≤ stabTil V₀ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hKM : K ≤ D.M := A3.subnormal_le hK.1
  calc
    (UC22.barImage D.M K).map ψ = barSub V₀ V hV K :=
      (barSub_eq_map_barImage hV hms ψ hψ hKM).symm
    _ = H := hbarK

theorem ker_comp_subtype_eq_center_of_mem_calC
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hbarK : barSub V₀ V hV K = H)
    (hsimple : IsSimpleGroup ↥H)
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil h125.pairFacts.le_normalizer
        h125.pairFacts.le_normalizer₀ m.2⟩) :
    (ψ.comp (UC22.barImage D.M K).subtype).ker =
      Subgroup.center (UC22.barImage D.M K) :=
  CFSG.ComponentImage.ker_comp_subtype_eq_center ψ
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_barImage_isComponent hK)
    (barImage_map_eq_of_mem_calC h125 hK hbarK ψ hψ) hsimple

theorem mem_normalizer_barImage_of_map_mem_normalizer
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hbarK : barSub V₀ V hV K = H)
    (hsimple : IsSimpleGroup ↥H)
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil h125.pairFacts.le_normalizer
        h125.pairFacts.le_normalizer₀ m.2⟩)
    {x : Bar2 D.M}
    (hx : ψ x ∈ Subgroup.normalizer (H : Set (MulAut (Vtil V₀ V hV)))) :
    x ∈ Subgroup.normalizer (UC22.barImage D.M K : Set (Bar2 D.M)) := by
  have hC : CFSG.IsComponent (UC22.barImage D.M K) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_barImage_isComponent hK
  have hmap : (UC22.barImage D.M K).map ψ = H :=
    barImage_map_eq_of_mem_calC h125 hK hbarK ψ hψ
  have hna := CFSG.ComponentImage.exists_noncommuting_map_of_isSimpleGroup ψ hC hmap hsimple
  have hx' : ψ x ∈ Subgroup.normalizer ((UC22.barImage D.M K).map ψ :
      Set (MulAut (Vtil V₀ V hV))) := by
    rwa [hmap]
  exact CFSG.ComponentImage.mem_normalizer_of_map_mem_normalizer ψ hC hna hx'

theorem mem_centralizer_barImage_of_map_mem_centralizer
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hbarK : barSub V₀ V hV K = H)
    (hsimple : IsSimpleGroup ↥H)
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil h125.pairFacts.le_normalizer
        h125.pairFacts.le_normalizer₀ m.2⟩)
    {x : Bar2 D.M}
    (hx : ψ x ∈ Subgroup.centralizer (H : Set (MulAut (Vtil V₀ V hV)))) :
    x ∈ Subgroup.centralizer (UC22.barImage D.M K : Set (Bar2 D.M)) := by
  have hC : CFSG.IsComponent (UC22.barImage D.M K) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_barImage_isComponent hK
  have hmap : (UC22.barImage D.M K).map ψ = H :=
    barImage_map_eq_of_mem_calC h125 hK hbarK ψ hψ
  have hna := CFSG.ComponentImage.exists_noncommuting_map_of_isSimpleGroup ψ hC hmap hsimple
  have hx' : ψ x ∈ Subgroup.centralizer ((UC22.barImage D.M K).map ψ :
      Set (MulAut (Vtil V₀ V hV))) := by
    rwa [hmap]
  exact CFSG.ComponentImage.mem_centralizer_of_map_mem_centralizer ψ hC hna hx'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
