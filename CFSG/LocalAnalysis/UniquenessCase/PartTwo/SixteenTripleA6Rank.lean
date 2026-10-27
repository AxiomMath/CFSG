module

public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTripleA6Cover
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.Quasithin.Background.F918V5GComp
public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.Background.F918G1
public import CFSG.Quasithin.Background.FFC5Two

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_faithful_barImage_of_tripleA6
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) (h127 : R127 D) (h119 : F11.R119 D)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : CFSG.Open.IsComponentOf H (Mbar D.M V₀ V hV))
    (hHhat : IsHat H (alternatingGroup (Fin 6)))
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil h125.pairFacts.le_normalizer
        h125.pairFacts.le_normalizer₀ m.2⟩) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧ barSub V₀ V hV K = H ∧
      CFSG.IsComponent (UC22.barImage D.M K) ∧
      (UC22.barImage D.M K).map ψ = H ∧
      Function.Injective (ψ.comp (UC22.barImage D.M K).subtype) ∧
      CFSG.Open.pRank 3 (UC22.barImage D.M K) = 2 := by
  classical
  obtain ⟨K, hK, hbarK⟩ := exists_calC_cover_of_component h125 h127 h119 hcomp
  have hCcomp : CFSG.IsComponent (UC22.barImage D.M K) :=
    UC22.uc22p22l_barImage_isComponent hK
  have hCmap : (UC22.barImage D.M K).map ψ = H :=
    barImage_map_eq_of_mem_calC h125 hK hbarK ψ hψ
  have hodd : Odd (Nat.card (Subgroup.center (UC22.barImage D.M K))) := by
    obtain ⟨eK⟩ := UC22.uc22p22l_barImage_equiv hK
    rw [← Nat.card_congr (Subgroup.centerCongr eK).toEquiv]
    exact UC22.uc22p20p_odd_center_bar2 K
  have hq : CFSG.Open.IsQuasisimple ↥(UC22.barImage D.M K) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hCcomp.1
  let f : ↥(UC22.barImage D.M K) →* ↥H :=
    (ψ.comp (UC22.barImage D.M K).subtype).codRestrict H (fun x => by
      rw [← hCmap]
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hfsurj : Function.Surjective f := by
    intro h
    have hh : (h : MulAut (Vtil V₀ V hV)) ∈ (UC22.barImage D.M K).map ψ := by
      rw [hCmap]
      exact h.2
    obtain ⟨c, hc, hcψ⟩ := Subgroup.mem_map.mp hh
    exact ⟨⟨c, hc⟩, Subtype.ext hcψ⟩
  have hfbij : Function.Bijective f :=
    bijective_of_surjective_isHat_a6_of_quasisimple_odd_center hq hodd hHhat f hfsurj
  refine ⟨K, hK, hbarK, hCcomp, hCmap, ?_, ?_⟩
  · intro x y hxy
    exact hfbij.1 (Subtype.ext hxy)
  · have eCH : ↥(UC22.barImage D.M K) ≃* ↥H := MulEquiv.ofBijective f hfbij
    have hHrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) = 2 :=
      CFSG.Quasithin.pRank_three_hatA6 hHhat
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (UC22.barImage D.M K),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eCH, hHrank]

theorem barLift_comp_mk'_eq_barHom
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {hms : D.M ≤ stabTil V₀ V}
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, hms m.2⟩) :
    ψ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) = barHom V₀ V hV hms := by
  apply MonoidHom.ext
  intro m
  rw [MonoidHom.comp_apply]
  change ψ (QuotientGroup.mk m) = actTil V₀ V hV ⟨m, hms m.2⟩
  exact hψ m

theorem range_eq_mbar
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {hms : D.M ≤ stabTil V₀ V}
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, hms m.2⟩) :
    ψ.range = Mbar D.M V₀ V hV := by
  have h1 : (ψ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))).range = ψ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), Subgroup.map_top]
  have h2 : (ψ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))).range =
      Mbar D.M V₀ V hV := by
    rw [barLift_comp_mk'_eq_barHom ψ hψ]
    exact range_barHom V₀ V hV hms
  exact h1.symm.trans h2

theorem s15_eq_one_of_tripleA6_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hN : TripleA6Six (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  by_contra hs
  have hs2 : 2 ≤ s15 D.M V₀ V hV L := by
    have h1 := Om8Excl.one_le_s15 D.M V₀ V hV L
    omega
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  have hcompH : CFSG.Open.IsComponentOf H A := hcomp
  have hNH : TripleA6Six H (commSub ⊤ H) (commSub ⊤ H ⊓ fixV H) := hN
  have hHhat : IsHat H (alternatingGroup (Fin 6)) := isHat_of_tripleA6Six hNH
  obtain ⟨Hx, hHxmem, hHxne⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := conjSet H A)
      (by
        have h1 : (conjSet H A).ncard = s15 D.M V₀ V hV L := rfl
        rw [h1]
        omega) H
  obtain ⟨g, hgA, hgHx⟩ := hHxmem
  have hH'ne : H.map (MulAut.conj g).toMonoidHom ≠ H := hgHx ▸ hHxne
  have hgnot : g ∉ Subgroup.normalizer (H : Set (MulAut (Vtil V₀ V hV))) :=
    fun hg => hH'ne (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)
  obtain ⟨_t, _htM, _ht2, _ht1, _htrk, hW⟩ := c.conc
  have hcross : commSub (commSub ⊤ H) (H.map (MulAut.conj g).toMonoidHom) = ⊥ :=
    (hW.2.1 g hgA hgnot).2
  obtain ⟨_Kf, _hKfield, _hKfin, Γ₀, _hK4, _hdet, _hHatΓ, _hsc, hReal⟩ := hNH
  obtain ⟨π, hπ⟩ := hReal
  have hfaith := FFC.faithful_on_of_realizes (FFModel.nat_faithful Γ₀) hπ
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  obtain ⟨K, hK, _hbarK, hCcomp, hCmap, hCinj, hCrank⟩ :=
    exists_faithful_barImage_of_tripleA6 c.setting.hyp16.hyp125 c.std.h127 c.std.h119
      hcompH hHhat ψ hψ
  have hcomp' : CFSG.Open.IsComponentOf (H.map (MulAut.conj g).toMonoidHom) A :=
    CFSG.Quasithin.F918V5G.isComponentOf_map_conj hcompH hgA
  have hH'hat : IsHat (H.map (MulAut.conj g).toMonoidHom) (alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv (H.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective) hHhat
  obtain ⟨K', _hK', _hbarK', hC'comp, hC'map, hC'inj, hC'rank⟩ :=
    exists_faithful_barImage_of_tripleA6 c.setting.hyp16.hyp125 c.std.h127 c.std.h119
      hcomp' hH'hat ψ hψ
  have hInterH : H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxfix : ∀ u ∈ commSub (⊤ : Subgroup (Vtil V₀ V hV)) H, x u = u := by
      intro u hu
      exact mem_fixV.mp (commSub_eq_bot_iff.mp hcross hu) x hx.2
    exact Subgroup.mem_bot.mpr (hfaith x hx.1 hxfix)
  have hInterC : UC22.barImage D.M K ⊓ UC22.barImage D.M K' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxψ : ψ x ∈ H ⊓ H.map (MulAut.conj g).toMonoidHom := by
      refine ⟨?_, ?_⟩
      · rw [← hCmap]
        exact Subgroup.mem_map.mpr ⟨x, hx.1, rfl⟩
      · rw [← hC'map]
        exact Subgroup.mem_map.mpr ⟨x, hx.2, rfl⟩
    have hxψ1 : ψ x = 1 := by
      have hmem : ψ x ∈ (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) := by
        rw [← hInterH]
        exact hxψ
      exact Subgroup.mem_bot.mp hmem
    have hx1 : (⟨x, hx.1⟩ : ↥(UC22.barImage D.M K)) = 1 :=
      hCinj (by simpa using hxψ1)
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hx1)
  have hCne : UC22.barImage D.M K ≠ UC22.barImage D.M K' := by
    intro heq
    apply hH'ne
    rw [← hC'map, ← heq, hCmap]
  have hcommute : ∀ x ∈ UC22.barImage D.M K, ∀ y ∈ UC22.barImage D.M K',
      x * y = y * x := by
    have hcommBot : ⁅UC22.barImage D.M K, UC22.barImage D.M K'⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hCcomp hC'comp).resolve_left hCne
    intro x hx y hy
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot hx
    exact (Subgroup.mem_centralizer_iff.mp hcent y hy).symm
  have hrank4 : 4 ≤ CFSG.Open.pRank 3
      (UC22.barImage D.M K ⊔ UC22.barImage D.M K') := by
    have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
      (q := 3) Nat.prime_three hcommute ?_
    · rw [hCrank, hC'rank] at hadd
      omega
    · have hcard : Nat.card ↥(UC22.barImage D.M K ⊓ UC22.barImage D.M K') = 1 := by
        rw [hInterC, Subgroup.card_bot]
      rw [hcard]
      norm_num
  have hupper : CFSG.Open.pRank 3
      (UC22.barImage D.M K ⊔ UC22.barImage D.M K') ≤ 3 := by
    have h1 : CFSG.Open.pRank 3 (UC22.barImage D.M K ⊔ UC22.barImage D.M K') ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) :=
      CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) = CFSG.Open.pRank 3 D.M :=
      (CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient D.M).symm
    have h3 : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
      CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
        (by norm_num) D.M D.maxLocal.1
    have h3e : CFSG.Open.evenRank G = 3 := c.std.h3
    omega
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
