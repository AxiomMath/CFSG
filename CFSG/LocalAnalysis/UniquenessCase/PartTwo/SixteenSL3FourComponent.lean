module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.Quasithin.H13.A5W1622q
import CFSG.Quasithin.EmptyFaithful.R3cBlocks
import CFSG.CGT.PushingUpLit.CGT6.EmbCommV
import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.Quasithin.Background.F918V5GComp
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

private theorem card_center_of_isSLn_three_two {X : Type} [Group X] (h : IsSLn X 3 2) :
    Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨F, hFfield, hFfinite, hFcard, ⟨e⟩⟩ := h
  let hFfield' : Field F := hFfield
  let hFfinite' : Finite F := hFfinite
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (K := F) (by
    rw [hFcard]
    norm_num)

private theorem exists_faithful_barImage_of_sl3_four
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) (h127 : R127 D) (h119 : F11.R119 D)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : CFSG.Open.IsComponentOf H (Mbar D.M V₀ V hV))
    (hSL : IsSLn ↥H 3 2)
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
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hK
  have hCmap : C.map ψ = H := by
    simpa [C] using barImage_map_eq_of_mem_calC h125 hK hbarK ψ hψ
  have hoddC : Odd (Nat.card ↥(Subgroup.center C)) := by
    obtain ⟨eK⟩ := UC22.uc22p22l_barImage_equiv hK
    rw [← Nat.card_congr (Subgroup.centerCongr eK).toEquiv]
    exact UC22.uc22p20p_odd_center_bar2 K
  let f : ↥C →* ↥H := (MulEquiv.subgroupCongr hCmap).toMonoidHom.comp (ψ.subgroupMap C)
  have hfsurj : Function.Surjective f :=
    (MulEquiv.subgroupCongr hCmap).surjective.comp (ψ.subgroupMap_surjective C)
  have hHnt : Nontrivial ↥H :=
    CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2)
  have hfker : f.ker ≤ Subgroup.center ↥C :=
    CFSG.Quasithin.H13.A5.ker_le_center_of_isQuasisimple hCcomp.1 f hfsurj hHnt
  obtain ⟨F, hFfield, hFfinite, hFcard, ⟨eH⟩⟩ := hSL
  let hFfield' : Field F := hFfield
  let hFfinite' : Finite F := hFfinite
  have hCharP : CharP F 2 :=
    CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow (f := 2) hFcard
  let π : ↥C →* ↥(StatedSL 3 F) := eH.toMonoidHom.comp f
  have hπsurj : Function.Surjective π := eH.surjective.comp hfsurj
  have hπker : π.ker = f.ker :=
    MonoidHom.ker_comp_of_injective f eH.toMonoidHom eH.injective
  have hπcen : π.ker ≤ Subgroup.center ↥C := by
    rw [hπker]
    exact hfker
  have hπodd : Odd (Nat.card π.ker) := by
    rw [hπker]
    exact Odd.of_dvd_nat hoddC (Subgroup.card_dvd_of_le hfker)
  obtain ⟨σ, hσ, -⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated
      (K := F) (n := 3) (by norm_num) hπsurj hπcen hπodd
  have hPerf : Group.IsPerfect ↥C := hCcomp.1.1
  have hπbot : π.ker = ⊥ :=
    CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section π hπcen σ hσ
  have hfkerbot : f.ker = ⊥ := by
    rw [← hπker]
    exact hπbot
  have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hfkerbot
  have hCinj : Function.Injective (ψ.comp C.subtype) := by
    intro x y hxy
    exact hfinj (Subtype.ext hxy)
  refine ⟨K, hK, hbarK, hCcomp, hCmap, hCinj, ?_⟩
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) C]
  have eCH : ↥C ≃* ↥H := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eCH]
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eH]
  exact CFSG.Quasithin.R3c.pRank_three_statedSL_three_even (n := 2) (by norm_num) hFcard

theorem s15_eq_one_of_sl3_four_component
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSL : IsSLn ↥(lBar V₀ V hV L) 3 2) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  by_contra hs
  have hs2 : 2 ≤ s15 D.M V₀ V hV L := by
    have h1 := Om8Excl.one_le_s15 D.M V₀ V hV L
    omega
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  have hcompH : CFSG.Open.IsComponentOf H A := hcomp
  have hSLH : IsSLn ↥H 3 2 := hSL
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
  have hcross : commSub (commSub (⊤ : Subgroup (Vtil V₀ V hV)) H)
      (H.map (MulAut.conj g).toMonoidHom) = ⊥ := (hW.2.1 g hgA hgnot).2
  have hHcomm : ⁅H, H.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
    (hW.2.1 g hgA hgnot).1
  have hInterH : H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : ↥H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyx : x * (y : MulAut (Vtil V₀ V hV)) = (y : MulAut (Vtil V₀ V hV)) * x :=
        Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hHcomm y.2) x hx.2
      exact Subtype.ext hyx.symm
    have hcardZ : Nat.card ↥(Subgroup.center H) = 3 := card_center_of_isSLn_three_two hSLH
    have hxodd : Odd (orderOf x) := by
      have hdvd : orderOf (⟨x, hx.1⟩ : ↥H) ∣ Nat.card ↥(Subgroup.center H) :=
        Subgroup.orderOf_dvd_natCard _ hxZ
      rw [hcardZ] at hdvd
      rw [Subgroup.orderOf_mk] at hdvd
      exact Odd.of_dvd_nat (by norm_num) hdvd
    have hfix : ∀ w ∈ commSub (⊤ : Subgroup (Vtil V₀ V hV)) H, x w = w := by
      intro w hw
      have hle : commSub (⊤ : Subgroup (Vtil V₀ V hV)) H ≤
          fixV (H.map (MulAut.conj g).toMonoidHom) :=
        commSub_eq_bot_iff.mp hcross
      exact mem_fixV.mp (hle hw) x hx.2
    have hx1 : x = 1 :=
      CFSG.CGT.PushingUpLit.CGT6.eq_one_of_trivial_on_commV
        (s15_Infra_vtil_sq_eq_one V₀ V hV) hx.1 hxodd (by
          intro w hw
          rw [CFSG.Quasithin.commV_eq_commSub] at hw
          exact hfix w hw)
    exact Subgroup.mem_bot.mpr hx1
  have hH'SL : IsSLn ↥(H.map (MulAut.conj g).toMonoidHom) 3 2 := by
    obtain ⟨F, hFfield, hFfinite, hFcard, ⟨e⟩⟩ := hSLH
    exact ⟨F, hFfield, hFfinite, hFcard,
      ⟨(H.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm.trans e⟩⟩
  have hcomp' : CFSG.Open.IsComponentOf (H.map (MulAut.conj g).toMonoidHom) A :=
    CFSG.Quasithin.F918V5G.isComponentOf_map_conj hcompH hgA
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  obtain ⟨K, hK, _hbarK, hCcomp, hCmap, hCinj, hCrank⟩ :=
    exists_faithful_barImage_of_sl3_four c.setting.hyp16.hyp125 c.std.h127 c.std.h119
      hcompH hSLH ψ hψ
  obtain ⟨K', _hK', _hbarK', hC'comp, hC'map, hC'inj, hC'rank⟩ :=
    exists_faithful_barImage_of_sl3_four c.setting.hyp16.hyp125 c.std.h127 c.std.h119
      hcomp' hH'SL ψ hψ
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  let C' : Subgroup (Bar2 D.M) := UC22.barImage D.M K'
  have hCcomp' : CFSG.IsComponent C := by simpa [C] using hCcomp
  have hC'comp' : CFSG.IsComponent C' := by simpa [C'] using hC'comp
  have hCmap' : C.map ψ = H := by simpa [C] using hCmap
  have hC'map' : C'.map ψ = H.map (MulAut.conj g).toMonoidHom := by
    simpa [C'] using hC'map
  have hCinj' : Function.Injective (ψ.comp C.subtype) := by simpa [C] using hCinj
  have hCrank' : CFSG.Open.pRank 3 C = 2 := by simpa [C] using hCrank
  have hC'rank' : CFSG.Open.pRank 3 C' = 2 := by simpa [C'] using hC'rank
  have hInterC : C ⊓ C' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxψ : ψ x ∈ H ⊓ H.map (MulAut.conj g).toMonoidHom := by
      constructor
      · rw [← hCmap']
        exact Subgroup.mem_map.mpr ⟨x, hx.1, rfl⟩
      · rw [← hC'map']
        exact Subgroup.mem_map.mpr ⟨x, hx.2, rfl⟩
    have hxψ1 : ψ x = 1 := by
      have hmem : ψ x ∈ (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) := by
        rw [← hInterH]
        exact hxψ
      exact Subgroup.mem_bot.mp hmem
    have hx1 : (⟨x, hx.1⟩ : ↥C) = 1 :=
      hCinj' (by simpa using hxψ1)
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hx1)
  have hCne : C ≠ C' := by
    intro heq
    apply hH'ne
    rw [← hC'map', ← heq, hCmap']
  have hcommute : ∀ x ∈ C, ∀ y ∈ C', x * y = y * x := by
    have hcommBot : ⁅C, C'⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hCcomp' hC'comp').resolve_left hCne
    intro x hx y hy
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot hx
    exact (Subgroup.mem_centralizer_iff.mp hcent y hy).symm
  have hrank4 : 4 ≤ CFSG.Open.pRank 3 (C ⊔ C') := by
    have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
      (q := 3) Nat.prime_three hcommute ?_
    · rw [hCrank', hC'rank'] at hadd
      omega
    · have hcard : Nat.card ↥(C ⊓ C') = 1 := by rw [hInterC, Subgroup.card_bot]
      rw [hcard]
      norm_num
  have hupper : CFSG.Open.pRank 3 (C ⊔ C') ≤ 3 := by
    have h1 : CFSG.Open.pRank 3 (C ⊔ C') ≤
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
