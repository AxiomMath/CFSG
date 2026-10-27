module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarImageCalC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeL5Cover
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.Vol2.Ch11SecOE2D
public import CFSG.Quasithin.H13.A5Rows
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_two_le_pRank_three_of_isLn_five_one {X : Type} [Group X] [Finite X]
    (h : IsLn X 5 1) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨eSL⟩ := CFSG.Quasithin.Vol2.Ch11.OE2.nonempty_sl_of_lieModel (d := 5) h
  let e : X ≃* GL (Fin 5) (ZMod 2) :=
    eSL.trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 5)
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (GL (Fin 5) (ZMod 2))) :=
    CFSG.Quasithin.H13.A5.two_le_pRank_gl5
  rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e] at hrank

theorem four_le_pRank_three_of_two_distinct_l5_covers
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V)
    {Lbar Lbar' : Subgroup (MulAut (Vtil V₀ V hV))}
    {K K' : Subgroup G}
    (hK : K ∈ calC D.M) (hK' : K' ∈ calC D.M)
    (hKbar : barSub V₀ V hV K = Lbar)
    (hK'bar : barSub V₀ V hV K' = Lbar')
    (hL : IsLn (Bar2 K) 5 1) (hL' : IsLn (Bar2 K') 5 1)
    (hne : Lbar ≠ Lbar') :
    4 ≤ CFSG.Open.pRank 3 D.M := by
  classical
  have hVeq : hV = h125.isElemAbelian := Subsingleton.elim _ _
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  let C' : Subgroup (Bar2 D.M) := UC22.barImage D.M K'
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hK
  have hC'comp : CFSG.IsComponent C' := UC22.uc22p22l_barImage_isComponent hK'
  have hCne : C ≠ C' := by
    intro heq
    have hpre : UC22.barPreimage D.M (UC22.barImage D.M K) =
        UC22.barPreimage D.M (UC22.barImage D.M K') := congrArg _ heq
    rw [UC22.barPreimage_barImage_eq_sup_pCore hK.1.le,
      UC22.barPreimage_barImage_eq_sup_pCore hK'.1.le] at hpre
    have hpre' : K ⊔ pCoreOf 2 D.M = K' ⊔ pCoreOf 2 D.M := by
      simpa only [pCoreOf] using hpre
    have hsupK : barSub V₀ V hV (K ⊔ pCoreOf 2 D.M) = barSub V₀ V hV K := by
      simpa only [hVeq] using barSub_sup_pCoreOf_eq_of_hyp125 h125 hK.1.le
    have hsupK' : barSub V₀ V hV (K' ⊔ pCoreOf 2 D.M) = barSub V₀ V hV K' := by
      simpa only [hVeq] using barSub_sup_pCoreOf_eq_of_hyp125 h125 hK'.1.le
    apply hne
    calc Lbar = barSub V₀ V hV K := hKbar.symm
      _ = barSub V₀ V hV (K ⊔ pCoreOf 2 D.M) := hsupK.symm
      _ = barSub V₀ V hV (K' ⊔ pCoreOf 2 D.M) := by rw [hpre']
      _ = barSub V₀ V hV K' := hsupK'
      _ = Lbar' := hK'bar
  have hZbar : Subgroup.center (Bar2 K) = ⊥ := by
    have hsimple : IsSimpleGroup (Bar2 K) := s16c167_cfg2_simple_ln hL
    have hnt : Nontrivial (Bar2 K) := hsimple.toNontrivial
    have hperfect : Group.IsPerfect (Bar2 K) := ⟨hK.2.2.1⟩
    exact @TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative (Bar2 K) _
      hsimple (@Group.IsPerfect.not_isMulCommutative (Bar2 K) _ hnt hperfect)
  have hZC : Subgroup.center C = ⊥ := by
    simpa only [C] using center_barImage_eq_bot_of_isSubnormal hK.1 hZbar
  have hcomm : C ≤ Subgroup.centralizer (C' : Set (Bar2 D.M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hCcomp hC'comp).resolve_left hCne)
  have hinf : C ⊓ C' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxcent : (⟨x, hx.1⟩ : ↥C) ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hy : (y : Bar2 D.M) ∈ C := y.2
      exact (Subgroup.mem_centralizer_iff.mp (hcomm hy) (x : Bar2 D.M) hx.2).symm
    have hx1 : (⟨x, hx.1⟩ : ↥C) = 1 := by
      have := hxcent
      rw [hZC] at this
      simpa using this
    exact Subtype.ext_iff.mp hx1
  have hCrank : 2 ≤ CFSG.Open.pRank 3 C := by
    obtain ⟨eC, -⟩ := UC22.uc22p22l_barImage_equiv hK
    have hLnC : IsLn ↥C 5 1 := by
      change CFSG.Blueprint.LieModel ↥C .PSL 5 2 1
      exact CFSG.Blueprint.LieModel.of_mulEquiv eC hL
    have h := s168e3_two_le_pRank_three_of_isLn_five_one hLnC
    exact h.trans (CFSG.SectionRank.pRank_eq_pRank_top_subgroup C).ge
  have hC'rank : 2 ≤ CFSG.Open.pRank 3 C' := by
    obtain ⟨eC', -⟩ := UC22.uc22p22l_barImage_equiv hK'
    have hLnC' : IsLn ↥C' 5 1 := by
      change CFSG.Blueprint.LieModel ↥C' .PSL 5 2 1
      exact CFSG.Blueprint.LieModel.of_mulEquiv eC' hL'
    have h := s168e3_two_le_pRank_three_of_isLn_five_one hLnC'
    exact h.trans (CFSG.SectionRank.pRank_eq_pRank_top_subgroup C').ge
  have hcommute : ∀ x ∈ C, ∀ y ∈ C', x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcomm hx) y hy).symm
  have hcop : Nat.Coprime 3 (Nat.card (C ⊓ C' : Subgroup (Bar2 D.M))) := by
    rw [hinf]
    simp
  have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
    (q := 3) Nat.prime_three hcommute hcop
  have h4sup : 4 ≤ CFSG.Open.pRank 3 (C ⊔ C') := by omega
  have htop : CFSG.Open.pRank 3 (C ⊔ C') ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  rw [CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient D.M]
  exact h4sup.trans htop


theorem false_of_two_le_s15_of_l5_component_at_three
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf
      (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsLn (lBar V₀ V hV L) 5 1)
    (hs : 2 ≤ s15 D.M V₀ V hV L) :
    False := by
  classical
  let S : Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
    {X | ∃ φ ∈ Mbar D.M V₀ V hV,
      X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom}
  have hs1 : 1 < S.ncard := by
    simpa only [S, s15] using (show 1 < s15 D.M V₀ V hV L by omega)
  obtain ⟨X, hXmem, hXne⟩ := Set.exists_ne_of_one_lt_ncard hs1 (lBar V₀ V hV L)
  obtain ⟨φ, hφM, hXeq⟩ := hXmem
  have hcompA : CFSG.Assembly.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hcomp
  have hMbarConj : (Mbar D.M V₀ V hV).map (MulAut.conj φ).toMonoidHom =
      Mbar D.M V₀ V hV :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hφM)
  have hcompX : CFSG.Open.IsComponentOf X (Mbar D.M V₀ V hV) := by
    rw [hXeq]
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcompA φ
    rw [hMbarConj] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mp h
  have hLX : IsLn X 5 1 := by
    rw [hXeq]
    change CFSG.Blueprint.LieModel
      ↥((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom) .PSL 5 2 1
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective (lBar V₀ V hV L)
        (MulAut.conj φ).toMonoidHom (MulAut.conj φ).injective) hL
  obtain ⟨K, hKmem, hKbar, hLK⟩ :=
    exists_calC_cover_of_l5_component (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp hL
  obtain ⟨K', hK'mem, hK'bar, hLK'⟩ :=
    exists_calC_cover_of_l5_component (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcompX hLX
  have h4 := four_le_pRank_three_of_two_distinct_l5_covers
    (D := D) (V₀ := V₀) (V := V) (hV := hV) c.setting.hyp16.hyp125
    hKmem hK'mem hKbar hK'bar hLK hLK' hXne.symm
  have hbound : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
  have h3 : CFSG.Open.evenRank G = 3 := c.std.h3
  omega

theorem s15_eq_one_of_l5_component_at_three
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf
      (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsLn (lBar V₀ V hV L) 5 1) :
    s15 D.M V₀ V hV L = 1 := by
  by_contra h
  have h1 := Om8Excl.one_le_s15 D.M V₀ V hV L
  exact false_of_two_le_s15_of_l5_component_at_three c hcomp hL (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
