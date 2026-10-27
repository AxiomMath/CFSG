module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Common
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKGammaLemmas
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.LieModelL3U3Torus
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.GroupTheory.ComponentCovering
public import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsU3)

private theorem genFittingFStar_eq_top_of_isQuasisimple {K : Type} [Group K]
    (hq : CFSG.Open.IsQuasisimple K) : genFittingFStar K = ⊤ := by
  have hqtop : CFSG.Open.IsQuasisimple (↥(⊤ : Subgroup K)) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv (G := K)) hq
  have hcomp : CFSG.Open.IsComponentOf (⊤ : Subgroup K) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.refl ⊤, hqtop⟩
  have hlayer : genFittingLayer K = ⊤ := eq_top_iff.mpr (le_sSup hcomp)
  rw [genFittingFStar.eq_sup, hlayer, sup_top_eq]

private theorem center_eq_bot_of_isSimpleGroup_of_isQuasisimple {X : Type} [Group X]
    (hsimple : IsSimpleGroup X) (hq : CFSG.Open.IsQuasisimple X) : Subgroup.center X = ⊥ := by
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hsub : Subsingleton (X ⧸ Subgroup.center X) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact @not_subsingleton (X ⧸ Subgroup.center X) hq.2.toNontrivial hsub

private theorem exists_ne_one_of_one_le_pRank {G : Type} [Group G] [Finite G]
    {Q : Subgroup G} (hQ : 1 ≤ CFSG.Open.pRank 3 Q) : ∃ y ∈ Q, y ≠ 1 := by
  obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) Q
  have hEc : 1 < Nat.card E := by
    rw [hcard]
    calc 1 < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 Q := Nat.pow_le_pow_right (by norm_num) hQ
  have hEne : E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot E).mp hEc
  obtain ⟨y, hyE, hy1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left hEne
  exact ⟨y, hEQ hyE, hy1⟩

private theorem map_conj_eq_of_isComponentOf_of_normalizer {G : Type} [Group G] [Finite G]
    {N X Q : Subgroup G} (hXN : CFSG.Open.IsComponentOf X N) (hXq : CFSG.Open.IsQuasisimple X)
    (hXsimple : IsSimpleGroup X) (hQX : Q ≤ X) (hQrank : 1 ≤ CFSG.Open.pRank 3 Q) {n : G}
    (hnN : n ∈ N) (hnQ : n ∈ Subgroup.normalizer (Q : Set G)) :
    X.map (MulAut.conj n).toMonoidHom = X := by
  by_contra hne
  have hXn : CFSG.Open.IsComponentOf (X.map (MulAut.conj n).toMonoidHom) N :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hXN hnN
  have hcomm : ⁅X.map (MulAut.conj n).toMonoidHom, X⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hXn hXN hne
  obtain ⟨y, hyQ, hy1⟩ := exists_ne_one_of_one_le_pRank hQrank
  have hyX : y ∈ X := hQX hyQ
  have hnQmap : Q.map (MulAut.conj n).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnQ
  have hynQ : MulAut.conj n y ∈ Q := by
    rw [← hnQmap]
    exact ⟨y, hyQ, rfl⟩
  have hynX : MulAut.conj n y ∈ X := hQX hynQ
  have hynXn : MulAut.conj n y ∈ X.map (MulAut.conj n).toMonoidHom :=
    ⟨y, hyX, rfl⟩
  have hcentral' : X.map (MulAut.conj n).toMonoidHom ≤
      Subgroup.centralizer (X : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcentral : MulAut.conj n y ∈ Subgroup.centralizer (X : Set G) :=
    hcentral' hynXn
  have hcenter : (⟨MulAut.conj n y, hynX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcentral a.1 a.2
  have hcenterBot : Subgroup.center ↥X = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_isQuasisimple hXsimple hXq
  have hmapBot : (Subgroup.center ↥X).map X.subtype = ⊥ := by
    rw [hcenterBot, Subgroup.map_bot]
  have hmemBot : MulAut.conj n y ∈ (⊥ : Subgroup G) := by
    rw [← hmapBot]
    exact ⟨⟨MulAut.conj n y, hynX⟩, hcenter, rfl⟩
  have hyn1 : MulAut.conj n y = 1 := by simpa using hmemBot
  exact hy1 (by
    have h1 : (MulAut.conj n) y = (MulAut.conj n) 1 := by simpa using hyn1
    exact (MulAut.conj n).injective h1)

theorem r879_of_inputs {G : Type} [Group G] [Finite G] (D : Data G)
    (hK329 : K329) (hSg : UC6S846.SigmaStd D) (h870 : R870 D) (h874 : R874 D) (h875 : R875 D)
    (h875c : R875Comp D) : R879 D := by
  intro L X H hmin hXU3
  obtain ⟨K, hKcomp, hXK, hnotKM⟩ := h875 L X H hmin
  have hXcomp : CFSG.Open.IsComponentOf X (H ⊓ D.M) := h875c L X H hmin
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 3) (H ⊓ D.M)
  have hPX : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ X) X :=
    hQ.inf_of_isSubnormal hXcomp.2.1
  have h874' := h874 L X H hmin Q hQ hPX
  have hQH : CFSG.ABGLocalTools.IsSylowOf 3 Q H := h874'.1
  have hΓM : rankThreeGamma 1 3 (Q ⊓ X) ≤ D.M := h874'.2
  have hQle : Q ≤ H ⊓ D.M := hQ.le
  have hQM : Q ≤ D.M := hQle.trans inf_le_right
  have hPXle : Q ⊓ X ≤ X := inf_le_right
  have hPK : Q ⊓ X ≤ K := hPXle.trans hXK
  have hXrankTop : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) :=
    CFSG.Blueprint.LieModel.two_le_pRank_psu3_of_dvd hXU3 Nat.prime_three (by norm_num)
  have hXrank : 1 < CFSG.Open.pRank 3 X := by
    have hle : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ CFSG.Open.pRank 3 X := by
      have := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) X.subtype
        X.subtype_injective ⊤
      rwa [Subgroup.map_top, Subgroup.range_subtype] at this
    omega
  have hQHrank : CFSG.Open.pRank 3 Q = CFSG.Open.pRank 3 H :=
    CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow Nat.prime_three hQH
  have hQMrank : CFSG.Open.pRank 3 Q ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_le_of_le Nat.prime_three hQM
  have hMrank : CFSG.Open.pRank 3 D.M ≤ 3 :=
    pRank_le_three_of_minCex hSg h870 hmin Nat.prime_three (by norm_num) hXrank
  have hHrank : CFSG.Open.pRank 3 H ≤ 3 := by
    calc CFSG.Open.pRank 3 H = CFSG.Open.pRank 3 Q := hQHrank.symm
      _ ≤ CFSG.Open.pRank 3 D.M := hQMrank
      _ ≤ 3 := hMrank
  have hKrank : CFSG.Open.pRank 3 K ≤ 3 :=
    (CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_le_of_le
      Nat.prime_three hKcomp.1).trans hHrank
  have hKtoprank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 := by
    have hle : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ CFSG.Open.pRank 3 K := by
      have := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) K.subtype
        K.subtype_injective ⊤
      rwa [Subgroup.map_top, Subgroup.range_subtype] at this
    exact hle.trans hKrank
  have hKtop : K ≠ ⊤ := by
    intro hKtop
    have hHtop : H = ⊤ := le_antisymm le_top (by simpa [hKtop] using hKcomp.1)
    exact hmin.mem.1.1 hHtop
  have hKgroup : CFSG.Open.IsKGroup ↥K := D.standing.kProper.isKGroup K hKtop
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hFtop : genFittingFStar ↥K = ⊤ :=
    genFittingFStar_eq_top_of_isQuasisimple hKq
  have hFq : CFSG.Open.IsQuasisimple ↥(genFittingFStar ↥K) := by
    rw [hFtop]
    exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv (G := ↥K)) hKq
  have hFKgroup : CFSG.Open.IsKGroup
      (↥(genFittingFStar ↥K) ⧸ Subgroup.center ↥(genFittingFStar ↥K)) := by
    rw [hFtop]
    have hKquot : CFSG.Open.IsKGroup (↥K ⧸ Subgroup.center ↥K) :=
      hKgroup.quotient (Subgroup.center ↥K)
    let e : (↥(⊤ : Subgroup ↥K) ⧸
          Subgroup.center ↥(⊤ : Subgroup ↥K)) ≃*
        (↥K ⧸ Subgroup.center ↥K) :=
      QuotientGroup.congr (Subgroup.center ↥(⊤ : Subgroup ↥K))
        (Subgroup.center ↥K) (Subgroup.topEquiv (G := ↥K))
        (Subgroup.map_center_eq (Subgroup.topEquiv (G := ↥K)))
    exact hKquot.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hX'Lie : CFSG.Blueprint.LieModel ↥(X.subgroupOf K) .PSU 3 2 3 :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hXK).symm hXU3
  have hXsimple : IsSimpleGroup ↥X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
      (by simp [CFSG.Blueprint.classicalTags]) hXU3
  have hP' : CFSG.ABGLocalTools.IsSylowOf 3 ((Q ⊓ X).subgroupOf K)
      (X.subgroupOf K) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff K]
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPK,
      inf_eq_left.mpr hXK] using hPX
  have hΓK : rankThreeGamma 1 3 ((Q ⊓ X).subgroupOf K) ≤
      Subgroup.normalizer (X.subgroupOf K : Set ↥K) := by
    rw [rankThreeGamma]
    refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
    intro QK hQKP hQKrank nK hnQK
    have hnK : nK.1 ∈ K := nK.2
    have hnH : nK.1 ∈ H := hKcomp.1 hnK
    let Qa : Subgroup G := QK.map K.subtype
    have hQaP : Qa ≤ Q ⊓ X := by
      have h := Subgroup.map_mono (f := K.subtype) hQKP
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPK] at h
    have hQaX : Qa ≤ X := hQaP.trans inf_le_right
    have hQarank : 1 ≤ CFSG.Open.pRank 3 Qa :=
      hQKrank.trans (CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) K.subtype
        K.subtype_injective QK)
    have hnQa : nK.1 ∈ Subgroup.normalizer (Qa : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hmap : QK.map (MulAut.conj nK).toMonoidHom = QK :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hnQK
      have h2 := congrArg (Subgroup.map K.subtype) hmap
      have hcomp : K.subtype.comp (MulAut.conj nK).toMonoidHom =
          (MulAut.conj nK.1).toMonoidHom.comp K.subtype := by
        ext x
        simp [MulAut.conj_apply]
      rw [Subgroup.map_map, hcomp] at h2
      simpa [Qa, Subgroup.map_map] using h2
    have hQaGamma : Subgroup.normalizer (Qa : Set G) ≤ rankThreeGamma 1 3 (Q ⊓ X) :=
      CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hQaP hQarank
    have hnM : nK.1 ∈ D.M := hQaGamma.trans hΓM hnQa
    have hnN : nK.1 ∈ H ⊓ D.M := ⟨hnH, hnM⟩
    have hmapX : X.map (MulAut.conj nK.1).toMonoidHom = X :=
      map_conj_eq_of_isComponentOf_of_normalizer hXcomp hXcomp.2.2 hXsimple
        hQaX hQarank hnN hnQa
    have hnNormX : nK.1 ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapX
    rw [← Subgroup.subgroupOf_normalizer_eq hXK]
    exact hnNormX
  have hK329' := hK329 ↥K hFq hFKgroup hKtoprank (X.subgroupOf K)
    ((Q ⊓ X).subgroupOf K) (by rw [hFtop]; exact le_top) hX'Lie hP' hΓK
  have hKleX : K ≤ X := Subgroup.subgroupOf_eq_top.mp (by simpa [hFtop] using hK329')
  have hXeqK : X = K := le_antisymm hXK hKleX
  exact hnotKM ((hXeqK ▸ hXcomp.1).trans inf_le_right)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
