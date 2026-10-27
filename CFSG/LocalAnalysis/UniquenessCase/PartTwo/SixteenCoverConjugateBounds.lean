module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeCovers
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_s_le_three_of_pRank_one_cover {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {K : Subgroup G}
    (hK : K ∈ calC D.M)
    (hbar : barSub V₀ V hV K = lBar V₀ V hV L)
    (hRkK : CFSG.Open.pRank 3 K = 1) :
    s15 D.M V₀ V hV L ≤ 3 := by
  classical
  set A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hA
  set H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L with hH
  by_contra hle
  have hs4 : 4 ≤ s15 D.M V₀ V hV L := by omega
  let Sset : Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
    {X | ∃ φ ∈ A, X = H.map (MulAut.conj φ).toMonoidHom}
  have hcardSset : Sset.ncard = s15 D.M V₀ V hV L := rfl
  let F : Finset (Subgroup (MulAut (Vtil V₀ V hV))) := (Set.toFinite Sset).toFinset
  have hFcard : F.card = s15 D.M V₀ V hV L := by
    rw [← hcardSset]
    exact (Set.ncard_eq_toFinset_card Sset (Set.toFinite Sset)).symm
  obtain ⟨T, hTF, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := F) (n := 4) (by rw [hFcard]; omega)
  have hex : ∀ x : {X // X ∈ T}, ∃ (φ : MulAut (Vtil V₀ V hV))
      (g : ↥(stabTil V₀ V)), φ ∈ A ∧ (g : G) ∈ D.M ∧
      x.1 = H.map (MulAut.conj φ).toMonoidHom ∧ actTil V₀ V hV g = φ := by
    intro x
    have hxT : x.1 ∈ F := hTF x.2
    have hx : x.1 ∈ Sset := (Set.toFinite Sset).mem_toFinset.mp hxT
    rcases hx with ⟨φ, hφ, hXeq⟩
    obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
    exact ⟨φ, g, hφ, hgM, hXeq, hgφ⟩
  choose φ g hφ hgM hXeq hact using hex
  let Kof : {X // X ∈ T} → Subgroup G :=
    fun x => K.map (MulAut.conj (g x : G)).toMonoidHom
  have hKof_calC : ∀ x, Kof x ∈ calC D.M := by
    intro x
    refine CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M
      (MulAut.conj (g x : G)) ?_ hK
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hgM x))
  have hbarKof : ∀ x, barSub V₀ V hV (Kof x) = x.1 := by
    intro x
    change barSub V₀ V hV (K.map (MulAut.conj (g x : G)).toMonoidHom) = x.1
    rw [s16c7_barSub_map_conj V₀ V hV (g x).2 K, hbar, hact x]
    exact (hXeq x).symm
  have hRkKof : ∀ x, CFSG.Open.pRank 3 (Kof x) = 1 := by
    intro x
    change CFSG.Open.pRank 3 (K.map (MulAut.conj (g x : G)).toMonoidHom) = 1
    rw [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
      (MulAut.conj (g x : G)).toMonoidHom (MulAut.conj (g x : G)).injective K]
    exact hRkK
  let S : Finset (Subgroup G) := T.attach.image Kof
  have hKof_inj : Function.Injective Kof := by
    intro x y hxy
    apply Subtype.ext
    have h1 : barSub V₀ V hV (Kof x) = barSub V₀ V hV (Kof y) := congrArg _ hxy
    rwa [hbarKof x, hbarKof y] at h1
  have hScard : S.card = 4 := by
    rw [Finset.card_image_of_injective _ hKof_inj, Finset.card_attach, hTcard]
  let Xjoin : Subgroup G := S.sup id
  have hXjoin_le_M : Xjoin ≤ D.M := by
    refine Finset.sup_le fun L hL => ?_
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hL
    exact s13_le_of_mem_calC (hKof_calC x)
  have hScond : ∀ L ∈ S, L ∈ calC D.M ∧ L ≤ Xjoin ∧ Xjoin ≤ normalizer (L : Set G) ∧
      CFSG.Open.pRank 3 L = 1 := by
    intro L hL
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hL
    refine ⟨hKof_calC x, ?_, ?_, hRkKof x⟩
    · exact Finset.le_sup (f := id) hL
    · refine Finset.sup_le fun Y hY => ?_
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hY
      exact s16h_calC_le_normalizer (hKof_calC x) (hKof_calC y)
  have hcard_le : S.card ≤ CFSG.Open.pRank 3 Xjoin :=
    s16h_card_le_pRank_of_pRank_one (M := D.M) (X := Xjoin) (S := S) hScond
  have h4 : 4 ≤ CFSG.Open.pRank 3 Xjoin := by rw [hScard] at hcard_le; exact hcard_le
  have hMrank : CFSG.Open.pRank 3 D.M ≤ evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
  have h3 : CFSG.Open.pRank 3 Xjoin ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hXjoin_le_M
  have h_even : evenRank G = 3 := c.std.h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
