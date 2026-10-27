module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem c8k_mem_uniqueSet {M A : Subgroup G} (hM : IsStronglyPEmbedded 3 M)
    (hAM : A ≤ M) (hA : Nat.card A = 3) :
    A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  refine ⟨hAM, fun g hAg => ?_⟩
  by_cases hg : g ∈ M
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  · exfalso
    exact hM.2.2 g hg (hA ▸ Subgroup.card_dvd_of_le (le_inf hAM hAg))

theorem c8_hyp91 (D : Data G) (hse : IsStronglyPEmbedded 3 D.M) {K : Subgroup G} (hK : K ≠ ⊤)
    (hKM : ¬ K ≤ D.M) {d : G} (hdK : d ∈ K) (hdM : d ∈ D.M) (hd3 : orderOf d = 3)
    (hrk : pRank 3 K ≤ 1) : F09.Hyp91 D (K ⊓ D.M) K (Subgroup.zpowers d) := by
  have hbr : CFSG.pRank 3 ↥K = CFSG.Open.pRank 3 K :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥K).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
  have hrk' : CFSG.Open.pRank 3 K ≤ 1 := by rw [← hbr]; exact hrk
  have hdY : d ∈ K ⊓ D.M := Subgroup.mem_inf.2 ⟨hdK, hdM⟩
  have hd1 : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
  have hOppK : Opp 3 (K ⊓ D.M) ≤ K := by
    change Subgroup.closure {x : G | x ∈ K ⊓ D.M ∧ ∃ k : ℕ, orderOf x = 3 ^ k} ≤ K
    exact (Subgroup.closure_le K).2 fun x hx => (Subgroup.mem_inf.1 hx.1).1
  have hdO : d ∈ Opp 3 (K ⊓ D.M) := by
    change d ∈ Subgroup.closure {x : G | x ∈ K ⊓ D.M ∧ ∃ k : ℕ, orderOf x = 3 ^ k}
    exact Subgroup.subset_closure ⟨hdY, 1, by rw [pow_one]; exact hd3⟩
  have hcard : Nat.card ↥(Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hd3]
  obtain ⟨N, hN, hKN⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
  have hNM : N ≠ D.M := fun h => hKM (h ▸ hKN)
  have hNmem : N ∈ calNOf (K ⊓ D.M) := ⟨hN, inf_le_left.trans hKN⟩
  have hne : calNOf (K ⊓ D.M) ≠ {D.M} := by
    intro h
    exact hNM (Set.mem_singleton_iff.1 (h ▸ hNmem))
  refine ⟨⟨inf_le_right, hne, fun A hAY hA => c8k_mem_uniqueSet hse (hAY.trans inf_le_right) hA⟩,
    ⟨inf_le_left, hKM, ?_⟩, Subgroup.zpowers_le.2 hdO, hcard⟩
  let J : Subgroup G :=
    ⨆ h : ↥K, (Opp 3 (K ⊓ D.M)).map (MulAut.conj (h : G)).toMonoidHom
  change CFSG.Open.pRank 3 J = 1
  have hJK : J ≤ K := by
    refine iSup_le fun h => ?_
    rintro x ⟨y, hy, rfl⟩
    show (h : G) * y * (h : G)⁻¹ ∈ K
    exact K.mul_mem (K.mul_mem h.2 (hOppK hy)) (K.inv_mem h.2)
  have hdJ : d ∈ J :=
    Subgroup.mem_iSup_of_mem (1 : ↥K)
      (Subgroup.mem_map.2 ⟨d, hdO, by simp [MulAut.conj_apply]⟩)
  have hlow : 1 ≤ CFSG.Open.pRank 3 J :=
    CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.zpowers_le.2 hdJ)
      (CFSG.Open.isElemAbelian_zpowers hd1) (k := 1) (by rw [hcard, pow_one])
  have hhigh : CFSG.Open.pRank 3 J ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hJK).trans hrk'
  exact le_antisymm hhigh hlow

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
