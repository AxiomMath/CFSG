module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal.TwoGroupNormalizerMaxLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal

variable {G : Type} [Group G] [Finite G]

theorem exists_maximal_pair {M L : Subgroup G} (hLM : L ≤ M) (hM : rankThreeIsMaxTwoLocal M)
    (hne : ¬ UniqueMax M L) :
    ∃ N R : Subgroup G, N ∈ calMOf L ∧ N ≠ M ∧ R ≤ M ⊓ N ∧ IsPGroup 2 R ∧
      L ≤ normalizer (R : Set G) ∧
      ∀ N' R' : Subgroup G, N' ∈ calMOf L → N' ≠ M → R' ≤ M ⊓ N' → IsPGroup 2 R' →
        L ≤ normalizer (R' : Set G) → Nat.card R' ≤ Nat.card R := by
  classical
  obtain ⟨N, hN, hNM⟩ : ∃ N ∈ calMOf L, N ≠ M := by
    by_contra h
    push Not at h
    exact hne (Set.eq_singleton_iff_unique_mem.2 ⟨⟨hM, hLM⟩, h⟩)
  let P : Set (Subgroup G × Subgroup G) :=
    {p | p.1 ∈ calMOf L ∧ p.1 ≠ M ∧ p.2 ≤ M ⊓ p.1 ∧ IsPGroup 2 p.2 ∧
      L ≤ normalizer (p.2 : Set G)}
  have hPne : P.Nonempty :=
    ⟨(N, ⊥), hN, hNM, bot_le, IsPGroup.of_bot, Subgroup.le_normalizer_of_normal⟩
  obtain ⟨p, hp, hmax⟩ :=
    Set.exists_max_image P (fun p => Nat.card p.2) (Set.toFinite P) hPne
  exact ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2,
    fun N' R' hN' hN'M hR' hR'2 hLR' => hmax (N', R') ⟨hN', hN'M, hR', hR'2, hLR'⟩⟩

theorem normalizer_le_of_lt {M L R R' : Subgroup G} (hR : IsPGroup 2 R) (hRne : R ≠ ⊥)
    (hLR : L ≤ normalizer (R : Set G)) (hR' : IsPGroup 2 R') (hRR' : R < R') (hR'M : R' ≤ M)
    (hLR' : L ≤ normalizer (R' : Set G))
    (hmax : ∀ N R'' : Subgroup G, N ∈ calMOf L → N ≠ M → R'' ≤ M ⊓ N → IsPGroup 2 R'' →
      L ≤ normalizer (R'' : Set G) → Nat.card R'' ≤ Nat.card R) :
    normalizer (R : Set G) ≤ M := by
  classical
  let R₁ : Subgroup G := R' ⊓ normalizer (R : Set G)
  have hRlt : R < R₁ := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hR' hRR'
  have hR₁2 : IsPGroup 2 R₁ := hR'.to_le inf_le_left
  have hR₁M : R₁ ≤ M := inf_le_left.trans hR'M
  have hLR₁ : L ≤ normalizer (R₁ : Set G) := by
    have h1 : L ≤ normalizer (normalizer (R : Set G) : Set G) :=
      hLR.trans Subgroup.le_normalizer
    have h2 : L ≤ normalizer (R' : Set G) ⊓ normalizer (normalizer (R : Set G) : Set G) :=
      le_inf hLR' h1
    exact h2.trans (Subgroup.inf_normalizer_le_normalizer_inf (H := R')
      (K := normalizer (R : Set G)))
  obtain ⟨N', hN'max, hN'ge⟩ := exists_rankThreeIsMaxTwoLocal_ge
    (N := normalizer (R : Set G)) ⟨R, hRne, hR, rfl⟩
  have hN'mem : N' ∈ calMOf L := ⟨hN'max, hLR.trans hN'ge⟩
  by_cases hN'M : N' = M
  · simpa [hN'M] using hN'ge
  · have hcard : Nat.card R₁ ≤ Nat.card R :=
      hmax N' R₁ hN'mem hN'M (le_inf hR₁M (inf_le_right.trans hN'ge)) hR₁2 hLR₁
    exact absurd (Subgroup.eq_of_le_of_card_ge hRlt.le hcard) hRlt.ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
