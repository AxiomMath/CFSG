module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4RankQModel
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup

theorem exists_equiv_statedProj_of_isLie811_l4 {Y : Type} [Group Y] {r f : ℕ}
    (hY : IsLie811 Y .l4 r f) :
    r.Prime ∧ 1 ≤ f ∧
      ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = r ^ f ∧ r ^ f % 3 = 1 ∧
          Nonempty (Y ⧸ center Y ≃* StatedProj (StatedSL 4 K))) ∨
        (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (r ^ f) ^ 2 ∧ r ^ f % 3 = 2 ∧
          Nonempty (Y ⧸ center Y ≃* StatedProj (StatedSU 4 (r ^ f) K)))) := by
  obtain ⟨-, -, hr, -, ⟨hmod, hM⟩ | ⟨hmod, hM⟩⟩ := hY
  · obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM.statedClassicalModel_of_ne_zero (by norm_num)
    exact ⟨hr, hf, Or.inl ⟨K, _, inferInstance, hK, hmod, ⟨e⟩⟩⟩
  · obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM.statedClassicalModel_of_ne_zero (by norm_num)
    exact ⟨hr, hf, Or.inr ⟨K, _, inferInstance, hK, hmod, ⟨e⟩⟩⟩

theorem forall_two_le_pRank_centralizer_of_isLie811_l4
    {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hY : IsLie811 Y .l4 r f) (hr5 : 5 ≤ r)
    (hf : f ≠ 1) {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → 2 ≤ pRank r (centralizer (X : Set Y)) := by
  have hZ : center Y = ⊥ :=
    center_eq_bot_of_isLie811_of_ne hY (by decide) (fun h => absurd h (by decide))
  obtain ⟨hr, hf1, ⟨K, _, _, hK, hmod, ⟨e⟩⟩ | ⟨K, _, _, hK, hmod, ⟨e⟩⟩⟩ :=
    exists_equiv_statedProj_of_isLie811_l4 hY
  · have h := (K6L4.forall_le_pRank_centralizer_of_equiv_statedSL hr (by omega) hK hmod
      (center Y) hZ e hA h27).1
    intro X hXA hX3
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (by omega : 2 ≤ f).trans (h X hXA hX3)
  · have h := (K6L4.forall_le_pRank_centralizer_of_equiv_statedSU hr (by omega) hf1 hK hmod
      (center Y) hZ e hA h27).1
    intro X hXA hX3
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (by omega : 2 ≤ f).trans (h X hXA hX3)

theorem one_le_pRank_centralizer_plane_of_isLie811_l4
    {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hY : IsLie811 Y .l4 r f) (hr5 : 5 ≤ r)
    (hf : f ≠ 1) {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∀ c, IsSumZeroCoords A c →
      1 ≤ pRank r (centralizer ({c (.ofAdd ![1, 1, -1, -1]), c (.ofAdd ![1, -1, 0, 0])} :
        Set Y)) := by
  have hZ : center Y = ⊥ :=
    center_eq_bot_of_isLie811_of_ne hY (by decide) (fun h => absurd h (by decide))
  obtain ⟨hr, hf1, ⟨K, _, _, hK, hmod, ⟨e⟩⟩ | ⟨K, _, _, hK, hmod, ⟨e⟩⟩⟩ :=
    exists_equiv_statedProj_of_isLie811_l4 hY
  · have h := (K6L4.forall_le_pRank_centralizer_of_equiv_statedSL hr (by omega) hK hmod
      (center Y) hZ e hA h27).2
    intro c hc
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (by omega : 1 ≤ f).trans (h c hc)
  · have h := (K6L4.forall_le_pRank_centralizer_of_equiv_statedSU hr (by omega) hf1 hK hmod
      (center Y) hZ e hA h27).2
    intro c hc
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (by omega : 1 ≤ f).trans (h c hc)

theorem two_le_pRank_centralizer_of_isLie811_l4
    {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hY : IsLie811 Y .l4 r f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {A : Subgroup Y} (hA : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) (hpq : p ∣ qMinusPi r f) :
    2 ≤ pRank p (centralizer (A : Set Y)) := by
  have hZ : center Y = ⊥ :=
    center_eq_bot_of_isLie811_of_ne hY (by decide) (fun h => absurd h (by decide))
  obtain ⟨hr, hf1, ⟨K, _, _, hK, hmod, ⟨e⟩⟩ | ⟨K, _, _, hK, hmod, ⟨e⟩⟩⟩ :=
    exists_equiv_statedProj_of_isLie811_l4 hY
  · have hpq' : p ∣ r ^ f - 1 := by simpa [qMinusPi, hmod] using hpq
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact K6L4.two_le_pRank_centralizer_of_equiv_statedSL (q := r ^ f) hK hmod hp (by omega)
      hpq' (center Y) hZ e hA h27
  · have hpq' : p ∣ r ^ f + 1 := by
      rw [qMinusPi, if_neg (by omega)] at hpq
      exact hpq
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact K6L4.two_le_pRank_centralizer_of_equiv_statedSU (q := r ^ f) hK hmod hp (by omega)
      hpq' (center Y) hZ e hA h27

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
