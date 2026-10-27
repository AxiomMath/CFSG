module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairOmGrp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairOmCorr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairOmMainA
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem s16c13bcA_pairFixed_statedOmegaMinus {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) (b c : K) :
    s16c13bcA_PairFixed (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus n K b c))
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) := by
  intro v
  have hn3 : 3 ≤ n - 1 := by omega
  by_cases hex : ∃ r : Fin (n - 1) ⊕ Fin (n - 1), v (minusEmb n r) ≠ 0
  · obtain ⟨r, hr⟩ := hex
    obtain ⟨i, j, hi, hj, hij⟩ := exists_three_distinct (n := n - 1) hn3 (minusIdx r)
    have hwQ : CFSG.Open.StatedQuadMinus n K b c
        (Pi.single (minusEmb n (Sum.swap r)) 1 : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) = 0 :=
      Q_minusSingle b c (Sum.swap r)
    have hw1 : (Pi.single (minusEmb n (Sum.swap r)) 1 :
          Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ⬝ᵥ (minusM n K b *ᵥ minusA n K i) = 0 := by
      simp only [single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact minusA_apply_eq_zero hi.symm
    have hw1' : (Pi.single (minusEmb n (Sum.swap r)) 1 :
          Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ⬝ᵥ (minusM n K b *ᵥ minusB n K i j) = 0 := by
      simp only [single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact s16c13bcA_minusB_apply_eq_zero hi.symm hj.symm
    have hw2 : (Pi.single (minusEmb n (Sum.swap r)) 1 :
          Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ⬝ᵥ (minusM n K b *ᵥ minusA n K j) = 0 := by
      simp only [single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact minusA_apply_eq_zero hj.symm
    have hw2' : (Pi.single (minusEmb n (Sum.swap r)) 1 :
          Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ⬝ᵥ
        (minusM n K b *ᵥ s16c13bcA_minusD n K i j) = 0 := by
      simp only [single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact s16c13bcA_minusD_apply_eq_zero hi.symm hj.symm
    have hvw : v ⬝ᵥ (minusM n K b *ᵥ
        (Pi.single (minusEmb n (Sum.swap r)) 1 :
          Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) ≠ 0 := by
      rw [(isQuadWith_minus (n := n) b c).symm]
      simp only [single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact hr
    obtain ⟨b₁, b₁', b₂, b₂', h1, h1', h11, h2, h2', h22, h12, h12', h1'2, h1'2',
      hv1, hv1', hv2, hv2'⟩ :=
      s16c13bcA_pairs_of_singular (isQuadWith_minus b c)
        (Q_minusA b c i) (Q_minusB b c hij) (B_minusB b hij)
        (Q_minusA b c j) (s16c13bcA_Q_minusD b c hij) (s16c13bcA_B_minusD b hij)
        (s16c13bcA_dot_minusA_minusA b hij) (s16c13bcA_dot_minusA_minusD b hij)
        (s16c13bcA_dot_minusB_minusA b hij) (s16c13bcA_dot_minusB_minusD b hij)
        hwQ hw1 hw1' hw2 hw2' hvw
    exact s16c13bcA_pair_omega (isQuadWith_minus b c) h1 h1' h11 h2 h2' h22 h12 h12'
      h1'2 h1'2' hv1 hv1' hv2 hv2'
  · simp only [not_exists, not_not] at hex
    have hl : ∀ i : Fin (n - 1), v (.inl i) = 0 :=
      fun i => by simpa [minusEmb] using hex (Sum.inl i)
    have hr : ∀ i : Fin (n - 1), v (.inr (.inl i)) = 0 :=
      fun i => by simpa [minusEmb] using hex (Sum.inr i)
    have h0 : 0 < n - 1 := by omega
    have h1 : 1 < n - 1 := by omega
    have hij : (⟨0, h0⟩ : Fin (n - 1)) ≠ ⟨1, h1⟩ := by simp [Fin.ext_iff]
    refine s16c13bcA_pair_omega (isQuadWith_minus b c)
      (Q_minusA b c ⟨0, h0⟩) (Q_minusB b c hij) (B_minusB b hij)
      (Q_minusA b c ⟨1, h1⟩) (s16c13bcA_Q_minusD b c hij) (s16c13bcA_B_minusD b hij)
      (s16c13bcA_dot_minusA_minusA b hij) (s16c13bcA_dot_minusA_minusD b hij)
      (s16c13bcA_dot_minusB_minusA b hij) (s16c13bcA_dot_minusB_minusD b hij)
      ?_ ?_ ?_ ?_
    · rw [dot_minusM]; simp [minusA, hl, hr]
    · rw [dot_minusM]; simp [minusB, hl, hr]
    · rw [dot_minusM]; simp [minusA, hl, hr]
    · rw [dot_minusM]; simp [s16c13bcA_minusD, hl, hr]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
