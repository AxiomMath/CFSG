module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoOmMPairA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairOmMainA
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open Matrix CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

private def s16k_e (K : Type) [Field K] {m : ℕ} (i : Fin (m - 1)) :
    Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl i) 1

private def s16k_f (K : Type) [Field K] {m : ℕ} (i : Fin (m - 1)) :
    Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inr (Sum.inl i)) 1

private def s16k_uu (K : Type) [Field K] (m : ℕ) :
    Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inr (Sum.inr 0)) 1

private theorem s16k_e_ne_zero {K : Type} [Field K] {m : ℕ} (i : Fin (m - 1)) :
    s16k_e K i ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl i)
  simp [s16k_e, Pi.single_apply] at this

private theorem s16k_uu_ne_zero {K : Type} [Field K] (m : ℕ) : s16k_uu K m ≠ 0 := by
  intro h
  have := congrFun h (Sum.inr (Sum.inr 0))
  simp [s16k_uu, Pi.single_apply] at this

private theorem s16k_Q_e {K : Type} [Field K] {m : ℕ} (b c : K) (i : Fin (m - 1)) :
    StatedQuadMinus m K b c (s16k_e K i) = 0 := by
  simpa [s16k_e, minusEmb] using Q_minusSingle (n := m) b c (Sum.inl i)

private theorem s16k_Q_uu {K : Type} [Field K] [CharP K 2] {m : ℕ} (b c : K) :
    StatedQuadMinus m K b c (s16k_uu K m) = 1 := by
  simp [CFSG.Open.StatedQuadMinus, s16k_uu, Pi.single_apply]

private theorem s16k_eq_zero_or_one {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2)
    (s : K) : s = 0 ∨ s = 1 := by
  classical
  have hcard : ({0, 1} : Finset K).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  have huniv : ({0, 1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, hK])
  have : s ∈ ({0, 1} : Finset K) := by rw [huniv]; exact Finset.mem_univ s
  simpa using this

private theorem s16k_dot_minusA_eq {K : Type} [Field K] {m : ℕ} (b : K)
    (x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) (i : Fin (m - 1)) :
    x ⬝ᵥ (minusM m K b *ᵥ minusA m K i) = x (Sum.inl i) + x (Sum.inr (Sum.inl i)) := by
  rw [dot_minusM]
  have hsum : (∑ k : Fin (m - 1),
      (x (Sum.inl k) * (minusA m K i) (Sum.inr (Sum.inl k)) +
        x (Sum.inr (Sum.inl k)) * (minusA m K i) (Sum.inl k))) =
      x (Sum.inl i) + x (Sum.inr (Sum.inl i)) := by
    rw [← Finset.sum_subset (s₁ := ({i} : Finset (Fin (m - 1)))) (s₂ := Finset.univ)]
    · rw [Finset.sum_singleton]
      simp [minusA, Pi.single_apply]
    · intro k _
      simp
    · intro k _ hk
      have hki : k ≠ i := by
        intro h; exact hk (by simpa [h])
      simp [minusA, Pi.single_apply, hki]
  rw [hsum]
  simp [minusA, Pi.single_apply]

private theorem s16k_dot_minusB_eq {K : Type} [Field K] {m : ℕ} (b : K)
    (x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) {i j : Fin (m - 1)} (hij : i ≠ j) :
    x ⬝ᵥ (minusM m K b *ᵥ minusB m K i j) =
      x (Sum.inr (Sum.inl i)) + x (Sum.inl j) + x (Sum.inr (Sum.inl j)) := by
  rw [dot_minusM]
  have hsum : (∑ k : Fin (m - 1),
      (x (Sum.inl k) * (minusB m K i j) (Sum.inr (Sum.inl k)) +
        x (Sum.inr (Sum.inl k)) * (minusB m K i j) (Sum.inl k))) =
      x (Sum.inr (Sum.inl i)) + x (Sum.inl j) + x (Sum.inr (Sum.inl j)) := by
    rw [← Finset.sum_subset (s₁ := ({i, j} : Finset (Fin (m - 1)))) (s₂ := Finset.univ)]
    · rw [Finset.sum_pair hij]
      simp [minusB, Pi.single_apply, hij, hij.symm]; ring
    · intro k _
      simp
    · intro k _ hk
      have hki : k ≠ i := by
        intro h; exact hk (by simp [h])
      have hkj : k ≠ j := by
        intro h; exact hk (by simp [h])
      simp [minusB, Pi.single_apply, hki, hkj]
  rw [hsum]
  simp [minusB, Pi.single_apply, hij, hij.symm]

private theorem s16k_dot_minusD_eq {K : Type} [Field K] {m : ℕ} (b : K)
    (x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) {i j : Fin (m - 1)} (hij : i ≠ j) :
    x ⬝ᵥ (minusM m K b *ᵥ s16c13bcA_minusD m K i j) =
      x (Sum.inl i) + x (Sum.inr (Sum.inl i)) + x (Sum.inr (Sum.inl j)) := by
  rw [dot_minusM]
  have hsum : (∑ k : Fin (m - 1),
      (x (Sum.inl k) * (s16c13bcA_minusD m K i j) (Sum.inr (Sum.inl k)) +
        x (Sum.inr (Sum.inl k)) * (s16c13bcA_minusD m K i j) (Sum.inl k))) =
      x (Sum.inl i) + x (Sum.inr (Sum.inl i)) + x (Sum.inr (Sum.inl j)) := by
    rw [← Finset.sum_subset (s₁ := ({i, j} : Finset (Fin (m - 1)))) (s₂ := Finset.univ)]
    · rw [Finset.sum_pair hij]
      simp [s16c13bcA_minusD, Pi.single_apply, hij, hij.symm]
    · intro k _
      simp
    · intro k _ hk
      have hki : k ≠ i := by
        intro h; exact hk (by simp [h])
      have hkj : k ≠ j := by
        intro h; exact hk (by simp [h])
      simp [s16c13bcA_minusD, Pi.single_apply, hki, hkj]
  rw [hsum]
  simp [s16c13bcA_minusD, Pi.single_apply, hij, hij.symm]

private theorem s16k_dot_minusA_zero {K : Type} [Field K] {m : ℕ} (b : K)
    {x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K} {i : Fin (m - 1)}
    (hxe : x (Sum.inl i) = 0) (hxf : x (Sum.inr (Sum.inl i)) = 0) :
    x ⬝ᵥ (minusM m K b *ᵥ minusA m K i) = 0 := by
  rw [s16k_dot_minusA_eq, hxe, hxf, add_zero]

private theorem s16k_dot_minusB_zero {K : Type} [Field K] {m : ℕ} (b : K)
    {x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K} {i j : Fin (m - 1)} (hij : i ≠ j)
    (hxf : x (Sum.inr (Sum.inl i)) = 0) (hxje : x (Sum.inl j) = 0)
    (hxjf : x (Sum.inr (Sum.inl j)) = 0) :
    x ⬝ᵥ (minusM m K b *ᵥ minusB m K i j) = 0 := by
  rw [s16k_dot_minusB_eq b x hij, hxf, hxje, hxjf, add_zero, add_zero]

private theorem s16k_dot_minusD_zero {K : Type} [Field K] {m : ℕ} (b : K)
    {x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K} {i j : Fin (m - 1)} (hij : i ≠ j)
    (hxe : x (Sum.inl i) = 0) (hxf : x (Sum.inr (Sum.inl i)) = 0)
    (hxjf : x (Sum.inr (Sum.inl j)) = 0) :
    x ⬝ᵥ (minusM m K b *ᵥ s16c13bcA_minusD m K i j) = 0 := by
  rw [s16k_dot_minusD_eq b x hij, hxe, hxf, hxjf, add_zero, add_zero]

private theorem s16k_dot_single_swap_eq_zero {K : Type} [Field K] [CharP K 2] {m : ℕ} (b c : K)
    {x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K} {r : Fin (m - 1) ⊕ Fin (m - 1)}
    (hxr : x (minusEmb m r) = 0) :
    x ⬝ᵥ (minusM m K b *ᵥ (Pi.single (minusEmb m (Sum.swap r)) 1)) = 0 := by
  rw [(isQuadWith_minus (n := m) b c).symm]
  simp only [single_dotProduct, one_mul]
  rw [minusM_mulVec_emb]
  exact hxr

private theorem s16k_dot_single_swap_ne_zero {K : Type} [Field K] [CharP K 2] {m : ℕ} (b c : K)
    {y : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K} {r : Fin (m - 1) ⊕ Fin (m - 1)}
    (hyr : y (minusEmb m r) ≠ 0) :
    y ⬝ᵥ (minusM m K b *ᵥ (Pi.single (minusEmb m (Sum.swap r)) 1)) ≠ 0 := by
  rw [(isQuadWith_minus (n := m) b c).symm]
  simp only [single_dotProduct, one_mul]
  rw [minusM_mulVec_emb]
  exact hyr

private theorem s16k_std_struct {K : Type} [Field K] [CharP K 2] {m : ℕ} (b c : K)
    {i j : Fin (m - 1)} (hij : i ≠ j) :
    StatedQuadMinus m K b c (minusA m K i) = 1 ∧
      StatedQuadMinus m K b c (minusB m K i j) = 1 ∧
      minusA m K i ⬝ᵥ (minusM m K b *ᵥ minusB m K i j) = 1 ∧
      StatedQuadMinus m K b c (minusA m K j) = 1 ∧
      StatedQuadMinus m K b c (s16c13bcA_minusD m K i j) = 1 ∧
      minusA m K j ⬝ᵥ (minusM m K b *ᵥ s16c13bcA_minusD m K i j) = 1 ∧
      minusA m K i ⬝ᵥ (minusM m K b *ᵥ minusA m K j) = 0 ∧
      minusA m K i ⬝ᵥ (minusM m K b *ᵥ s16c13bcA_minusD m K i j) = 0 ∧
      minusB m K i j ⬝ᵥ (minusM m K b *ᵥ minusA m K j) = 0 ∧
      minusB m K i j ⬝ᵥ (minusM m K b *ᵥ s16c13bcA_minusD m K i j) = 0 :=
  ⟨Q_minusA (n := m) b c i, Q_minusB (n := m) b c hij, B_minusB (n := m) b hij,
    Q_minusA (n := m) b c j, s16c13bcA_Q_minusD (n := m) b c hij,
    s16c13bcA_B_minusD (n := m) b hij, s16c13bcA_dot_minusA_minusA (n := m) b hij,
    s16c13bcA_dot_minusA_minusD (n := m) b hij, s16c13bcA_dot_minusB_minusA (n := m) b hij,
    s16c13bcA_dot_minusB_minusD (n := m) b hij⟩

private theorem s16k_std_four {K : Type} [Field K] [CharP K 2] [Finite K] {m : ℕ}
    (b c : K) {i j : Fin (m - 1)} (hij : i ≠ j)
    {x y : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K}
    (hxie : x (Sum.inl i) = 0) (hxif : x (Sum.inr (Sum.inl i)) = 0)
    (hxje : x (Sum.inl j) = 0) (hxjf : x (Sum.inr (Sum.inl j)) = 0)
    (hyie : y (Sum.inl i) = 0) (hyif : y (Sum.inr (Sum.inl i)) = 0)
    (hyje : y (Sum.inl j) = 0) (hyjf : y (Sum.inr (Sum.inl j)) = 0) :
    ∃ B : Subgroup ↥(StatedOmega (StatedQuadMinus m K b c)), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧
      ∀ g ∈ B, natAct (StatedOmega (StatedQuadMinus m K b c)) g (Multiplicative.ofAdd x) =
          Multiplicative.ofAdd x ∧
        natAct (StatedOmega (StatedQuadMinus m K b c)) g (Multiplicative.ofAdd y) =
          Multiplicative.ofAdd y :=
  s16k_pair_omega_two_subgroup (isQuadWith_minus (n := m) b c) (s16k_std_struct b c hij)
    ⟨s16k_dot_minusA_zero b hxie hxif, s16k_dot_minusB_zero b hij hxif hxje hxjf,
      s16k_dot_minusA_zero b hxje hxjf, s16k_dot_minusD_zero b hij hxie hxif hxjf⟩
    ⟨s16k_dot_minusA_zero b hyie hyif, s16k_dot_minusB_zero b hij hyif hyje hyjf,
      s16k_dot_minusA_zero b hyje hyjf, s16k_dot_minusD_zero b hij hyie hyif hyjf⟩

private theorem s16k_core {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 5 ≤ m)
    {b c : K} (x0 y : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)
    (hx0e : ∀ i : Fin (m - 1), (i : ℕ) ≠ 0 → x0 (Sum.inl i) = 0)
    (hx0f : ∀ i : Fin (m - 1), (i : ℕ) ≠ 0 → x0 (Sum.inr (Sum.inl i)) = 0) :
    ∃ B : Subgroup ↥(StatedOmega (StatedQuadMinus m K b c)), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧
      ∀ g ∈ B, natAct (StatedOmega (StatedQuadMinus m K b c)) g (Multiplicative.ofAdd x0) =
          Multiplicative.ofAdd x0 ∧
        natAct (StatedOmega (StatedQuadMinus m K b c)) g (Multiplicative.ofAdd y) =
          Multiplicative.ofAdd y := by
  let i0 : Fin (m - 1) := ⟨0, by omega⟩
  let i1 : Fin (m - 1) := ⟨1, by omega⟩
  let i2 : Fin (m - 1) := ⟨2, by omega⟩
  let i3 : Fin (m - 1) := ⟨3, by omega⟩
  have h10 : i1 ≠ i0 := by
    intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  have h20 : i2 ≠ i0 := by
    intro h; have := congrArg Fin.val h; simp [i0, i2] at this
  have h30 : i3 ≠ i0 := by
    intro h; have := congrArg Fin.val h; simp [i0, i3] at this
  have h12 : i1 ≠ i2 := by
    intro h; have := congrArg Fin.val h; simp [i1, i2] at this
  have h13 : i1 ≠ i3 := by
    intro h; have := congrArg Fin.val h; simp [i1, i3] at this
  have h23 : i2 ≠ i3 := by
    intro h; have := congrArg Fin.val h; simp [i2, i3] at this
  have hval : ∀ i : Fin (m - 1), i ≠ i0 → (i : ℕ) ≠ 0 := fun i hi h => hi (Fin.ext h)
  by_cases hclean : ∀ r : Fin (m - 1), r ≠ i0 →
      y (Sum.inl r) = 0 ∧ y (Sum.inr (Sum.inl r)) = 0
  · exact s16k_std_four b c h12 (hx0e i1 (hval i1 h10)) (hx0f i1 (hval i1 h10))
      (hx0e i2 (hval i2 h20)) (hx0f i2 (hval i2 h20))
      (hclean i1 h10).1 (hclean i1 h10).2 (hclean i2 h20).1 (hclean i2 h20).2
  · obtain ⟨r, hr⟩ := not_forall.mp hclean
    obtain ⟨hr0, hrP⟩ := not_imp.mp hr
    have hyr : y (Sum.inl r) ≠ 0 ∨ y (Sum.inr (Sum.inl r)) ≠ 0 := not_and_or.mp hrP
    have hr0' : (r : ℕ) ≠ 0 := hval r hr0
    have hpick : ∃ i j : Fin (m - 1), i ≠ i0 ∧ j ≠ i0 ∧ i ≠ r ∧ j ≠ r ∧ i ≠ j := by
      by_cases hr1 : r = i1
      · exact ⟨i2, i3, h20, h30, by rw [hr1]; exact h12.symm, by rw [hr1]; exact h13.symm, h23⟩
      · by_cases hr2 : r = i2
        · exact ⟨i1, i3, h10, h30, by rw [hr2]; exact h12, by rw [hr2]; exact h23.symm, h13⟩
        · exact ⟨i1, i2, h10, h20, fun h => hr1 h.symm, fun h => hr2 h.symm, h12⟩
    obtain ⟨i, j, hi0, hj0, hir, hjr, hij⟩ := hpick
    obtain ⟨r', hr'idx, hyr', hx0r⟩ : ∃ r' : Fin (m - 1) ⊕ Fin (m - 1),
        minusIdx r' = r ∧ y (minusEmb m r') ≠ 0 ∧ x0 (minusEmb m r') = 0 := by
      rcases hyr with h | h
      · exact ⟨Sum.inl r, rfl, by simpa [minusEmb] using h,
          by simpa [minusEmb] using hx0e r hr0'⟩
      · exact ⟨Sum.inr r, rfl, by simpa [minusEmb] using h,
          by simpa [minusEmb] using hx0f r hr0'⟩
    let w : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K :=
      Pi.single (minusEmb m (Sum.swap r')) 1
    have hw1 : w ⬝ᵥ (minusM m K b *ᵥ minusA m K i) = 0 := by
      simp only [w, single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact minusA_apply_eq_zero (r := r') (by rw [hr'idx]; exact hir.symm)
    have hw1' : w ⬝ᵥ (minusM m K b *ᵥ minusB m K i j) = 0 := by
      simp only [w, single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact s16c13bcA_minusB_apply_eq_zero (r := r') (by rw [hr'idx]; exact hir.symm)
        (by rw [hr'idx]; exact hjr.symm)
    have hw2 : w ⬝ᵥ (minusM m K b *ᵥ minusA m K j) = 0 := by
      simp only [w, single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact minusA_apply_eq_zero (r := r') (by rw [hr'idx]; exact hjr.symm)
    have hw2' : w ⬝ᵥ (minusM m K b *ᵥ s16c13bcA_minusD m K i j) = 0 := by
      simp only [w, single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact s16c13bcA_minusD_apply_eq_zero (r := r') (by rw [hr'idx]; exact hir.symm)
        (by rw [hr'idx]; exact hjr.symm)
    obtain ⟨hs1, hs1', hs11, hs2, hs2', hs22, hs12, hs12', hs1'2, hs1'2'⟩ := s16k_std_struct b c hij
    obtain ⟨b₁, b₁', b₂, b₂', hb1, hb1', hb11, hb2, hb2', hb22, hb12, hb12', hb1'2, hb1'2',
      hv1, hv1', hv2, hv2', hu1, hu1', hu2, hu2'⟩ :=
      s16k_pairs_of_singular_two (isQuadWith_minus (n := m) b c) hs1 hs1' hs11 hs2 hs2' hs22 hs12
        hs12' hs1'2 hs1'2' (Q_minusSingle (n := m) b c (Sum.swap r')) hw1 hw1' hw2 hw2'
        (s16k_dot_single_swap_ne_zero b c hyr')
        (s16k_dot_minusA_zero b (hx0e i (hval i hi0)) (hx0f i (hval i hi0)))
        (s16k_dot_minusB_zero b hij (hx0f i (hval i hi0)) (hx0e j (hval j hj0))
          (hx0f j (hval j hj0)))
        (s16k_dot_minusA_zero b (hx0e j (hval j hj0)) (hx0f j (hval j hj0)))
        (s16k_dot_minusD_zero b hij (hx0e i (hval i hi0)) (hx0f i (hval i hi0))
          (hx0f j (hval j hj0)))
        (s16k_dot_single_swap_eq_zero b c hx0r)
    exact s16k_pair_omega_two_subgroup (isQuadWith_minus (n := m) b c)
      ⟨hb1, hb1', hb11, hb2, hb2', hb22, hb12, hb12', hb1'2, hb1'2'⟩
      ⟨hu1, hu1', hu2, hu2'⟩ ⟨hv1, hv1', hv2, hv2'⟩

private theorem s16k_transport {K : Type} [Field K] {m : ℕ} {b c : K}
    (x y : Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))
    {x0 y' : Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)}
    (A : ↥(StatedOmega (StatedQuadMinus m K b c)))
    (hAx : natAct (StatedOmega (StatedQuadMinus m K b c)) A x = x0)
    (hAy : natAct (StatedOmega (StatedQuadMinus m K b c)) A y = y')
    (B' : Subgroup ↥(StatedOmega (StatedQuadMinus m K b c))) (hB'p : IsPGroup 3 B')
    (hB'nc : ¬ IsCyclic ↥B')
    (hB'fix : ∀ g ∈ B', natAct (StatedOmega (StatedQuadMinus m K b c)) g x0 = x0 ∧
      natAct (StatedOmega (StatedQuadMinus m K b c)) g y' = y') :
    ∃ B : Subgroup ↥(StatedOmega (StatedQuadMinus m K b c)), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧
      ∀ g ∈ B, natAct (StatedOmega (StatedQuadMinus m K b c)) g x = x ∧
        natAct (StatedOmega (StatedQuadMinus m K b c)) g y = y := by
  refine ⟨B'.map (MulAut.conj A⁻¹).toMonoidHom, hB'p.map _, ?_, ?_⟩
  · intro hcyc
    exact hB'nc
      ((MulEquiv.isCyclic (B'.equivMapOfInjective _ (MulAut.conj A⁻¹).injective)).mpr hcyc)
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
    have hAinv_x0 : natAct (StatedOmega (StatedQuadMinus m K b c)) A⁻¹ x0 = x := by
      rw [← hAx, ← s16k_natAct_mul, inv_mul_cancel, s16k_natAct_one]
    have hAinv_y' : natAct (StatedOmega (StatedQuadMinus m K b c)) A⁻¹ y' = y := by
      rw [← hAy, ← s16k_natAct_mul, inv_mul_cancel, s16k_natAct_one]
    change natAct (StatedOmega (StatedQuadMinus m K b c)) ((MulAut.conj A⁻¹) g') x = x ∧
      natAct (StatedOmega (StatedQuadMinus m K b c)) ((MulAut.conj A⁻¹) g') y = y
    rw [MulAut.conj_apply, inv_inv]
    exact ⟨by rw [s16k_natAct_mul, s16k_natAct_mul, hAx, (hB'fix g' hg').1, hAinv_x0],
      by rw [s16k_natAct_mul, s16k_natAct_mul, hAy, (hB'fix g' hg').2, hAinv_y']⟩

private theorem s16k_omegaMinus_pair_fix_aux {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 5 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (x y : Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) (hx : x ≠ 1) :
    ∃ B : Subgroup ↥(StatedOmega (StatedQuadMinus m K b c)), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧
      ∀ g ∈ B, natAct (StatedOmega (StatedQuadMinus m K b c)) g x = x ∧
        natAct (StatedOmega (StatedQuadMinus m K b c)) g y = y := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hm4 : 4 ≤ m := by omega
  set xv : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := Multiplicative.toAdd x with hxv
  set yv : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := Multiplicative.toAdd y with hyv
  have hx0 : xv ≠ 0 := fun h => hx (toAdd_eq_zero.mp h)
  let i0 : Fin (m - 1) := ⟨0, by omega⟩
  by_cases hQx : StatedQuadMinus m K b c xv = 0
  · obtain ⟨A, hA, hAx⟩ :=
      CFSG.ClassicalGroups.Orthogonal.statedOmegaMinus_exists_mulVec_eq (by omega : 3 ≤ m) hirr hx0
        (s16k_e_ne_zero (K := K) i0)
        (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus, hQx]; exact (s16k_Q_e b c i0).symm)
    let AΩ : ↥(StatedOmega (StatedQuadMinus m K b c)) := ⟨A, hA⟩
    set yv' : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K :=
      (((A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)) : Matrix _ _ K) *ᵥ yv with hyv'
    have hAy : natAct (StatedOmega (StatedQuadMinus m K b c)) AΩ y =
        Multiplicative.ofAdd yv' := rfl
    have hAx' : natAct (StatedOmega (StatedQuadMinus m K b c)) AΩ x =
        Multiplicative.ofAdd (s16k_e K i0) := congrArg Multiplicative.ofAdd hAx
    obtain ⟨B', hB'p, hB'nc, hB'fix⟩ :=
      s16k_core hm (s16k_e K i0) yv'
        (fun i hi => by
          have hi0 : i ≠ i0 := fun h => hi (by simpa using congrArg Fin.val h)
          simp [s16k_e, Pi.single_apply, hi0])
        (fun i hi => by
          have hi0 : i ≠ i0 := fun h => hi (by simpa using congrArg Fin.val h)
          simp [s16k_e, Pi.single_apply, hi0])
    exact s16k_transport x y AΩ hAx' hAy B' hB'p hB'nc hB'fix
  · have hQx1 : StatedQuadMinus m K b c xv = 1 :=
      (s16k_eq_zero_or_one (by rw [← Nat.card_eq_fintype_card]; exact hK)
        (StatedQuadMinus m K b c xv)).resolve_left hQx
    obtain ⟨A, hA, hAx⟩ :=
      CFSG.ClassicalGroups.Orthogonal.statedOmegaMinus_exists_mulVec_eq (by omega : 3 ≤ m) hirr hx0
        (s16k_uu_ne_zero (K := K) m)
        (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus, hQx1]; exact (s16k_Q_uu b c).symm)
    let AΩ : ↥(StatedOmega (StatedQuadMinus m K b c)) := ⟨A, hA⟩
    set yv' : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K :=
      (((A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)) : Matrix _ _ K) *ᵥ yv with hyv'
    have hAy : natAct (StatedOmega (StatedQuadMinus m K b c)) AΩ y =
        Multiplicative.ofAdd yv' := rfl
    have hAx' : natAct (StatedOmega (StatedQuadMinus m K b c)) AΩ x =
        Multiplicative.ofAdd (s16k_uu K m) := congrArg Multiplicative.ofAdd hAx
    obtain ⟨B', hB'p, hB'nc, hB'fix⟩ :=
      s16k_core hm (s16k_uu K m) yv'
        (fun _ _ => by simp [s16k_uu, Pi.single_apply])
        (fun _ _ => by simp [s16k_uu, Pi.single_apply])
    exact s16k_transport x y AΩ hAx' hAy B' hB'p hB'nc hB'fix

theorem s16k_omegaMinus_pair_fix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 5 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (x y : Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) (hxy : x ≠ 1 ∨ y ≠ 1) :
    ∃ B : Subgroup ↥(StatedOmega (StatedQuadMinus m K b c)), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧
      ∀ g ∈ B, natAct (StatedOmega (StatedQuadMinus m K b c)) g x = x ∧
        natAct (StatedOmega (StatedQuadMinus m K b c)) g y = y := by
  rcases hxy with hx | hy
  · exact s16k_omegaMinus_pair_fix_aux hK hm hirr x y hx
  · obtain ⟨B, hBp, hBnc, hfix⟩ := s16k_omegaMinus_pair_fix_aux hK hm hirr y x hy
    exact ⟨B, hBp, hBnc, fun g hg => ⟨(hfix g hg).2, (hfix g hg).1⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
