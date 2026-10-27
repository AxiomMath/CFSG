module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.EmptyFaithful.S153EB6A

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.Assembly.LowTwoRank

private def elemMap {K : Type} [Field K] {n : ℕ} (i : Fin n) (c : Fin n → K) :
    (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun v := fun l => if l = i then v i else v l + c l * v i
  map_add' v w := by
    funext l
    by_cases h : l = i
    · simp [h]
    · simp only [h, ite_false, Pi.add_apply]
      ring
  map_smul' r v := by
    funext l
    by_cases h : l = i
    · simp [h]
    · simp only [h, ite_false, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

private theorem elemMap_neg {K : Type} [Field K] {n : ℕ} (i : Fin n) (c v : Fin n → K) :
    elemMap i (-c) (elemMap i c v) = v := by
  funext l
  by_cases h : l = i <;> simp [elemMap, h]

@[expose] def cblock {K : Type} [Field K] {n : ℕ} (j k : Fin n) :
    (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun v := fun l => if l = j then v k else if l = k then v j + v k else v l
  map_add' v w := by
    funext l
    by_cases h1 : l = j
    · simp [h1]
    · by_cases h2 : l = k
      · subst h2
        simp only [h1, ite_false, ite_true, Pi.add_apply]
        ring
      · simp [h1, h2]
  map_smul' r v := by
    funext l
    by_cases h1 : l = j
    · simp [h1]
    · by_cases h2 : l = k
      · subst h2
        simp only [h1, ite_false, ite_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
      · simp [h1, h2]

theorem cblock_cube {K : Type} [Field K] {n : ℕ} (h2 : (2 : K) = 0) {j k : Fin n}
    (hjk : j ≠ k) (v : Fin n → K) : cblock j k (cblock j k (cblock j k v)) = v := by
  funext l
  by_cases h1 : l = j
  · subst h1
    simp [cblock, hjk.symm]
    linear_combination (v k) * h2
  by_cases h3 : l = k
  · subst h3
    simp [cblock, hjk.symm]
    linear_combination (v j + v l) * h2
  simp [cblock, h1, h3]

theorem cblock_fix {K : Type} [Field K] {n : ℕ} {j k : Fin n}
    (v : Fin n → K) (hj : v j = 0) (hk : v k = 0) : cblock j k v = v := by
  funext l
  by_cases h1 : l = j
  · subst h1
    simp [cblock, hk, hj]
  by_cases h3 : l = k
  · subst h3
    simp [cblock, hj, hk, h1]
  simp [cblock, h1, h3]

theorem cblock_ne {K : Type} [Field K] {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    cblock j k (Pi.single j (1 : K)) ≠ Pi.single j 1 := by
  intro h
  have := congrFun h j
  simp [cblock, hjk.symm] at this

theorem exists_stated_of_cube {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (f : (Fin n → K) →ₗ[K] (Fin n → K)) (hf : ∀ v, f (f (f v)) = v) :
    ∃ γ : ↥(StatedSL n K), γ ^ 3 = 1 ∧
      ∀ v, ((γ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v = f v := by
  have hMM : LinearMap.toMatrix' f * (LinearMap.toMatrix' f * LinearMap.toMatrix' f) = 1 := by
    have h1 : f ∘ₗ (f ∘ₗ f) = LinearMap.id := LinearMap.ext fun v => hf v
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id]
  set M := LinearMap.toMatrix' f with hM
  have hMM' : (M * M) * M = 1 := by rw [mul_assoc]; exact hMM
  let γ0 : Matrix.GeneralLinearGroup (Fin n) K := Units.mk M (M * M) hMM hMM'
  have hdet : M.det = 1 := by
    have h1 := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h1
    rcases card_two_cases hK M.det with h | h
    · rw [h] at h1; simp at h1
    · exact h
  refine ⟨⟨γ0, Subgroup.subset_closure hdet⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show M ^ 3 = 1
    rw [pow_succ, pow_two]
    exact hMM'
  · intro v
    exact LinearMap.toMatrix'_mulVec f v

theorem natSL_fix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (n : ℕ) (hn : 3 ≤ n)
    (m : Multiplicative (Fin n → K)) :
    ∃ γ : ↥(StatedSL n K), γ ^ 3 = 1 ∧ natAct (StatedSL n K) γ m = m ∧
      ∃ m', natAct (StatedSL n K) γ m' ≠ m' := by
  have h2 := two_eq_zero_of_card_two hK
  obtain ⟨g, ginv, hgi, hig, j, k, hjk, hgj, hgk⟩ : ∃ (g ginv : (Fin n → K) →ₗ[K] (Fin n → K)),
      (∀ v, ginv (g v) = v) ∧ (∀ v, g (ginv v) = v) ∧
      ∃ j k : Fin n, j ≠ k ∧ g (Multiplicative.toAdd m) j = 0 ∧ g (Multiplicative.toAdd m) k = 0 := by
    by_cases hm : ∃ i, Multiplicative.toAdd m i ≠ 0
    · obtain ⟨i, hi⟩ := hm
      have hi1 : Multiplicative.toAdd m i = 1 := (card_two_cases hK _).resolve_left hi
      obtain ⟨j, k, hjk, hji, hki⟩ : ∃ j k : Fin n, j ≠ k ∧ j ≠ i ∧ k ≠ i := by
        have hc : 1 < (Finset.univ.erase i).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp only [Finset.card_univ, Fintype.card_fin]
          omega
        obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 hc
        exact ⟨j, k, hjk, (Finset.mem_erase.1 hj).1, (Finset.mem_erase.1 hk).1⟩
      refine ⟨elemMap i (-(Multiplicative.toAdd m)), elemMap i (Multiplicative.toAdd m),
        fun v => ?_, fun v => ?_, j, k, hjk, ?_, ?_⟩
      · have := elemMap_neg i (-(Multiplicative.toAdd m)) v
        rwa [neg_neg] at this
      · exact elemMap_neg i (Multiplicative.toAdd m) v
      · simp [elemMap, hji, hi1]
      · simp [elemMap, hki, hi1]
    · push Not at hm
      have hz : ∀ l, Multiplicative.toAdd m l = 0 := hm
      refine ⟨LinearMap.id, LinearMap.id, fun _ => rfl, fun _ => rfl, ⟨0, by omega⟩, ⟨1, by omega⟩,
        ?_, hz _, hz _⟩
      intro h
      have := congrArg Fin.val h
      simp at this
  have hfv : ∀ v, (ginv ∘ₗ (cblock j k ∘ₗ g)) v = ginv (cblock j k (g v)) := fun v => rfl
  have hcube : ∀ v, (ginv ∘ₗ (cblock j k ∘ₗ g)) ((ginv ∘ₗ (cblock j k ∘ₗ g))
      ((ginv ∘ₗ (cblock j k ∘ₗ g)) v)) = v := by
    intro v
    simp only [hfv, hig, hgi, cblock_cube h2 hjk]
  obtain ⟨γ, hγ3, hγv⟩ := exists_stated_of_cube hK (ginv ∘ₗ (cblock j k ∘ₗ g)) hcube
  refine ⟨γ, hγ3, ?_, ?_⟩
  · simp only [natAct]
    rw [hγv, hfv, cblock_fix _ hgj hgk, hgi]
    rfl
  · refine ⟨Multiplicative.ofAdd (ginv (Pi.single j 1)), ?_⟩
    simp only [natAct]
    intro h
    have h1 := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd] at h1
    rw [hγv, hfv, hig] at h1
    have h2' := congrArg g h1
    rw [hig, hig] at h2'
    exact cblock_ne hjk h2'

end S153EB6

end CFSG.Quasithin
