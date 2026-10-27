module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSplit

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.UnbalancedCatalog IntermediateField

section OddDegree

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem binary_aniso_ext [FiniteDimensional k K] (hodd : Odd (finrank k K)) (α β γ : k)
    (h : ∀ s t : k, α * s ^ 2 + β * s * t + γ * t ^ 2 = 0 → s = 0 ∧ t = 0) (s t : K)
    (hst : algebraMap k K α * s ^ 2 + algebraMap k K β * s * t + algebraMap k K γ * t ^ 2 = 0) :
    s = 0 ∧ t = 0 := by
  have hinj : Function.Injective (algebraMap k K) := (algebraMap k K).injective
  have hα : α ≠ 0 := by
    intro h0
    exact one_ne_zero (h 1 0 (by simp [h0])).1
  have hα' : algebraMap k K α ≠ 0 := fun h0 => hα (hinj (by rw [h0, map_zero]))
  by_cases ht : t = 0
  · subst ht
    refine ⟨?_, rfl⟩
    have h1 : algebraMap k K α * s ^ 2 = 0 := by simpa using hst
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hα'
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
  · exfalso
    set z : K := s / t with hz
    have hroot : algebraMap k K α * z ^ 2 + algebraMap k K β * z + algebraMap k K γ = 0 := by
      rw [hz]
      field_simp
      linear_combination hst
    have hnot : ∀ z₀ : k, algebraMap k K z₀ ≠ z := by
      intro z₀ hz₀
      rw [← hz₀] at hroot
      have h1 : α * z₀ ^ 2 + β * z₀ + γ = 0 := hinj (by simpa using hroot)
      exact one_ne_zero (h z₀ 1 (by linear_combination h1)).2
    have hint : IsIntegral k z := Algebra.IsIntegral.isIntegral z
    set p : Polynomial k := Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X +
      Polynomial.C γ with hp
    have hp0 : p ≠ 0 := by
      intro h0
      have := Polynomial.natDegree_quadratic (b := β) (c := γ) hα
      rw [← hp, h0] at this
      simp at this
    have hroot' : Polynomial.aeval z p = 0 := by simpa [hp] using hroot
    have hdvd : minpoly k z ∣ p := minpoly.dvd k z hroot'
    have hle : (minpoly k z).natDegree ≤ 2 :=
      (Polynomial.Monic.natDegree_le_of_dvd (minpoly.monic hint) hp0 hdvd).trans
        (Polynomial.natDegree_quadratic hα).le
    have hge : 2 ≤ (minpoly k z).natDegree := by
      rw [minpoly.two_le_natDegree_iff hint]
      rintro ⟨z₀, hz₀⟩
      exact hnot z₀ hz₀
    have hdeg : (minpoly k z).natDegree = 2 := le_antisymm hle hge
    have hfr : finrank k k⟮z⟯ = 2 := by rw [IntermediateField.adjoin.finrank hint, hdeg]
    have htower := Module.finrank_mul_finrank k k⟮z⟯ K
    rw [hfr] at htower
    obtain ⟨r, hr⟩ := hodd
    omega

end OddDegree

section Extend

variable {k K W V : Type} [Field k] [Field K] [Algebra k K] [AddCommGroup W] [Module k W]
  [AddCommGroup V] [Module K V]

theorem tail_aniso_of_le_two [FiniteDimensional k K] (hodd : Odd (finrank k K))
    {Q₀ : QuadraticForm k W} {R : QuadraticForm K V} (ι : W →+ V)
    (hι : ∀ w, R (ι w) = algebraMap k K (Q₀ w)) {δ : ℕ} (hδ : δ ≤ 2) (t : Fin δ → W)
    (ht : ∀ z : Fin δ → k, Q₀ (∑ j, z j • t j) = 0 → z = 0) :
    ∀ Z : Fin δ → K, R (∑ j, Z j • ι (t j)) = 0 → Z = 0 := by
  have hpol : ∀ u w, polar R (ι u) (ι w) = algebraMap k K (polar Q₀ u w) := by
    intro u w
    simp only [QuadraticMap.polar, ← map_add, hι, map_sub]
  interval_cases δ
  · intro Z _
    funext i
    exact i.elim0
  · intro Z hZ
    have h0 : Q₀ (t 0) ≠ 0 := by
      intro h0
      have := ht (fun _ => 1) (by simpa using h0)
      exact one_ne_zero (congrFun this 0)
    simp only [Fin.sum_univ_one] at hZ
    rw [map_smul_eq_sq, hι] at hZ
    have : Z 0 ^ 2 = 0 := by
      rcases mul_eq_zero.mp hZ with h1 | h1
      · exact h1
      · exact absurd (by simpa using h1) h0
    funext i
    fin_cases i
    simpa using pow_eq_zero_iff (two_ne_zero) |>.mp this
  · intro Z hZ
    simp only [Fin.sum_univ_two] at hZ
    have hk : ∀ s u : k, Q₀ (s • t 0 + u • t 1) =
        s ^ 2 * Q₀ (t 0) + u ^ 2 * Q₀ (t 1) + s * u * polar Q₀ (t 0) (t 1) := by
      intro s u
      rw [QuadraticMap.map_add (⇑Q₀), map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
        polar_smul_right_eq]
      ring
    have hK : R (Z 0 • ι (t 0) + Z 1 • ι (t 1)) =
        Z 0 ^ 2 * algebraMap k K (Q₀ (t 0)) + Z 1 ^ 2 * algebraMap k K (Q₀ (t 1)) +
          Z 0 * Z 1 * algebraMap k K (polar Q₀ (t 0) (t 1)) := by
      rw [QuadraticMap.map_add (⇑R), map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
        polar_smul_right_eq, hι, hι, hpol]
      ring
    have h2 := binary_aniso_ext hodd (Q₀ (t 0)) (polar Q₀ (t 0) (t 1)) (Q₀ (t 1))
      (fun s u hsu => by
        have := ht ![s, u] (by
          simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          rw [hk]
          linear_combination hsu)
        exact ⟨congrFun this 0, congrFun this 1⟩) (Z 0) (Z 1) (by
        rw [hK] at hZ
        linear_combination hZ)
    funext i
    fin_cases i
    · exact h2.1
    · exact h2.2

variable [FiniteDimensional k K]

@[expose] noncomputable def HypSplit.extend {Q₀ : QuadraticForm k W} {R : QuadraticForm K V}
    (ι : W →+ V) (hι : ∀ w, R (ι w) = algebraMap k K (Q₀ w)) {m δ : ℕ} (H : HypSplit Q₀ m δ)
    (hδ : δ ≤ 2)
    (hodd : Odd (finrank k K)) (bK : Basis (Fin m ⊕ Fin m ⊕ Fin δ) K V)
    (hbK : ∀ a, bK a = ι (H.b a)) : HypSplit R m δ where
  b := bK
  eval x y z := by
    have hpol : ∀ u w, polar R (ι u) (ι w) = algebraMap k K (polar Q₀ u w) := by
      intro u w
      simp only [QuadraticMap.polar, ← map_add, hι, map_sub]
    let P : Fin m → HypPair R := fun i =>
      { e := ι (H.b (.inl i))
        f := ι (H.b (.inr (.inl i)))
        Q_e := by rw [hι, H.Q_inl, map_zero]
        Q_f := by rw [hι, H.Q_inr, map_zero]
        polar_ef := by
          have h : polar Q₀ (H.b (.inl i)) (H.b (.inr (.inl i))) = 1 := (H.hypPair i).polar_ef
          rw [hpol, h, map_one] }
    have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := fun i j hij =>
      { ee := by
          have h : polar Q₀ (H.b (.inl i)) (H.b (.inl j)) = 0 := (H.hypPair_orth hij).ee
          show polar R (ι (H.b (.inl i))) (ι (H.b (.inl j))) = 0
          rw [hpol, h, map_zero]
        ef := by
          have h : polar Q₀ (H.b (.inl i)) (H.b (.inr (.inl j))) = 0 := (H.hypPair_orth hij).ef
          show polar R (ι (H.b (.inl i))) (ι (H.b (.inr (.inl j)))) = 0
          rw [hpol, h, map_zero]
        fe := by
          have h : polar Q₀ (H.b (.inr (.inl i))) (H.b (.inl j)) = 0 := (H.hypPair_orth hij).fe
          show polar R (ι (H.b (.inr (.inl i)))) (ι (H.b (.inl j))) = 0
          rw [hpol, h, map_zero]
        ff := by
          have h : polar Q₀ (H.b (.inr (.inl i))) (H.b (.inr (.inl j))) = 0 :=
            (H.hypPair_orth hij).ff
          show polar R (ι (H.b (.inr (.inl i)))) (ι (H.b (.inr (.inl j)))) = 0
          rw [hpol, h, map_zero] }
    have htail : ∀ j i, ι (H.b (.inr (.inr j))) ∈ (P i).perp := by
      intro j i
      rw [HypPair.mem_perp]
      have h := (HypPair.mem_perp).mp (H.tail_mem_perp j i)
      have h1 : polar Q₀ (H.b (.inl i)) (H.b (.inr (.inr j))) = 0 := h.1
      have h2 : polar Q₀ (H.b (.inr (.inl i))) (H.b (.inr (.inr j))) = 0 := h.2
      constructor
      · show polar R (ι (H.b (.inl i))) (ι (H.b (.inr (.inr j)))) = 0
        rw [hpol, h1, map_zero]
      · show polar R (ι (H.b (.inr (.inl i)))) (ι (H.b (.inr (.inr j)))) = 0
        rw [hpol, h2, map_zero]
    have hw : ∀ i, (∑ j, z j • ι (H.b (.inr (.inr j)))) ∈ (P i).perp := fun i =>
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (htail j i)
    have key : R (∑ i, x i • ι (H.b (.inl i)) + ∑ i, y i • ι (H.b (.inr (.inl i)))) =
        ∑ i, x i * y i := map_sum_hyp hP x y
    have key2 : polar R (∑ i, x i • ι (H.b (.inl i)) + ∑ i, y i • ι (H.b (.inr (.inl i))))
        (∑ j, z j • ι (H.b (.inr (.inr j)))) = 0 := polar_sum_hyp_eq_zero x y hw
    simp only [hbK]
    rw [QuadraticMap.map_add (⇑R), key, key2]
    ring
  aniso Z hZ := by
    simp only [hbK] at hZ
    exact tail_aniso_of_le_two hodd ι hι hδ (fun j => H.b (.inr (.inr j))) H.aniso Z hZ

end Extend

end CFSG.RankThree.PartOne.KCOrthogonalDescent
