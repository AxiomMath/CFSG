module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.Quasithin.H13.Ln2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem eq_conj_of_mulAut (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    (φ : MulAut (SpecialLinearGroup (Fin n) K))
    (hU : ∀ u ∈ unitriangular n K, φ u ∈ unitriangular n K)
    (hQ : ∀ g ∈ stabilizer (flagSpace n K 1), φ g ∈ stabilizer (flagSpace n K 1)) :
    ∃ u ∈ unitriangular n K, ∀ g, φ g = u * g * u⁻¹ := by
  classical
  obtain ⟨A, σ, ε, hε, hφ⟩ := CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hn φ
  have hσ : σ = 1 := RingEquiv.ext fun c => by
    rcases eq_zero_or_eq_one_of_card_two hK c with rfl | rfl <;> simp
  subst hσ
  rw [map_one, mul_one] at hφ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hφ
    have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
      have h1 := units_eq_one_of_card_two hK (Matrix.GeneralLinearGroup.det A)
      have h2 := congrArg Units.val h1
      simpa using h2
    set g₀ : SpecialLinearGroup (Fin n) K := ⟨A, hdet⟩ with hg₀
    have hinv : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g₀⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.coe_units_inv, Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, hdet]
      simp [hg₀]
    have hφg : ∀ g, φ g = g₀ * g * g₀⁻¹ := by
      intro g
      apply Subtype.ext
      rw [hφ, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hinv]
      rfl
    have hN : g₀ ∈ Subgroup.normalizer
        (unitriangular n K : Set (SpecialLinearGroup (Fin n) K)) := by
      have hle : (unitriangular n K).map (MulAut.conj g₀).toMonoidHom ≤ unitriangular n K := by
        rintro _ ⟨u, hu, rfl⟩
        show g₀ * u * g₀⁻¹ ∈ unitriangular n K
        rw [← hφg]
        exact hU u hu
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle ?_)
      rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective]
    rw [normalizer_unitriangular] at hN
    exact ⟨g₀, upperTriangular_le_unitriangular hK hN, hφg⟩
  · exfalso
    rw [pow_one] at hφ
    set W := flagSpace n K 1 with hW
    have hφhom : φ.toMonoidHom =
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A :
        SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K).comp
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n K :
          SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K) := by
      rw [hφ]
      exact MonoidHom.ext fun g => rfl
    have h1 : (stabilizer W).map φ.toMonoidHom =
        stabilizer ((dotOrth W).map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) := by
      rw [hφhom, ← Subgroup.map_map, map_stabilizer_slGraphAut, map_stabilizer_slConjugation]
    have hQ' : (stabilizer W).map φ.toMonoidHom = stabilizer W := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨g, hg, rfl⟩
        exact hQ g hg
      · rw [Subgroup.card_map_of_injective φ.injective]
    rw [h1] at hQ'
    have h2 : projStabilizer ((dotOrth W).map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) =
        projStabilizer W := by
      unfold projStabilizer
      rw [hQ']
    have hdW : Module.finrank K W = 1 := finrank_flagSpace (by omega)
    have hdW' : Module.finrank K ((dotOrth W).map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) =
        n - 1 := by
      have := LinearEquiv.finrank_map_eq
        ((A : Matrix (Fin n) (Fin n) K).toLinearEquiv' A.invertible) (dotOrth W)
      exact this.trans (by rw [finrank_dotOrth, hdW])
    obtain ⟨p, hchar⟩ := CharP.exists K
    have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
    obtain ⟨-, hdisj, -⟩ := intrinsic_extremal_parabolics (K := K) (n := n) p hn
    exact Set.disjoint_left.1 hdisj ⟨W, hdW, rfl⟩ ⟨_, hdW', h2⟩

omit [Finite K] in
theorem liftT_mem_perfectCore {n : ℕ} {I : Set ℕ} {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) {i j : Fin m} (hij : i ≠ j) :
    (liftT a m h hij : SpecialLinearGroup (Fin n) K) ∈ perfectCore (flagStabilizer n K I) := by
  classical
  set P₀ : Subgroup (SpecialLinearGroup (Fin n) K) :=
    Subgroup.closure {x | ∃ (i j : Fin m) (hij : i ≠ j), x = liftT a m h hij} with hP₀
  have hP₀H : P₀ ≤ flagStabilizer n K I := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, j, hij, rfl⟩
    exact liftT_mem_flagStabilizer a m h hno hij
  have hgen : ∀ (i j : Fin m) (hij : i ≠ j), liftT a m h hij ∈ P₀ := fun i j hij =>
    Subgroup.subset_closure ⟨i, j, hij, rfl⟩
  have hP₀perf : ⁅P₀, P₀⁆ = P₀ := by
    have h1 : ⁅P₀, P₀⁆ ≤ P₀ := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
    have h2 : P₀ ≤ ⁅P₀, P₀⁆ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, j, hij, rfl⟩
      obtain ⟨k, hki, hkj⟩ : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
        by_contra hcon
        push Not at hcon
        have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := fun k _ => by
          by_cases hki : k = i
          · simp [hki]
          · simp [hcon k hki]
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_le_two (a := i) (b := j)
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        omega
      have hcomm : ⁅(liftT a m h (Ne.symm hki) : SpecialLinearGroup (Fin n) K),
          (liftT a m h hkj : SpecialLinearGroup (Fin n) K)⁆ = liftT a m h hij := by
        have := SpecialLinearGroup.commutatorElement_transvection
          (blkIdxN_ne (h := h) (Ne.symm hki)) (blkIdxN_ne (h := h) hkj)
          (blkIdxN_ne (h := h) hij) (1 : K) 1
        rw [mul_one] at this
        exact this
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator (hgen _ _ _) (hgen _ _ _)
    exact le_antisymm h1 h2
  exact le_perfectCore_of_perfect hP₀H hP₀perf (hgen i j hij)

omit [Finite K] in
theorem liftT_not_mem_stabilizer {n : ℕ} {a m : ℕ} (h : a + m ≤ n) {i j : Fin m} (hij : i ≠ j)
    {d : ℕ} (hd1 : (j : ℕ) + a < d) (hd2 : d ≤ (i : ℕ) + a) :
    (liftT a m h hij : SpecialLinearGroup (Fin n) K) ∉ stabilizer (flagSpace n K d) := by
  intro hmem
  have h1 := stabilizer_entries hmem (k := blkIdxN a m h i) (l := blkIdxN a m h j)
    (by simp only [blkIdxN]; omega) (by simp only [blkIdxN]; omega)
  rw [coe_liftT] at h1
  have hne : blkIdxN a m h i ≠ blkIdxN a m h j := blkIdxN_ne hij
  simp [Matrix.add_apply, hne] at h1

theorem sup_perfectCore_eq_top (hK : Nat.card K = 2) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5) :
    perfectCore (flagStabilizer n K {1}) ⊔ perfectCore (flagStabilizer n K {3}) ⊔
      unitriangular n K = ⊤ := by
  classical
  set A := perfectCore (flagStabilizer n K {1}) ⊔ perfectCore (flagStabilizer n K {3}) ⊔
    unitriangular n K with hA
  have hB : upperTriangular n K ≤ A :=
    (upperTriangular_le_unitriangular hK).trans le_sup_right
  obtain ⟨hAeq, -⟩ := borel_overgroups A hB
  suffices hI : borelOvergroupCuts A = ∅ by
    rw [hAeq, hI, flagStabilizer_empty]
  ext d
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hd
  obtain ⟨hd1, hdn, hr⟩ := hd
  have hAle : A ≤ stabilizer (flagSpace n K d) := by
    rw [hAeq]
    exact iInf₂_le d ⟨hd1, hdn, hr⟩
  rcases (by omega : d ≤ 2 ∨ 3 ≤ d) with hd2 | hd3
  ·
    have h3 : 0 + 3 ≤ n := by omega
    have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      omega
    have hij : (⟨d, by omega⟩ : Fin 3) ≠ ⟨d - 1, by omega⟩ := by
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    have hx := liftT_mem_perfectCore (K := K) h3 le_rfl hno hij
    exact liftT_not_mem_stabilizer (K := K) h3 hij (by simp; omega) (by simp)
      (hAle ((le_sup_right.trans le_sup_left : perfectCore (flagStabilizer n K {3}) ≤ A) hx))
  ·
    have h1 : 1 + (n - 1) ≤ n := by omega
    have hno : ∀ c ∈ ({1} : Set ℕ), ¬ (1 < c ∧ c < 1 + (n - 1)) := by
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      omega
    have hij : (⟨d - 1, by omega⟩ : Fin (n - 1)) ≠ ⟨d - 2, by omega⟩ := by
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    have hx := liftT_mem_perfectCore (K := K) h1 (by omega) hno hij
    exact liftT_not_mem_stabilizer (K := K) h1 hij (by simp; omega) (by simp; omega)
      (hAle ((le_sup_left.trans le_sup_left : perfectCore (flagStabilizer n K {1}) ≤ A) hx))

end CFSG.Quasithin.H13.Ln2
