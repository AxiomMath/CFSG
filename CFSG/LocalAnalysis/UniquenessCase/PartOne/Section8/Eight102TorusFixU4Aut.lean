module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102TorusFixU4Elem
public import CFSG.Milestones.ASVolI.F431.BCoreU4
import CFSG.Milestones.ASVolI.F411.aSwL3BField

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

theorem exists_conj_mul_burnsideF4m_U4_fieldAut_pow (h : UnitaryFieldData 2 n K)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2) (α : MulAut (hypSU h 2 0)) :
    ∃ y : hypSU h 2 0, ∃ j : ℕ, α = MulAut.conj y * ASVolI.burnsideF4m_U4_fieldAut h σ ^ j := by
  obtain ⟨a, σ', hα⟩ := ASVolI.burnsideF4m_U4_normalForm h α
  obtain ⟨j, hj⟩ :=
    @CFSG.ASVolI.burnsideF411a_ringEquiv_pow K _ h.finite 2 ⟨h.prime⟩ h.charP σ'
  refine ⟨a, j, ?_⟩
  have hσ' : σ' = σ ^ j := by
    ext x
    rw [hj x,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.pow_apply_of_frobenius hσ j x]
  rw [hα, hσ', map_pow (ASVolI.burnsideF4m_U4_fieldAut h) σ j]

theorem burnsideF4m_U4_fieldAut_pow_two_mul_eq_one (h : UnitaryFieldData 2 n K)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2) :
    ASVolI.burnsideF4m_U4_fieldAut h σ ^ (2 * n) = 1 := by
  have hfin : Finite K := h.finite
  have hft : Fintype K := @Fintype.ofFinite K hfin
  have hcard : Fintype.card K = 2 ^ (2 * n) := by
    rw [← @Nat.card_eq_fintype_card K hft, h.card]
  have hpow : σ ^ (2 * n) = 1 := by
    ext x
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.pow_apply_of_frobenius hσ (2 * n) x]
    change x ^ 2 ^ (2 * n) = x
    rw [← hcard]
    exact @FiniteField.pow_card K _ hft x
  rw [← map_pow (ASVolI.burnsideF4m_U4_fieldAut h) σ (2 * n), hpow,
    map_one (ASVolI.burnsideF4m_U4_fieldAut h)]

theorem burnsideF4m_U4_fieldAut_mem_torusPow (h : UnitaryFieldData 2 n K) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) {m : ℕ} {g : hypSU h 2 0} (hg : g ∈ Syl3.torusPow h 2 0 m) :
    ASVolI.burnsideF4m_U4_fieldAut h σ g ∈ Syl3.torusPow h 2 0 m := by
  rw [Syl3.mem_torusPow] at hg ⊢
  obtain ⟨a, ha, hg⟩ := hg
  refine ⟨fun i => Units.map σ.toRingHom.toMonoidHom (a i), ?_, ?_⟩
  · intro i
    rw [← map_pow (Units.map σ.toRingHom.toMonoidHom) (a i) m, ha i,
      map_one (Units.map σ.toRingHom.toMonoidHom)]
  · rw [show ASVolI.burnsideF4m_U4_fieldAut h σ g =
        ASVolI.burnsideF4m_U4_fieldElt h σ g from rfl,
      ASVolI.burnsideF4m_U4_coe_fieldElt,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, hg,
      Matrix.diagonal_map (map_zero σ)]
    rw [Matrix.diagonal_eq_diagonal_iff]
    intro x
    rcases x with i | k | i
    · fin_cases i <;> simp [torusEntries, hσ]
    · exact k.elim0
    · fin_cases i <;> simp [torusEntries, hσ]

theorem burnsideF4m_U4_fieldAut_pow_torusFixElem (h : UnitaryFieldData 2 n K) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) (j : ℕ) (μ : Kˣ) :
    (ASVolI.burnsideF4m_U4_fieldAut h σ ^ j) (torusFixElem h μ) =
      torusFixElem h (μ ^ 2 ^ j) := by
  have hstep : ∀ ν : Kˣ, ASVolI.burnsideF4m_U4_fieldAut h σ (torusFixElem h ν) =
      torusFixElem h (ν ^ 2) := by
    intro ν
    apply Subtype.ext
    apply Units.ext
    rw [show ASVolI.burnsideF4m_U4_fieldAut h σ (torusFixElem h ν) =
        ASVolI.burnsideF4m_U4_fieldElt h σ (torusFixElem h ν) from rfl,
      ASVolI.burnsideF4m_U4_coe_fieldElt,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, coe_torusFixElem,
      coe_torusFixElem, Matrix.diagonal_map (map_zero σ)]
    rw [Matrix.diagonal_eq_diagonal_iff]
    intro x
    rcases x with i | k | i
    · fin_cases i <;> simp [torusEntries, hσ]
    · exact k.elim0
    · fin_cases i <;> simp [torusEntries, hσ]
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, hstep]
      have hpow : (μ ^ 2 ^ j) ^ 2 = μ ^ 2 ^ (j + 1) := by
        rw [← pow_mul, pow_succ]
      rw [hpow]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
