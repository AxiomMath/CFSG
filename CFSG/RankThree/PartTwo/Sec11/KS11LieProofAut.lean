module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

section DichotomyLinear

variable {K : Type} [Field K] {p f : ℕ}

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts

theorem aut_pgl_or_field_linear (hK : PiField true p f K)
    (α : MulAut (projImage (slPi true 3 (p ^ f) K))) (hα3 : α ^ 3 = 1) :
    (∃ y ∈ glPi true 3 (p ^ f) K, ∀ m : projImage (slPi true 3 (p ^ f) K),
        (α m : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹) ∨
    (∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
      ((∀ c, σ c = c ^ piCard true (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard true (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi true 3 (p ^ f) K, ∀ s (hs : s ∈ slPi true 3 (p ^ f) K),
        (α (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹)) := by
  have := hK.finite
  set ψ := pslEquivProjective (p ^ f) K with hψ
  set α' := MulAut.congr ψ α with hα'
  have hα'3 : α' ^ 3 = 1 := by
    rw [hα', ← map_pow, hα3, map_one]
  have hproj : ∀ t : SpecialLinearGroup (Fin 3) K,
      ψ.symm (proj 3 K t) = slToPsl (p ^ f) K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
  have hcoe : ∀ s : SpecialLinearGroup (Fin 3) K,
      α (slToPsl (p ^ f) K s) = ψ.symm (α' (proj 3 K s)) := by
    intro s
    rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hproj,
      MulEquiv.symm_apply_apply]
  have hslPi : ∀ s (hs : s ∈ slPi true 3 (p ^ f) K),
      projOf _ ⟨s, hs⟩ = slToPsl (p ^ f) K (slPiTrueEquiv (p ^ f) K ⟨s, hs⟩) := by
    intro s hs
    change projOf _ ⟨s, hs⟩ = projOf _ ((slPiTrueEquiv (p ^ f) K).symm
      (slPiTrueEquiv (p ^ f) K ⟨s, hs⟩))
    rw [MulEquiv.symm_apply_apply]
  by_cases hD : α' ∈ linearAutGroup 3 K
  · left
    obtain ⟨A, hA⟩ := (mem_linearAutGroup_iff (n := 3) (K := K)).mp hD
    refine ⟨A, mem_glPi_true _ _, fun m => ?_⟩
    obtain ⟨s, rfl⟩ := slToPsl_surjective (K := K) (p ^ f) m
    rw [hcoe, ← hA, conjAut_proj, hproj, coe_slToPsl, coe_slToPsl, toGL_slConjugation, map_mul,
      map_mul, map_inv]
  · right
    obtain ⟨σ, hσ3, H, hαH⟩ := linear_order_three_field_descent le_rfl α' hα'3 hD
    obtain ⟨h3f, hσc⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime hK.one_le
      (hK.card : Nat.card K = p ^ f) hσ3
    obtain ⟨f₀, rfl⟩ := h3f
    have hf₀ : 3 * f₀ / 3 = f₀ := by omega
    have hf₀' : 2 * (3 * f₀) / 3 = 2 * f₀ := by omega
    refine ⟨f₀, rfl, σ, ?_, H * frobGL σ H⁻¹, mem_glPi_true _ _, fun s hs => ?_⟩
    · rcases hσc with h | h
      · exact Or.inl fun c => by rw [h, hf₀]; rfl
      · exact Or.inr fun c => by
          rw [h, hf₀']
          change c ^ p ^ (2 * f₀) = c ^ (p ^ f₀) ^ 2
          rw [← pow_mul, mul_comm]
    · rw [hslPi s hs, hcoe, hαH, MulAut.mul_apply, MulAut.mul_apply, ← map_inv, conjAut_proj,
        fieldAut_proj, conjAut_proj, hproj, coe_slToPsl, toGL_slConjugation, toGL_map_eq_frobGL,
        toGL_slConjugation, toGL_slPiTrueEquiv, inv_inv, conj_frobGL_conj]

end DichotomyLinear

section DichotomyUnitary

variable {K : Type} [Field K] {p f : ℕ}

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem aut_pgl_or_field_unitary (hK : PiField false p f K) (hq2 : 2 < p ^ f)
    (α : MulAut (projImage (slPi false 3 (p ^ f) K))) (hα3 : α ^ 3 = 1) :
    (∃ y ∈ glPi false 3 (p ^ f) K, ∀ m : projImage (slPi false 3 (p ^ f) K),
        (α m : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹) ∨
    (∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
      ((∀ c, σ c = c ^ piCard false (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard false (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi false 3 (p ^ f) K, ∀ s (hs : s ∈ slPi false 3 (p ^ f) K),
        (α (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹)) := by
  have h := hK.unitary
  have := hK.finite
  set ψ := psuEquivUnitary h with hψ
  set α' := MulAut.congr ψ α with hα'
  have hα'3 : α' ^ 3 = 1 := by
    rw [hα', ← map_pow, hα3, map_one]
  have hproj : ∀ t : unitarySU p f K 3, ψ.symm (unitaryProj h 3 t) = suToPsu p f K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
  have hcoe : ∀ s : unitarySU p f K 3,
      α (suToPsu p f K s) = ψ.symm (α' (unitaryProj h 3 s)) := by
    intro s
    rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hproj,
      MulEquiv.symm_apply_apply]
  have hslPi : ∀ s (hs : s ∈ slPi false 3 (p ^ f) K),
      projOf _ ⟨s, hs⟩ = suToPsu p f K ⟨s, hs⟩ := fun s hs => rfl
  by_cases hD : α' ∈ (psuConj h).range
  · left
    obtain ⟨A, hA⟩ := hD
    refine ⟨A, (mem_glPi_false h).mpr A.2, fun m => ?_⟩
    obtain ⟨s, rfl⟩ := suToPsu_surjective (p := p) (f := f) (K := K) m
    rw [hcoe, ← hA, psuConj_unitaryProj, hproj, coe_suToPsu, coe_suToPsu, coe_suConj, map_mul,
      map_mul, Subgroup.coe_inv, map_inv]
  · right
    obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq2 α' hα'3 hD
    have hcard : Nat.card K = p ^ (2 * f) := by
      rw [hK.card]
      change (p ^ f) ^ 2 = p ^ (2 * f)
      rw [← pow_mul, mul_comm]
    obtain ⟨h3f, hσc⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime (by
      have := hK.one_le; omega) hcard hσ3
    obtain ⟨f₀, rfl⟩ : 3 ∣ f := by
      have hc : Nat.Coprime 3 2 := by norm_num
      exact hc.dvd_of_dvd_mul_left h3f
    have hf₀ : 2 * (3 * f₀) / 3 = 2 * f₀ := by omega
    have hf₀' : 2 * (2 * (3 * f₀)) / 3 = 4 * f₀ := by omega
    have hH : (H : GL (Fin 3) K) * frobGL σ (H : GL (Fin 3) K)⁻¹ ∈
        glPi false 3 (p ^ (3 * f₀)) K := by
      refine (mem_glPi_false h).mpr ?_
      rw [← mem_unitaryIsom3]
      exact mul_mem H.2 (glAut_mem_unitaryIsom3 σ (inv_mem H.2))
    refine ⟨f₀, rfl, σ, ?_, _, hH, fun s hs => ?_⟩
    · rcases hσc with hc | hc
      · exact Or.inl fun c => by
          rw [hc, hf₀]
          change c ^ p ^ (2 * f₀) = c ^ (p ^ f₀) ^ 2
          rw [← pow_mul, mul_comm]
      · exact Or.inr fun c => by
          rw [hc, hf₀']
          change c ^ p ^ (4 * f₀) = c ^ ((p ^ f₀) ^ 2) ^ 2
          rw [← pow_mul, ← pow_mul]
          ring_nf
    · rw [hslPi s hs, hcoe, hαH, MulAut.mul_apply, MulAut.mul_apply, ← map_inv,
        psuConj_unitaryProj, psuField_unitaryProj, psuConj_unitaryProj, hproj, coe_suToPsu,
        coe_suConj, coe_suField, coe_suConj, glAut_eq_frobGL, ← conj_frobGL_conj]
      simp only [Subgroup.coe_inv, inv_inv]

end DichotomyUnitary

section Dichotomy

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem aut_pgl_or_field (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    (α : MulAut (projImage (slPi π 3 (p ^ f) K))) (hα3 : α ^ 3 = 1) :
    (∃ y ∈ glPi π 3 (p ^ f) K, ∀ m : projImage (slPi π 3 (p ^ f) K),
        (α m : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹) ∨
    (∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
      ((∀ c, σ c = c ^ piCard π (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard π (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi π 3 (p ^ f) K, ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
        (α (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹)) := by
  cases π
  · exact aut_pgl_or_field_unitary hK hq2 α hα3
  · exact aut_pgl_or_field_linear hK α hα3

end Dichotomy

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
