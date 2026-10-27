module

public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProofL34Model

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Type

open CFSG CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProof (stdSylow stdTorus cycBar)
open Matrix

variable {K : Type} [Field K]

theorem exists_conj_of_pow_three [Finite K] (hK4 : Nat.card K = 4) {q : ℕ}
    (β : MulAut (projImage (slPi true 3 q K))) (hβ : β ^ 3 = 1) :
    ∃ y : GL (Fin 3) K, ∀ m : projImage (slPi true 3 q K),
      ((β m : projImage (slPi true 3 q K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * (m : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹ := by
  set ψ := pslEquivProjective q K with hψ
  set α := MulAut.congr ψ β with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hβ, map_one]
  have hD : α ∈ linearAutGroup 3 K := by
    by_contra hD
    obtain ⟨σ, hσ3, -⟩ := KFacts.linear_order_three_field_descent le_rfl α hα3 hD
    obtain ⟨h3f, -⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two
      (f := 2) (by norm_num) (by rw [hK4]; norm_num) hσ3
    omega
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hD
  refine ⟨A, fun m => ?_⟩
  have hproj : ∀ t : SpecialLinearGroup (Fin 3) K, ψ.symm (proj 3 K t) = slToPsl q K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
  obtain ⟨s, rfl⟩ := slToPsl_surjective (K := K) q m
  have hcoe : β (slToPsl q K s) = ψ.symm (α (proj 3 K s)) := by
    rw [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hproj]
  rw [hcoe, ← hA, conjAut_proj, hproj, coe_slToPsl, coe_slToPsl, toGL_slConjugation, map_mul,
    map_mul, map_inv]

theorem not_comm_stdSylow {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ¬ ∀ a ∈ stdSylow K, ∀ b ∈ stdSylow K, a * b = b * a := by
  intro h
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set t : Kˣ := Units.mk0 τ hτ0 with ht
  have htmem : diagHom (t, 1, 1) ∈ stdTypeC K := by
    refine ⟨(t, 1, 1), ⟨?_, one_mem _, one_mem _⟩, rfl⟩
    change t ∈ rootsOfUnity 3 K
    rw [mem_rootsOfUnity]
    exact Units.ext (by simp [ht, hτ])
  have hs : ProjGenLinGroup.mk (diagHom (t, 1, 1)) ∈ stdSylow K :=
    Subgroup.mem_sup_left ⟨_, htmem, rfl⟩
  have hc : cycBar K ∈ stdSylow K := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have h1 := h _ hc _ hs
  have h2 : ProjGenLinGroup.mk (cycThree * diagUnits t 1 1 * cycThree⁻¹) =
      ProjGenLinGroup.mk (diagUnits t 1 1 : GL (Fin 3) K) := by
    rw [map_mul, map_mul, map_inv]
    change cycBar K * ProjGenLinGroup.mk (diagHom (t, 1, 1)) * (cycBar K)⁻¹ = _
    rw [h1, mul_inv_cancel_right]
    rfl
  rw [cycThree_conj_diagUnits] at h2
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h2
  have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  have e2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hu
  simp [coe_diagUnits, Matrix.mul_apply, Fin.sum_univ_three, ht] at e0 e2
  apply hτ1
  rw [← e0, e2, Units.val_one]

end CFSG.RankThree.PartTwo.Sec16.Proof1613Type
