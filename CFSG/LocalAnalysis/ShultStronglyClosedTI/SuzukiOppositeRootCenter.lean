module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiOppositeRootRestriction

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open SuzukiModel SuzukiLayerKernel

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem pow_two_pow_succ_add_one_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective fun y : K => y ^ (2 ^ (a + 1) + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -⟩ := suzuki_frobenius_exponents a K hK
  have hn : 2 ^ (a + 1) + 1 ≠ 0 := Nat.succ_ne_zero _
  intro y y' h
  simp only at h
  by_cases hy : y = 0
  · rw [hy, zero_pow hn] at h
    rw [hy, (pow_eq_zero_iff hn).1 h.symm]
  by_cases hy' : y' = 0
  · rw [hy', zero_pow hn] at h
    exact hy.elim ((pow_eq_zero_iff hn).1 h)
  have hz : ∀ c : Kˣ, c ^ (2 ^ (a + 1) + 1 : ℤ) = c ^ (2 ^ (a + 1) + 1) := fun c => by
    exact_mod_cast zpow_natCast c (2 ^ (a + 1) + 1)
  have e := @hbij.1 (Units.mk0 y hy) (Units.mk0 y' hy') (by
    simp only [hz]
    exact Units.ext (by simpa using h))
  simpa using congrArg Units.val e

theorem suzukiSElt_sq (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) :
    suzukiSElt a K u v ^ 2 = suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) :=
  congrArg (fun x : suzukiU a K => (x : suzukiGroup a K))
    (SuzukiRootAutomorphism.unipotentElt_sq hK u v)

theorem suzuki_opposite_root_center_action_faithful (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (γ : MulAut (suzukiGroup a K))
    (hγU : (suzukiU a K).map γ.toMonoidHom = suzukiU a K)
    (hγU' : ((suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom).map γ.toMonoidHom =
      (suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom)
    (hγQ : ∀ b : K, γ (suzukiSElt a K 0 b) = suzukiSElt a K 0 b) : γ = 1 := by
  have hZ : ∀ v ∈ suzukiZ0 a K, γ v = v := fun v hv => by
    obtain ⟨b, rfl⟩ := (mem_suzukiZ0_iff hK).1 hv
    exact hγQ b
  have hUZ : ∀ x ∈ suzukiU a K, x⁻¹ * γ x ∈ suzukiZ0 a K := by
    intro x hx
    have hγx : γ x ∈ suzukiU a K := by
      rw [← hγU]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
    obtain ⟨u', v', hu'⟩ := (mem_suzukiU_iff hK).1 hγx
    have hsq := congrArg (· ^ 2) hu'
    simp only [← map_pow, suzukiSElt_sq hK, hγQ, suzukiSElt_inj] at hsq
    obtain rfl := pow_two_pow_succ_add_one_injective hK hsq.2
    rw [← hu']
    exact suzukiSElt_inv_mul_mem_suzukiZ0 hK _ _ _
  obtain ⟨s, hs, hγs⟩ := suzuki_rank_one_Sylow_layer_kernel ha hK
    ((suzukiU_isPGroup_index hK).1.toSylow (suzukiU_isPGroup_index hK).2) (suzukiZ0 a K)
    (map_omega₁_suzukiU hK).symm γ hγU hZ hUZ
  exact suzuki_opposite_pair_inner_root_restriction_rigidity ha hK γ hγU hγU'
    ⟨s, hs, fun x _ => by rw [hγs, MulAut.conj_apply]⟩

end CFSG.ShultStronglyClosedTI
