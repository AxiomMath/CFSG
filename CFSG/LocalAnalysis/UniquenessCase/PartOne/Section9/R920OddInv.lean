module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.RepresentationTheory.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC6Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_of_fixed_of_inv {U W W₂ A : Subgroup G} {r p : ℕ} [Fact p.Prime] (hr : Odd r)
    (hpow : ∀ u ∈ U, u ^ r ∈ W) (hWU : W ≤ U) (hW₂W : W₂ ≤ W)
    (hWn : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W) (hW₂n : ∀ u ∈ U, ∀ w ∈ W₂, u * w * u⁻¹ ∈ W₂)
    (hAp : IsPGroup p A) (hp : ¬ p ∣ Nat.card W₂) (hAW₂ : ∀ a ∈ A, ∀ w ∈ W₂, a * w * a⁻¹ ∈ W₂)
    {t : G} (htU : ∀ u ∈ U, t * u * t⁻¹ ∈ U) (htA : ∀ a ∈ A, a * t = t * a)
    (htW : ∀ w ∈ W, w * t * w⁻¹ * t⁻¹ ∈ W₂) (htinv : ∀ u ∈ U, u * (t * u * t⁻¹) ∈ W)
    (hCA : ∀ n ∈ U, (∀ a ∈ A, a * n * a⁻¹ = n) → n ∈ W) :
    ∀ u ∈ U, (∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ W) → u ∈ W := by
  intro u hu hfix
  have hyU : u * (t * u⁻¹ * t⁻¹) ∈ U := U.mul_mem hu (htU _ (U.inv_mem hu))
  have key : ∀ a ∈ A, (u * (t * u⁻¹ * t⁻¹))⁻¹ * (a * (u * (t * u⁻¹ * t⁻¹)) * a⁻¹) ∈ W₂ := by
    intro a ha
    have hat : a * t * a⁻¹ = t := by rw [htA a ha, mul_inv_cancel_right]
    have hw : u⁻¹ * (a * u * a⁻¹) ∈ W := by
      have h := hWn u⁻¹ (U.inv_mem hu) _ (hfix a ha)
      rwa [show u⁻¹ * (a * u * a⁻¹ * u⁻¹) * u⁻¹⁻¹ = u⁻¹ * (a * u * a⁻¹) by group] at h
    have h := hW₂n _ (htU u hu) _ (htW _ hw)
    have e : (u * (t * u⁻¹ * t⁻¹))⁻¹ * (a * (u * (t * u⁻¹ * t⁻¹)) * a⁻¹) =
        (u * (t * u⁻¹ * t⁻¹))⁻¹ * (a * u * a⁻¹ *
          ((a * t * a⁻¹) * (a * u * a⁻¹)⁻¹ * (a * t * a⁻¹)⁻¹)) := by group
    rw [e, hat]
    convert h using 1
    group
  obtain ⟨n, hn, hnA⟩ := UC6.exists_fixed_in_coset_uc6 A W₂ hAp hp hAW₂ _ key
  have hnU : n ∈ U := by
    have h := U.mul_mem hyU (hWU (hW₂W hn))
    rwa [mul_inv_cancel_left] at h
  have hyW : u * (t * u⁻¹ * t⁻¹) ∈ W := by
    have h := W.mul_mem (hCA n hnU hnA) (W.inv_mem (hW₂W hn))
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h
  have hu2 : u ^ 2 ∈ W := by
    have h := W.mul_mem hyW (W.inv_mem (htinv u⁻¹ (U.inv_mem hu)))
    rwa [show u * (t * u⁻¹ * t⁻¹) * (u⁻¹ * (t * u⁻¹ * t⁻¹))⁻¹ = u ^ 2 by rw [sq]; group] at h
  obtain ⟨k, rfl⟩ := hr
  have h := W.mul_mem (W.inv_mem (W.pow_mem hu2 k)) (hpow u hu)
  rwa [← pow_mul, pow_succ, inv_mul_cancel_left] at h

theorem apply_eq_neg_of_mul_self {Q k V : Type*} [Group Q] [CommRing k] [AddCommGroup V]
    [Module k V] (ρ : Representation k Q V)
    (hirr : ∀ U : Submodule k V, (∀ g : Q, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) {t : Q}
    (hc : ∀ g : Q, ρ (t * g) = ρ (g * t)) (hsq : ρ (t * t) = 1) (hne : ρ t ≠ 1) (v : V) :
    ρ t v = -v := by
  have hmem : ∀ w : V, w ∈ LinearMap.ker (ρ t - 1) ↔ ρ t w = w := fun w => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hinv : ∀ g : Q, ∀ w ∈ LinearMap.ker (ρ t - 1), ρ g w ∈ LinearMap.ker (ρ t - 1) := by
    intro g w hw
    rw [hmem] at hw ⊢
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hw]
  have hbot : LinearMap.ker (ρ t - 1) = ⊥ := by
    refine (hirr _ hinv).resolve_right fun htop => hne (LinearMap.ext fun w => ?_)
    have hw : w ∈ LinearMap.ker (ρ t - 1) := htop ▸ Submodule.mem_top
    rw [hmem] at hw
    rw [hw, Module.End.one_apply]
  have h1 : ρ t v + v ∈ LinearMap.ker (ρ t - 1) := by
    rw [hmem, map_add, ← Module.End.mul_apply, ← map_mul, hsq, Module.End.one_apply, add_comm]
  rw [hbot, Submodule.mem_bot] at h1
  exact eq_neg_of_add_eq_zero_left h1

theorem le_pCore_two_of_normal {Γ : Type*} [Group Γ] [Finite Γ]
    (hs : IsSimpleGroup (Γ ⧸ CFSG.pCore 2 Γ)) (h3 : 3 ∣ Nat.card (Γ ⧸ CFSG.pCore 2 Γ))
    {N : Subgroup Γ} [N.Normal] (hN : ¬ 3 ∣ Nat.card N) : N ≤ CFSG.pCore 2 Γ := by
  haveI := hs
  haveI : (N.map (QuotientGroup.mk' (CFSG.pCore 2 Γ))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (CFSG.pCore 2 Γ)))
    with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have hdvd := Subgroup.card_map_dvd N (QuotientGroup.mk' (CFSG.pCore 2 Γ))
    rw [h, Subgroup.card_top] at hdvd
    exact hN (h3.trans hdvd)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
