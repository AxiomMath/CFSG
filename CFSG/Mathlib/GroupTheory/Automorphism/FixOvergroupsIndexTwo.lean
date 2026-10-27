module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.GroupTheory.AutomorphismAction

open Subgroup

private theorem map_conj_eq_self_of_mem {K : Type*} [Group K] {X : Subgroup K} {n : K}
    (hn : n ∈ X) : X.map (MulAut.conj n).toMonoidHom = X := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    change MulAut.conj n x ∈ X
    rw [MulAut.conj_apply]
    exact X.mul_mem (X.mul_mem hn hx) (X.inv_mem hn)
  · rintro y hy
    refine ⟨n⁻¹ * y * n, X.mul_mem (X.mul_mem (X.inv_mem hn) hy) hn, ?_⟩
    change MulAut.conj n (n⁻¹ * y * n) = y
    rw [MulAut.conj_apply]
    group

private theorem conj_injective_of_center_eq_bot {K : Type*} [Group K]
    (hZ : center K = ⊥) : Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro x y hxy
  have h : ∀ g : K, x * y⁻¹ * g = g * (x * y⁻¹) := by
    intro g
    have h1 := congrArg (fun α : MulAut K => α (y⁻¹ * g * y)) hxy
    simp only [MulAut.conj_apply] at h1
    calc x * y⁻¹ * g = (x * (y⁻¹ * g * y) * x⁻¹) * x * y⁻¹ := by group
      _ = (y * (y⁻¹ * g * y) * y⁻¹) * x * y⁻¹ := by rw [h1]
      _ = g * (x * y⁻¹) := by group
  have hmem : x * y⁻¹ ∈ center K := Subgroup.mem_center_iff.mpr fun g => (h g).symm
  rw [hZ, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

private def fixingSubgroup {K : Type*} [Group K] (N : Subgroup (MulAut K))
    (𝒳 : Set (Subgroup K)) : Subgroup (MulAut K) where
  carrier := {α | α ∈ N ∧ ∀ X ∈ 𝒳, X.map α.toMonoidHom = X}
  mul_mem' := by
    rintro α β ⟨hαN, hα⟩ ⟨hβN, hβ⟩
    refine ⟨N.mul_mem hαN hβN, fun X hX => ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe] at hα hβ ⊢
    rw [MulAut.mul_def, MulEquiv.toMonoidHom_trans, ← Subgroup.map_map, hβ X hX, hα X hX]
  one_mem' := by
    refine ⟨N.one_mem, fun X _ => ?_⟩
    simp [MulAut.one_def]
  inv_mem' := by
    rintro α ⟨hαN, hα⟩
    refine ⟨N.inv_mem hαN, fun X hX => ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe] at hα ⊢
    simpa only [MulAut.inv_def] using
      (Subgroup.map_symm_eq_iff_map_eq (e := α) (H := X) (K := X)).mpr (hα X hX)

theorem map_eq_of_card_le_two_mul_card_normalizer {K : Type*} [Group K] [Finite K]
    (hZ : center K = ⊥) {T : Subgroup K} {N : Subgroup (MulAut K)}
    (hTN : ∀ n ∈ normalizer (T : Set K), MulAut.conj n ∈ N)
    (hN : Nat.card N ≤ 2 * Nat.card (normalizer (T : Set K)))
    {𝒳 : Set (Subgroup K)} (h𝒳 : ∀ X ∈ 𝒳, normalizer (T : Set K) ≤ X)
    {φ : MulAut K} (hφN : φ ∈ N) (hφ : φ ∉ (MulAut.conj : K →* MulAut K).range)
    (hφ𝒳 : ∀ X ∈ 𝒳, X.map φ.toMonoidHom = X) {α : MulAut K} (hα : α ∈ N)
    {X : Subgroup K} (hX : X ∈ 𝒳) : X.map α.toMonoidHom = X := by
  let N₀ : Subgroup K := normalizer (T : Set K)
  let V : Subgroup (MulAut K) := N₀.map (MulAut.conj : K →* MulAut K)
  let F : Subgroup (MulAut K) := fixingSubgroup N 𝒳
  have hconj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    conj_injective_of_center_eq_bot hZ
  have hcardV : Nat.card V = Nat.card N₀ := Subgroup.card_map_of_injective hconj
  have hVF : V ≤ F := by
    intro α hα
    obtain ⟨n, hn, rfl⟩ := hα
    exact ⟨hTN n hn, fun Y hY => map_conj_eq_self_of_mem (h𝒳 Y hY hn)⟩
  have hφF : φ ∈ F := ⟨hφN, hφ𝒳⟩
  have hφV : φ ∉ V := by
    intro h
    obtain ⟨n, _, rfl⟩ := h
    exact hφ ⟨n, rfl⟩
  have hVFne : V ≠ F := by
    intro h
    exact hφV (h.symm ▸ hφF)
  have hVltF : V < F := lt_of_le_of_ne hVF hVFne
  have hdvd : Nat.card V ∣ Nat.card F := Subgroup.card_dvd_of_le hVF
  have hlt : Nat.card V < Nat.card F := Subgroup.card_lt_of_lt hVltF
  have h2 : 2 * Nat.card V ≤ Nat.card F := by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have hk1 : k ≤ 1 := Nat.lt_succ_iff.mp (Nat.not_le.mp hk2)
      have hle : Nat.card V * k ≤ Nat.card V * 1 := Nat.mul_le_mul le_rfl hk1
      rw [Nat.mul_one, ← hk] at hle
      exact (not_lt_of_ge hle) hlt
    calc 2 * Nat.card V = Nat.card V * 2 := Nat.mul_comm _ _
      _ ≤ Nat.card V * k := Nat.mul_le_mul le_rfl hk2
      _ = Nat.card F := hk.symm
  have hFN : F ≤ N := fun _ hα => hα.1
  have hNF : Nat.card N ≤ Nat.card F := by
    calc Nat.card N ≤ 2 * Nat.card N₀ := hN
      _ = 2 * Nat.card V := by rw [hcardV]
      _ ≤ Nat.card F := h2
  have hFN_eq : F = N := Subgroup.eq_of_le_of_card_ge hFN hNF
  have hαF : α ∈ F := hFN_eq.symm ▸ hα
  exact hαF.2 X hX

end CFSG.GroupTheory.AutomorphismAction
