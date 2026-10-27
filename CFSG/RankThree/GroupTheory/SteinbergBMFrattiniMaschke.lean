module

public import CFSG.GH74.BNPair.L15Maschke
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup SemidirectProduct

theorem exists_invariant_complement_section {p : ℕ} [Fact p.Prime] {A P : Type*} [Group A]
    [Group P] [Finite A] [Finite P] [MulDistribMulAction A P] (hA : Nat.Coprime p (Nat.card A))
    {N W : Subgroup P} (hNW : N ≤ W) (hpow : ∀ x : P, x ^ p ∈ N)
    (hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ N) (hN : ∀ a : A, ∀ x ∈ N, a • x ∈ N)
    (hW : ∀ a : A, ∀ x ∈ W, a • x ∈ W) :
    ∃ W' : Subgroup P, N ≤ W' ∧ (∀ a : A, ∀ x ∈ W', a • x ∈ W') ∧ W ⊔ W' = ⊤ ∧ W ⊓ W' = N := by
  set ρ := MulDistribMulAction.toMulAut A P with hρ
  have : Finite (P ⋊[ρ] A) := Finite.of_equiv (P × A) SemidirectProduct.equivProd.symm
  have hconj : ∀ (a : A) (x : P),
      (inr a : P ⋊[ρ] A) * inl x * (inr a)⁻¹ = inl (a • x) := fun a x => by
    rw [← map_inv, ← inl_aut]
    rfl
  set Q : Subgroup (P ⋊[ρ] A) := (inl : P →* P ⋊[ρ] A).range with hQ
  set D : Subgroup (P ⋊[ρ] A) := (inr : A →* P ⋊[ρ] A).range with hD
  have hDcard : Nat.card D = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective inr_injective).toEquiv).symm
  obtain ⟨N₀, hΦN₀, hN₀Q, hN₀inv, hsup, hinf⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := p) (Q := Q) (Φ := N.map inl)
      (D := D) (T := W.map inl) (map_le_range _ _)
      (by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        exact ⟨x * y * x⁻¹ * y⁻¹, hcomm x y, by simp only [map_mul, map_inv]⟩)
      (by
        rintro _ ⟨x, rfl⟩
        exact ⟨x ^ p, hpow x, map_pow _ _ _⟩)
      (by rwa [hDcard])
      (by
        rintro _ ⟨a, rfl⟩ _ ⟨x, rfl⟩
        exact ⟨a • x, (hconj a x).symm⟩)
      (by
        rintro _ ⟨a, rfl⟩ _ ⟨x, hx, rfl⟩
        exact ⟨a • x, hN a x hx, (hconj a x).symm⟩)
      (map_mono hNW) (map_le_range _ _)
      (by
        rintro _ ⟨a, rfl⟩ _ ⟨x, hx, rfl⟩
        exact ⟨a • x, hW a x hx, (hconj a x).symm⟩)
  have hmap : (N₀.comap inl).map (inl : P →* P ⋊[ρ] A) = N₀ := map_comap_eq_self hN₀Q
  refine ⟨N₀.comap inl, fun n hn => hΦN₀ ⟨n, hn, rfl⟩, fun a x hx => ?_, ?_, ?_⟩
  · show inl (a • x) ∈ N₀
    rw [← hconj]
    exact hN₀inv _ ⟨a, rfl⟩ _ hx
  · apply map_injective (inl_injective (φ := ρ))
    rw [Subgroup.map_sup, hmap, hsup, ← MonoidHom.range_eq_map]
  · apply map_injective (inl_injective (φ := ρ))
    rw [map_inf_eq _ _ _ inl_injective, hmap, hinf]

end CFSG.RankThree.GroupTheory.SteinbergBM
