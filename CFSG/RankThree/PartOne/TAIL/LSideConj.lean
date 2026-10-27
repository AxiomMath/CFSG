module

public import CFSG.RankThree.PartOne.TAIL.LSideIrr
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup
open scoped Pointwise

section Sylow

variable {M : Type*} [Group M] [Finite M]

theorem exists_sylow_card_forty_nine (hM : ¬ 7 ^ 3 ∣ Nat.card M) (H : Subgroup M)
    (hH : Nat.card H = 49) : ∃ P : Sylow 7 M, (P : Subgroup M) = H := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp : IsPGroup 7 H := IsPGroup.of_card (n := 2) (by rw [hH]; norm_num)
  obtain ⟨P, hHP⟩ := hp.exists_le_sylow
  refine ⟨P, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have h1 : 7 ^ k ∣ Nat.card M := hk ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup M)
  have h2 : 7 ^ 2 ∣ 7 ^ k := by
    have := Subgroup.card_dvd_of_le hHP
    rwa [hH, hk] at this
  have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have hk3 : k ≤ 2 := by
    by_contra hk3
    exact hM ((Nat.pow_dvd_pow 7 (by omega : 3 ≤ k)).trans h1)
  have hkk : k = 2 := le_antisymm hk3 hk2
  exact (Subgroup.eq_of_le_of_card_ge hHP (by rw [hH, hk, hkk]; norm_num)).symm

theorem exists_conj_of_card_forty_nine (hM : ¬ 7 ^ 3 ∣ Nat.card M) {B₀ B : Subgroup M}
    (h₀ : Nat.card B₀ = 49) (h : Nat.card B = 49) :
    ∃ u : M, ∀ x : M, x ∈ B ↔ u⁻¹ * x * u ∈ B₀ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_card_forty_nine hM B₀ h₀
  obtain ⟨P, hP⟩ := exists_sylow_card_forty_nine hM B h
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P₀ P
  have hconj : B₀.map (MulAut.conj g).toMonoidHom = B := by
    rw [← hP, ← hg, ← hP₀, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, fun x => ?_⟩
  rw [← hconj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

variable {B₀ B : Subgroup M} {u : M}

omit [Finite M] in
theorem irr_of_conj (hu : ∀ x : M, x ∈ B ↔ u⁻¹ * x * u ∈ B₀)
    (hI : ∀ d ∈ B₀, d ≠ 1 → ∃ g ∈ Subgroup.normalizer (B₀ : Set M),
      g * d * g⁻¹ ∉ Subgroup.zpowers d) :
    ∀ d ∈ B, d ≠ 1 → ∃ g ∈ Subgroup.normalizer (B : Set M),
      g * d * g⁻¹ ∉ Subgroup.zpowers d := by
  intro d hd hd1
  have hd0 : u⁻¹ * d * u ∈ B₀ := (hu d).1 hd
  have hd01 : u⁻¹ * d * u ≠ 1 := by
    intro h
    apply hd1
    have : d = u * (u⁻¹ * d * u) * u⁻¹ := by group
    rw [this, h]
    group
  obtain ⟨g₀, hg₀, hng⟩ := hI _ hd0 hd01
  refine ⟨u * g₀ * u⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hg₀ ⊢
    intro x
    rw [hu x, hu (u * g₀ * u⁻¹ * x * (u * g₀ * u⁻¹)⁻¹)]
    have : u⁻¹ * (u * g₀ * u⁻¹ * x * (u * g₀ * u⁻¹)⁻¹) * u = g₀ * (u⁻¹ * x * u) * g₀⁻¹ := by
      group
    rw [this]
    exact hg₀ _
  · intro hmem
    apply hng
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    have h1 : (MulAut.conj u⁻¹) (d ^ m) = ((MulAut.conj u⁻¹) d) ^ m := map_zpow _ _ _
    rw [MulAut.conj_apply, MulAut.conj_apply] at h1
    have h2 := congrArg (fun y => u⁻¹ * y * u) hm
    simp only [inv_inv] at h1
    calc (u⁻¹ * d * u) ^ m = u⁻¹ * d ^ m * u := h1.symm
      _ = u⁻¹ * (u * g₀ * u⁻¹ * d * (u * g₀ * u⁻¹)⁻¹) * u := h2
      _ = g₀ * (u⁻¹ * d * u) * g₀⁻¹ := by group

theorem aut_pm_of_conj {δ : MulAut M} (hu : ∀ x : M, x ∈ B ↔ u⁻¹ * x * u ∈ B₀)
    (hδ : ∀ b ∈ B₀, δ b = b⁻¹)
    (hAut : ∀ β : MulAut M, ∃ (g : M) (ε : ℕ), ε ≤ 1 ∧ β = MulAut.conj g * δ ^ ε)
    (α : MulAut M) (hα : ∀ x : M, x ∈ B ↔ α x ∈ B) :
    ∃ l ∈ Subgroup.normalizer (B : Set M),
      (∀ x ∈ B, l * α x * l⁻¹ = x) ∨ (∀ x ∈ B, l * α x * l⁻¹ = x⁻¹) := by
  obtain ⟨g, ε, hε, hαg⟩ := hAut α
  interval_cases ε
  · have hαx : ∀ x, α x = g * x * g⁻¹ := by
      intro x
      rw [hαg, pow_zero, mul_one]
      rfl
    have hgN : g ∈ Subgroup.normalizer (B : Set M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hα x, hαx]
    refine ⟨g⁻¹, Subgroup.inv_mem _ hgN, Or.inl fun x _ => ?_⟩
    rw [hαx]
    group
  · have hαx : ∀ x, α x = g * δ x * g⁻¹ := by
      intro x
      rw [hαg, pow_one]
      rfl
    set w : M := g * δ u * u⁻¹ with hw
    have hαB : ∀ x ∈ B, α x = w * x⁻¹ * w⁻¹ := by
      intro x hx
      have hb : u⁻¹ * x * u ∈ B₀ := (hu x).1 hx
      have hδb := hδ _ hb
      have hδx : δ x = δ u * (u⁻¹ * x * u)⁻¹ * (δ u)⁻¹ := by
        calc δ x = δ (u * (u⁻¹ * x * u) * u⁻¹) := by congr 1; group
          _ = δ u * δ (u⁻¹ * x * u) * (δ u)⁻¹ := by rw [map_mul, map_mul, map_inv]
          _ = δ u * (u⁻¹ * x * u)⁻¹ * (δ u)⁻¹ := by rw [hδb]
      rw [hαx, hδx, hw]
      group
    have hwN : w ∈ Subgroup.normalizer (B : Set M) := by
      refine mem_normalizer_of_conj_mem' fun b hb => ?_
      have h1 : α b⁻¹ = w * b * w⁻¹ := by
        rw [hαB _ (Subgroup.inv_mem _ hb), inv_inv]
      rw [← h1]
      exact (hα _).1 (Subgroup.inv_mem _ hb)
    refine ⟨w⁻¹, Subgroup.inv_mem _ hwN, Or.inr fun x hx => ?_⟩
    rw [hαB x hx]
    group

end Sylow

end CFSG.RankThree.PartOne.TAIL
