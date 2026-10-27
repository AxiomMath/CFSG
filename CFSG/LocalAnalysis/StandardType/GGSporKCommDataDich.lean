module

public import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import Mathlib

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Monster.B.Pinned
open scoped commutatorElement Matrix

variable {G : Type*} [Group G]

private theorem gkdi_coord_pow {p n : ℕ} [NeZero p] {q : Fin n → G} {z : G}
    {M : Matrix (Fin n) (Fin n) (ZMod p)} (hD : CommData p q z M) {g : G}
    (hg : g ∈ Subgroup.closure (Set.range q)) (k : ℕ) :
    coord p q z M (g ^ k) = k • coord p q z M g := by
  induction k with
  | zero => rw [pow_zero, hD.coord_one, zero_smul]
  | succ k ih =>
    rw [pow_succ, hD.coord_mul (pow_mem hg k) hg, ih, succ_nsmul]

theorem commData_dich_of_irred {p n : ℕ} [Fact p.Prime] [Finite G] {q : Fin n → G} {z : G}
    {M : Matrix (Fin n) (Fin n) (ZMod p)} (hD : CommData p q z M) {i₀ j₀ : Fin n}
    (hz : bcomm (q i₀) (q j₀) = z) {k : ℕ} (a : Fin k → G)
    (ha : ∀ i j, (a i)⁻¹ * q j * a i ∈ Subgroup.closure (Set.range q))
    (hirr : ∀ W : Submodule (ZMod p) (Fin n → ZMod p),
      (∀ i, ∀ v ∈ W, v ᵥ* CommData.actMat p q z M (a i) ∈ W) → W = ⊥ ∨ W = ⊤)
    (N : Subgroup G) (hNQ : N ≤ Subgroup.closure (Set.range q))
    (hN : ∀ i, a i ∈ Subgroup.normalizer (N : Set G)) :
    N ≤ Subgroup.zpowers z ∨ N = Subgroup.closure (Set.range q) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hinv : ∀ i, ∀ g ∈ N, (a i)⁻¹ * g * a i ∈ N := by
    intro i g hg
    have h1 : (a i)⁻¹ ∈ Subgroup.normalizer (N : Set G) := inv_mem (hN i)
    have := (Subgroup.mem_normalizer_iff.1 h1 g).1 hg
    simpa using this
  let W : Submodule (ZMod p) (Fin n → ZMod p) :=
    { carrier := {v | ∃ g ∈ N, coord p q z M g = v}
      add_mem' := by
        rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
        exact ⟨g * h, N.mul_mem hg hh, hD.coord_mul (hNQ hg) (hNQ hh)⟩
      zero_mem' := ⟨1, N.one_mem, hD.coord_one⟩
      smul_mem' := by
        rintro c _ ⟨g, hg, rfl⟩
        refine ⟨g ^ c.val, N.pow_mem hg _, ?_⟩
        rw [gkdi_coord_pow hD (hNQ hg), ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val] }
  have hW : ∀ i, ∀ v ∈ W, v ᵥ* CommData.actMat p q z M (a i) ∈ W := by
    rintro i _ ⟨g, hg, rfl⟩
    exact ⟨(a i)⁻¹ * g * a i, hinv i g hg, hD.coord_conj (ha i) (hNQ hg)⟩
  have hker : ∀ g ∈ Subgroup.closure (Set.range q), coord p q z M g = 0 →
      g ∈ Subgroup.zpowers z := by
    intro g hg h0
    have : (⟨g, hg⟩ : Subgroup.closure (Set.range q)) ∈ hD.coordHom.ker := by
      rw [MonoidHom.mem_ker, CommData.coordHom_apply]
      show Multiplicative.ofAdd (coord p q z M g) = 1
      rw [h0]; rfl
    rw [hD.ker_coordHom] at this
    exact Subgroup.mem_subgroupOf.1 this
  rcases hirr W hW with h | h
  · left
    intro g hg
    refine hker g (hNQ hg) ?_
    have : coord p q z M g ∈ W := ⟨g, hg, rfl⟩
    rw [h] at this
    exact this
  · right
    have hsplit : ∀ g ∈ Subgroup.closure (Set.range q), ∃ m ∈ N, ∃ y ∈ Subgroup.zpowers z,
        g = m * y := by
      intro g hg
      have : coord p q z M g ∈ W := by rw [h]; trivial
      obtain ⟨m, hm, hmg⟩ := this
      refine ⟨m, hm, m⁻¹ * g, ?_, by group⟩
      apply hker _ (mul_mem (inv_mem (hNQ hm)) hg)
      rw [hD.coord_mul (inv_mem (hNQ hm)) hg, hD.coord_inv (hNQ hm), hmg]
      abel
    obtain ⟨m₁, hm₁, y₁, hy₁, e₁⟩ := hsplit (q i₀) (Subgroup.subset_closure ⟨i₀, rfl⟩)
    obtain ⟨m₂, hm₂, y₂, hy₂, e₂⟩ := hsplit (q j₀) (Subgroup.subset_closure ⟨j₀, rfl⟩)
    have hzN : z ∈ N := by
      have hQ1 : m₁ ∈ Subgroup.closure (Set.range q) := hNQ hm₁
      have hQ2 : m₂ ∈ Subgroup.closure (Set.range q) := hNQ hm₂
      have hy1Q : y₁ ∈ Subgroup.closure (Set.range q) :=
        Subgroup.zpowers_le.2 hD.mem_z hy₁
      have hy2Q : y₂ ∈ Subgroup.closure (Set.range q) :=
        Subgroup.zpowers_le.2 hD.mem_z hy₂
      have hb1 : ∀ k : G, k ∈ Subgroup.closure (Set.range q) → bcomm y₁ k = 1 := fun k hk =>
        bcomm_eq_one_iff.2 (hD.commute_of_mem hk hy₁).symm
      have hb2 : ∀ k : G, k ∈ Subgroup.closure (Set.range q) → bcomm y₂ k = 1 := fun k hk =>
        bcomm_eq_one_iff.2 (hD.commute_of_mem hk hy₂).symm
      have hc1 : bcomm (m₁ * y₁) (m₂ * y₂) = bcomm m₁ (m₂ * y₂) := by
        rw [hD.bcomm_mul hQ1 hy1Q (mul_mem hQ2 hy2Q), hb1 _ (mul_mem hQ2 hy2Q), mul_one]
      have hc2 : bcomm m₁ (m₂ * y₂) = bcomm m₁ m₂ := by
        rw [bcomm_swap, hD.bcomm_mul hQ2 hy2Q hQ1, hb2 _ hQ1, mul_one, ← bcomm_swap]
      have : z = bcomm m₁ m₂ := by
        rw [← hz, e₁, e₂, hc1, hc2]
      rw [this]
      simp only [bcomm]
      exact N.mul_mem (N.mul_mem (N.mul_mem (N.inv_mem hm₁) (N.inv_mem hm₂)) hm₁) hm₂
    apply le_antisymm hNQ
    intro g hg
    obtain ⟨m, hm, y, hy, rfl⟩ := hsplit g hg
    exact N.mul_mem hm (Subgroup.zpowers_le.2 hzN hy)

end CFSG.StandardType.SporadicShape
