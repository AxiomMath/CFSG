module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Core

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique

theorem exists_conj_of_isSylowTwoOf_top {Γ : Type*} [Group Γ] [Finite Γ] {S₁ S₂ : Subgroup Γ}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : Γ, S₂ = S₁.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowTwoOf_top_iff] at h₁ h₂
  let P₁ : Sylow 2 Γ := h₁.1.toSylow h₁.2
  let P₂ : Sylow 2 Γ := h₂.1.toSylow h₂.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P₁ P₂
  refine ⟨g, ?_⟩
  have h3 : ((g • P₁ : Sylow 2 Γ) : Subgroup Γ) = S₂ := by rw [hg]; rfl
  rw [← h3, Sylow.coe_subgroup_smul]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact ⟨y, hy, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  · rintro ⟨y, hy, rfl⟩
    refine (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, hy, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply]

theorem NoFiveIndex.of_sylow {Γ : Type*} [Group Γ] [Finite Γ] {S₁ : Subgroup Γ}
    (hS₁ : IsSylowTwoOf S₁ ⊤)
    (h : ∀ U : Subgroup Γ, S₁ ≤ U → ∀ b : ℕ, S₁.relIndex U = 5 ^ b → b = 0) : NoFiveIndex Γ := by
  intro S₀ U hS₀ hle b hb
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hS₀ hS₁
  refine h (U.map (MulAut.conj g).toMonoidHom) ?_ b ?_
  · rw [hg]
    exact Subgroup.map_mono hle
  · rw [hg, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hb

theorem card_eq_relIndex_mul {Γ : Type*} [Group Γ] {S U : Subgroup Γ} (h : S ≤ U) :
    Nat.card U = S.relIndex U * Nat.card S := by
  rw [← Subgroup.relIndex_mul_card (H := S) (K := U), inf_of_le_left h]

theorem lt_five_of_five_pow_le {b : ℕ} (h : 5 ^ b ≤ 2520) : b < 5 := by
  by_contra hb
  have := Nat.pow_le_pow_right (by norm_num : 0 < 5) (not_lt.mp hb)
  norm_num at this
  omega

theorem NoFiveIndex.of_card_overgroups {Γ : Type*} [Group Γ] [Finite Γ] {S₁ : Subgroup Γ}
    (hS₁ : IsSylowTwoOf S₁ ⊤) {s : ℕ} (hs : Nat.card S₁ = s) (hs0 : 0 < s) (L : List ℕ)
    (hL : ∀ U : Subgroup Γ, S₁ ≤ U → Nat.card U ∈ L) (hle : ∀ x ∈ L, x ≤ 2520)
    (hcheck : ∀ c < 5, 0 < c → 5 ^ c * s ∉ L) : NoFiveIndex Γ := by
  refine NoFiveIndex.of_sylow hS₁ fun U hU b hb => ?_
  by_contra h0
  have hcard : Nat.card U = 5 ^ b * s := by rw [card_eq_relIndex_mul hU, hb, hs]
  have hmem := hL U hU
  have h1 := hle _ hmem
  rw [hcard] at h1 hmem
  have hb5 : b < 5 := lt_five_of_five_pow_le (le_trans (Nat.le_mul_of_pos_right _ hs0) h1)
  exact hcheck b hb5 (Nat.pos_of_ne_zero h0) hmem

end CFSG.Quasithin.H23P4
