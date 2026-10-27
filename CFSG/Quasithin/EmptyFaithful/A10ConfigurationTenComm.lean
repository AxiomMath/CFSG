module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTenK

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem eq_u₁ {ℓ : Bool} (hCB : Subgroup.centralizer (E.B : Set G) = E.B) {c : G}
    (hcK : c ∈ E.K) (hcs : E.Acts ℓ c s3) {β : G} (hβB : β ∈ E.B)
    (hec : E.e₁ * c * E.e₁⁻¹ = β * c) :
    ∃ τ₀ : G, (τ₀ = 1 ∨ τ₀ = E.t) ∧ (E.u₁ * β * E.u₁⁻¹) * (c⁻¹ * β * c) = τ₀ := by
  have hu : E.Acts ℓ E.u₁ sw34 := E.acts_u₁ ℓ
  obtain ⟨δ, hδdef⟩ : ∃ δ : G, δ = E.u₁ * c * E.u₁⁻¹ * c := ⟨_, rfl⟩
  have hδ1 : E.Acts ℓ δ 1 := by
    have h := E.acts_mul (E.acts_mul (E.acts_mul hu hcs) (E.acts_inv hu)) hcs
    rw [sw34_s3] at h
    rw [hδdef]
    exact h
  have hδB : δ ∈ E.B := E.mem_B_of_acts_one hCB hδ1
  have hucu : E.u₁ * c * E.u₁⁻¹ = δ * c⁻¹ := by rw [hδdef]; group
  have hββ : β⁻¹ = β := inv_eq_of_mul_eq_one_right (E.sq_of_mem_B hβB)
  have key : E.e₁ * (E.u₁ * c * E.u₁⁻¹) * E.e₁⁻¹ = E.u₁ * (E.e₁ * c * E.e₁⁻¹) * E.u₁⁻¹ := by
    calc E.e₁ * (E.u₁ * c * E.u₁⁻¹) * E.e₁⁻¹ = (E.e₁ * E.u₁) * c * (E.e₁ * E.u₁)⁻¹ := by group
      _ = (E.u₁ * E.e₁) * c * (E.u₁ * E.e₁)⁻¹ := by rw [E.e₁_u₁]
      _ = E.u₁ * (E.e₁ * c * E.e₁⁻¹) * E.u₁⁻¹ := by group
  obtain ⟨A, hAdef⟩ : ∃ A : G, A = E.e₁ * δ * E.e₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : G, X = E.u₁ * β * E.u₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : G, Y = c⁻¹ * β * c := ⟨_, rfl⟩
  have hY : Y ∈ E.B := by
    rw [hYdef]
    exact E.conj_mem_B_of_mem_K hcK hβB
  have hLHS : E.e₁ * (E.u₁ * c * E.u₁⁻¹) * E.e₁⁻¹ = A * (β * c)⁻¹ := by
    rw [hucu, hAdef, ← hec]
    group
  have hRHS : E.u₁ * (E.e₁ * c * E.e₁⁻¹) * E.u₁⁻¹ = X * (δ * c⁻¹) := by
    rw [hec, hXdef, ← hucu]
    group
  rw [hLHS, hRHS] at key
  have key2 : A * Y = X * δ := by
    calc A * Y = A * (c⁻¹ * β⁻¹ * c) := by rw [hYdef, hββ]
      _ = A * (β * c)⁻¹ * c := by group
      _ = X * (δ * c⁻¹) * c := by rw [key]
      _ = X * δ := by group
  obtain ⟨τ₀, hτ₀, hAδ⟩ : ∃ τ₀ : G, (τ₀ = 1 ∨ τ₀ = E.t) ∧ A * δ = τ₀ := by
    rcases E.e₁_transvection hδB with h | h
    · exact ⟨1, Or.inl rfl, by rw [hAdef]; exact h⟩
    · exact ⟨E.t, Or.inr rfl, by rw [hAdef]; exact h⟩
  have hYδ : Y * δ = δ * Y := E.B_commute Y hY δ hδB
  have hXτ : X = τ₀ * Y := by
    calc X = X * (δ * δ) := by rw [E.sq_of_mem_B hδB, mul_one]
      _ = (X * δ) * δ := by rw [mul_assoc]
      _ = (A * Y) * δ := by rw [key2]
      _ = A * (Y * δ) := by rw [mul_assoc]
      _ = A * (δ * Y) := by rw [hYδ]
      _ = (A * δ) * Y := by rw [mul_assoc]
      _ = τ₀ * Y := by rw [hAδ]
  refine ⟨τ₀, hτ₀, ?_⟩
  rw [← hXdef, ← hYdef, hXτ, mul_assoc, E.sq_of_mem_B hY, mul_one]

theorem commutator_cases {ℓ : Bool} (hCB : Subgroup.centralizer (E.B : Set G) = E.B) {c : G}
    (hcK : c ∈ E.K) (hc3 : c ^ 3 = 1) (hcs : E.Acts ℓ c s3) :
    E.e₁ * c * E.e₁⁻¹ * c⁻¹ = 1 ∨ E.e₁ * c * E.e₁⁻¹ * c⁻¹ = E.pt ℓ 0 * E.pt ℓ 3 := by
  obtain ⟨β, hβdef⟩ : ∃ β : G, β = E.e₁ * c * E.e₁⁻¹ * c⁻¹ := ⟨_, rfl⟩
  rw [← hβdef]
  have he : E.Acts ℓ E.e₁ sw12 := E.acts_e₁ ℓ
  have hu : E.Acts ℓ E.u₁ sw34 := E.acts_u₁ ℓ
  have hβ1 : E.Acts ℓ β 1 := by
    have h := E.acts_mul (E.acts_mul (E.acts_mul he hcs) (E.acts_inv he)) (E.acts_inv hcs)
    rw [sw12_s3] at h
    rw [hβdef]
    exact h
  have hβB : β ∈ E.B := E.mem_B_of_acts_one hCB hβ1
  have hec : E.e₁ * c * E.e₁⁻¹ = β * c := by rw [hβdef]; group
  have hc3' : c * c * c = 1 := by rw [← pow_three']; exact hc3
  have eq1 : β * (c * β * c⁻¹) * (c * (c * β * c⁻¹) * c⁻¹) = 1 := by
    have h1 : (E.e₁ * c * E.e₁⁻¹) * (E.e₁ * c * E.e₁⁻¹) * (E.e₁ * c * E.e₁⁻¹) = 1 := by
      calc (E.e₁ * c * E.e₁⁻¹) * (E.e₁ * c * E.e₁⁻¹) * (E.e₁ * c * E.e₁⁻¹)
          = E.e₁ * (c * c * c) * E.e₁⁻¹ := by group
        _ = 1 := by rw [hc3']; group
    rw [hec] at h1
    calc β * (c * β * c⁻¹) * (c * (c * β * c⁻¹) * c⁻¹)
        = (β * c) * (β * c) * (β * c) * (c * c * c)⁻¹ := by group
      _ = 1 := by rw [h1, hc3']; group
  rcases E.B_cases ℓ hβB with hβ | ⟨i, hβ⟩ | ⟨i, j, hij, hβ⟩
  · exact Or.inl hβ
  · exfalso
    rw [hβ, hcs i, hcs (s3 i)] at eq1
    refine norm_pt ℓ i (E.injective ?_)
    simp only [map_mul, map_one]
    exact eq1
  · have hk1 := E.acts_conj_pair hcs i j
    have hk2 := E.acts_conj_pair hcs (s3 i) (s3 j)
    rw [hβ, hk1, hk2] at eq1
    have hW : (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
      refine norm_pair ℓ i j hij (E.injective ?_)
      simp only [map_mul, map_one]
      exact eq1
    obtain ⟨τ₀, hτ₀, hXY⟩ := E.eq_u₁ hCB hcK hcs hβB hec
    have hk3 := E.acts_conj_pair hu i j
    have hk4 := E.acts_conj_pair (E.acts_inv hcs) i j
    rw [inv_inv] at hk4
    rw [hβ, hk3, hk4] at hXY
    have hX : (ptm ℓ (sw34 i) * ptm ℓ (sw34 j) * (ptm ℓ (s3⁻¹ i) * ptm ℓ (s3⁻¹ j)) = 1 ∨
        ptm ℓ (sw34 i) * ptm ℓ (sw34 j) * (ptm ℓ (s3⁻¹ i) * ptm ℓ (s3⁻¹ j)) = t0) := by
      rcases hτ₀ with rfl | rfl
      · left
        apply E.injective
        simp only [map_mul, map_one]
        exact hXY
      · right
        apply E.injective
        simp only [map_mul]
        exact hXY
    obtain ⟨hi, hj⟩ := eq2_pair ℓ i j hW hX
    right
    rw [hβ, hi, hj]

end Emb

end CFSG.Quasithin.A10
