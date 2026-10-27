module

public import CFSG.Milestones.ASVolI.F411.SwapRed

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

theorem burnsideF411a_mul_conj_mul_inv {G : Type*} [Group G] (β : MulAut G) (x : G) :
    β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := by
  ext y
  simp [MulAut.conj_apply]

theorem burnsideF411a_conj_aux {G : Type*} [Group G] (a g : G) (T S : MulAut G)
    (hTS : T * S = S * T) :
    ∃ y : G, (MulAut.conj a * T) * (MulAut.conj g * S) * (MulAut.conj a * T)⁻¹ =
      MulAut.conj y * (MulAut.conj g * S) := by
  refine ⟨a * T g * S a⁻¹ * g⁻¹, ?_⟩
  have h1 : T * S * T⁻¹ = S := by rw [hTS, mul_inv_cancel_right]
  have h2 := burnsideF411a_mul_conj_mul_inv T g
  have h3 := burnsideF411a_mul_conj_mul_inv S a⁻¹
  have h4 : (MulAut.conj a)⁻¹ = MulAut.conj a⁻¹ := (map_inv MulAut.conj a).symm
  calc (MulAut.conj a * T) * (MulAut.conj g * S) * (MulAut.conj a * T)⁻¹
      = MulAut.conj a * (T * MulAut.conj g * T⁻¹) * (T * S * T⁻¹) * (MulAut.conj a)⁻¹ := by
        group
    _ = MulAut.conj a * MulAut.conj (T g) * S * (MulAut.conj a)⁻¹ := by rw [h1, h2]
    _ = MulAut.conj a * MulAut.conj (T g) * (S * (MulAut.conj a)⁻¹ * S⁻¹) * S := by group
    _ = MulAut.conj a * MulAut.conj (T g) * MulAut.conj (S a⁻¹) * S := by rw [h4, h3]
    _ = MulAut.conj (a * T g * S a⁻¹ * g⁻¹) * (MulAut.conj g * S) := by
        simp only [map_mul, map_inv]
        group

theorem burnsideF411a_exists_conj_mul {G : Type*} [Group G] (τ₀ : MulAut G)
    (hgen : ∀ α : MulAut G, ∃ (x : G) (m : ℕ), α = MulAut.conj x * τ₀ ^ m) (ζ α : MulAut G) :
    ∃ y : G, ζ * α * ζ⁻¹ = MulAut.conj y * α := by
  obtain ⟨a, j, rfl⟩ := hgen ζ
  obtain ⟨g, k, rfl⟩ := hgen α
  exact burnsideF411a_conj_aux a g (τ₀ ^ j) (τ₀ ^ k) (pow_mul_comm τ₀ j k)

theorem burnsideF411a_isLieParabolics_symm {E : Type} [Group E] {p : ℕ}
    {H B P₁ P₂ : Subgroup E} (h : IsLieParabolics p H B P₁ P₂) :
    IsLieParabolics p H B P₂ P₁ := by
  obtain ⟨hS, hne, hinf, hmax⟩ := h
  exact ⟨hS, hne.symm, by rw [inf_comm, hinf], fun Q => (hmax Q).trans or_comm⟩

theorem burnsideF411a_swap_of_graph {E : Type} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    {Gp M₁ M₂ : Subgroup E} (hN : Gp.Normal) (hC : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (τ₀ : MulAut ↥Gp)
    (hgen : ∀ α : MulAut ↥Gp, ∃ (x : ↥Gp) (m : ℕ), α = MulAut.conj x * τ₀ ^ m)
    (ζ : MulAut ↥Gp)
    (hζ1 : ((Gp ⊓ M₁).subgroupOf Gp).map ζ.toMonoidHom = (Gp ⊓ M₂).subgroupOf Gp)
    (hζ2 : ((Gp ⊓ M₂).subgroupOf Gp).map ζ.toMonoidHom = (Gp ⊓ M₁).subgroupOf Gp) :
    burnsideF411_Swap M₁ M₂ := by
  haveI := hN
  have hM₁ := burnsideF411_eq_normalizer hN hsplit hP
  have hsplit' : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₂ ⊓ M₁, e = n * h := fun e => by
    obtain ⟨n, hn, h, hh, rfl⟩ := hsplit e
    exact ⟨n, hn, h, ⟨hh.2, hh.1⟩, rfl⟩
  have hM₂ := burnsideF411_eq_normalizer hN hsplit' (burnsideF411a_isLieParabolics_symm hP)
  refine burnsideF411_swap_of_aut hC hM₁ hM₂ ζ (fun e => ?_) hζ1 hζ2
  obtain ⟨y, hy⟩ := burnsideF411a_exists_conj_mul τ₀ hgen ζ (MulAut.conjNormal e)
  refine ⟨(y : E) * e, ?_⟩
  rw [map_mul, MulAut.conjNormal_val, hy]

end CFSG.ASVolI
