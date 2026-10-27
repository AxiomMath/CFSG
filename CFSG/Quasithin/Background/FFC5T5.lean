module

public import CFSG.Quasithin.Background.FFC5T4
public import CFSG.Quasithin.Background.FFC5Idx

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank

section T6

variable {V : Type} [CommGroup V]

namespace B510Fa

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Fa G G₁ G₂)

include h in
theorem hLW₂ : ∀ g ∈ G₂, ∀ w ∈ fixV G₁, g w ∈ fixV G₁ := fun _ hg w hw => (h.stab hg w).2 hw

include h in
theorem hc₂ : ∀ g ∈ G₂, ∀ v : V, g v * v⁻¹ ∈ fixV G₁ := fun g hg v =>
  h.commV_le (Subgroup.subset_closure ⟨g, hg, v, rfl⟩)

include h in
theorem hu_of_vanishing (hidx : (commV G₁ ⊔ fixV G₁).index = 2)
    (hvan : ∀ z ∈ Z1A (muW h.hLW₂), ∃ m : Additive ↥(fixV G₁), ∀ g : ↥G₂,
      ((Additive.toMul (z g - (muW h.hLW₂ g m - m)) : ↥(fixV G₁)) : V) ∈ fixV G) :
    ∃ u : V, u ∉ commV G₁ ⊔ fixV G₁ ∧ ∀ g ∈ G₂, g u * u⁻¹ ∈ fixV G := by
  obtain ⟨u, hu⟩ : ∃ u : V, u ∉ commV G₁ ⊔ fixV G₁ := by
    by_contra hcon
    push Not at hcon
    have : commV G₁ ⊔ fixV G₁ = ⊤ := eq_top_iff.2 fun x _ => hcon x
    rw [← Subgroup.index_eq_one] at this
    omega
  obtain ⟨m, hm⟩ := hvan _ (cocyF_mem_Z1A h.hLW₂ h.hc₂ u)
  refine ⟨u * (((Additive.toMul m : ↥(fixV G₁)) : V))⁻¹, ?_, fun g hg => ?_⟩
  · intro hmem
    apply hu
    have h1 : u = (u * (((Additive.toMul m : ↥(fixV G₁)) : V))⁻¹) * ((Additive.toMul m : ↥(fixV G₁)) : V) := by
      simp
    rw [h1]
    exact (commV G₁ ⊔ fixV G₁).mul_mem hmem (Subgroup.mem_sup_right ((Additive.toMul m : ↥(fixV G₁)).2))
  · have h1 := hm ⟨g, hg⟩
    have h2 : ((Additive.toMul (cocyF h.hc₂ u ⟨g, hg⟩ - (muW h.hLW₂ ⟨g, hg⟩ m - m)) : ↥(fixV G₁)) : V) =
        g (u * (((Additive.toMul m : ↥(fixV G₁)) : V))⁻¹) * (u * (((Additive.toMul m : ↥(fixV G₁)) : V))⁻¹)⁻¹ := by
      rw [toMul_sub, Subgroup.coe_div, muW_sub_apply]
      show g u * u⁻¹ / (g ((Additive.toMul m : ↥(fixV G₁)) : V) * ((Additive.toMul m : ↥(fixV G₁)) : V)⁻¹) = _
      rw [map_mul, map_inv, div_eq_mul_inv]
      simp [mul_comm, mul_left_comm, mul_assoc]
    rw [h2] at h1
    exact h1

include h in
theorem hvan_of_theta {Γ : Type*} [Group Γ] (ρ : Γ →* ↥G₂) (hρ : Function.Surjective ρ)
    {X : Type*} [AddCommGroup X] (μ : Γ →* AddMonoid.End X) (θ : Additive ↥(fixV G₁) →+ X)
    (hθs : Function.Surjective θ)
    (hθk : ∀ w, θ w = 0 ↔ ((Additive.toMul w : ↥(fixV G₁)) : V) ∈ fixV G)
    (hθ : ∀ γ w, θ (muW h.hLW₂ (ρ γ) w) = μ γ (θ w)) (hH1 : ∀ F ∈ Z1A μ, F ∈ B1A μ) :
    ∀ z ∈ Z1A (muW h.hLW₂), ∃ m : Additive ↥(fixV G₁), ∀ g : ↥G₂,
      ((Additive.toMul (z g - (muW h.hLW₂ g m - m)) : ↥(fixV G₁)) : V) ∈ fixV G := by
  intro z hz
  obtain ⟨m, hm⟩ := coboundary_mod_C h.hLW₂ ρ hρ μ θ hθs hθ hH1 hz
  exact ⟨m, fun g => (hθk _).1 (hm g)⟩

include h in
theorem vanishing_s5 (hS : (FFModel.symDn 5).Realizes G₂ (fixV G₁) (fixV G)) :
    ∀ z ∈ Z1A (muW h.hLW₂), ∃ m : Additive ↥(fixV G₁), ∀ g : ↥G₂,
      ((Additive.toMul (z g - (muW h.hLW₂ g m - m)) : ↥(fixV G₁)) : V) ∈ fixV G := by
  obtain ⟨π, hπ⟩ := hS
  obtain ⟨θ, hθs, hθk, hθ⟩ := sym5_theta h.hLW₂ hπ
  exact h.hvan_of_theta π hπ.1 muE θ hθs hθk hθ Z1A_muE_le_B1A

include h in
theorem vanishing_natK {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) (ha : 1 < a)
    (hS : (FFModel.nat (StatedSL 3 K)).Realizes G₂ (fixV G₁) (fixV G)) :
    ∀ z ∈ Z1A (muW h.hLW₂), ∃ m : Additive ↥(fixV G₁), ∀ g : ↥G₂,
      ((Additive.toMul (z g - (muW h.hLW₂ g m - m)) : ↥(fixV G₁)) : V) ∈ fixV G := by
  obtain ⟨π, hπ⟩ := hS
  obtain ⟨θ, hθs, hθk, hθ⟩ := natK_theta h.hLW₂ hπ
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_two_of_card_pow hK
  have hF : Fintype.card K = 2 ^ a := by rw [← Nat.card_eq_fintype_card]; exact hK
  exact h.hvan_of_theta (π.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
    (hπ.1.comp (specialLinearGroupEquivStatedSL 3 K).surjective) mu3 θ hθs hθk hθ
    (fun F hF' => mem_B1A_mu3 hF ha hF')

include h in
theorem vanishing_natK2 {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) (ha : 1 < a)
    {π : ↥(StatedSL 3 K) →* ↥G₂}
    (hS : ∃ I : Fin 2 → Subgroup V, (∀ i, fixV G ≤ I i) ∧
      (∀ i, I i ⊓ (fixV G ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) = fixV G) ∧
      (fixV G ⊔ ⨆ i, I i) = fixV G₁ ∧ ∀ i, (FFModel.nat (StatedSL 3 K)).RealizesVia G₂ (I i) (fixV G) π)
    (hπs : Function.Surjective π) :
    ∀ z ∈ Z1A (muW h.hLW₂), ∃ m : Additive ↥(fixV G₁), ∀ g : ↥G₂,
      ((Additive.toMul (z g - (muW h.hLW₂ g m - m)) : ↥(fixV G₁)) : V) ∈ fixV G := by
  obtain ⟨θ, hθs, hθk, hθ⟩ := natK2_theta h.hLW₂ hS
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_two_of_card_pow hK
  have hF : Fintype.card K = 2 ^ a := by rw [← Nat.card_eq_fintype_card]; exact hK
  exact h.hvan_of_theta (π.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
    (hπs.comp (specialLinearGroupEquivStatedSL 3 K).surjective) (muProd K) θ hθs hθk hθ
    (muProd_h1 hF ha)

end B510Fa

end T6

end FFC

end CFSG.Quasithin
