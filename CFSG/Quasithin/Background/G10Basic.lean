module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

instance finite_linearEquiv_zmod2 (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective _ DFunLike.coe_injective

namespace G101Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
  (h : G101Hyp B Γ v₁ W X X₀)

include h

theorem isRefl : B.IsRefl := by
  have hAlt : B.IsAlt := fun v => h.alt v
  exact hAlt.isRefl

theorem nondegenerate' : B.Nondegenerate := by
  refine ⟨fun v hv => h.nondegenerate v hv, fun v hv => h.nondegenerate v fun w => ?_⟩
  exact h.isRefl _ _ (hv w)

theorem finrank_isotropic_le : 2 * Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) V := by
  have hW : W ≤ B.orthogonal W := fun w hw => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun n hn => h.isotropic n hn w hw
  have h1 := Submodule.finrank_mono hW
  have h2 := LinearMap.BilinForm.finrank_orthogonal h.nondegenerate' W
  have h3 : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le W
  omega

theorem X_isElemAbelian : IsElemAbelian 2 X := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact h.X_comm a a.2 b b.2
  · have := h.X_sq x hx
    rw [pow_two]
    exact this

theorem exists_card_X : ∃ k : ℕ, Nat.card X = 2 ^ k := by
  have : IsPGroup 2 X := fun g => ⟨1, by
    have := h.X_sq g g.2
    rw [pow_one, pow_two]
    exact Subtype.ext this⟩
  exact this.exists_card_eq

theorem dim_le_two_mul : Module.finrank (ZMod 2) V ≤ 2 * (Nat.log 2 (X₀.relIndex X) + 1) := by
  have h1 := h.finrank_isotropic_le
  have h2 := h.rank
  have hd : 0 < Module.finrank (ZMod 2) V :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨v₁, h.point⟩
  omega

theorem log_relIndex_le_pRank : Nat.log 2 (X₀.relIndex X) ≤ CFSG.Open.pRank 2 Γ := by
  obtain ⟨k, hk⟩ := h.exists_card_X
  have hdvd : X₀.relIndex X ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card X₀ X
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hjeq, Nat.log_pow Nat.one_lt_two]
  have hkle : k ≤ CFSG.Open.pRank 2 Γ := by
    refine le_csSup ?_ ⟨X, h.X_le, h.X_isElemAbelian, hk⟩
    refine ⟨Nat.card (V ≃ₗ[ZMod 2] V), ?_⟩
    rintro m ⟨E, -, -, hE⟩
    have : 2 ^ m ≤ Nat.card (V ≃ₗ[ZMod 2] V) := by
      rw [← hE]
      exact Nat.card_le_card_of_injective (fun e : E => (e : V ≃ₗ[ZMod 2] V)) Subtype.val_injective
    exact (Nat.lt_pow_self Nat.one_lt_two).le.trans this
  exact hj.trans hkle

omit [Finite V] h in
theorem stabilizer_eq_subgroupOf :
    MulAction.stabilizer ↥Γ v₁ = (Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁).subgroupOf Γ := by
  ext γ
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    SetLike.coe_mem, true_and]
  rfl

theorem isSylowTwoOf_of_stabilizer {T : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hT : IsSylowTwoOf T (Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁)) : IsSylowTwoOf T Γ := by
  obtain ⟨hTC, hTp, hTi⟩ := hT
  refine ⟨hTC.trans inf_le_left, hTp, ?_⟩
  have hmul := Subgroup.relIndex_mul_relIndex T (Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁) Γ
    hTC inf_le_left
  have hΓ : ¬ 2 ∣ (Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁).relIndex Γ := by
    have h1 : Odd ((Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁).relIndex Γ) := by
      have := h.odd_index
      rwa [stabilizer_eq_subgroupOf] at this
    exact fun hd => (Nat.not_even_iff_odd.2 h1) (even_iff_two_dvd.2 hd)
  show ¬ 2 ∣ T.relIndex Γ
  rw [← hmul]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h1 | h1
  · exact hTi h1
  · exact hΓ h1

theorem g10_9 {T H : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hT : IsSylowTwoOf T (Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁))
    (hXT : X ≤ T ∧ T ≤ Subgroup.normalizer (X : Set (V ≃ₗ[ZMod 2] V)))
    (hH : ∀ γ ∈ Γ, ∀ k ∈ H, γ * k * γ⁻¹ ∈ H) :
    IsSylowTwoOf T Γ ∧ ∀ x ∈ X, ∀ t ∈ T ⊓ H, x * t * x⁻¹ * t⁻¹ ∈ X ⊓ H := by
  refine ⟨h.isSylowTwoOf_of_stabilizer hT, fun x hx t ht => ⟨?_, ?_⟩⟩
  · have h1 : t * x⁻¹ * t⁻¹ ∈ X := by
      have := (Subgroup.mem_normalizer_iff.1 (hXT.2 ht.1) x⁻¹).1 (X.inv_mem hx)
      simpa [mul_assoc] using this
    have := X.mul_mem hx h1
    simpa [mul_assoc] using this
  · have hxΓ : x ∈ Γ := h.X_le hx
    have h1 : x * t * x⁻¹ ∈ H := hH x hxΓ t ht.2
    exact H.mul_mem h1 (H.inv_mem ht.2)

end G101Hyp

end CFSG.Quasithin
