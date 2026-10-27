module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_eq_card {X N : Subgroup G} [N.Normal] (hXN : X ⊓ N = ⊥) :
    X.relIndex (X ⊔ N) = Nat.card N := by
  have h1 := Subgroup.relIndex_mul_relIndex ⊥ X (X ⊔ N) bot_le le_sup_left
  have h2 := Subgroup.relIndex_mul_relIndex ⊥ N (X ⊔ N) bot_le le_sup_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h1 h2
  rw [Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_left, hXN,
    Subgroup.relIndex_bot_left] at h2
  have hX : 0 < Nat.card X := Nat.card_pos
  have : Nat.card X * X.relIndex (X ⊔ N) = Nat.card X * Nat.card N := by
    rw [h1, ← h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hX this

theorem exists_mul_mem_normalizer {p : ℕ} [hp : Fact p.Prime] {X N : Subgroup G} [hN : N.Normal]
    (hX : IsPGroup p X) (hNp : ¬ p ∣ Nat.card N) {w : G}
    (hw : X.map (MulAut.conj w).toMonoidHom ≤ X ⊔ N) :
    ∃ n ∈ N, n * w ∈ Subgroup.normalizer (X : Set G) := by
  set H := X ⊔ N with hH
  have hXN : X ⊓ N = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
    obtain ⟨k, hk⟩ := hX ⟨z, hz.1⟩
    have h1 : orderOf z ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf z ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨z, hz.2⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hNp)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hidx : X.relIndex H = Nat.card N := relIndex_sup_eq_card hXN
  set Y := X.map (MulAut.conj w).toMonoidHom with hY
  have hcardY : Nat.card Y = Nat.card X := Subgroup.card_map_of_injective (MulAut.conj w).injective
  have hYp : IsPGroup p Y := hX.map _
  have hidxY : Y.relIndex H = Nat.card N := by
    have h1 := Subgroup.relIndex_mul_relIndex ⊥ Y H bot_le hw
    have h2 := Subgroup.relIndex_mul_relIndex ⊥ X H bot_le le_sup_left
    rw [Subgroup.relIndex_bot_left] at h1 h2
    rw [hcardY] at h1
    have hX0 : 0 < Nat.card X := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hX0 (h1.trans h2.symm)).trans hidx
  let P₁ : Sylow p ↥H := (hX.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm).toSylow
    (by rw [show (X.subgroupOf H).index = X.relIndex H from rfl, hidx]; exact hNp)
  let P₂ : Sylow p ↥H := (hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hw).symm).toSylow
    (by rw [show (Y.subgroupOf H).index = Y.relIndex H from rfl, hidxY]; exact hNp)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥H P₁ P₂
  have hhH : (h : G) ∈ (N : Set G) * (X : Set G) := by
    have : (h : G) ∈ ((N ⊔ X : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact h.2
    rwa [Subgroup.normal_mul N X] at this
  obtain ⟨n, hn, x, hx, hnx⟩ := hhH
  refine ⟨n⁻¹, N.inv_mem hn, Subgroup.mem_normalizer_iff.mpr fun z => ?_⟩
  have key : ∀ z : G, z ∈ X → (h : G) * z * (h : G)⁻¹ ∈ Y := by
    intro z hz
    have hmem : (⟨z, le_sup_left (a := X) (b := N) hz⟩ : ↥H) ∈ (P₁ : Subgroup ↥H) :=
      Subgroup.mem_subgroupOf.mpr hz
    have h1 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj h) _ hmem
    rw [← Sylow.coe_subgroup_smul, hh, MulAut.smul_def, MulAut.conj_apply] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have key' : ∀ z : G, z ∈ Y → (h : G)⁻¹ * z * (h : G) ∈ X := by
    intro z hz
    have hmem : (⟨z, hw hz⟩ : ↥H) ∈ (P₂ : Subgroup ↥H) := Subgroup.mem_subgroupOf.mpr hz
    have h1 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj h⁻¹) _ hmem
    rw [← Sylow.coe_subgroup_smul, ← hh, inv_smul_smul, MulAut.smul_def, MulAut.conj_apply] at h1
    have := Subgroup.mem_subgroupOf.mp h1
    simpa using this
  have hxX : ∀ z, z ∈ X ↔ x * z * x⁻¹ ∈ X := fun z =>
    ⟨fun hz => X.mul_mem (X.mul_mem hx hz) (X.inv_mem hx), fun hz => by
      have := X.mul_mem (X.mul_mem (X.inv_mem hx) hz) hx
      simpa [mul_assoc] using this⟩
  have hYw : ∀ z, z ∈ Y ↔ w⁻¹ * z * w ∈ X := fun z => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hu
    · intro hz
      exact ⟨_, hz, by simp [MulAut.conj_apply, mul_assoc]⟩
  constructor
  · intro hz
    have h1 : w * z * w⁻¹ ∈ Y := (hYw _).mpr (by simpa [mul_assoc] using hz)
    have h2 := key' _ h1
    rw [← hnx] at h2
    have h3 : x * (x⁻¹ * n⁻¹ * (w * z * w⁻¹) * (n * x)) * x⁻¹ ∈ X := (hxX _).mp (by
      simpa [mul_assoc] using h2)
    have e : n⁻¹ * w * z * (n⁻¹ * w)⁻¹ = x * (x⁻¹ * n⁻¹ * (w * z * w⁻¹) * (n * x)) * x⁻¹ := by
      group
    rw [e]
    exact h3
  · intro hz
    have e : (h : G) * (x⁻¹ * (n⁻¹ * w * z * (n⁻¹ * w)⁻¹) * x) * (h : G)⁻¹ =
        w * z * w⁻¹ := by
      rw [← hnx]
      group
    have h1 : x⁻¹ * (n⁻¹ * w * z * (n⁻¹ * w)⁻¹) * x ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem hx) hz) hx
    have h2 := key _ h1
    rw [e] at h2
    have := (hYw _).mp h2
    simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
