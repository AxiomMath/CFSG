module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H20
public import CFSG.Quasithin.Vol2.Ch10SecQ9H21

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

variable {G H : Type*} [Group G] [Group H]

theorem le_normalizer_of_conj {U N : Subgroup H} (h : ∀ u ∈ U, ∀ z ∈ N, u * z * u⁻¹ ∈ N) :
    U ≤ Subgroup.normalizer (N : Set H) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨h u hu z, fun hz => ?_⟩
  have := h u⁻¹ (U.inv_mem hu) _ hz
  rwa [show u⁻¹ * (u * z * u⁻¹) * u⁻¹⁻¹ = z by group] at this

theorem le_normalizer_inf_centralizer {X S : Subgroup H}
    (hSX : S ≤ Subgroup.normalizer (X : Set H)) :
    X ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (X : Set H) : Subgroup H) : Set H) ∧
      S ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (X : Set H) : Subgroup H) : Set H) := by
  refine ⟨le_normalizer_of_conj fun x hx a ha => ?_, le_normalizer_of_conj fun s hs a ha => ?_⟩
  · have hxa : x * a = a * x := Subgroup.mem_centralizer_iff.mp ha.2 x hx
    rw [hxa, mul_inv_cancel_right]
    exact ha
  · refine ⟨S.mul_mem (S.mul_mem hs ha.1) (S.inv_mem hs), ?_⟩
    show s * a * s⁻¹ ∈ Subgroup.centralizer (X : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : s⁻¹ * z * s ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSX hs)) z).mp hz
      rwa [inv_inv] at this
    have h1 := Subgroup.mem_centralizer_iff.mp ha.2 _ hz'
    calc z * (s * a * s⁻¹) = s * ((s⁻¹ * z * s) * a) * s⁻¹ := by group
      _ = s * (a * (s⁻¹ * z * s)) * s⁻¹ := by rw [h1]
      _ = s * a * s⁻¹ * z := by group

theorem ker_le_pCore {X : Subgroup G} (φ : ↥X →* H) (hφ : ∀ x, φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    φ.ker ≤ CFSG.pCore 2 ↥X :=
  le_sSup ⟨inferInstance, fun g => by
    obtain ⟨k, hk⟩ := hφ g.1 g.2
    exact ⟨k, Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hk)⟩⟩

theorem card_range_ge [Finite G] {X : Subgroup G} (φ : ↥X →* H)
    (hφ : ∀ x, φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) (hcard : Nat.card X = Nat.card (o2G X) * 168) :
    168 ≤ Nat.card φ.range := by
  have h1 := card_eq_ker_mul_range φ
  have h2 : Nat.card φ.ker ≤ Nat.card (o2G X) := by
    rw [card_o2G]
    exact Subgroup.card_le_of_le (ker_le_pCore φ hφ)
  have hpos : 0 < Nat.card (o2G X) := Nat.card_pos
  rw [hcard] at h1
  by_contra hlt
  have hlt' : Nat.card φ.range < 168 := by omega
  have := Nat.mul_le_mul h2 (le_of_lt hlt')
  nlinarith

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
