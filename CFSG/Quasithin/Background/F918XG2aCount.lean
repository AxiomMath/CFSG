module

public import CFSG.Quasithin.Background.F918X0
public import CFSG.Quasithin.Background.FFC2Core

public section

namespace CFSG.Quasithin.F918X

theorem stableMod_of_simple_lt {W : Type*} [CommGroup W] [Finite W] {G L : Subgroup (MulAut W)}
    (hLG : L < G) (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hself : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hs : IsSimpleGroup ↥L)
    (haut : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L) :
    StableMod L ∧ Subgroup.center ↥L = ⊥ := by
  have hZ : Subgroup.center ↥L = ⊥ := CFSG.Quasithin.FFC.center_eq_bot_of_simple hnab
  have hGn : G ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hLn g hg x hx, fun hx => ?_⟩
    have h := hLn g⁻¹ (G.inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h
  have hGc : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g = 1 := by
    intro g hg hcomm
    have hgL : g ∈ L := hself g hg hcomm
    have hcen : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have : Finite (MulAut W) := MulEquiv.finite_left
  have : Finite (MulAut ↥L) := MulEquiv.finite_left
  have hreal : Nat.card ↥G ≤ Nat.card (realized L) := card_le_card_realized hGn hGc
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hLG.le
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  have hlt : Nat.card ↥L < Nat.card ↥G := by
    by_contra hge
    exact hLG.ne (Subgroup.eq_of_le_of_card_ge hLG.le (not_lt.mp hge))
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hk
      omega
    · simp at hk
      omega
    · omega
  have h2 : 2 * Nat.card ↥L ≤ Nat.card ↥G := by
    rw [hk, mul_comm]
    exact Nat.mul_le_mul_left _ hk2
  exact ⟨stableMod_of_card (by omega), hZ⟩

end CFSG.Quasithin.F918X
