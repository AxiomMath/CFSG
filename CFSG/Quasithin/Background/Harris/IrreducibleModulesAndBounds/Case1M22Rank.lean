module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint

theorem autRank_succ_of_card_mulAut_le {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥) (hAut : Nat.card (MulAut S) ≤ 2 * Nat.card S) {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (B : Subgroup (MulAut S)) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hs : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 ^ (r + 1) := by
  let c : S →* MulAut S := MulAut.conj
  have hcinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro s hs1
    have hmem : s ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) hs1
      have h2 : s * g * s⁻¹ = g := this
      calc g * s = (s * g * s⁻¹) * s := by rw [h2]
        _ = s * g := by group
    rwa [hcen, Subgroup.mem_bot] at hmem
  have hnorm : c.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨s, rfl⟩ φ
    refine ⟨φ s, ?_⟩
    ext x
    simp [c, MulAut.conj_apply]
  have hIcard : Nat.card c.range = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective hcinj).toEquiv).symm
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hidx : c.range.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index c.range
    rw [hIcard] at h1
    by_contra hlt
    push Not at hlt
    have : 2 * Nat.card S < Nat.card S * c.range.index := by
      rw [mul_comm]
      exact Nat.mul_lt_mul_of_pos_left hlt hpos
    omega
  have hK : Nat.card (B ⊓ c.range : Subgroup (MulAut S)) ≤ 2 ^ r := by
    have hcomap : Nat.card (B.comap c) ≤ 2 ^ r := by
      refine hr (B.comap c) ?_ ?_
      · intro x hx y hy
        apply hcinj
        rw [map_mul, map_mul]
        exact hc _ hx _ hy
      · intro x hx
        apply hcinj
        rw [map_mul, map_one]
        exact hs _ hx
    have hmap : (B.comap c).map c = B ⊓ c.range := by
      rw [Subgroup.map_comap_eq, inf_comm]
    rw [← hmap, Subgroup.card_map_of_injective hcinj]
    exact hcomap
  have hrel : (B ⊓ c.range).relIndex B ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.relIndex_dvd_index_of_normal (H := c.range)
      (K := B))).trans hidx
  have h1 := Subgroup.card_mul_index ((B ⊓ c.range).subgroupOf B)
  have h2 : Nat.card ((B ⊓ c.range).subgroupOf B) = Nat.card (B ⊓ c.range : Subgroup (MulAut S)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : ((B ⊓ c.range).subgroupOf B).index = (B ⊓ c.range).relIndex B := rfl
  rw [h2, h3] at h1
  calc Nat.card B = Nat.card (B ⊓ c.range : Subgroup (MulAut S)) * (B ⊓ c.range).relIndex B :=
        h1.symm
    _ ≤ 2 ^ r * 2 := Nat.mul_le_mul hK hrel
    _ = 2 ^ (r + 1) := by rw [pow_succ]

theorem m22_autRank :
    ∀ B : Subgroup (MulAut (NativeSporadic.Carrier .M22)),
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 5 := by
  have : Finite (NativeSporadic.Carrier .M22) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card NativeSporadic.M22 ≠ 0
      rw [CFSG.Sporadic.Schreier.m22_card]
      norm_num)
  exact autRank_succ_of_card_mulAut_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
    CFSG.Sporadic.Schreier.m22_mulAut_card (r := 4) CFSG.QuasithinUnique.Setup.X1.m22_rank_le

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
