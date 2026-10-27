module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open MulAction

theorem card_dvd_of_free {G X : Type*} [Group G] [MulAction G X]
    (h : ∀ g : G, ∀ x : X, g • x = x → g = 1) : Nat.card G ∣ Nat.card X := by
  have hst : ∀ b : X, stabilizer G b = ⊥ := fun b => by
    ext g
    rw [mem_stabilizer_iff, Subgroup.mem_bot]
    exact ⟨h g b, fun hg => by rw [hg, one_smul]⟩
  rw [Nat.card_congr (selfEquivOrbitsQuotientProd hst), Nat.card_prod]
  exact Dvd.intro_left _ rfl

variable {G Ω : Type*} [Group G] [MulAction G Ω]

@[expose, instance_reducible] def actOnOrbitCompl (Γ P : Subgroup G) (hPΓ : P ≤ Γ) (x : Ω)
    (hfix : ∀ g ∈ P, g • x = x) : MulAction P ↥(orbit Γ x \ {x}) where
  smul g y := ⟨(g : G) • y.1, by
    obtain ⟨⟨γ, hγ⟩, hy⟩ := mem_orbit_iff.1 y.2.1
    refine ⟨mem_orbit_iff.2 ⟨⟨(g : G) * γ, Γ.mul_mem (hPΓ g.2) hγ⟩, ?_⟩, ?_⟩
    · rw [← hy]
      exact mul_smul (g : G) γ x
    · intro hx
      apply y.2.2
      have hx' : (g : G) • y.1 = x := hx
      have h1 : y.1 = x := by
        calc y.1 = (g : G)⁻¹ • ((g : G) • y.1) := (inv_smul_smul _ _).symm
          _ = (g : G)⁻¹ • x := by rw [hx']
          _ = x := hfix _ (P.inv_mem g.2)
      exact h1⟩
  one_smul y := Subtype.ext (one_smul G y.1)
  mul_smul a b y := Subtype.ext (mul_smul (a : G) (b : G) y.1)

theorem card_dvd_ncard_orbit_sub_one [Finite Ω] {Γ P : Subgroup G} (hPΓ : P ≤ Γ) {x : Ω}
    (hfix : ∀ g ∈ P, g • x = x) (hfree : ∀ g ∈ P, ∀ y : Ω, y ≠ x → g • y = y → g = 1) :
    Nat.card P ∣ (orbit Γ x).ncard - 1 := by
  let _ : MulAction P ↥(orbit Γ x \ {x}) := actOnOrbitCompl Γ P hPΓ x hfix
  have hdvd : Nat.card P ∣ Nat.card ↥(orbit Γ x \ {x}) := by
    refine card_dvd_of_free fun g y hgy => ?_
    have hgy' : (g : G) • y.1 = y.1 := congrArg Subtype.val hgy
    have hy : y.1 ≠ x := y.2.2
    have := hfree g g.2 y.1 hy hgy'
    exact Subtype.ext this
  rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (mem_orbit_self x)] at hdvd
  exact hdvd

theorem ncard_orbit_dvd [Finite G] {Γ P : Subgroup G} (hPΓ : P ≤ Γ) {x : Ω}
    (hfix : ∀ g ∈ P, g • x = x) {s : ℕ} (hs : Nat.card Γ = Nat.card P * s) :
    (orbit Γ x).ncard ∣ s := by
  have hmul := Subgroup.card_mul_index (stabilizer Γ x)
  rw [index_stabilizer] at hmul
  have hPS : P.subgroupOf Γ ≤ stabilizer Γ x := fun g hg =>
    mem_stabilizer_iff.2 (hfix g (Subgroup.mem_subgroupOf.1 hg))
  have hd : Nat.card P ∣ Nat.card (stabilizer Γ x) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΓ).toEquiv]
    exact Subgroup.card_dvd_of_le hPS
  obtain ⟨c, hc⟩ := hd
  have hpos : 0 < Nat.card P := Nat.card_pos
  rw [hc, hs] at hmul
  refine ⟨c, ?_⟩
  have : Nat.card P * ((orbit Γ x).ncard * c) = Nat.card P * s := by
    rw [← hmul]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hpos this).symm

end CFSG.Quasithin.H13.NQCore.U3O
