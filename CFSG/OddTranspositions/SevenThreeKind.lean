module

public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.OddTranspositions.Blocks

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

def Delta (D : Set G) (z : G) : Set G := {x | x ∈ D ∧ Commute x z}

@[expose] def thirdK (D : Set G) (z : G) : Subgroup G := Subgroup.closure (Delta D z)

theorem Delta_subset_D {z : G} : Delta D z ⊆ D := fun _ hx => hx.1

theorem mem_Delta_iff {z x : G} : x ∈ Delta D z ↔ x ∈ D ∧ Commute x z := Iff.rfl

theorem vertices_mem_Delta {u w v z : G} (htri : IsTriangle D u w v)
    (hzu : Commute z u) (hzv : Commute z v) (hzw : Commute z w) :
    u ∈ Delta D z ∧ v ∈ Delta D z ∧ w ∈ Delta D z :=
  ⟨⟨htri.1, hzu.symm⟩, ⟨htri.2.1, hzv.symm⟩, ⟨htri.2.2.1, hzw.symm⟩⟩

theorem thirdK_le_centralizer {z : G} :
    thirdK D z ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [thirdK, Subgroup.closure_le]
  intro x hx
  exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx.2.eq.symm)

theorem Delta_subset_thirdK {z : G} : Delta D z ⊆ thirdK D z := Subgroup.subset_closure

theorem Delta_conj_mem {z k : G} (hN : IsNormalSet D) (hk : k ∈ thirdK D z) {x : G}
    (hx : x ∈ Delta D z) : k * x * k⁻¹ ∈ Delta D z := by
  have hkz : Commute k z := by
    have h := thirdK_le_centralizer hk
    rw [Subgroup.mem_centralizer_iff] at h
    exact (h z (Set.mem_singleton z)).symm
  refine ⟨hN k x hx.1, ?_⟩
  have h : Commute (k * x * k⁻¹) (k * z * k⁻¹) := hx.2.conj k
  have hconjz : k * z * k⁻¹ = z := by rw [hkz.eq]; group
  rwa [hconjz] at h

theorem thirdK_orbits_commute (hS : Setup G D) {z : G}
    {O₁ O₂ : Set G} (hO₁ : O₁ ⊆ Delta D z) (hO₂ : O₂ ⊆ Delta D z)
    (hinv₁ : ∀ k ∈ thirdK D z, ∀ x ∈ O₁, k * x * k⁻¹ ∈ O₁)
    (hinv₂ : ∀ k ∈ thirdK D z, ∀ x ∈ O₂, k * x * k⁻¹ ∈ O₂)
    (hdisj : Disjoint O₁ O₂) :
    ∀ x ∈ O₁, ∀ y ∈ O₂, Commute x y :=
  commute_of_isOddTransp_invariant_partition (hS.oddT.mono Delta_subset_D) hO₁ hO₂
    hinv₁ hinv₂ hdisj

theorem conj_eq_of_orderOf_mul_eq_three {b v : G} (hb : b * b = 1) (hv : v * v = 1)
    (h3 : orderOf (b * v) = 3) : v * b * v = b * v * b := by
  have hx3 : b * v * b * v * b * v = 1 := by
    have h := pow_orderOf_eq_one (b * v)
    rw [h3] at h
    simpa [pow_succ, pow_two, mul_assoc] using h
  have h1 : b * v * b * v * b = v := by
    have := congrArg (fun x => x * v) hx3
    have hL : (b * v * b * v * b * v) * v = b * v * b * v * b := by
      calc (b * v * b * v * b * v) * v = b * v * b * v * b * (v * v) := by group
        _ = b * v * b * v * b := by rw [hv, mul_one]
    rwa [hL, one_mul] at this
  have h3' : v * b * v = b * v * b := by
    have := congrArg (fun x => b * x * b) h1
    have hL : b * (b * v * b * v * b) * b = v * b * v := by
      calc b * (b * v * b * v * b) * b = (b * b) * v * b * v * (b * b) := by group
        _ = v * b * v := by rw [hb, one_mul, mul_one]
    rwa [hL] at this
  exact h3'

theorem thirdK_lt_top_of_no_solvable_normal
    (hZ : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {z : G} (hz1 : z ≠ 1) : thirdK D z < ⊤ := by
  have hK : thirdK D z ≠ ⊤ := by
    intro htop
    have hcent : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ thirdK D z := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp (thirdK_le_centralizer hg) z (by simp)).symm
    have hZne : Subgroup.center G ≠ ⊥ := by
      intro hbot
      have hzbot : z ∈ (⊥ : Subgroup G) := hbot ▸ hcent
      exact hz1 (Subgroup.mem_bot.mp hzbot)
    have hsolv : Group.IsSolvable (Subgroup.center G) :=
      isSolvable_of_comm (fun a b => Subtype.ext (Subgroup.mem_center_iff.mp a.2 b).symm)
    exact hZne (hZ (Subgroup.center G) inferInstance hsolv)
  exact lt_top_iff_ne_top.mpr hK

end CFSG.OddTranspositions
