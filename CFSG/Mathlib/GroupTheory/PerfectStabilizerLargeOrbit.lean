module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.IsPerfect

public section

open MulAction
open scoped Pointwise

namespace CFSG.GroupTheory

theorem isPerfect_of_isPerfect_stabilizer_of_large_orbit
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X]
    (x : X)
    (hP : Group.IsPerfect (MulAction.stabilizer G x))
    (hbig : ∃ y : X,
      2 * Nat.card (MulAction.orbit (MulAction.stabilizer G x) y) > Nat.card X) :
    Group.IsPerfect G := by
  classical
  let P : Subgroup G := MulAction.stabilizer G x
  let D : Subgroup G := commutator G
  have hPD : P ≤ D := by
    have hPcomm : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp hP
    calc
      P = ⁅P, P⁆ := hPcomm.symm
      _ ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mono le_top le_top
      _ = D := rfl
  obtain ⟨y, hy⟩ := hbig
  let O : Set X := MulAction.orbit P y
  let Ω : Set X := MulAction.orbit D y
  have hy' : 2 * O.ncard > Nat.card X := by
    simpa only [O, Nat.card_coe_set_eq] using hy
  have hOΩ : O ⊆ Ω := by
    intro z hz
    obtain ⟨p, rfl⟩ := MulAction.mem_orbit_iff.mp hz
    simpa only [MulAction.subgroup_smul_def] using
      (MulAction.mem_orbit y (⟨p, hPD p.2⟩ : D))
  have hΩbig : 2 * Ω.ncard > Nat.card X := by
    have hle : O.ncard ≤ Ω.ncard := Set.ncard_le_ncard hOΩ
    omega
  have hΩuniv : Ω = Set.univ := by
    have hmem : y ∈ Ω := MulAction.mem_orbit_self y
    have hinv : ∀ g : G, g • Ω = Ω := by
      intro g
      have hEq : g • Ω = MulAction.orbit D (g • y) :=
        MulAction.smul_orbit_eq_orbit_smul D y g
      have hcard : (MulAction.orbit D (g • y)).ncard = Ω.ncard := by
        rw [← hEq, Set.ncard_smul_set]
      have hbig' : 2 * (MulAction.orbit D (g • y)).ncard > Nat.card X := by
        rw [hcard]
        exact hΩbig
      have hnotdisj : ¬ Disjoint Ω (MulAction.orbit D (g • y)) := by
        intro hdisj
        have hunion : (Ω ∪ MulAction.orbit D (g • y)).ncard =
            Ω.ncard + (MulAction.orbit D (g • y)).ncard :=
          Set.ncard_union_eq hdisj
        have hle : (Ω ∪ MulAction.orbit D (g • y)).ncard ≤ Nat.card X :=
          Set.ncard_le_card _
        omega
      rcases MulAction.orbit.eq_or_disjoint (G := D) y (g • y) with heq | hdis
      · exact hEq.trans heq.symm
      · exact (hnotdisj hdis).elim
    ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G y z
      have hz : g • y ∈ g • Ω := Set.smul_mem_smul_set hmem
      rw [hg] at hz
      rw [hinv g] at hz
      exact hz
  have : MulAction.IsPretransitive D X :=
    (MulAction.isPretransitive_iff_orbit_eq_univ (G := D) y).mpr hΩuniv
  have hGD : (⊤ : Subgroup G) ≤ D := by
    intro g _
    obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D x (g • x)
    have hd' : (d : G) • x = g • x := by
      simpa only [MulAction.subgroup_smul_def] using hd
    have hfix : (d : G)⁻¹ * g ∈ P := by
      rw [MulAction.mem_stabilizer_iff]
      rw [mul_smul, ← hd', inv_smul_smul]
    have hmemD : (d : G)⁻¹ * g ∈ D := hPD hfix
    have hg_eq : g = (d : G) * ((d : G)⁻¹ * g) := by group
    rw [hg_eq]
    exact D.mul_mem d.2 hmemD
  have hDtop : D = ⊤ := (le_antisymm hGD le_top).symm
  exact ⟨by simpa [D] using hDtop⟩

end CFSG.GroupTheory
