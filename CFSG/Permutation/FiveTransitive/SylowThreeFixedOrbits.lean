module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.SylowThreeFixedOrbits

open MulAction
open scoped BigOperators

@[expose] def orbitAction {G Y : Type*} [Group G] [MulAction G Y] (S : Subgroup G) (y : Y) :
    SubMulAction S Y where
  carrier := orbit G y
  smul_mem' s _ hz := mem_orbit_of_mem_orbit s.val hz

theorem odd_orbit_of_sylow_fixed
    {G Y : Type*} [Group G] [Finite G] [MulAction G Y]
    (y : Y) (S : Sylow 2 G) (hy : y ∈ fixedPoints S Y) :
    ¬ 2 ∣ Nat.card (orbit G y) := by
  have hle : (S : Subgroup G) ≤ stabilizer G y := by
    intro s hs
    exact mem_fixedPoints.mp hy ⟨s,hs⟩
  have hd := Subgroup.index_dvd_of_le hle
  rw [index_stabilizer, ← Nat.card_coe_set_eq] at hd
  intro h
  exact S.not_dvd_index (h.trans hd)

theorem card_orbits_eq_one_or_three
    {G Y : Type*} [Group G] [Finite G] [MulAction G Y] [Finite Y]
    (S : Sylow 2 G) (hS : Nat.card (fixedPoints S Y) = 3)
    (hpoint : ∀ y : Y, ∃ T : Sylow 2 G, y ∈ fixedPoints T Y) :
    Nat.card (orbitRel.Quotient G Y) = 1 ∨ Nat.card (orbitRel.Quotient G Y) = 3 := by
  classical
  let _ : Fintype Y := Fintype.ofFinite Y
  let _ : Fintype (orbitRel.Quotient G Y) := Fintype.ofFinite _
  have hodd (y : Y) : ¬ 2 ∣ Nat.card (orbit G y) := by
    obtain ⟨T,hT⟩ := hpoint y
    exact odd_orbit_of_sylow_fixed y T hT
  have hmeet (y : Y) : ∃ z : fixedPoints S Y, z.val ∈ orbit G y := by
    let O := orbitAction (S : Subgroup G) y
    have hm := S.isPGroup'.card_modEq_card_fixedPoints O
    have hnonzero : Nat.card (fixedPoints S O) ≠ 0 := by
      intro he
      have ho := hodd y
      change Nat.card (orbit G y) % 2 = Nat.card (fixedPoints S O) % 2 at hm
      rw [he, Nat.zero_mod] at hm
      exact ho (Nat.dvd_of_mod_eq_zero hm)
    obtain ⟨z⟩ : Nonempty (fixedPoints S O) := Finite.card_pos_iff.mp (Nat.pos_of_ne_zero hnonzero)
    refine ⟨⟨z.val.val, ?_⟩, z.val.property⟩
    rw [mem_fixedPoints]
    intro s
    exact congrArg Subtype.val (mem_fixedPoints.mp z.property s)
  let f : fixedPoints S Y → orbitRel.Quotient G Y := fun z => Quotient.mk'' z.val
  have hf : Function.Surjective f := by
    intro o
    obtain ⟨z,hz⟩ := hmeet o.out
    refine ⟨z, ?_⟩
    change Quotient.mk'' z.val = o
    exact (Quotient.sound (orbitRel_apply.mpr hz)).trans (Quotient.out_eq o)
  have hle : Nat.card (orbitRel.Quotient G Y) ≤ 3 := by
    simpa only [hS] using Nat.card_le_card_of_surjective f hf
  have hsum : Nat.card Y = ∑ o : orbitRel.Quotient G Y, Nat.card (orbit G o.out) := by
    rw [Nat.card_congr (selfEquivSigmaOrbits G Y)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hmod (y : Y) : Nat.card (orbit G y) % 2 = 1 := by
    have h := hodd y
    have hm := Nat.mod_lt (Nat.card (orbit G y)) (by decide : 0 < 2)
    have hn : Nat.card (orbit G y) % 2 ≠ 0 := fun he => h (Nat.dvd_of_mod_eq_zero he)
    omega
  have horbitmod : Nat.card Y % 2 = Nat.card (orbitRel.Quotient G Y) % 2 := by
    rw [hsum, Finset.sum_nat_mod]
    simp_rw [hmod]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card]
  have htotal := S.isPGroup'.card_modEq_card_fixedPoints Y
  change Nat.card Y % 2 = Nat.card (fixedPoints S Y) % 2 at htotal
  rw [hS] at htotal
  omega

end FiveTransitive.SylowThreeFixedOrbits

end CFSG
