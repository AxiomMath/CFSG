module

public import CFSG.Permutation.FiveTransitive.Degree15FourTuples

public section

namespace CFSG

namespace FiveTransitive.Degree17

open MulAction SubMulAction Subgroup

theorem card_conjugacy_orbit_mul_thirteen
    {P : Type} [Group P] [Fintype P]
    (u : P)
    (hcentralizer :
      Nat.card (Subgroup.centralizer ({u} : Set P)) = 13) :
    Nat.card (MulAction.orbit (ConjAct P) u) * 13 =
      Nat.card P := by
  classical
  letI : Fintype (MulAction.orbit (ConjAct P) u) :=
    Fintype.ofFinite _
  letI :
      Fintype (MulAction.stabilizer (ConjAct P) u) :=
    Fintype.ofFinite _
  have hstabilizer :
      Fintype.card (MulAction.stabilizer (ConjAct P) u) = 13 := by
    rw [← Nat.card_eq_fintype_card,
      ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
    exact hcentralizer
  have horbitCard :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct P) u
  rw [hstabilizer, ConjAct.card,
    ← Nat.card_eq_fintype_card] at horbitCard
  simpa only [Nat.card_eq_fintype_card] using horbitCard

theorem card_fixedBy_four_of_mem_conjugacy_orbit
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 17)
    (u : P) (huorder : orderOf u = 13)
    (a : MulAction.orbit (ConjAct P) u) :
    Fintype.card
      (MulAction.fixedBy (Fin 4 ↪ X) (a.1 : P)) = 24 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 13 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 13 := huorder
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      norm_num) (by
        rw [hcard, hgorder]
        norm_num)
  have hgsupport : g.support.card = 13 := by
    rw [← hgcycle.orderOf, hgorder]
  obtain ⟨q, hq⟩ :=
    isConj_iff.mp
      (ConjAct.mem_orbit_conjAct.mp a.prop)
  have hconjPerm :
      ((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹ =
          g :=
    congrArg Subtype.val hq
  have hasupport :
      ((a.1 : P) : Equiv.Perm X).support.card = 13 := by
    calc
      ((a.1 : P) : Equiv.Perm X).support.card =
          (((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹).support.card :=
        Equiv.Perm.card_support_conj.symm
      _ = g.support.card := by rw [hconjPerm]
      _ = 13 := hgsupport
  have hfixedX :
      Fintype.card
        (MulAction.fixedBy X (a.1 : P)) = 4 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      hasupport]
  calc
    Fintype.card
        (MulAction.fixedBy (Fin 4 ↪ X) (a.1 : P)) =
        (Fintype.card
          (MulAction.fixedBy X (a.1 : P))).descFactorial
            (Fintype.card (Fin 4)) :=
      Degree15.card_fixedBy_embedding (a.1 : P)
    _ = 24 := by
      rw [hfixedX, Fintype.card_fin]
      norm_num [Nat.descFactorial]

end FiveTransitive.Degree17

end CFSG
