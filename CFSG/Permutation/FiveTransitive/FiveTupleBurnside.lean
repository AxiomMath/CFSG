module

public import CFSG.Permutation.FiveTransitive.OrbitBounds
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.FiveTupleBurnside

open MulAction SubMulAction Subgroup

theorem conjugacy_orbit_overfills
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 5 ≤ Fintype.card X)
    (hP5 : MulAction.IsMultiplyPretransitive P X 5)
    (u : P) (fixedCount : ℕ)
    (hcentralizer :
      Nat.card (Subgroup.centralizer ({u} : Set P)) <
        fixedCount)
    (hfixed :
      ∀ a : MulAction.orbit (ConjAct P) u,
        Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) =
            fixedCount) :
    False := by
  classical
  let A := MulAction.orbit (ConjAct P) u
  letI : Fintype A := Fintype.ofFinite _
  let val : A → P := fun a => a.1
  have hvalInjective : Function.Injective val :=
    Subtype.val_injective
  let C : Subgroup P :=
    Subgroup.centralizer ({u} : Set P)
  have hAcard :
      Fintype.card A * Nat.card C = Nat.card P := by
    letI :
        Fintype (MulAction.stabilizer (ConjAct P) u) :=
      Fintype.ofFinite _
    have hstabilizer :
        Fintype.card (MulAction.stabilizer (ConjAct P) u) =
          Nat.card C := by
      rw [← Nat.card_eq_fintype_card,
        ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
    have horbitCard :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (ConjAct P) u
    rw [hstabilizer, ConjAct.card,
      ← Nat.card_eq_fintype_card] at horbitCard
    simpa [A, Nat.card_eq_fintype_card] using horbitCard
  let T := Fin 5 ↪ X
  letI : MulAction.IsPretransitive P T := by
    change MulAction.IsMultiplyPretransitive P X 5
    exact hP5
  letI : Nonempty T :=
    Fintype.card_pos_iff.mp (by
      change 0 < Fintype.card (Fin 5 ↪ X)
      rw [Fintype.card_embedding_eq, Fintype.card_fin,
        Nat.descFactorial_pos]
      exact hcard)
  letI : Unique (MulAction.orbitRel.Quotient P T) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P T).mp hP5)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      P T
  have hburnside' :
      (∑ q : P,
          Fintype.card (MulAction.fixedBy T q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  have hfixed' (a : A) :
      Fintype.card (MulAction.fixedBy T (val a)) =
        fixedCount :=
    hfixed a
  have hselectedSum :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy T (val a))) =
        Fintype.card A * fixedCount := by
    simp_rw [hfixed']
    simp
  have hselectedLe :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy T (val a))) ≤
        ∑ q : P,
          Fintype.card (MulAction.fixedBy T q) := by
    calc
      (∑ a : A,
          Fintype.card (MulAction.fixedBy T (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card (MulAction.fixedBy T q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card (MulAction.fixedBy T q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P,
          Fintype.card (MulAction.fixedBy T q) := by
        simp
  have hoverfill :
      Fintype.card A * fixedCount ≤ Nat.card P := by
    calc
      Fintype.card A * fixedCount =
          ∑ a : A,
            Fintype.card (MulAction.fixedBy T (val a)) :=
        hselectedSum.symm
      _ ≤ ∑ q : P,
          Fintype.card (MulAction.fixedBy T q) :=
        hselectedLe
      _ = Nat.card P := hburnside'
  rw [← hAcard] at hoverfill
  have hApos : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr
      ⟨⟨u, MulAction.mem_orbit_self u⟩⟩
  have hstrict :
      Fintype.card A * Nat.card C <
        Fintype.card A * fixedCount :=
    Nat.mul_lt_mul_of_pos_left hcentralizer hApos
  omega

end FiveTransitive.FiveTupleBurnside

end CFSG
