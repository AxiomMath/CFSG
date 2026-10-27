module

public import CFSG.Permutation.FiveTransitive.Degree19SevenCentralizer
public import CFSG.Permutation.FiveTransitive.FiveTupleBurnside
public import CFSG.Permutation.FiveTransitive.Degree15FourTuples
public import CFSG.Permutation.FiveTransitive.Degree19SylowSevenCard

public section

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction SubMulAction Subgroup

private theorem nonidentity_sylowSeven_support_card_eq_fourteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 7 P) (hScard : Nat.card S = 7)
    (u : S) (hu : u ≠ 1) :
    (((u : S) : P) : Equiv.Perm X).support.card = 14 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let g : Equiv.Perm X := ((u : S) : P)
  have huorder : orderOf u = 7 :=
    Degree15.orderOf_eq_prime_of_card_eq_prime hScard hu
  have hgorder : orderOf g = 7 := by
    calc
      orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 7 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 19 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 19 := hcard
  have hmTwo : m + 1 = 2 := by
    have hmLe : m + 1 ≤ 2 := by
      nlinarith
    rcases (show m + 1 = 1 ∨ m + 1 = 2 by omega) with
      hmOne | hmTwo
    · have hgcycle : g.IsCycle := by
        rw [← Equiv.Perm.card_cycleType_eq_one, hm, hmOne]
        simp
      have hgsupport : g.support.card = 7 := by
        omega
      exact (hnotAlt
        (Degree19Seven.alternatingGroup_le_of_sevenCycle
          X P hcard h5 (u : P).prop hgcycle hgsupport)).elim
    · exact hmTwo
  have hcycleType : g.cycleType = {7, 7} := by
    rw [hm, hgorder, hmTwo]
    norm_num
  rw [← g.sum_cycleType, hcycleType]
  norm_num

private theorem card_fixedBy_five_of_mem_double_seven_conjugacy_orbit
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (u : P)
    (husupport :
      (u : Equiv.Perm X).support.card = 14)
    (a : MulAction.orbit (ConjAct P) u) :
    Fintype.card
      (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) = 120 := by
  classical
  let g : Equiv.Perm X := u
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
      ((a.1 : P) : Equiv.Perm X).support.card = 14 := by
    calc
      ((a.1 : P) : Equiv.Perm X).support.card =
          (((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹).support.card :=
        Equiv.Perm.card_support_conj.symm
      _ = g.support.card := by rw [hconjPerm]
      _ = 14 := husupport
  have hfixedX :
      Fintype.card
        (MulAction.fixedBy X (a.1 : P)) = 5 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      hasupport]
  calc
    Fintype.card
        (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) =
        (Fintype.card
          (MulAction.fixedBy X (a.1 : P))).descFactorial
            (Fintype.card (Fin 5)) :=
      Degree15.card_fixedBy_embedding (a.1 : P)
    _ = 120 := by
      rw [hfixedX, Fintype.card_fin]
      norm_num [Nat.descFactorial]

theorem seven_not_dvd_card_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P) :
    ¬7 ∣ Nat.card P := by
  classical
  intro hseven
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S : Sylow 7 P := Sylow.nonempty.some
  have hScard : Nat.card S = 7 :=
    sylowSeven_card_eq_seven
      X P hcard h5 hnotAlt hseven S
  have hsevenS : 7 ∣ Nat.card S := by
    rw [hScard]
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := S) 7 hsevenS
  have hu : u ≠ 1 := by
    intro hu
    rw [hu, orderOf_one] at huorder
    norm_num at huorder
  let uP : P := u
  have husupport :
      (uP : Equiv.Perm X).support.card = 14 :=
    nonidentity_sylowSeven_support_card_eq_fourteen
      X P hcard h5 hnotAlt S hScard u hu
  have hcentralizer :
      Nat.card
          (Subgroup.centralizer ({uP} : Set P)) ≤ 14 := by
    simpa only [uP] using
      sylowSeven_element_centralizer_card_le_fourteen
        X P hcard h5 hnotAlt S hScard u hu
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  exact FiveTupleBurnside.conjugacy_orbit_overfills
    X P (by rw [hcard]; norm_num) hP5 uP 120
    (by omega)
    (card_fixedBy_five_of_mem_double_seven_conjugacy_orbit
      X P hcard uP husupport)

end FiveTransitive.Degree19

end CFSG
