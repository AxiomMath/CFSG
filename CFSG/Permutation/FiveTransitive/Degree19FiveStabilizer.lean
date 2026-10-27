module

public import CFSG.Permutation.FiveTransitive.Degree19DoubleFiveCentralizer
public import CFSG.Permutation.FiveTransitive.Degree15FourTuples
public import CFSG.Permutation.FiveTransitive.FiveTupleBurnside

public section

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction SubMulAction Subgroup

theorem card_fixedBy_five_of_mem_double_five_conjugacy_orbit
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (u : P)
    (husupport :
      (u : Equiv.Perm X).support.card = 10)
    (a : MulAction.orbit (ConjAct P) u) :
    Fintype.card
      (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) =
        15120 := by
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
      ((a.1 : P) : Equiv.Perm X).support.card = 10 := by
    calc
      ((a.1 : P) : Equiv.Perm X).support.card =
          (((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹).support.card :=
        Equiv.Perm.card_support_conj.symm
      _ = g.support.card := by rw [hconjPerm]
      _ = 10 := husupport
  have hfixedX :
      Fintype.card
        (MulAction.fixedBy X (a.1 : P)) = 9 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      hasupport]
  calc
    Fintype.card
        (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) =
        (Fintype.card
          (MulAction.fixedBy X (a.1 : P))).descFactorial
            (Fintype.card (Fin 5)) :=
      Degree15.card_fixedBy_embedding (a.1 : P)
    _ = 15120 := by
      rw [hfixedX, Fintype.card_fin]
      norm_num [Nat.descFactorial]

theorem five_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬5 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  intro hfive
  let H : Subgroup P := fixingSubgroup P s
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := H) 5 hfive
  let uP : P := u
  let g : Equiv.Perm X := uP
  have huPorder : orderOf uP = 5 := by
    calc
      orderOf uP = orderOf u := Subgroup.orderOf_coe _
      _ = 5 := huorder
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf uP := Subgroup.orderOf_coe _
      _ = 5 := huPorder
  have hfix :
      ∀ x ∈ s, uP • x = x :=
    (mem_fixingSubgroup_iff P).mp u.prop
  have hsupportSubset :
      (g.support : Set X) ⊆ sᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxs
    apply Equiv.Perm.mem_support.mp hx
    exact hfix x hxs
  have hcomplement : sᶜ.ncard = 14 := by
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hsupportLe : g.support.card ≤ 14 := by
    rw [← Set.ncard_coe_finset]
    exact
      (Set.ncard_le_ncard hsupportSubset).trans_eq
        hcomplement
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hmLe : m + 1 ≤ 2 := by
    nlinarith
  have hmCases : m + 1 = 1 ∨ m + 1 = 2 := by
    omega
  have hgNe : g ≠ 1 := by
    intro hg
    rw [hg, orderOf_one] at hgorder
    norm_num at hgorder
  have hsupportTen : g.support.card = 10 := by
    rcases hmCases with hmOne | hmTwo
    · have hsupportFive : g.support.card = 5 := by
        omega
      exact (hnotAlt
        (Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
          X P h5 (by omega) uP.prop hgNe (by
            rw [hsupportFive]))).elim
    · omega
  have hcentralizer :
      Nat.card
          (Subgroup.centralizer ({uP} : Set P)) ≤ 4050 :=
    double_five_centralizer_card_le_four_thousand_fifty
      X P hcard h5 hnotAlt uP huPorder hsupportTen
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ := h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  exact FiveTupleBurnside.conjugacy_orbit_overfills
    X P (by rw [hcard]; norm_num) hP5 uP 15120
    (by omega)
    (card_fixedBy_five_of_mem_double_five_conjugacy_orbit
      X P hcard uP hsupportTen)

end FiveTransitive.Degree19

end CFSG
