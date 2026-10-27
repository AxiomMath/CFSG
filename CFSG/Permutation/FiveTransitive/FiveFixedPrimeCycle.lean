module

public import CFSG.Permutation.FiveTransitive.FewFixedPrimeCycle
public import CFSG.Permutation.FiveTransitive.FourFixedPrimeCycle

public section

namespace CFSG

namespace FiveTransitive.FiveFixedPrimeCycle

open MulAction SubMulAction Subgroup

private theorem card_fixedBy_five_of_mem_conjugacy_orbit
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    {p : ℕ} (hp : p.Prime) (hpSeven : 7 ≤ p)
    (hcard : Fintype.card X = p + 5)
    (u : P) (huorder : orderOf u = p)
    (a : MulAction.orbit (ConjAct P) u) :
    Fintype.card
      (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) = 120 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = p := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = p := huorder
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      exact hp) (by
        rw [hcard, hgorder]
        omega)
  have hgsupport : g.support.card = p := by
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
      ((a.1 : P) : Equiv.Perm X).support.card = p := by
    calc
      ((a.1 : P) : Equiv.Perm X).support.card =
          (((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹).support.card :=
        Equiv.Perm.card_support_conj.symm
      _ = g.support.card := by rw [hconjPerm]
      _ = p := hgsupport
  have hfixedX :
      Fintype.card
        (MulAction.fixedBy X (a.1 : P)) = 5 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      hasupport]
    omega
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

theorem alternatingGroup_le_of_prime_dvd_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    {p : ℕ} (hp : p.Prime) (hpSeven : 7 ≤ p)
    (hpLt : p < 120)
    (hcard : Fintype.card X = p + 5)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hpdiv : p ∣ Nat.card P) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' p hpdiv
  by_contra hnotAlt
  have hcentralizer :
      Nat.card
          (Subgroup.centralizer ({u} : Set P)) = p :=
    FewFixedPrimeCycle.centralizer_card_eq_prime_of_not_alternating
      X P hp hpSeven (by norm_num) hcard h5 hnotAlt
        u huorder
  let A := MulAction.orbit (ConjAct P) u
  letI : Fintype A := Fintype.ofFinite _
  let val : A → P := fun a => a.1
  have hvalInjective : Function.Injective val :=
    Subtype.val_injective
  have hAcard :
      Fintype.card A * p = Nat.card P := by
    simpa [A, Nat.card_eq_fintype_card] using
      FourFixedPrimeCycle.card_conjugacy_orbit_mul_prime
        u hcentralizer
  have hfixed (a : A) :
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) (val a)) = 120 :=
    card_fixedBy_five_of_mem_conjugacy_orbit
      X P hp hpSeven hcard u huorder a
  have hselectedSum :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) =
        Fintype.card A * 120 := by
    simp_rw [hfixed]
    simp
  have hselectedLe :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) ≤
        ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) := by
    calc
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card
              (MulAction.fixedBy (Fin 5 ↪ X) q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) := by
        simp
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
  letI : Nonempty (Fin 5 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq, Fintype.card_fin,
        hcard]
      exact Nat.descFactorial_pos.mpr (by omega))
  letI : Unique
      (MulAction.orbitRel.Quotient P (Fin 5 ↪ X)) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P (Fin 5 ↪ X)).mp hP5)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      P (Fin 5 ↪ X)
  have hburnside' :
      (∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  have hoverfill :
      Fintype.card A * 120 ≤ Nat.card P := by
    calc
      Fintype.card A * 120 =
          ∑ a : A,
            Fintype.card
              (MulAction.fixedBy (Fin 5 ↪ X) (val a)) :=
        hselectedSum.symm
      _ ≤ ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) :=
        hselectedLe
      _ = Nat.card P := hburnside'
  rw [← hAcard] at hoverfill
  have hApos : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr
      ⟨⟨u, MulAction.mem_orbit_self u⟩⟩
  nlinarith

end FiveTransitive.FiveFixedPrimeCycle

end CFSG
