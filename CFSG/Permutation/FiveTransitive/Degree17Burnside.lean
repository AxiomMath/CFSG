module

public import CFSG.Permutation.FiveTransitive.Degree17Conjugacy
public import CFSG.Permutation.FiveTransitive.Degree17Centralizer
public import Mathlib.CategoryTheory.Action.Concrete

public section

namespace CFSG

namespace FiveTransitive.Degree17

open MulAction SubMulAction Subgroup

private theorem conjugacy_orbit_overfills_four_tuple_burnside
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 17)
    (hP4 : MulAction.IsMultiplyPretransitive P X 4)
    (u : P)
    (hAcard :
      Nat.card (MulAction.orbit (ConjAct P) u) * 13 =
        Nat.card P)
    (hfixed :
      ∀ a : MulAction.orbit (ConjAct P) u,
        Fintype.card
          (MulAction.fixedBy (Fin 4 ↪ X) (a.1 : P)) = 24) :
    False := by
  classical
  let A := MulAction.orbit (ConjAct P) u
  letI : Fintype A := Fintype.ofFinite _
  let val : A → P := fun a => a.1
  have hvalInjective : Function.Injective val :=
    Subtype.val_injective
  let T := Fin 4 ↪ X
  letI : MulAction.IsPretransitive P T := by
    change MulAction.IsMultiplyPretransitive P X 4
    exact hP4
  letI : Nonempty T := Fintype.card_pos_iff.mp (by
    change 0 < Fintype.card (Fin 4 ↪ X)
    rw [Fintype.card_embedding_eq, Fintype.card_fin, hcard]
    norm_num)
  letI : Unique (MulAction.orbitRel.Quotient P T) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P T).mp hP4)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P T
  have hburnside' :
      (∑ q : P, Fintype.card (MulAction.fixedBy T q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  have hfixed' (a : A) :
      Fintype.card (MulAction.fixedBy T (val a)) = 24 :=
    hfixed a
  have hselectedSum :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy T (val a))) =
        Fintype.card A * 24 := by
    simp_rw [hfixed']
    simp
  have hselectedLe :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy T (val a))) ≤
        ∑ q : P, Fintype.card (MulAction.fixedBy T q) := by
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
  have hApos : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr
      ⟨⟨u, MulAction.mem_orbit_self u⟩⟩
  have hoverfill : Fintype.card A * 24 ≤ Nat.card P := by
    calc
      Fintype.card A * 24 =
          ∑ a : A,
            Fintype.card (MulAction.fixedBy T (val a)) :=
        hselectedSum.symm
      _ ≤ ∑ q : P,
          Fintype.card (MulAction.fixedBy T q) :=
        hselectedLe
      _ = Nat.card P := hburnside'
  change Nat.card A * 13 = Nat.card P at hAcard
  rw [Nat.card_eq_fintype_card] at hAcard
  rw [← hAcard] at hoverfill
  omega

theorem alternatingGroup_le_of_five_transitive_of_card_eq_seventeen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 17)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ P := by
  classical
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq
      (s := (Set.univ : Set X)) (n := 5) (by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
        omega)
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hindex :
      (fixingSubgroup P s).index = 742560 := by
    omega
  have hindexCard := (fixingSubgroup P s).index_mul_card
  have h13dvd : 13 ∣ Nat.card P := by
    rw [hindex] at hindexCard
    rw [← hindexCard]
    exact dvd_mul_of_dvd_left (by norm_num) _
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' 13 h13dvd
  by_contra hnotAlt
  have hcentralizer :
      Nat.card (Subgroup.centralizer ({u} : Set P)) = 13 :=
    centralizer_card_eq_thirteen_of_not_alternating
      X P hcard h5 hnotAlt u huorder
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5) (by omega) (by
        rw [Nat.card_eq_fintype_card, hcard]
        omega)
  exact conjugacy_orbit_overfills_four_tuple_burnside
    X P hcard hP4 u
    (card_conjugacy_orbit_mul_thirteen u hcentralizer)
    (card_fixedBy_four_of_mem_conjugacy_orbit
      X P hcard u huorder)

end FiveTransitive.Degree17

end CFSG
