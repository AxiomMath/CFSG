module

public import CFSG.Permutation.FiveTransitive.HallConfigurationSets
public import CFSG.Permutation.FiveTransitive.HallReflectionFactories
public import CFSG.Permutation.FiveTransitive.HallReflectionTransitivity
public import CFSG.Permutation.FiveTransitive.HallRegularOrbits

public section

namespace CFSG

namespace FiveTransitive.Research.HallBranchOrbitData

open MulAction
open Research.HallConfiguration
open Research.HallOrbitTransitivity
open Research.HallReflectionData
open Research.HallReflectionFactories
open Research.HallReflectionTransitivity
open Research.HallRegularOrbits
open Research.HallConfigurationSets

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem exists_regularOrbitData_six
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 27 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hsix : SixPointConfiguration e a b p q) :
    ∃ y : X,
      y ∉ exceptionalSet (X := X) a b ∧
      5 ≤ (MulAction.orbit
        (hallCentralizer (X := X) a b) y).ncard ∧
      (∀ x : X, x ∉ exceptionalSet (X := X) a b →
        (MulAction.orbit (hallCentralizer (X := X) a b) x).ncard =
          (MulAction.orbit
            (hallCentralizer (X := X) a b) y).ncard) ∧
      (∀ x : X, x ∉ exceptionalSet (X := X) a b →
        ∃ k : hallCentralizer (X := X) a b,
          (k : G) • x ∈ regularFourSet a b y) := by
  classical
  rcases hsix with ⟨hq, hpq, hFa, hFb, hFc, hEcard₀⟩
  have hap : a • p = q := hq.symm
  have hEcard : (exceptionalSet (X := X) a b).ncard = 6 := by
    simpa only [exceptionalSet, exceptionalFixedSet] using hEcard₀
  have he : ∀ i, e i ∈ exceptionalSet (X := X) a b := by
    intro i
    fin_cases i <;> simp [exceptionalSet, hFa, hFc]
  have hoddC : Odd (Nat.card (hallCentralizer (X := X) a b)) :=
    hallCentralizer_card_odd e a b he hodd
  have hbp : b • p = p := by
    change p ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have hbq : b • q = q := by
    change q ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have h6 : Function.Injective (exceptionalSixMap e p q) :=
    exceptionalSixMap_injective e a b haTwo haBase hbBase
      p q hap hpq hbp hbq
  have hsigma := exceptionalReflection_mapsTo_and_involutive_six
    e a b p q hFa hFb hFc h6
  have hreflect := reflectionFactory_six
    h4 (by omega) e hodd a b haTwo hbTwo hab haBase hbBase
      p q hap hpq hFa hFb hFc
  have hE_lt : (exceptionalSet (X := X) a b).ncard <
      (Set.univ : Set X).ncard := by
    rw [hEcard, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  obtain ⟨y, _hyUniv, hy⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hE_lt
  have hconnectRaw :=
    exists_hallCentralizer_maps_into_fourSet_of_reflections
      a b haTwo hbTwo hab (exceptionalSet (X := X) a b) rfl
      (exceptionalReflection e p q) hsigma.1 hsigma.2 hoddC
      hreflect y hy
  have hconnect : ∀ x : X, x ∉ exceptionalSet (X := X) a b →
      ∃ k : hallCentralizer (X := X) a b,
        (k : G) • x ∈ regularFourSet a b y := by
    intro x hx
    simpa only [regularFourSet] using hconnectRaw x hx
  have hcommon := regular_orbit_ncard_eq a b y hconnect
  have hcompl := compl_exceptionalSet_ncard_eq_four_mul_orbit_ncard
    a b haTwo hbTwo hab hoddC y hy hconnect
  have hsplit := Set.ncard_add_ncard_compl
    (exceptionalSet (X := X) a b)
  have htLower : 5 ≤
      (MulAction.orbit (hallCentralizer (X := X) a b) y).ncard := by
    rw [hEcard, hcompl, Nat.card_eq_fintype_card] at hsplit
    omega
  exact ⟨y, hy, htLower, hcommon, hconnect⟩

theorem exists_regularOrbitData_seven
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 27 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hseven : SevenPointConfiguration e a b p q) :
    ∃ r y : X,
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      MulAction.fixedBy X a = {e 0, e 1, r} ∧
      MulAction.fixedBy X b = {p, q, r} ∧
      MulAction.fixedBy X (a * b) = {e 2, e 3, r} ∧
      MulAction.fixedBy X a ∩ MulAction.fixedBy X b = {r} ∧
      exceptionalSet (X := X) a b = Set.range e ∪ {p, q, r} ∧
      Disjoint (Set.range e) ({p, q, r} : Set X) ∧
      ({p, q, r} : Set X).ncard = 3 ∧
      y ∉ exceptionalSet (X := X) a b ∧
      5 ≤ (MulAction.orbit
        (hallCentralizer (X := X) a b) y).ncard ∧
      (∀ x : X, x ∉ exceptionalSet (X := X) a b →
        (MulAction.orbit (hallCentralizer (X := X) a b) x).ncard =
          (MulAction.orbit
            (hallCentralizer (X := X) a b) y).ncard) ∧
      (∀ x : X, x ∉ exceptionalSet (X := X) a b →
        ∃ k : hallCentralizer (X := X) a b,
          (k : G) • x ∈ regularFourSet a b y) := by
  classical
  obtain ⟨r, hpq, hpr, hqr, hFa, hFb, hFc, hD,
      hSet, hBT, hTcard⟩ :=
    sevenPointConfiguration_sets e a b p q hseven
  have hq : q = a • p := hseven.1
  have hap : a • p = q := hq.symm
  have hEcard : (exceptionalSet (X := X) a b).ncard = 7 := by
    rw [hSet, Set.ncard_union_eq hBT,
      Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin, hTcard]
  have he : ∀ i, e i ∈ exceptionalSet (X := X) a b := by
    intro i
    rw [hSet]
    exact Or.inl ⟨i, rfl⟩
  have hoddC : Odd (Nat.card (hallCentralizer (X := X) a b)) :=
    hallCentralizer_card_odd e a b he hodd
  have hbp : b • p = p := by
    change p ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have hbq : b • q = q := by
    change q ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have hbr : b • r = r := by
    change r ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have h6 : Function.Injective (exceptionalSixMap e p q) :=
    exceptionalSixMap_injective e a b haTwo haBase hbBase
      p q hap hpq hbp hbq
  have hbmove (i : Fin 4) : b • e i ≠ e i := by
    rw [hbBase]
    fin_cases i <;> exact e.injective.ne (by decide)
  have hrei (i : Fin 4) : r ≠ e i := by
    intro h
    apply hbmove i
    calc
      b • e i = b • r := congrArg (fun z : X ↦ b • z) h.symm
      _ = r := hbr
      _ = e i := h
  have hrNotRange : r ∉ Set.range (exceptionalSixMap e p q) := by
    rintro ⟨i, hi⟩
    fin_cases i
    · exact hpr (by simpa [exceptionalSixMap] using hi)
    · exact hqr (by simpa [exceptionalSixMap] using hi)
    · exact hrei 0 (by simpa [exceptionalSixMap] using hi.symm)
    · exact hrei 1 (by simpa [exceptionalSixMap] using hi.symm)
    · exact hrei 2 (by simpa [exceptionalSixMap] using hi.symm)
    · exact hrei 3 (by simpa [exceptionalSixMap] using hi.symm)
  have hsigma := exceptionalReflection_mapsTo_and_involutive_seven
    e a b p q r hFa hFb hFc h6 hrNotRange
  have hreflect := reflectionFactory_seven
    h4 (by omega) e hodd a b haTwo hbTwo hab haBase hbBase
      p q r hap hpq hFa hFb hFc hD
  have hE_lt : (exceptionalSet (X := X) a b).ncard <
      (Set.univ : Set X).ncard := by
    rw [hEcard, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  obtain ⟨y, _hyUniv, hy⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hE_lt
  have hconnectRaw :=
    exists_hallCentralizer_maps_into_fourSet_of_reflections
      a b haTwo hbTwo hab (exceptionalSet (X := X) a b) rfl
      (exceptionalReflection e p q) hsigma.1 hsigma.2 hoddC
      hreflect y hy
  have hconnect : ∀ x : X, x ∉ exceptionalSet (X := X) a b →
      ∃ k : hallCentralizer (X := X) a b,
        (k : G) • x ∈ regularFourSet a b y := by
    intro x hx
    simpa only [regularFourSet] using hconnectRaw x hx
  have hcommon := regular_orbit_ncard_eq a b y hconnect
  have hcompl := compl_exceptionalSet_ncard_eq_four_mul_orbit_ncard
    a b haTwo hbTwo hab hoddC y hy hconnect
  have hsplit := Set.ncard_add_ncard_compl
    (exceptionalSet (X := X) a b)
  have htLower : 5 ≤
      (MulAction.orbit (hallCentralizer (X := X) a b) y).ncard := by
    rw [hEcard, hcompl, Nat.card_eq_fintype_card] at hsplit
    omega
  exact ⟨r, y, hpq, hpr, hqr, hFa, hFb, hFc, hD,
    hSet, hBT, hTcard, hy, htLower, hcommon, hconnect⟩

end FiveTransitive.Research.HallBranchOrbitData

end CFSG
