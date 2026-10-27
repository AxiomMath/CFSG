module

public import CFSG.Permutation.FiveTransitive.HallVFourOrbits

public section

namespace CFSG

namespace FiveTransitive.Research.HallConfiguration

open MulAction
open Research.HallInvolutionConsequence
open Research.HallVFourOrbits
open Research.SharpFourDegreeCompletion

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

@[expose] def exceptionalFixedSet (a b : G) : Set X :=
  (MulAction.fixedBy X a ∪ MulAction.fixedBy X b) ∪
    MulAction.fixedBy X (a * b)

@[expose] def SixPointConfiguration (e : Fin 4 ↪ X) (a b : G) (p q : X) : Prop :=
  q = a • p ∧
  p ≠ q ∧
  MulAction.fixedBy X a = {e 0, e 1} ∧
  MulAction.fixedBy X b = {p, q} ∧
  MulAction.fixedBy X (a * b) = {e 2, e 3} ∧
  (exceptionalFixedSet (X := X) a b).ncard = 6

@[expose] def SevenPointConfiguration (e : Fin 4 ↪ X) (a b : G) (p q : X) : Prop :=
  q = a • p ∧
  p ≠ q ∧
  ∃ r : X,
    MulAction.fixedBy X a = {e 0, e 1, r} ∧
    MulAction.fixedBy X b = {p, q, r} ∧
    MulAction.fixedBy X (a * b) = {e 2, e 3, r} ∧
    MulAction.fixedBy X a ∩ MulAction.fixedBy X b = {r} ∧
    (exceptionalFixedSet (X := X) a b).ncard = 7

theorem exists_hall_configuration
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e))) :
    ∃ a b : G, ∃ p q : X,
      a ^ 2 = 1 ∧ a ≠ 1 ∧
      b ^ 2 = 1 ∧ b ≠ 1 ∧
      (a * b) ^ 2 = 1 ∧ a * b ≠ 1 ∧
      Commute a b ∧
      (∀ i, a • e i =
        e (Research.SharpFourBound.baseSingleSwap i)) ∧
      (∀ i, b • e i =
        e (Research.SharpFourBound.baseDoubleSwap i)) ∧
      (SixPointConfiguration e a b p q ∨
        SevenPointConfiguration e a b p q) := by
  classical
  obtain ⟨a, b, haTwo, haNe, hbTwo, hbNe, hab, haBase, hbBase⟩ :=
    exists_commuting_single_double_lifts h4 e hodd
  let c : G := a * b
  have hcTwo : c ^ 2 = 1 := by
    simpa only [c] using product_involution_sq a b haTwo hbTwo hab
  have hcNe : c ≠ 1 := by
    simpa only [c] using product_lift_ne_one e a b haBase hbBase
  obtain ⟨qab, hqab⟩ :=
    all_involutions_conjugate h4 hX e hodd
      a b haTwo hbTwo haNe hbNe
  obtain ⟨qcb, hqcb⟩ :=
    all_involutions_conjugate h4 hX e hodd
      c b hcTwo hbTwo hcNe hbNe
  have hcardAB : (MulAction.fixedBy X a).ncard =
      (MulAction.fixedBy X b).ncard :=
    fixedBy_ncard_eq_of_conjugate a b qab hqab
  have hcardCB : (MulAction.fixedBy X c).ncard =
      (MulAction.fixedBy X b).ncard :=
    fixedBy_ncard_eq_of_conjugate c b qcb hqcb
  obtain ⟨p, hbp, hap⟩ :=
    exists_double_fixed_single_moved e a b haBase hbBase hcardAB
  let q : X := a • p
  let Fa : Set X := MulAction.fixedBy X a
  let Fb : Set X := MulAction.fixedBy X b
  let Fc : Set X := MulAction.fixedBy X c
  let D : Set X := Fa ∩ Fb
  have hFbCases : Fb.ncard = 2 ∨ Fb.ncard = 3 := by
    simpa only [Fb] using
      involution_fixedBy_ncard_eq_two_or_three
        h4 hX e hodd b hbTwo hbNe
  have hFbUpper : Fb.ncard ≤ 3 := by
    rcases hFbCases with htwo | hthree <;> omega
  obtain ⟨hFb, hFa, hFc⟩ :=
    fixedBy_decomposition e a b haTwo hbTwo hab haBase hbBase
      hcardAB (by simpa only [Fc, c] using hcardCB)
      (by simpa only [Fb] using hFbUpper) p hbp hap
  have hFb' : Fb = {p, q} ∪ D := by
    simpa only [Fb, Fa, D, q] using hFb
  have hFa' : Fa = {e 0, e 1} ∪ D := by
    simpa only [Fb, Fa, D] using hFa
  have hFc' : Fc = {e 2, e 3} ∪ D := by
    simpa only [Fb, Fa, Fc, D, c] using hFc
  have hpq : p ≠ q := by
    simpa only [q] using hap.symm
  have haq : a • q = p := by
    dsimp only [q]
    rw [← mul_smul, ← pow_two, haTwo, one_smul]
  have hpairD : Disjoint ({p, q} : Set X) D := by
    rw [Set.disjoint_left]
    intro z hz hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hap hD.1
    · exact hpq (haq.symm.trans hD.1)
  have hpairCard : ({p, q} : Set X).ncard = 2 :=
    Set.ncard_pair hpq
  have hFbCard : Fb.ncard = 2 + D.ncard := by
    rw [hFb', Set.ncard_union_eq hpairD, hpairCard]
  have hac : a * c = b := by
    dsimp only [c]
    rw [← mul_assoc, ← pow_two, haTwo, one_mul]
  have hbc : b * c = a := by
    dsimp only [c]
    calc
      b * (a * b) = (b * a) * b := by rw [← mul_assoc]
      _ = (a * b) * b := by rw [← hab.eq]
      _ = a * (b * b) := by rw [mul_assoc]
      _ = a := by rw [← pow_two, hbTwo, mul_one]
  have hFaFc : Fa ∩ Fc = D := by
    ext x
    constructor
    · rintro ⟨hxa, hxc⟩
      refine ⟨hxa, ?_⟩
      change b • x = x
      change a • x = x at hxa
      change c • x = x at hxc
      calc
        b • x = (a * c) • x := by rw [hac]
        _ = a • (c • x) := mul_smul _ _ _
        _ = a • x := by rw [hxc]
        _ = x := hxa
    · rintro ⟨hxa, hxb⟩
      refine ⟨hxa, ?_⟩
      change c • x = x
      change a • x = x at hxa
      change b • x = x at hxb
      dsimp only [c]
      rw [mul_smul, hxb, hxa]
  have hFbFc : Fb ∩ Fc = D := by
    ext x
    constructor
    · rintro ⟨hxb, hxc⟩
      refine ⟨?_, hxb⟩
      change a • x = x
      change b • x = x at hxb
      change c • x = x at hxc
      calc
        a • x = (b * c) • x := by rw [hbc]
        _ = b • (c • x) := mul_smul _ _ _
        _ = b • x := by rw [hxc]
        _ = x := hxb
    · rintro ⟨hxa, hxb⟩
      refine ⟨hxb, ?_⟩
      change c • x = x
      change a • x = x at hxa
      change b • x = x at hxb
      dsimp only [c]
      rw [mul_smul, hxb, hxa]
  let U : Set X := (Fa ∪ Fb) ∪ Fc
  refine ⟨a, b, p, q, haTwo, haNe, hbTwo, hbNe, ?_, ?_, hab,
    haBase, hbBase, ?_⟩
  · simpa only [c] using hcTwo
  · simpa only [c] using hcNe
  rcases hFbCases with hFbTwo | hFbThree
  · have hDcard : D.ncard = 0 := by omega
    have hDempty : D = ∅ :=
      (Set.ncard_eq_zero (s := D) (Set.toFinite D)).mp hDcard
    have hFaPair : Fa = {e 0, e 1} := by
      rw [hFa', hDempty, Set.union_empty]
    have hFbPair : Fb = {p, q} := by
      rw [hFb', hDempty, Set.union_empty]
    have hFcPair : Fc = {e 2, e 3} := by
      rw [hFc', hDempty, Set.union_empty]
    have hUle : U.ncard ≤ 6 := by
      have houter := Set.ncard_union_le (Fa ∪ Fb) Fc
      have hinner := Set.ncard_union_le Fa Fb
      have hFaCard : Fa.ncard = 2 := by
        simpa only [Fa, Fb] using hcardAB.trans hFbTwo
      have hFcCard : Fc.ncard = 2 := by
        simpa only [Fc, Fb, c] using hcardCB.trans hFbTwo
      dsimp only [U]
      omega
    have hUcases : U.ncard = 6 ∨ U.ncard = 7 := by
      simpa only [U, Fa, Fb, Fc, c] using
        exceptional_fixed_union_ncard_eq_six_or_seven
          e a b haTwo hbTwo hab haBase hbBase hcardAB
            (by simpa only [c] using hcardCB)
            (by simpa only [Fb] using hFbUpper) p hbp hap
    have hUcard : U.ncard = 6 := by
      rcases hUcases with hsix | hseven
      · exact hsix
      · omega
    left
    refine ⟨rfl, hpq, ?_, ?_, ?_, ?_⟩
    · simpa only [Fa] using hFaPair
    · simpa only [Fb] using hFbPair
    · simpa only [Fc, c] using hFcPair
    · simpa only [exceptionalFixedSet, U, Fa, Fb, Fc, c] using hUcard
  · have hDcard : D.ncard = 1 := by omega
    obtain ⟨r, hDr⟩ := Set.ncard_eq_one.mp hDcard
    have hFaTriple : Fa = {e 0, e 1, r} := by
      calc
        Fa = {e 0, e 1} ∪ D := hFa'
        _ = {e 0, e 1, r} := by
          rw [hDr]
          ext x
          simp only [Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff]
          tauto
    have hFbTriple : Fb = {p, q, r} := by
      calc
        Fb = {p, q} ∪ D := hFb'
        _ = {p, q, r} := by
          rw [hDr]
          ext x
          simp only [Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff]
          tauto
    have hFcTriple : Fc = {e 2, e 3, r} := by
      calc
        Fc = {e 2, e 3} ∪ D := hFc'
        _ = {e 2, e 3, r} := by
          rw [hDr]
          ext x
          simp only [Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff]
          tauto
    have hFaCard : Fa.ncard = 3 := by
      simpa only [Fa, Fb] using hcardAB.trans hFbThree
    have hFcCard : Fc.ncard = 3 := by
      simpa only [Fc, Fb, c] using hcardCB.trans hFbThree
    have hFaFbUnionCard : (Fa ∪ Fb).ncard = 5 := by
      have hsum := Set.ncard_union_add_ncard_inter Fa Fb
      have hinter : (Fa ∩ Fb).ncard = 1 := by
        change D.ncard = 1
        exact hDcard
      omega
    have hUnionInter : (Fa ∪ Fb) ∩ Fc = D := by
      calc
        (Fa ∪ Fb) ∩ Fc = (Fa ∩ Fc) ∪ (Fb ∩ Fc) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_union]
          tauto
        _ = D := by rw [hFaFc, hFbFc, Set.union_self]
    have hUcard : U.ncard = 7 := by
      have hsum := Set.ncard_union_add_ncard_inter (Fa ∪ Fb) Fc
      have hinter : ((Fa ∪ Fb) ∩ Fc).ncard = 1 := by
        rw [hUnionInter]
        exact hDcard
      dsimp only [U]
      omega
    right
    refine ⟨rfl, hpq, r, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Fa] using hFaTriple
    · simpa only [Fb] using hFbTriple
    · simpa only [Fc, c] using hFcTriple
    · change Fa ∩ Fb = {r}
      exact hDr
    · simpa only [exceptionalFixedSet, U, Fa, Fb, Fc, c] using hUcard

end FiveTransitive.Research.HallConfiguration

end CFSG
