module

public import CFSG.Permutation.FiveTransitive.HallOrbitTransitivity
public import CFSG.Permutation.FiveTransitive.HallExceptionalOrientation

public section

namespace CFSG

namespace FiveTransitive.Research.HallReflectionData

open MulAction
open Research.HallOrbitTransitivity
open Research.HallExceptionalOrientation
open Research.HallInvolutionConsequence

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

@[expose] def exceptionalSixMap (e : Fin 4 ↪ X) (p q : X) : Fin 6 → X :=
  ![p, q, e 0, e 1, e 2, e 3]

noncomputable def exceptionalReflection
    (e : Fin 4 ↪ X) (p q : X) : Equiv.Perm X := by
  classical
  exact Equiv.swap (e 0) (e 1) *
    Equiv.swap (e 2) q * Equiv.swap (e 3) p

theorem exceptionalSixMap_injective
    (e : Fin 4 ↪ X) (a b : G)
    (_haTwo : a ^ 2 = 1)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hap : a • p = q) (hpq : p ≠ q)
    (hbp : b • p = p) (hbq : b • q = q) :
    Function.Injective (exceptionalSixMap e p q) := by
  have ha0 : a • e 0 = e 0 := by rw [haBase]; rfl
  have ha1 : a • e 1 = e 1 := by rw [haBase]; rfl
  have hb0move : b • e 0 ≠ e 0 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hb1move : b • e 1 ≠ e 1 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hb2move : b • e 2 ≠ e 2 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hb3move : b • e 3 ≠ e 3 := by
    rw [hbBase]
    exact e.injective.ne (by decide)
  have hpe0 : p ≠ e 0 := by
    intro h
    apply hpq
    rw [← hap, h, ha0]
  have hpe1 : p ≠ e 1 := by
    intro h
    apply hpq
    rw [← hap, h, ha1]
  have hpe2 : p ≠ e 2 := by
    intro h
    apply hb2move
    rw [← h, hbp]
  have hpe3 : p ≠ e 3 := by
    intro h
    apply hb3move
    rw [← h, hbp]
  have hqe0 : q ≠ e 0 := by
    intro h
    apply hb0move
    rw [← h, hbq]
  have hqe1 : q ≠ e 1 := by
    intro h
    apply hb1move
    rw [← h, hbq]
  have hqe2 : q ≠ e 2 := by
    intro h
    apply hb2move
    rw [← h, hbq]
  have hqe3 : q ≠ e 3 := by
    intro h
    apply hb3move
    rw [← h, hbq]
  have hqp : q ≠ p := hpq.symm
  have he0p : e 0 ≠ p := hpe0.symm
  have he1p : e 1 ≠ p := hpe1.symm
  have he2p : e 2 ≠ p := hpe2.symm
  have he3p : e 3 ≠ p := hpe3.symm
  have he0q : e 0 ≠ q := hqe0.symm
  have he1q : e 1 ≠ q := hqe1.symm
  have he2q : e 2 ≠ q := hqe2.symm
  have he3q : e 3 ≠ q := hqe3.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [exceptionalSixMap, e.injective.eq_iff, hpq,
      hpe0, hpe1, hpe2, hpe3, hqe0, hqe1, hqe2, hqe3,
      hqp, he0p, he1p, he2p, he3p, he0q, he1q, he2q, he3q] at hij ⊢

private theorem exceptionalReflection_values
    (e : Fin 4 ↪ X) (p q : X)
    (h6 : Function.Injective (exceptionalSixMap e p q)) :
    exceptionalReflection e p q (e 0) = e 1 ∧
      exceptionalReflection e p q (e 1) = e 0 ∧
      exceptionalReflection e p q (e 2) = q ∧
      exceptionalReflection e p q q = e 2 ∧
      exceptionalReflection e p q (e 3) = p ∧
      exceptionalReflection e p q p = e 3 := by
  have hpq : p ≠ q := by
    simpa [exceptionalSixMap] using h6.ne (show (0 : Fin 6) ≠ 1 by decide)
  have hpe0 : p ≠ e 0 := by
    simpa [exceptionalSixMap] using h6.ne (show (0 : Fin 6) ≠ 2 by decide)
  have hpe1 : p ≠ e 1 := by
    simpa [exceptionalSixMap] using h6.ne (show (0 : Fin 6) ≠ 3 by decide)
  have hpe2 : p ≠ e 2 := by
    simpa [exceptionalSixMap] using h6.ne (show (0 : Fin 6) ≠ 4 by decide)
  have hpe3 : p ≠ e 3 := by
    simpa [exceptionalSixMap] using h6.ne (show (0 : Fin 6) ≠ 5 by decide)
  have hqe0 : q ≠ e 0 := by
    simpa [exceptionalSixMap] using h6.ne (show (1 : Fin 6) ≠ 2 by decide)
  have hqe1 : q ≠ e 1 := by
    simpa [exceptionalSixMap] using h6.ne (show (1 : Fin 6) ≠ 3 by decide)
  have hqe2 : q ≠ e 2 := by
    simpa [exceptionalSixMap] using h6.ne (show (1 : Fin 6) ≠ 4 by decide)
  have hqe3 : q ≠ e 3 := by
    simpa [exceptionalSixMap] using h6.ne (show (1 : Fin 6) ≠ 5 by decide)
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have h03 : e 0 ≠ e 3 := e.injective.ne (by decide)
  have h12 : e 1 ≠ e 2 := e.injective.ne (by decide)
  have h13 : e 1 ≠ e 3 := e.injective.ne (by decide)
  have h23 : e 2 ≠ e 3 := e.injective.ne (by decide)
  simp only [exceptionalReflection, Equiv.Perm.mul_apply]
  simp [Equiv.swap_apply_def, hpq, hpq.symm,
    hpe0, hpe0.symm, hpe1, hpe1.symm, hpe2, hpe2.symm,
    hpe3, hpe3.symm, hqe0, hqe0.symm, hqe1, hqe1.symm,
    hqe2, hqe2.symm, hqe3, hqe3.symm, h01, h01.symm,
    h02, h02.symm, h03, h03.symm, h12, h12.symm,
    h13, h13.symm, h23, h23.symm]

private theorem left_quarterTurn_relations
    (a b u : G) (haTwo : a ^ 2 = 1) (hab : Commute a b)
    (huSq : u ^ 2 = a) (hua : u * a = a * u)
    (hub : u * b = (a * b) * u) :
    (a * u) ^ 2 = a ∧
      (a * u) * a = a * (a * u) ∧
      (a * u) * b = (a * b) * (a * u) := by
  have haa : a * a = 1 := by simpa [pow_two] using haTwo
  have huu : u * u = a := by simpa [pow_two] using huSq
  constructor
  · calc
      (a * u) ^ 2 = (a * u) * (a * u) := by rw [pow_two]
      _ = a * (u * a) * u := by group
      _ = a * (a * u) * u := by rw [hua]
      _ = (a * a) * (u * u) := by group
      _ = a := by rw [haa, one_mul, huu]
  constructor
  · calc
      (a * u) * a = a * (u * a) := by rw [mul_assoc]
      _ = a * (a * u) := by rw [hua]
  · calc
      (a * u) * b = a * (u * b) := by rw [mul_assoc]
      _ = a * ((a * b) * u) := by rw [hub]
      _ = b * u := by
        rw [← mul_assoc, ← mul_assoc, haa, one_mul]
      _ = (a * b) * (a * u) := by
        symm
        calc
          (a * b) * (a * u) = a * (b * a) * u := by group
          _ = a * (a * b) * u := by rw [hab.eq.symm]
          _ = (a * a) * (b * u) := by group
          _ = b * u := by rw [haa, one_mul]

private theorem regular_b_smul
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b) (y : X)
    (hya : a • y ≠ y) (hyb : b • y ≠ y)
    (hyc : (a * b) • y ≠ y) :
    a • (b • y) ≠ b • y ∧
      b • (b • y) ≠ b • y ∧
      (a * b) • (b • y) ≠ b • y := by
  have haa (z : X) : a • (a • z) = z := by
    rw [← mul_smul, ← pow_two, haTwo, one_smul]
  have hbb (z : X) : b • (b • z) = z := by
    rw [← mul_smul, ← pow_two, hbTwo, one_smul]
  constructor
  · intro h
    apply hya
    calc
      a • y = b • (a • (b • y)) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        calc
          a = a * (b * b) := by rw [← pow_two, hbTwo, mul_one]
          _ = (a * b) * b := by rw [mul_assoc]
          _ = (b * a) * b := by rw [hab.eq]
      _ = b • (b • y) := congrArg (fun z : X ↦ b • z) h
      _ = y := hbb y
  constructor
  · simpa only [hbb y] using hyb.symm
  · intro h
    have hcb : (a * b) • (b • y) = a • y := by
      rw [← mul_smul]
      congr 1
      rw [mul_assoc, ← pow_two, hbTwo, mul_one]
    have haby : a • y = b • y := hcb.symm.trans h
    apply hyc
    calc
      (a * b) • y = a • (b • y) := mul_smul _ _ _
      _ = a • (a • y) := congrArg (fun z : X ↦ a • z) haby.symm
      _ = y := haa y

private theorem regular_a_smul
    (a b : G) (haTwo : a ^ 2 = 1) (hab : Commute a b)
    (x : X)
    (hxa : a • x ≠ x) (hxb : b • x ≠ x)
    (hxc : (a * b) • x ≠ x) :
    a • (a • x) ≠ a • x ∧
      b • (a • x) ≠ a • x ∧
      (a * b) • (a • x) ≠ a • x := by
  have haa : a • (a • x) = x := by
    rw [← mul_smul, ← pow_two, haTwo, one_smul]
  constructor
  · simpa only [haa] using hxa.symm
  constructor
  · intro h
    apply hxb
    apply MulAction.injective a
    calc
      a • (b • x) = b • (a • x) := by
        rw [← mul_smul, ← mul_smul, hab.eq]
      _ = a • x := h
  · intro h
    apply hxc
    apply MulAction.injective a
    calc
      a • ((a * b) • x) = (a * b) • (a • x) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        calc
          a * (a * b) = (a * a) * b := by rw [← mul_assoc]
          _ = b := by rw [← pow_two, haTwo, one_mul]
          _ = (a * b) * a := by
            symm
            calc
              (a * b) * a = a * (b * a) := by rw [mul_assoc]
              _ = a * (a * b) := by rw [hab.eq.symm]
              _ = (a * a) * b := by rw [← mul_assoc]
              _ = b := by rw [← pow_two, haTwo, one_mul]
      _ = a • x := h

private theorem exceptionalReflection_apply_of_not_range
    (e : Fin 4 ↪ X) (p q z : X)
    (hz : z ∉ Set.range (exceptionalSixMap e p q)) :
    exceptionalReflection e p q z = z := by
  classical
  have hne : ∀ i : Fin 6, z ≠ exceptionalSixMap e p q i := by
    intro i h
    exact hz ⟨i, h.symm⟩
  have h0 : z ≠ p := by simpa [exceptionalSixMap] using hne 0
  have h1 : z ≠ q := by simpa [exceptionalSixMap] using hne 1
  have h2 : z ≠ e 0 := by simpa [exceptionalSixMap] using hne 2
  have h3 : z ≠ e 1 := by simpa [exceptionalSixMap] using hne 3
  have h4 : z ≠ e 2 := by simpa [exceptionalSixMap] using hne 4
  have h5 : z ≠ e 3 := by simpa [exceptionalSixMap] using hne 5
  simp [exceptionalReflection, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, h0, h1, h2, h3, h4, h5]

private theorem exceptionalReflection_involutive
    (e : Fin 4 ↪ X) (p q : X)
    (h6 : Function.Injective (exceptionalSixMap e p q)) :
    Function.Involutive (exceptionalReflection e p q) := by
  classical
  obtain ⟨h0, h1, h2, hq, h3, hp⟩ :=
    exceptionalReflection_values e p q h6
  intro z
  by_cases hz : z ∈ Set.range (exceptionalSixMap e p q)
  · obtain ⟨i, rfl⟩ := hz
    fin_cases i
    · change exceptionalReflection e p q
        (exceptionalReflection e p q p) = p
      rw [hp, h3]
    · change exceptionalReflection e p q
        (exceptionalReflection e p q q) = q
      rw [hq, h2]
    · change exceptionalReflection e p q
        (exceptionalReflection e p q (e 0)) = e 0
      rw [h0, h1]
    · change exceptionalReflection e p q
        (exceptionalReflection e p q (e 1)) = e 1
      rw [h1, h0]
    · change exceptionalReflection e p q
        (exceptionalReflection e p q (e 2)) = e 2
      rw [h2, hq]
    · change exceptionalReflection e p q
        (exceptionalReflection e p q (e 3)) = e 3
      rw [h3, hp]
  · have hzfix : exceptionalReflection e p q z = z :=
      exceptionalReflection_apply_of_not_range e p q z hz
    rw [hzfix, hzfix]

theorem exceptionalReflection_mapsTo_and_involutive_six
    (e : Fin 4 ↪ X) (a b : G) (p q : X)
    (hFa : MulAction.fixedBy X a = {e 0, e 1})
    (hFb : MulAction.fixedBy X b = {p, q})
    (hFc : MulAction.fixedBy X (a * b) = {e 2, e 3})
    (h6 : Function.Injective (exceptionalSixMap e p q)) :
    Set.MapsTo (exceptionalReflection e p q)
        (exceptionalSet (X := X) a b) (exceptionalSet (X := X) a b) ∧
      ∀ z ∈ exceptionalSet (X := X) a b,
        exceptionalReflection e p q (exceptionalReflection e p q z) = z := by
  classical
  obtain ⟨h0, h1, h2, hq, h3, hp⟩ :=
    exceptionalReflection_values e p q h6
  constructor
  · intro z hz
    simp only [exceptionalSet, hFa, hFb, hFc, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with ((hz | hz) | (hz | hz)) | (hz | hz)
    all_goals subst z
    · rw [h0]; simp
    · rw [h1]; simp
    · rw [hp]; simp
    · rw [hq]; simp
    · rw [h2]; simp
    · rw [h3]; simp
  · intro z _
    exact exceptionalReflection_involutive e p q h6 z

theorem exceptionalReflection_mapsTo_and_involutive_seven
    (e : Fin 4 ↪ X) (a b : G) (p q r : X)
    (hFa : MulAction.fixedBy X a = {e 0, e 1, r})
    (hFb : MulAction.fixedBy X b = {p, q, r})
    (hFc : MulAction.fixedBy X (a * b) = {e 2, e 3, r})
    (h6 : Function.Injective (exceptionalSixMap e p q))
    (hr : r ∉ Set.range (exceptionalSixMap e p q)) :
    Set.MapsTo (exceptionalReflection e p q)
        (exceptionalSet (X := X) a b) (exceptionalSet (X := X) a b) ∧
      ∀ z ∈ exceptionalSet (X := X) a b,
        exceptionalReflection e p q (exceptionalReflection e p q z) = z := by
  classical
  obtain ⟨h0, h1, h2, hq, h3, hp⟩ :=
    exceptionalReflection_values e p q h6
  have hrfix : exceptionalReflection e p q r = r :=
    exceptionalReflection_apply_of_not_range e p q r hr
  constructor
  · intro z hz
    simp only [exceptionalSet, hFa, hFb, hFc, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with ((hz | hz | hz) | (hz | hz | hz)) | (hz | hz | hz)
    all_goals subst z
    · rw [h0]; simp
    · rw [h1]; simp
    · rw [hrfix]; simp
    · rw [hp]; simp
    · rw [hq]; simp
    · rw [hrfix]; simp
    · rw [h2]; simp
    · rw [h3]; simp
    · rw [hrfix]; simp
  · intro z _
    exact exceptionalReflection_involutive e p q h6 z

private theorem not_mem_exceptionalSet_of_regular
    (a b : G) (x : X)
    (hxa : a • x ≠ x) (hxb : b • x ≠ x)
    (hxc : (a * b) • x ≠ x) :
    x ∉ exceptionalSet (X := X) a b := by
  intro hx
  rcases hx with (h | h) | h
  · exact hxa h
  · exact hxb h
  · exact hxc h

private theorem fixed_regular_of_ncard_two
    (E : Set X) (a v : G) (x : X)
    (hmove : a • x ≠ x)
    (hvx : v • x = x) (hvax : v • (a • x) = a • x)
    (hcard : (MulAction.fixedBy X v).ncard = 2) :
    ∀ z : X, z ∉ E → v • z = z → z = x ∨ z = a • x := by
  have hsub : ({x, a • x} : Set X) ⊆ MulAction.fixedBy X v := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hvx
    · exact hvax
  have hpair : ({x, a • x} : Set X).ncard = 2 :=
    Set.ncard_pair hmove.symm
  have heq : ({x, a • x} : Set X) = MulAction.fixedBy X v :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hpair, hcard])
  intro z _ hz
  have hzmem : z ∈ MulAction.fixedBy X v := hz
  rw [← heq] at hzmem
  exact hzmem

private theorem fixed_regular_of_ncard_three
    (E : Set X) (a v : G) (x r : X)
    (hxE : x ∉ E) (haxE : a • x ∉ E) (hrE : r ∈ E)
    (hmove : a • x ≠ x)
    (hvx : v • x = x) (hvax : v • (a • x) = a • x)
    (hvr : v • r = r)
    (hcard : (MulAction.fixedBy X v).ncard = 3) :
    ∀ z : X, z ∉ E → v • z = z → z = x ∨ z = a • x := by
  have hxr : x ≠ r := fun h ↦ hxE (h.symm ▸ hrE)
  have haxr : a • x ≠ r := fun h ↦ haxE (h.symm ▸ hrE)
  have hsub : ({x, a • x, r} : Set X) ⊆ MulAction.fixedBy X v := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact hvx
    · exact hvax
    · exact hvr
  have htriple : ({x, a • x, r} : Set X).ncard = 3 := by
    apply Set.ncard_eq_three.mpr
    exact ⟨x, a • x, r, hmove.symm, hxr, haxr, rfl⟩
  have heq : ({x, a • x, r} : Set X) = MulAction.fixedBy X v :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [htriple, hcard])
  intro z hzE hz
  have hzmem : z ∈ MulAction.fixedBy X v := hz
  rw [← heq] at hzmem
  rcases hzmem with hz | hz | hz
  · exact Or.inl hz
  · exact Or.inr hz
  · exact (hzE (hz.symm ▸ hrE)).elim

theorem exists_HallReflectionAt_six
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hap : a • p = q) (hpq : p ≠ q)
    (hbp : b • p = p) (hbq : b • q = q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1})
    (hFb : MulAction.fixedBy X b = {p, q})
    (hFc : MulAction.fixedBy X (a * b) = {e 2, e 3})
    (y : X) (hya : a • y ≠ y) (hyb : b • y ≠ y)
    (hyc : (a * b) • y ≠ y)
    (u : G)
    (huY : u • y = b • y)
    (huAY : u • (a • y) = (a * b) • y)
    (huBY : u • (b • y) = a • y)
    (huCY : u • ((a * b) • y) = y)
    (huSq : u ^ 2 = a)
    (hua : u * a = a * u)
    (hub : u * b = (a * b) * u) :
    ∃ x₀ : X, ∃ u' v : G,
      (u' = u ∨ u' = a * u) ∧ v = b * u' ∧
      (x₀ = y ∨ x₀ = b • y) ∧
      x₀ ∈ MulAction.orbit (Subgroup.closure ({a, b} : Set G)) y ∧
      x₀ ∉ exceptionalSet (X := X) a b ∧
      HallReflectionAt (exceptionalSet (X := X) a b)
        (exceptionalReflection e p q) a b x₀ v := by
  classical
  obtain ⟨u', huChoice, hu0, hu1, hu2, huq, hu3, hup⟩ :=
    exists_oriented_quarterTurn_six h4 e hodd a b haTwo hbTwo hab
      haBase hbBase p q hap hFa hFb hFc y hya u huY huAY huSq hua hub
  have huRel :
      u' ^ 2 = a ∧ u' * a = a * u' ∧
        u' * b = (a * b) * u' := by
    rcases huChoice with rfl | rfl
    · exact ⟨huSq, hua, hub⟩
    · exact left_quarterTurn_relations a b u haTwo hab huSq hua hub
  let v : G := b * u'
  have href := oriented_quarterTurn_reflection_action
    e b u' hbBase p q hbp hbq hu0 hu1 hu2 huq hu3 hup
  have hvSq : v ^ 2 = 1 := by
    simpa only [v] using quarter_reflection_sq
      a b u' haTwo hbTwo hab huRel.1 huRel.2.2
  have hvComm : Commute v a := by
    simpa only [v] using quarter_reflection_commute_first
      a b u' hab huRel.2.1
  have hvInter : v * b = (a * b) * v := by
    simpa only [v] using quarter_reflection_intertwines_second
      a b u' hbTwo hab huRel.2.2
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have hbNe : b ≠ 1 := by
    intro hb
    have h := hbBase 0
    rw [hb, one_smul] at h
    exact h01 h
  have hvNe : v ≠ 1 := by
    intro hv
    have h := href.1
    change v • e 0 = e 1 at h
    rw [hv, one_smul] at h
    exact h01 h
  have hvCard : (MulAction.fixedBy X v).ncard = 2 := by
    obtain ⟨c, hc⟩ := all_involutions_conjugate
      h4 hX e hodd v b hvSq hbTwo hvNe hbNe
    calc
      (MulAction.fixedBy X v).ncard =
          (MulAction.fixedBy X b).ncard :=
        Research.SharpFourDegreeCompletion.fixedBy_ncard_eq_of_conjugate
          v b c hc
      _ = 2 := by rw [hFb, Set.ncard_pair hpq]
  have h6 : Function.Injective (exceptionalSixMap e p q) :=
    exceptionalSixMap_injective e a b haTwo haBase hbBase
      p q hap hpq hbp hbq
  have hsigma := exceptionalReflection_values e p q h6
  have hvOn : ∀ z ∈ exceptionalSet (X := X) a b,
      v • z = exceptionalReflection e p q z := by
    intro z hz
    simp only [exceptionalSet, hFa, hFb, hFc, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with ((hz | hz) | (hz | hz)) | (hz | hz)
    all_goals subst z
    · simpa only [v] using href.1.trans hsigma.1.symm
    · simpa only [v] using href.2.1.trans hsigma.2.1.symm
    · simpa only [v] using href.2.2.2.2.2.trans hsigma.2.2.2.2.2.symm
    · simpa only [v] using href.2.2.2.1.trans hsigma.2.2.2.1.symm
    · simpa only [v] using href.2.2.1.trans hsigma.2.2.1.symm
    · simpa only [v] using href.2.2.2.2.1.trans hsigma.2.2.2.2.1.symm
  rcases huChoice with huEq | huEq
  · have hvY : v • y = y := by
      simp only [v, huEq, mul_smul, huY]
      rw [← mul_smul, ← pow_two, hbTwo, one_smul]
    have hvAY : v • (a • y) = a • y := by
      calc
        v • (a • y) = b • (u • (a • y)) := by
          simp only [v, huEq, mul_smul]
        _ = b • ((a * b) • y) := by rw [huAY]
        _ = a • y := by
          rw [← mul_smul]
          congr 1
          calc
            b * (a * b) = a * (b * b) := by
              rw [← mul_assoc, ← hab.eq, mul_assoc]
            _ = a := by rw [← pow_two, hbTwo, mul_one]
    have hyE := not_mem_exceptionalSet_of_regular a b y hya hyb hyc
    refine ⟨y, u', v, Or.inl huEq, rfl, Or.inl rfl,
      MulAction.mem_orbit_self y,
      hyE, ?_⟩
    exact
      { sq := hvSq
        ne_one := hvNe
        commute_first := hvComm
        intertwines_second := hvInter
        fixes_point := hvY
        fixes_first_translate := hvAY
        fixed_regular := fixed_regular_of_ncard_two
          (exceptionalSet (X := X) a b) a v y hya hvY hvAY hvCard
        on_exceptional := hvOn }
  · have hreg := regular_b_smul a b haTwo hbTwo hab y hya hyb hyc
    have hvBY : v • (b • y) = b • y := by
      calc
        v • (b • y) = b • (a • (u • (b • y))) := by
          simp only [v, huEq, mul_smul]
        _ = b • (a • (a • y)) := by rw [huBY]
        _ = b • y := congrArg (fun z : X ↦ b • z) (by
          rw [← mul_smul, ← pow_two, haTwo, one_smul])
    have hvABY : v • (a • (b • y)) = a • (b • y) := by
      have haby : a • (b • y) = (a * b) • y := by rw [mul_smul]
      calc
        v • (a • (b • y)) =
            b • (a • (u • ((a * b) • y))) := by
          rw [haby]
          simp only [v, huEq, mul_smul]
        _ = b • (a • y) := by rw [huCY]
        _ = (a * b) • y := by rw [← mul_smul, hab.eq.symm]
        _ = a • (b • y) := by rw [mul_smul]
    have hbYE := not_mem_exceptionalSet_of_regular
      a b (b • y) hreg.1 hreg.2.1 hreg.2.2
    have horbit : b • y ∈
        MulAction.orbit (Subgroup.closure ({a, b} : Set G)) y := by
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨b, Subgroup.subset_closure (by simp)⟩, rfl⟩
    refine ⟨b • y, u', v, Or.inr huEq, rfl, Or.inr rfl,
      horbit, hbYE, ?_⟩
    exact
      { sq := hvSq
        ne_one := hvNe
        commute_first := hvComm
        intertwines_second := hvInter
        fixes_point := hvBY
        fixes_first_translate := hvABY
        fixed_regular := fixed_regular_of_ncard_two
          (exceptionalSet (X := X) a b) a v (b • y)
          hreg.1 hvBY hvABY hvCard
        on_exceptional := hvOn }

theorem exists_HallReflectionAt_seven
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q r : X) (hap : a • p = q) (hpq : p ≠ q)
    (hbp : b • p = p) (hbq : b • q = q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1, r})
    (hFb : MulAction.fixedBy X b = {p, q, r})
    (hFc : MulAction.fixedBy X (a * b) = {e 2, e 3, r})
    (hD : MulAction.fixedBy X a ∩ MulAction.fixedBy X b = {r})
    (y : X) (hya : a • y ≠ y) (hyb : b • y ≠ y)
    (hyc : (a * b) • y ≠ y)
    (u : G)
    (huY : u • y = b • y)
    (huAY : u • (a • y) = (a * b) • y)
    (huBY : u • (b • y) = a • y)
    (huCY : u • ((a * b) • y) = y)
    (huSq : u ^ 2 = a)
    (hua : u * a = a * u)
    (hub : u * b = (a * b) * u) :
    ∃ x₀ : X, ∃ u' v : G,
      (u' = u ∨ u' = a * u) ∧ v = b * u' ∧
      (x₀ = y ∨ x₀ = b • y) ∧
      x₀ ∈ MulAction.orbit (Subgroup.closure ({a, b} : Set G)) y ∧
      x₀ ∉ exceptionalSet (X := X) a b ∧
      HallReflectionAt (exceptionalSet (X := X) a b)
        (exceptionalReflection e p q) a b x₀ v := by
  classical
  obtain ⟨u', huChoice, hu0, hu1, hur, hu2, huq, hu3, hup⟩ :=
    exists_oriented_quarterTurn h4 e hodd a b haTwo hbTwo hab
      haBase hbBase p q r hap hFa hFb hD y hya
      u huY huAY huSq hua hub
  have huRel :
      u' ^ 2 = a ∧ u' * a = a * u' ∧
        u' * b = (a * b) * u' := by
    rcases huChoice with rfl | rfl
    · exact ⟨huSq, hua, hub⟩
    · exact left_quarterTurn_relations a b u haTwo hab huSq hua hub
  let v : G := b * u'
  have href := oriented_quarterTurn_reflection_action
    e b u' hbBase p q hbp hbq hu0 hu1 hu2 huq hu3 hup
  have hvSq : v ^ 2 = 1 := by
    simpa only [v] using quarter_reflection_sq
      a b u' haTwo hbTwo hab huRel.1 huRel.2.2
  have hvComm : Commute v a := by
    simpa only [v] using quarter_reflection_commute_first
      a b u' hab huRel.2.1
  have hvInter : v * b = (a * b) * v := by
    simpa only [v] using quarter_reflection_intertwines_second
      a b u' hbTwo hab huRel.2.2
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have hbNe : b ≠ 1 := by
    intro hb
    have h := hbBase 0
    rw [hb, one_smul] at h
    exact h01 h
  have hvNe : v ≠ 1 := by
    intro hv
    have h := href.1
    change v • e 0 = e 1 at h
    rw [hv, one_smul] at h
    exact h01 h
  have har : a • r = r := by
    have hr : r ∈ MulAction.fixedBy X a := by rw [hFa]; simp
    exact hr
  have hbr : b • r = r := by
    have hr : r ∈ MulAction.fixedBy X b := by rw [hFb]; simp
    exact hr
  have haq : a • q = p := by
    calc
      a • q = a • (a • p) := congrArg (fun z : X ↦ a • z) hap.symm
      _ = (a ^ 2) • p := by rw [pow_two, mul_smul]
      _ = p := by rw [haTwo, one_smul]
  have hpr : p ≠ r := by
    intro h
    apply hpq
    have hqr : q = r :=
      hap.symm.trans ((congrArg (fun z : X ↦ a • z) h).trans har)
    exact h.trans hqr.symm
  have hqr : q ≠ r := by
    intro h
    apply hpr
    calc
      p = a • q := haq.symm
      _ = a • r := congrArg (fun z : X ↦ a • z) h
      _ = r := har
  have hvCard : (MulAction.fixedBy X v).ncard = 3 := by
    obtain ⟨c, hc⟩ := all_involutions_conjugate
      h4 hX e hodd v b hvSq hbTwo hvNe hbNe
    calc
      (MulAction.fixedBy X v).ncard =
          (MulAction.fixedBy X b).ncard :=
        Research.SharpFourDegreeCompletion.fixedBy_ncard_eq_of_conjugate
          v b c hc
      _ = 3 := by
        rw [hFb]
        apply Set.ncard_eq_three.mpr
        exact ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have h6 : Function.Injective (exceptionalSixMap e p q) :=
    exceptionalSixMap_injective e a b haTwo haBase hbBase
      p q hap hpq hbp hbq
  have hsigma := exceptionalReflection_values e p q h6
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
  have hsigmaR : exceptionalReflection e p q r = r :=
    exceptionalReflection_apply_of_not_range e p q r hrNotRange
  have hvr : v • r = r := by
    change (b * u') • r = r
    rw [mul_smul, hur, hbr]
  have hvOn : ∀ z ∈ exceptionalSet (X := X) a b,
      v • z = exceptionalReflection e p q z := by
    intro z hz
    simp only [exceptionalSet, hFa, hFb, hFc, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with ((hz | hz | hz) | (hz | hz | hz)) | (hz | hz | hz)
    all_goals subst z
    · simpa only [v] using href.1.trans hsigma.1.symm
    · simpa only [v] using href.2.1.trans hsigma.2.1.symm
    · exact hvr.trans hsigmaR.symm
    · simpa only [v] using href.2.2.2.2.2.trans hsigma.2.2.2.2.2.symm
    · simpa only [v] using href.2.2.2.1.trans hsigma.2.2.2.1.symm
    · exact hvr.trans hsigmaR.symm
    · simpa only [v] using href.2.2.1.trans hsigma.2.2.1.symm
    · simpa only [v] using href.2.2.2.2.1.trans hsigma.2.2.2.2.1.symm
    · exact hvr.trans hsigmaR.symm
  have hrE : r ∈ exceptionalSet (X := X) a b := by
    simp [exceptionalSet, hFa]
  rcases huChoice with huEq | huEq
  · have hvY : v • y = y := by
      simp only [v, huEq, mul_smul, huY]
      rw [← mul_smul, ← pow_two, hbTwo, one_smul]
    have hvAY : v • (a • y) = a • y := by
      calc
        v • (a • y) = b • (u • (a • y)) := by
          simp only [v, huEq, mul_smul]
        _ = b • ((a * b) • y) := by rw [huAY]
        _ = a • y := by
          rw [← mul_smul]
          congr 1
          calc
            b * (a * b) = a * (b * b) := by
              rw [← mul_assoc, ← hab.eq, mul_assoc]
            _ = a := by rw [← pow_two, hbTwo, mul_one]
    have hyE := not_mem_exceptionalSet_of_regular a b y hya hyb hyc
    have hregA := regular_a_smul a b haTwo hab y hya hyb hyc
    have haYE := not_mem_exceptionalSet_of_regular
      a b (a • y) hregA.1 hregA.2.1 hregA.2.2
    refine ⟨y, u', v, Or.inl huEq, rfl, Or.inl rfl,
      MulAction.mem_orbit_self y,
      hyE, ?_⟩
    exact
      { sq := hvSq
        ne_one := hvNe
        commute_first := hvComm
        intertwines_second := hvInter
        fixes_point := hvY
        fixes_first_translate := hvAY
        fixed_regular := fixed_regular_of_ncard_three
          (exceptionalSet (X := X) a b) a v y r hyE haYE hrE
          hya hvY hvAY hvr hvCard
        on_exceptional := hvOn }
  · have hreg := regular_b_smul a b haTwo hbTwo hab y hya hyb hyc
    have hvBY : v • (b • y) = b • y := by
      calc
        v • (b • y) = b • (a • (u • (b • y))) := by
          simp only [v, huEq, mul_smul]
        _ = b • (a • (a • y)) := by rw [huBY]
        _ = b • y := congrArg (fun z : X ↦ b • z) (by
          rw [← mul_smul, ← pow_two, haTwo, one_smul])
    have hvABY : v • (a • (b • y)) = a • (b • y) := by
      have haby : a • (b • y) = (a * b) • y := by rw [mul_smul]
      calc
        v • (a • (b • y)) =
            b • (a • (u • ((a * b) • y))) := by
          rw [haby]
          simp only [v, huEq, mul_smul]
        _ = b • (a • y) := by rw [huCY]
        _ = (a * b) • y := by rw [← mul_smul, hab.eq.symm]
        _ = a • (b • y) := by rw [mul_smul]
    have hbYE := not_mem_exceptionalSet_of_regular
      a b (b • y) hreg.1 hreg.2.1 hreg.2.2
    have hregA := regular_a_smul
      a b haTwo hab (b • y) hreg.1 hreg.2.1 hreg.2.2
    have habYE := not_mem_exceptionalSet_of_regular
      a b (a • (b • y)) hregA.1 hregA.2.1 hregA.2.2
    have horbit : b • y ∈
        MulAction.orbit (Subgroup.closure ({a, b} : Set G)) y := by
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨b, Subgroup.subset_closure (by simp)⟩, rfl⟩
    refine ⟨b • y, u', v, Or.inr huEq, rfl, Or.inr rfl,
      horbit, hbYE, ?_⟩
    exact
      { sq := hvSq
        ne_one := hvNe
        commute_first := hvComm
        intertwines_second := hvInter
        fixes_point := hvBY
        fixes_first_translate := hvABY
        fixed_regular := fixed_regular_of_ncard_three
          (exceptionalSet (X := X) a b) a v (b • y) r hbYE habYE hrE
          hreg.1 hvBY hvABY hvr hvCard
        on_exceptional := hvOn }

end FiveTransitive.Research.HallReflectionData

end CFSG
