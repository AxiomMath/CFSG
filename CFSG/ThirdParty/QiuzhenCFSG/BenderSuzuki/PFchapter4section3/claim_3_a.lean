module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section3

/-! # Peterfalvi, Part II, Chapter IV, Section 3, Claim (3)(a) -/

/-- The finite-field core of Peterfalvi's Claim (3).  If `X + theta X` is
constant away from the two exceptional values occurring in equation `(*)`,
then an odd-order field automorphism `theta` is trivial. -/
public theorem claim_3_a
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (theta : F ≃+* F) (hthetaOdd : Odd (orderOf theta))
    (A c : F)
    (hconstant : ∀ X : F, X ≠ 0 → X ≠ A → X + theta X = c) :
    theta = 1 := by
  classical
  by_contra htheta
  have hnot_fixed : ¬ ∀ x : F, theta x = x := by
    intro hfixed
    apply htheta
    ext x
    simpa using hfixed x
  obtain ⟨x, hx⟩ := not_forall.mp hnot_fixed
  have hx0 : x ≠ 0 := by
    intro hx0
    subst x
    simp at hx
  have hx1 : x ≠ 1 := by
    intro hx1
    subst x
    simp at hx
  have htheta2x : theta (theta x) ≠ x := by
    intro htheta2x
    have htheta_sq_x : (theta ^ 2) x = x := by
      simpa [pow_two, RingAut.mul_apply] using htheta2x
    have htheta_even_x : ∀ k : ℕ, (theta ^ (2 * k)) x = x := by
      intro k
      rw [pow_mul]
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, RingAut.mul_apply, htheta_sq_x, ih]
    rcases hthetaOdd with ⟨k, hk⟩
    apply hx
    calc
      theta x = theta ((theta ^ (2 * k)) x) := by rw [htheta_even_x]
      _ = (theta ^ (2 * k + 1)) x := by rw [pow_succ', RingAut.mul_apply]
      _ = (theta ^ orderOf theta) x := by rw [hk]
      _ = x := by simp
  have hthetax0 : theta x ≠ 0 := by
    intro h
    apply hx0
    apply theta.injective
    simpa using h
  have hthetax1 : theta x ≠ 1 := by
    intro h
    apply hx1
    apply theta.injective
    simpa using h
  have htheta2x0 : theta (theta x) ≠ 0 := by
    intro h
    apply hthetax0
    apply theta.injective
    simpa using h
  have htheta2x1 : theta (theta x) ≠ 1 := by
    intro h
    apply hthetax1
    apply theta.injective
    simpa using h
  have htheta2x_thetax : theta (theta x) ≠ theta x := by
    intro h
    exact hx (theta.injective h)
  have hcard : 5 ≤ Nat.card F := by
    letI : Fintype F := Fintype.ofFinite F
    let orbit : Finset F := {0, 1, x, theta x, theta (theta x)}
    have horbit_card : orbit.card = 5 := by
      have h0 : 0 ∉ ({1, x, theta x, theta (theta x)} : Finset F) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨zero_ne_one, hx0.symm, hthetax0.symm, htheta2x0.symm⟩
      have h1 : 1 ∉ ({x, theta x, theta (theta x)} : Finset F) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hx1.symm, hthetax1.symm, htheta2x1.symm⟩
      have hxorbit : x ∉ ({theta x, theta (theta x)} : Finset F) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hx h.symm, fun h => htheta2x h.symm⟩
      have hthetaxorbit : theta x ∉ ({theta (theta x)} : Finset F) := by
        simp only [Finset.mem_singleton]
        intro h
        exact htheta2x_thetax h.symm
      simp [orbit, Finset.card_insert_of_notMem, h0, h1, hxorbit,
        hthetaxorbit]
    rw [← horbit_card]
    simpa [Nat.card_eq_fintype_card] using Finset.card_le_univ orbit
  have hexists_not_mem (s : Finset F) (hs : s.card < Nat.card F) :
      ∃ x : F, x ∉ s := by
    letI : Fintype F := Fintype.ofFinite F
    by_contra h
    push Not at h
    have hsub : Finset.univ ⊆ s := by
      intro z _hz
      exact h z
    have hle := Finset.card_le_card hsub
    have hlt : s.card < (Finset.univ : Finset F).card := by
      simpa [Nat.card_eq_fintype_card] using hs
    exact (not_lt_of_ge hle) hlt
  have hsmallX : ({0, A} : Finset F).card < Nat.card F :=
    lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨X, hX⟩ := hexists_not_mem {0, A} hsmallX
  have hX' : X ≠ 0 ∧ X ≠ A := by simpa using hX
  have hX0 : X ≠ 0 := hX'.1
  have hXA : X ≠ A := hX'.2
  have hsmallY : ({0, A, X, A + X} : Finset F).card < Nat.card F :=
    lt_of_le_of_lt Finset.card_le_four (by omega)
  obtain ⟨Y, hY⟩ := hexists_not_mem {0, A, X, A + X} hsmallY
  have hY' : Y ≠ 0 ∧ Y ≠ A ∧ Y ≠ X ∧ Y ≠ A + X := by
    simpa using hY
  have hY0 : Y ≠ 0 := hY'.1
  have hYA : Y ≠ A := hY'.2.1
  have hYX : Y ≠ X := hY'.2.2.1
  have hYAX : Y ≠ A + X := hY'.2.2.2
  have hXY0 : X + Y ≠ 0 := by
    intro h
    exact hYX (CharTwo.add_eq_zero.mp h).symm
  have hXYA : X + Y ≠ A := by
    intro h
    apply hYAX
    calc
      Y = X + (X + Y) := by
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      _ = X + A := by rw [h]
      _ = A + X := add_comm _ _
  have hc : c = 0 := by
    have hXc := hconstant X hX0 hXA
    have hYc := hconstant Y hY0 hYA
    have hXYc := hconstant (X + Y) hXY0 hXYA
    calc
      c = (X + Y) + theta (X + Y) := hXYc.symm
      _ = (X + theta X) + (Y + theta Y) := by rw [map_add]; ring
      _ = c + c := by rw [hXc, hYc]
      _ = 0 := CharTwo.add_self_eq_zero c
  have hfix_good : ∀ z : F, z ≠ 0 → z ≠ A → theta z = z := by
    intro z hz0 hzA
    have hz := hconstant z hz0 hzA
    rw [hc] at hz
    exact (CharTwo.add_eq_zero.mp hz).symm
  have hXA0 : X + A ≠ 0 := by
    intro h
    exact hXA (CharTwo.add_eq_zero.mp h)
  have hXAA : X + A ≠ A := by
    intro h
    apply hX0
    linear_combination h
  have hthetaA : theta A = A := by
    have hmap := theta.map_add X A
    rw [hfix_good (X + A) hXA0 hXAA, hfix_good X hX0 hXA] at hmap
    exact add_left_cancel hmap.symm
  apply htheta
  ext z
  by_cases hz0 : z = 0
  · subst z
    simp
  by_cases hzA : z = A
  · subst z
    exact hthetaA
  exact hfix_good z hz0 hzA

end PFchapter4section3
end CFSG.BenderSuzuki
