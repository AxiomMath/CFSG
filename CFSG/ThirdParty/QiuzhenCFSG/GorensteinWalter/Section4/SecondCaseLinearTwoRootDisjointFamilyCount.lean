module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Counting disjoint minimal subgroups in two root groups

This module isolates the finite counting endpoint in the equation-(11)
minimal-invariant-subgroup bound.
-/

noncomputable section
namespace CFSG.GorensteinWalter

universe u v

/-- If pairwise disjoint punctured subgroups lie in at most two groups of
order `q`, and every punctured subgroup has at least `2p` elements, then the
family has cardinal at most `(q - 1) / p`. -/
public theorem secondCase_linear_twoRoot_disjoint_family_count
    {G : Type u} [Group G] [Finite G]
    {Fam : Type u} [Finite Fam]
    {Roots : Type v} [Finite Roots]
    (W : Fam → Subgroup G) (S : Roots → Subgroup G) (root : Fam → Roots)
    (p q : ℕ) (hp : 0 < p)
    (hWle : ∀ i, W i ≤ S (root i))
    (hdisj : ∀ i j, i ≠ j → ∀ z : G,
      z ∈ W i → z ∈ W j → z = 1)
    (hsize : ∀ i, 2 * p ≤ Nat.card {z : W i // (z : G) ≠ 1})
    (hRoots : Nat.card Roots ≤ 2)
    (hScard : ∀ j, Nat.card (S j) = q) :
    Nat.card Fam ≤ (q - 1) / p := by
  classical
  let : Fintype Fam := Fintype.ofFinite Fam
  let : Fintype Roots := Fintype.ofFinite Roots
  let SharpW : Fam → Type u := fun i => {z : W i // (z : G) ≠ 1}
  let SharpS : Roots → Type u := fun j => {z : S j // (z : G) ≠ 1}
  let f : (Σ i : Fam, SharpW i) → (Σ j : Roots, SharpS j) := fun z =>
    ⟨root z.1, ⟨⟨(z.2 : G), hWle z.1 z.2.1.2⟩, z.2.2⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hz : (a.2 : G) = (b.2 : G) :=
      congrArg (fun z : Σ j : Roots, SharpS j => ((z.2 : S z.1) : G)) hab
    have hij : a.1 = b.1 := by
      by_contra hne
      have hza : (a.2 : G) ∈ W a.1 := a.2.1.2
      have hzb : (a.2 : G) ∈ W b.1 := by
        rw [hz]
        exact b.2.1.2
      exact a.2.2 (hdisj a.1 b.1 hne (a.2 : G) hza hzb)
    cases a with
    | mk ai av =>
      cases b with
      | mk bi bv =>
        simp_all only [Sigma.mk.injEq]
        constructor
        · trivial
        · cases hij
          have hzW : (av : W ai) = (bv : W ai) := Subtype.ext hz
          exact heq_of_eq (Subtype.ext hzW)
  have hSharpS : ∀ j, Nat.card (SharpS j) = q - 1 := by
    intro j
    let : Fintype (S j) := Fintype.ofFinite (S j)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, hScard]
    simp
  have hlower : Nat.card Fam * (2 * p) ≤
      Nat.card (Σ i : Fam, SharpW i) := by
    rw [Nat.card_sigma]
    calc
      Nat.card Fam * (2 * p) = ∑ _i : Fam, (2 * p) := by simp
      _ ≤ ∑ i : Fam, Nat.card (SharpW i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hsize i
  have hinjcard : Nat.card (Σ i : Fam, SharpW i) ≤
      Nat.card (Σ j : Roots, SharpS j) :=
    Nat.card_le_card_of_injective f hinj
  have hrootcard : Nat.card (Σ j : Roots, SharpS j) =
      Nat.card Roots * (q - 1) := by
    rw [Nat.card_sigma]
    calc
      (∑ j : Roots, Nat.card (SharpS j)) =
          ∑ _j : Roots, (q - 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hSharpS j
      _ = Nat.card Roots * (q - 1) := by simp
  have hcap : Nat.card (Σ j : Roots, SharpS j) ≤ 2 * (q - 1) := by
    rw [hrootcard]
    exact Nat.mul_le_mul_right (q - 1) hRoots
  have htwice : 2 * p * Nat.card Fam ≤ 2 * (q - 1) := by
    calc
      2 * p * Nat.card Fam = Nat.card Fam * (2 * p) := by ring
      _ ≤ Nat.card (Σ i : Fam, SharpW i) := hlower
      _ ≤ Nat.card (Σ j : Roots, SharpS j) := hinjcard
      _ ≤ 2 * (q - 1) := hcap
  have hpFam : Nat.card Fam * p ≤ q - 1 := by
    have htwice' : 2 * (Nat.card Fam * p) ≤ 2 * (q - 1) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using htwice
    omega
  exact (Nat.le_div_iff_mul_le hp).2 hpFam

end CFSG.GorensteinWalter
