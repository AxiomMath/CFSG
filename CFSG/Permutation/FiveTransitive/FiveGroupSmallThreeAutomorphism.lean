module

public import CFSG.Permutation.FiveTransitive.FiveGroupSmallThreeFixed
public import CFSG.Permutation.FiveTransitive.FreeComplementCard
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.FiveGroupSmallThreeAutomorphism

open MulAction

private theorem fixed_cyclic_eq
    {A Q : Type*} [Group A] [Group Q] [Finite Q]
    [MulDistribMulAction A Q] [FaithfulSMul A Q]
    (hA : IsPGroup 3 A) (hQ : IsPGroup 5 Q) (hcard : Nat.card Q ≤ 125)
    (a : A) (ha : a ≠ 1) :
    FixedPoints.subgroup (Subgroup.zpowers a) Q = FixedPoints.subgroup A Q := by
  classical
  have hmove : ∃ q : Q, a • q ≠ q := by
    by_contra hn
    push Not at hn
    exact ha (FaithfulSMul.eq_of_smul_eq_smul (fun q => (hn q).trans (one_smul A q).symm))
  obtain ⟨q,hq⟩ := hmove
  have hglobal := FiveGroupSmallThreeFixed.card_and_fixed hA hQ hcard ⟨a,q,hq⟩
  have hlocal := FiveGroupSmallThreeFixed.card_and_fixed
    (hA.to_subgroup (Subgroup.zpowers a)) hQ hcard
    ⟨⟨a,Subgroup.mem_zpowers a⟩,q,hq⟩
  have hle : FixedPoints.subgroup A Q ≤ FixedPoints.subgroup (Subgroup.zpowers a) Q :=
    fun x hx b => hx b.val
  apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rcases hglobal with hg | hg <;> rcases hlocal with hl | hl <;> omega

private theorem card_le_three
    {A Q : Type*} [Group A] [Group Q] [Finite A] [Finite Q]
    [MulDistribMulAction A Q] [FaithfulSMul A Q]
    (hA : IsPGroup 3 A) (hQ : IsPGroup 5 Q) (hcard : Nat.card Q ≤ 125) :
    Nat.card A ≤ 3 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  by_cases htriv : ∀ a : A, a = 1
  · let _ : Subsingleton A := ⟨fun a b => (htriv a).trans (htriv b).symm⟩
    rw [Nat.card_of_subsingleton (1 : A)]
    decide
  push Not at htriv
  obtain ⟨a,ha⟩ := htriv
  have hmove : ∃ q : Q, a • q ≠ q := by
    by_contra hn
    push Not at hn
    exact ha (FaithfulSMul.eq_of_smul_eq_smul (fun q => (hn q).trans (one_smul A q).symm))
  obtain ⟨q,hq⟩ := hmove
  have hcards := FiveGroupSmallThreeFixed.card_and_fixed hA hQ hcard ⟨a,q,hq⟩
  let C := FixedPoints.subgroup A Q
  have hfree : ∀ a : A, ∀ q : Q, q ∉ (C : Set Q) → a • q = q → a = 1 := by
    intro b r hr hbr
    by_contra hb
    have hrfix : r ∈ FixedPoints.subgroup (Subgroup.zpowers b) Q := by
      intro c
      obtain ⟨z,hz⟩ := Subgroup.mem_zpowers_iff.mp c.property
      change (c : A) • r = r
      rw [← hz]
      exact (stabilizer A r).zpow_mem hbr z
    rw [fixed_cyclic_eq hA hQ hcard b hb] at hrfix
    exact hr hrfix
  have hdvd := FreeComplementCard.card_dvd_complement A Q (C : Set Q)
    (fun b r hr => by simpa only [hr b] using hr) hfree
  rw [← Nat.card_coe_set_eq] at hdvd
  change Nat.card A ∣ Nat.card Q - Nat.card C at hdvd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hA
  have he1 : e ≤ 1 := by
    by_contra hn
    have h9 : 9 ∣ Nat.card A := by
      rw [he]
      exact pow_dvd_pow 3 (by omega : 2 ≤ e)
    have hnine := h9.trans hdvd
    rcases hcards with hc | hc <;> rcases hc with ⟨hQcard,hCcard⟩ <;>
      change Nat.card (FixedPoints.subgroup A Q) = _ at hCcard <;>
      change 9 ∣ Nat.card Q - Nat.card (FixedPoints.subgroup A Q) at hnine <;>
      rw [hQcard,hCcard] at hnine <;> norm_num at hnine
  rw [he]
  calc
    3 ^ e ≤ 3 ^ 1 := Nat.pow_le_pow_right (by decide) he1
    _ = 3 := by norm_num

theorem nine_not_dvd_card_mulAut
    (Q : Type*) [Group Q] [Finite Q]
    (hQ : IsPGroup 5 Q) (hcard : Nat.card Q ≤ 125) :
    ¬ 9 ∣ Nat.card (MulAut Q) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let S : Sylow 3 (MulAut Q) := default
  have hS : Nat.card S ≤ 3 := card_le_three S.isPGroup' hQ hcard
  have hcop : Nat.Coprime 9 (S : Subgroup (MulAut Q)).index := by
    exact Nat.Coprime.pow_left 2
      ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr S.not_dvd_index)
  intro hn
  rw [← (S : Subgroup (MulAut Q)).card_mul_index] at hn
  have hd : 9 ∣ Nat.card S := hcop.dvd_mul_right.mp hn
  have hpos : 0 < Nat.card S := Nat.card_pos
  have := Nat.le_of_dvd hpos hd
  omega

end FiveTransitive.FiveGroupSmallThreeAutomorphism

end CFSG
