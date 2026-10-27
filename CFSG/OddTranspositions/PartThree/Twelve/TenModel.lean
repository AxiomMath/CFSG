module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSpTools
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther

variable {k : ℕ} {F : Type} [Field F]

structure IsSpQuadForm (Q : (Fin k ⊕ Fin k → F) → F) : Prop where
  smul : ∀ (c : F) (x : Fin k ⊕ Fin k → F), Q (c • x) = c ^ 2 * Q x
  add : ∀ x y : Fin k ⊕ Fin k → F, Q (x + y) = Q x + Q y + spForm k F x y

def spOrthSubgroup (Q : (Fin k ⊕ Fin k → F) → F) : Subgroup (StatedSp k F) where
  carrier := {g | ∀ x, Q (spEnd g x) = Q x}
  mul_mem' {a b} ha hb x := by rw [spEnd_mul, Module.End.mul_apply, ha, hb]
  one_mem' x := by rw [spEnd_one, Module.End.one_apply]
  inv_mem' {a} ha x := by
    have h := ha (spEnd a⁻¹ x)
    rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one,
      Module.End.one_apply] at h
    exact h.symm

theorem mem_spOrthSubgroup {Q : (Fin k ⊕ Fin k → F) → F} {g : StatedSp k F} :
    g ∈ spOrthSubgroup Q ↔ ∀ x, Q (spEnd g x) = Q x :=
  Iff.rfl

namespace IsSpQuadForm

variable {Q : (Fin k ⊕ Fin k → F) → F} (hQ : IsSpQuadForm Q)
include hQ

theorem Q_zero : Q 0 = 0 := by
  have h := hQ.smul 0 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_mul] at h

theorem Q_spTransvection (v : Fin k ⊕ Fin k → F) (c : F) (x : Fin k ⊕ Fin k → F) :
    Q (spEnd (spTransvection v c) x) = Q x + spForm k F x v ^ 2 * (c ^ 2 * Q v + c) := by
  rw [spEnd_spTransvection, hQ.add, hQ.smul, map_smul, smul_eq_mul]
  ring

theorem spTransvection_mem_iff {v : Fin k ⊕ Fin k → F} (hv : v ≠ 0) (c : F) :
    spTransvection v c ∈ spOrthSubgroup Q ↔ c ^ 2 * Q v + c = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ : ∃ x, spForm k F x v ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv (spForm_nondegenerate.2 v hall)
    have h1 := h x
    rw [hQ.Q_spTransvection] at h1
    have h2 : spForm k F x v ^ 2 * (c ^ 2 * Q v + c) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 hx)
  · intro h x
    rw [hQ.Q_spTransvection, h, mul_zero, add_zero]

theorem mem_of_forall_Q_eq_one [Finite F] [CharP F 2] (hF : 2 < Nat.card F) (g : StatedSp k F)
    (hg : ∀ v, Q v = 1 → Q (spEnd g v) = 1) : g ∈ spOrthSubgroup Q := by
  classical
  set D : (Fin k ⊕ Fin k → F) → F := fun x => Q (spEnd g x) + Q x with hD
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hadd : ∀ x y, D (x + y) = D x + D y := by
    intro x y
    simp only [hD, map_add, hQ.add, spForm_spEnd_spEnd]
    linear_combination (spForm k F x y) * h2
  have hsmul : ∀ (c : F) x, D (c • x) = c ^ 2 * D x := by
    intro c x
    simp only [hD, map_smul, hQ.smul]
    ring
  have hone : ∀ v, Q v = 1 → D v = 0 := by
    intro v hv
    simp only [hD, hg v hv, hv]
    linear_combination h2
  have hns : ∀ x, Q x ≠ 0 → D x = 0 := by
    intro x hx
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (Q x)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by rw [hr, mul_zero])
    have hv : Q (r⁻¹ • x) = 1 := by
      rw [hQ.smul, hr]
      field_simp
    have hx' : x = r • (r⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hr0, one_smul]
    rw [hx', hsmul, hone _ hv, mul_zero]
  have hall : ∀ x, D x = 0 := by
    intro x
    by_cases hx : Q x = 0
    · by_cases hx0 : x = 0
      · simp only [hD, hx0, map_zero, hQ.Q_zero, add_zero]
      obtain ⟨y, hy⟩ : ∃ y, spForm k F y x ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hx0 (spForm_nondegenerate.2 x hall)
      have : Fintype F := Fintype.ofFinite F
      set t₀ : F := Q y / spForm k F y x with ht₀
      obtain ⟨t₁, ht₁, t₂, ht₂, ht12⟩ : ∃ t₁ ∈ Finset.univ.erase t₀, ∃ t₂ ∈ Finset.univ.erase t₀,
          t₁ ≠ t₂ := by
        apply Finset.one_lt_card.mp
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          ← Nat.card_eq_fintype_card]
        omega
      have hQt : ∀ t : F, t ≠ t₀ → Q (y + t • x) ≠ 0 := by
        intro t ht h0
        apply ht
        rw [hQ.add, hQ.smul, hx, mul_zero, add_zero, map_smul, smul_eq_mul] at h0
        rw [ht₀, eq_div_iff hy]
        linear_combination h0 - Q y * h2
      have h1 := hns _ (hQt t₁ (Finset.ne_of_mem_erase ht₁))
      have h2' := hns _ (hQt t₂ (Finset.ne_of_mem_erase ht₂))
      have h3 : D ((t₁ + t₂) • x) = 0 := by
        have e : (t₁ + t₂) • x = (y + t₁ • x) + (y + t₂ • x) := by
          rw [add_smul, add_add_add_comm, ← two_smul F y, h2, zero_smul, zero_add]
        rw [e, hadd, h1, h2', add_zero]
      rw [hsmul] at h3
      have ht : t₁ + t₂ ≠ 0 := fun h => ht12 (by linear_combination h - t₂ * h2)
      exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 2 ht)
    · exact hns x hx
  intro x
  have h := hall x
  simp only [hD] at h
  linear_combination h - Q x * h2

theorem normalizer_spOrthSubgroup [Finite F] [CharP F 2] (hF : 2 < Nat.card F) :
    Subgroup.normalizer (spOrthSubgroup Q : Set (StatedSp k F)) = spOrthSubgroup Q := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine le_antisymm (fun g hg => hQ.mem_of_forall_Q_eq_one hF g fun v hv => ?_)
    Subgroup.le_normalizer
  have hv0 : v ≠ 0 := fun h => by
    rw [h, hQ.Q_zero] at hv
    exact zero_ne_one hv
  have hmem : spTransvection v 1 ∈ spOrthSubgroup Q := by
    rw [hQ.spTransvection_mem_iff hv0, hv]
    linear_combination h2
  have h1 := (Subgroup.mem_normalizer_iff.mp hg _).mp hmem
  rw [conj_spTransvection] at h1
  have hgv0 : spEnd g v ≠ 0 := fun h => hv0 (by
    have := congrArg (spEnd g⁻¹) h
    rwa [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply,
      map_zero] at this)
  rw [hQ.spTransvection_mem_iff hgv0] at h1
  linear_combination h1 - h2

end IsSpQuadForm

end CFSG.OddTranspositions.PartThree

end
