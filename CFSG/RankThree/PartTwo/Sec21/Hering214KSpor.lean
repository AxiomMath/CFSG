module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofBar
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)

section AutBound

variable {Y : Type} [Group Y] [Finite Y]

theorem card_range_conj_eq (hZ : Subgroup.center Y = ⊥) :
    Nat.card (MulAut.conj : Y →* MulAut Y).range = Nat.card Y :=
  (Nat.card_congr (MonoidHom.ofInjective
    (Item211LieProof.conj_injective_of_center_eq_bot hZ)).toEquiv).symm

theorem exists_conj_of_pow_three_of_card_le (hZ : Subgroup.center Y = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) {α : MulAut Y} (h3 : α ^ 3 = 1) :
    ∃ y : Y, α = MulAut.conj y := by
  classical
  set I : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range with hI
  haveI : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal Y
  have hIcard : Nat.card I = Nat.card Y := card_range_conj_eq hZ
  have hYpos : 0 < Nat.card Y := Nat.card_pos
  have hfin : Finite (MulAut Y) :=
    Finite.of_injective (fun α : MulAut Y => (α : Y → Y)) DFunLike.coe_injective
  have hidx : I.index ≤ 2 := by
    have h := I.card_mul_index
    rw [hIcard] at h
    by_contra hcon
    push Not at hcon
    have : Nat.card Y * 3 ≤ Nat.card Y * I.index := Nat.mul_le_mul_left _ hcon
    omega
  have hidx0 : I.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpow := Subgroup.pow_index_mem I α
  have hα : α ∈ I := by
    interval_cases hi : I.index
    · exact absurd rfl hidx0
    · simpa using hpow
    · have h2 : α ^ 2 ∈ I := hpow
      have e : α = α ^ 3 * (α ^ 2)⁻¹ := by group
      rw [e, h3, one_mul]
      exact I.inv_mem h2
  obtain ⟨y, hy⟩ := hα
  exact ⟨y, hy.symm⟩

theorem card_sylow_three_of_padicValNat {N : ℕ} (hY : Nat.card Y = N) (hN : padicValNat 3 N = 2)
    (P : Sylow 3 Y) : Nat.card P = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [P.card_eq_multiplicity, hY, Nat.factorization_def _ Nat.prime_three, hN]
  norm_num

end AutBound

end CFSG.RankThree.PartTwo.Sec21.Hering214
