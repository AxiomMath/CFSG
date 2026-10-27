module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem card_outer_psu6 {X : Type} [Group X] (hmod : StatedClassicalModel X .PSU 6 2 1) :
    Nat.card (Outer X) = 6 := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hU : UnitaryFieldData 2 1 K := ⟨hℓ, hm, by rw [hK]; norm_num⟩
  have hq : ¬(6 = 3 ∧ 2 ^ 1 = 2) := fun ⟨h1, _⟩ => absurd h1 (by norm_num)
  have h1 := (unitary_full_diagonal_outer_order hU (n := 6) (by norm_num) hq).2.2.2.2.1
  have e' : X ≃* unitaryPSU hU 6 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  rw [Nat.card_congr (equivalence e').toEquiv, h1]
  norm_num

theorem exists_conj_of_pow_five_psu6 {X : Type} [Group X]
    (hmod : StatedClassicalModel X .PSU 6 2 1) (α : MulAut X) (hα : α ^ 5 = 1) :
    ∃ a : X, α = MulAut.conj a := by
  have hcard := card_outer_psu6 hmod
  have h1 : (QuotientGroup.mk α : Outer X) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow, hα]
    rfl
  have h2 : orderOf (QuotientGroup.mk α : Outer X) ∣ 5 := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk α : Outer X) ∣ 6 := hcard ▸ orderOf_dvd_natCard _
  have h4 : orderOf (QuotientGroup.mk α : Outer X) ∣ Nat.gcd 5 6 := Nat.dvd_gcd h2 h3
  have h5 : orderOf (QuotientGroup.mk α : Outer X) = 1 := by
    have : Nat.gcd 5 6 = 1 := by norm_num
    rw [this] at h4
    exact Nat.dvd_one.mp h4
  have h6 : (QuotientGroup.mk α : Outer X) = 1 := orderOf_eq_one_iff.mp h5
  have h7 : α ∈ inner X := (QuotientGroup.eq_one_iff α).mp h6
  obtain ⟨a, ha⟩ := h7
  exact ⟨a, ha.symm⟩

end CFSG.RankThree.PartOne.F106
