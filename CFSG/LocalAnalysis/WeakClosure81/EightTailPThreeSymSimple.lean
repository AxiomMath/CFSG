module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64
import CFSG.LocalAnalysis.ComponentClassification.Sol78Thm11

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin Subgroup

theorem isSimpleGroup_of_isSpGp {L : Type} [Group L] {m n : ℕ} (h : IsSpGp L m n) (hm : 2 ≤ m)
    (hn : 2 ≤ n ∨ 6 ≤ m) : IsSimpleGroup L := by
  obtain ⟨k, hmk, F, hFld, hFin, hFcard, ⟨e⟩⟩ := h
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  have hk : 1 ≤ k := by omega
  haveI : NeZero k := ⟨by omega⟩
  have hn1 : 1 ≤ n := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hFcard] at h1
    have h2 : n ≠ 0 := Nat.one_lt_two_pow_iff.1 h1
    omega
  have hcard : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ k) ∨
      (Nat.card F = 2 ∧ 3 ≤ k) := by
    by_cases hn2 : 2 ≤ n
    · left; right
      rw [hFcard]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    · right; right
      have hk3 : 3 ≤ k := by
        rcases hn with h2 | h6
        · omega
        · omega
      refine ⟨?_, hk3⟩
      have hn_eq : n = 1 := by omega
      rw [hFcard, hn_eq, pow_one]
  have hproj : IsSimpleGroup (StatedProj (StatedSp k F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F k hk hcard
  have hsimple : IsSimpleGroup (StatedSp k F) :=
    (MulEquiv.ofBijective _
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
        (r := k) (K := F))).isSimpleGroup_congr.2 hproj
  exact (MulEquiv.isSimpleGroup_congr e).2 hsimple

theorem isSimpleGroup_of_isPSUGp {L : Type} [Group L] {m n : ℕ} (h : IsPSUGp L m n)
    (hm : 4 ≤ m ∨ (m = 3 ∧ 2 ≤ n)) : IsSimpleGroup L := by
  have hm0 : m ≠ 0 := by rcases hm with h | ⟨h, -⟩ <;> omega
  have hmodel : CFSG.Open.StatedClassicalModel L .PSU m 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hm0 h
  exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity L m 2 n hmodel).2

theorem false_of_isSimpleGroup_center_quot_symGp {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    (hm : 4 ≤ m) (hodd : Odd (Nat.card (Subgroup.center Y)))
    (h : IsSymGp (Y ⧸ fusionOddCore Y) m) (hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y)) :
    False := by
  let Z := Subgroup.center Y
  let O := fusionOddCore Y
  have hZO : Z ≤ O := CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hodd
  haveI : (O.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.map (QuotientGroup.mk' Z)) with hbot | htop
  · have hOZ : O ≤ Z := by
      have h' := (Subgroup.map_eq_bot_iff (H := O) (f := QuotientGroup.mk' Z)).mp hbot
      rwa [QuotientGroup.ker_mk'] at h'
    have hOeqZ : O = Z := le_antisymm hOZ hZO
    obtain ⟨e⟩ := h
    haveI : IsSimpleGroup (Y ⧸ Z) := hsimple
    haveI : IsSimpleGroup (Y ⧸ O) :=
      (QuotientGroup.quotientMulEquivOfEq hOeqZ).isSimpleGroup
    exact CFSG.ComponentClassification.Sol78.not_isSimpleGroup_perm_fin (by omega)
      (e.symm.isSimpleGroup)
  · have hOtop : O = ⊤ := by
      have h1 : Subgroup.comap (QuotientGroup.mk' Z) (O.map (QuotientGroup.mk' Z)) = ⊤ := by
        rw [htop, Subgroup.comap_top]
      rw [QuotientGroup.comap_map_mk'] at h1
      rwa [sup_eq_right.mpr hZO] at h1
    obtain ⟨e⟩ := h
    haveI : Subsingleton (Y ⧸ O) := by
      rw [hOtop]; exact QuotientGroup.subsingleton_quotient_top
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hsub : Subsingleton (Equiv.Perm (Fin m)) := e.toEquiv.symm.subsingleton
    exact not_subsingleton_iff_nontrivial.mpr inferInstance hsub

theorem isSpGp_four_one_of_isSymGp_of_spPSU {Y : Type} [Group Y] [Finite Y] {m : ℕ} (hm : 4 ≤ m)
    (hodd : Odd (Nat.card (Subgroup.center Y))) (h : IsSymGp (Y ⧸ fusionOddCore Y) m)
    {m' n' : ℕ} (hm' : 3 < m')
    (h' : IsSpGp (Y ⧸ Subgroup.center Y) m' n' ∨ IsPSUGp (Y ⧸ Subgroup.center Y) m' n') :
    IsSpGp (Y ⧸ Subgroup.center Y) 4 1 := by
  rcases h' with hsp | hpsu
  · have hsp' := hsp
    obtain ⟨k, hmk, F, hFld, hFin, hFcard, ⟨_⟩⟩ := hsp
    have hn'1 : 1 ≤ n' := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hFcard] at h1
      have h2 : n' ≠ 0 := Nat.one_lt_two_pow_iff.1 h1
      omega
    by_cases hcase : 2 ≤ n' ∨ 6 ≤ m'
    · exact (false_of_isSimpleGroup_center_quot_symGp hm hodd h
        (isSimpleGroup_of_isSpGp hsp' (by omega) hcase)).elim
    · have hnot2 : ¬ (2 ≤ n') := (not_or.mp hcase).1
      have hnot6 : ¬ (6 ≤ m') := (not_or.mp hcase).2
      have hn1 : n' = 1 := by
        have h2 : n' < 2 := not_le.1 hnot2
        omega
      have hm4 : m' = 4 := by
        have h6 : m' < 6 := not_le.1 hnot6
        omega
      rw [hm4, hn1] at hsp'
      exact hsp'
  · exact (false_of_isSimpleGroup_center_quot_symGp hm hodd h
      (isSimpleGroup_of_isPSUGp hpsu (Or.inl (by omega)))).elim

end CFSG.LocalAnalysis.WeakClosure81

end
