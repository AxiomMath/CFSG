module

public import CFSG.RankThree.PartOne.KS.J2FiveStructure
public import CFSG.RankThree.PartOne.KS.Combine
public import CFSG.RankThree.PartOne.KS.Arith

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped Pointwise

theorem j2Five_class_ncard {i N Nc : ℕ} (hi : i < 6)
    (hO : j2FiveCentCheck i Nc = true) (hN : N * Nc = 1209600) :
    {y : Equiv.Perm (Fin 315) | ∃ g ∈ j2R, y = g * j2FiveLine ⟨i, hi⟩ * g⁻¹}.ncard = N := by
  have h := ncard_class_mul_card_centralizer j2R (j2FiveLine ⟨i, hi⟩)
  obtain ⟨hCeq, hcard⟩ := j2FiveC_eq hi hO
  rw [← hCeq, hcard, card_j2R, ← hN] at h
  have hpos : 0 < Nc := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hN; omega
  exact Nat.eq_of_mul_eq_mul_right hpos h

theorem j2Five_exponent : Monoid.exponent j2FiveQ = 5 := by
  have hdvd : Monoid.exponent j2FiveQ ∣ 5 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (j2FiveQ_pow_five g.2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h | h
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 h
    have := congrArg Subtype.val
      (hs.elim (⟨j2FiveLine 0, j2FiveLine_mem_Q 0⟩ : j2FiveQ) 1)
    exact j2FiveLine_ne_one 0 this
  · exact h

theorem j2Five_record (i : Fin 6) :
    (j2FiveC i = j2R ⊓ centralizer ({j2FiveLine i} : Set (Equiv.Perm (Fin 315))) ∧
        j2FiveQ ≤ j2FiveC i ∧
        centralizer (j2FiveQ : Set (Equiv.Perm (Fin 315))) ⊓ j2FiveC i = j2FiveQ ∧
        {y : Equiv.Perm (Fin 315) | ∃ g ∈ j2R, y = g * j2FiveLine i * g⁻¹}.ncard =
          (if i.val = 0 ∨ i.val = 1 ∨ i.val = 4 then 24192 else 4032)) ∧
      ((i.val = 0 ∨ i.val = 1 ∨ i.val = 4) →
        Nat.card (j2FiveC i) = 50 ∧ (j2FiveQ.subgroupOf (j2FiveC i)).Normal) ∧
      ((i.val = 2 ∨ i.val = 3 ∨ i.val = 5) →
        Nat.card (j2FiveC i) = 300 ∧ j2FiveD i ≤ j2FiveC i ∧ j2FiveD i ≤ j2P ∧
          ((j2FiveD i).subgroupOf (j2FiveC i)).Normal ∧ IsSimpleGroup (j2FiveD i) ∧
          (∃ g ∈ j2FiveD i, ∃ h ∈ j2FiveD i, g * h ≠ h * g) ∧ Nat.card (j2FiveD i) = 60 ∧
          centralizer (j2FiveD i : Set (Equiv.Perm (Fin 315))) ⊓ j2FiveC i =
            zpowers (j2FiveLine i)) := by
  obtain ⟨v, hv⟩ := i
  interval_cases v
  · obtain ⟨h1, h2, h3, h4, h5⟩ := j2FiveGood_structure (i := 0) hv j2Five_cent_check_0
      j2Five_good_check_0
    exact ⟨⟨h1, h3, h4, by simpa using j2Five_class_ncard (N := 24192) hv j2Five_cent_check_0 (by norm_num)⟩,
      fun _ => ⟨h2, h5⟩, fun h => by simp at h⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := j2FiveGood_structure (i := 1) hv j2Five_cent_check_1
      j2Five_good_check_1
    exact ⟨⟨h1, h3, h4, by simpa using j2Five_class_ncard (N := 24192) hv j2Five_cent_check_1 (by norm_num)⟩,
      fun _ => ⟨h2, h5⟩, fun h => by simp at h⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      j2FiveBad_structure (i := 2) hv j2Five_cent_check_2 j2Five_bad_check_2
    exact ⟨⟨h1, h3, h4, by simpa using j2Five_class_ncard (N := 4032) hv j2Five_cent_check_2 (by norm_num)⟩,
      fun h => by simp at h, fun _ => ⟨h2, h5, h6, h7, h8, h9, h10, h11⟩⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      j2FiveBad_structure (i := 3) hv j2Five_cent_check_3 j2Five_bad_check_3
    exact ⟨⟨h1, h3, h4, by simpa using j2Five_class_ncard (N := 4032) hv j2Five_cent_check_3 (by norm_num)⟩,
      fun h => by simp at h, fun _ => ⟨h2, h5, h6, h7, h8, h9, h10, h11⟩⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := j2FiveGood_structure (i := 4) hv j2Five_cent_check_4
      j2Five_good_check_4
    exact ⟨⟨h1, h3, h4, by simpa using j2Five_class_ncard (N := 24192) hv j2Five_cent_check_4 (by norm_num)⟩,
      fun _ => ⟨h2, h5⟩, fun h => by simp at h⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      j2FiveBad_structure (i := 5) hv j2Five_cent_check_5 j2Five_bad_check_5
    exact ⟨⟨h1, h3, h4, by simpa using j2Five_class_ncard (N := 4032) hv j2Five_cent_check_5 (by norm_num)⟩,
      fun h => by simp at h, fun _ => ⟨h2, h5, h6, h7, h8, h9, h10, h11⟩⟩

theorem R3E_J2_full_five_centralizer_structure :
    (j2FiveQ ≤ j2P ∧ (∀ g ∈ j2FiveQ, ∀ h ∈ j2FiveQ, g * h = h * g) ∧
      Monoid.exponent j2FiveQ = 5 ∧ Nat.card j2FiveQ = 25 ∧
      ∃ S : Sylow 5 j2P, (S : Subgroup j2P) = j2FiveQ.subgroupOf j2P) ∧
    ({H : Subgroup (Equiv.Perm (Fin 315)) | H ≤ j2FiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => zpowers (j2FiveLine i)) ∧
      Function.Injective (fun i : Fin 6 => zpowers (j2FiveLine i))) ∧
    (∀ i : Fin 6, j2FiveC i = j2R ⊓ centralizer ({j2FiveLine i} : Set (Equiv.Perm (Fin 315))) ∧
        j2FiveQ ≤ j2FiveC i ∧
        centralizer (j2FiveQ : Set (Equiv.Perm (Fin 315))) ⊓ j2FiveC i = j2FiveQ ∧
        {y : Equiv.Perm (Fin 315) | ∃ g ∈ j2R, y = g * j2FiveLine i * g⁻¹}.ncard =
          (if i.val = 0 ∨ i.val = 1 ∨ i.val = 4 then 24192 else 4032)) ∧
    (∀ i : Fin 6, (i.val = 0 ∨ i.val = 1 ∨ i.val = 4) →
        Nat.card (j2FiveC i) = 50 ∧ (j2FiveQ.subgroupOf (j2FiveC i)).Normal) ∧
    (∀ i : Fin 6, (i.val = 2 ∨ i.val = 3 ∨ i.val = 5) →
        Nat.card (j2FiveC i) = 300 ∧ j2FiveD i ≤ j2P ∧ IsSimpleGroup (j2FiveD i) ∧
          (∃ g ∈ j2FiveD i, ∃ h ∈ j2FiveD i, g * h ≠ h * g) ∧ Nat.card (j2FiveD i) = 60 ∧
          ((j2FiveD i).subgroupOf (j2FiveC i)).Normal ∧
          centralizer (j2FiveD i : Set (Equiv.Perm (Fin 315))) ⊓ j2FiveC i =
            zpowers (j2FiveLine i) ∧ Nat.card (zpowers (j2FiveLine i)) = 5) := by
  refine ⟨⟨j2FiveQ_le_P, fun g hg h hh => (Subgroup.mem_centralizer_iff.1
      (j2FiveQ_le_centralizer hh) g hg), j2Five_exponent, card_j2FiveQ, j2FiveQ_sylow⟩,
    j2FiveQ_lines, fun i => (j2Five_record i).1, fun i hi => (j2Five_record i).2.1 hi,
    fun i hi => ?_⟩
  obtain ⟨h1, -, h3, h4, h5, h6, h7, h8⟩ := (j2Five_record i).2.2 hi
  exact ⟨h1, h3, h5, h6, h7, h4, h8, by rw [Nat.card_zpowers, orderOf_j2FiveLine]⟩


theorem j2_card_le : Nat.card j2R ≤ 2 * Nat.card j2P := by
  rw [card_j2R, card_j2P]

theorem j2FiveQ_isPGroup : IsPGroup 5 j2FiveQ := fun g => ⟨1, by
  apply Subtype.ext
  simpa using j2FiveQ_pow_five g.2⟩

theorem j2Five_core_bot (i : Fin 6) (B : Subgroup (Equiv.Perm (Fin 315))) (hPB : j2P ≤ B)
    (hBR : B ≤ j2R) :
    inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({j2FiveLine i} : Set (Equiv.Perm (Fin 315)))) = ⊥ := by
  obtain ⟨⟨hCeq, hQC, hQeq, -⟩, hgood, hbad⟩ := j2Five_record i
  by_cases hg : i.val = 0 ∨ i.val = 1 ∨ i.val = 4
  · obtain ⟨-, hnorm⟩ := hgood hg
    have hQx : j2FiveQ ≤ centralizer ({j2FiveLine i} : Set (Equiv.Perm (Fin 315))) :=
      le_trans j2FiveQ_le_centralizer
        (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (j2FiveLine_mem_Q i)))
    refine line_core_bot_of_normal_pgroup Nat.prime_five hPB hBR j2FiveQ_le_P j2FiveQ_isPGroup
      hQx ?_ ?_
    · rw [← hCeq]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).1 hnorm
    · rw [← hCeq]
      refine j2FiveQ_isPGroup.to_le ?_
      rw [inf_comm]
      exact hQeq.le
  · have hbad' : i.val = 2 ∨ i.val = 3 ∨ i.val = 5 := by
      have := i.2
      omega
    obtain ⟨-, hDC, hDP, hDn, hDs, hnonab, -, hcent⟩ := hbad hbad'
    have hDq : IsQuasisimple (j2FiveD i) := by
      have := hDs
      obtain ⟨g, hg, h, hh, hne⟩ := hnonab
      exact isQuasisimple_of_isSimpleGroup ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hne (congrArg Subtype.val e)⟩
    refine line_core_bot_of_normal_component Nat.prime_five hPB hBR hDP hDq
      ((hDC.trans hCeq.le).trans inf_le_right) ?_ ?_
    · rw [← hCeq]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).1 hDn
    · rw [← hCeq, inf_comm, hcent]
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_j2FiveLine, pow_one])

theorem almostSimpleLocalCoresTrivial_five_J2 : AlmostSimpleLocalCoresTrivial 5 (Carrier .J2) := by
  intro H _ _ K _ hK hC x hx
  obtain ⟨e⟩ := hK
  have hline := core_bot_of_lines (P := j2P) (R := j2R) Nat.prime_five j2FiveQ_sylow
    j2FiveQ_lines.1 (fun i B hPB hBR => j2Five_core_bot i B hPB hBR)
  exact aschbacherCore_centralizer_eq_bot_of_model j2_autModel j2_card_le Nat.prime_five
    (by norm_num) hline K (e.trans j2PermEquiv) hC x hx

theorem sporadicPlaneOdd_J2 : SporadicPlaneOdd (Carrier .J2) := by
  refine sporadicPlaneOdd_of_almostSimple {5} (fun q hq _ => ?_) ?_
  · rw [Finset.mem_singleton.mp hq]
    exact almostSimplePlaneOdd_of_localCoresTrivial Nat.prime_five
      almostSimpleLocalCoresTrivial_five_J2
  · intro T _ _ _ hnab hTA p hp hp3 hpS
    obtain ⟨e⟩ := hTA
    have hp5 : p ≠ 5 := fun h => hpS (by simp [h])
    have hcard : Nat.card (MulAut T) = 2 ^ 8 * 3 ^ 3 * 5 ^ 2 * 7 := by
      obtain ⟨-, -, -, -, h⟩ := ctuc_j2_full_automorphism_permutation_model
      rw [Nat.card_congr (MulAut.congr (e.trans j2PermEquiv)).toEquiv, h]
      norm_num
    rw [hcard]
    exact not_sq_dvd_mul_of_coprime (B := 2) hp (coprime_two_three_five_pow hp hp3 hp5 8 3 2)
      (by norm_num) (by decide) (by norm_num)

end CFSG.RankThree.PartOne
