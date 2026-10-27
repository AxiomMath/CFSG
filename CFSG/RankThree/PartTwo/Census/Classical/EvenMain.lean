module

public import CFSG.RankThree.PartTwo.Census.Interface
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
import CFSG.RankThree.PartTwo.Census.Classical.EvenHyperbolic
import CFSG.RankThree.PartTwo.Census.Classical.EvenLinear
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial

section Bridges

variable (r : ℕ) (q : TauCeti.PrimePower)

theorem excluded433_A_of_localRank_three_le (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    [Fact q.p.Prime]
    (h : localRank 3 (ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent))
      ≤ 2) : Excluded433 (.lie ⟨.A r q, hv⟩) :=
  fun _ _ _ hG e => hG.false_of_localRank_three_le_two
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)) h

theorem excluded433_A_of_four_le (hv : (TauCeti.LieTypeIndex.A r q).Valid) [Fact q.p.Prime]
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (h : 4 ≤ localRank s (ProjectiveSpecialLinearGroup (Fin (r + 1))
      (GaloisField q.p q.exponent))) : Excluded433 (.lie ⟨.A r q, hv⟩) :=
  fun _ _ _ hG e => hG.false_of_four_le_localRank
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)) hs hs2 h

theorem excluded433_A_of_three_le (hv : (TauCeti.LieTypeIndex.A r q).Valid) [Fact q.p.Prime]
    {s : ℕ} (hs : s.Prime) (hs3 : 3 < s)
    (h : 3 ≤ localRank s (ProjectiveSpecialLinearGroup (Fin (r + 1))
      (GaloisField q.p q.exponent))) : Excluded433 (.lie ⟨.A r q, hv⟩) :=
  fun _ _ _ hG e => hG.false_of_three_le_localRank
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)) hs hs3 h

theorem excluded433_twistedA_of_localRank_three_le
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) [Fact q.p.Prime]
    (h : localRank 3 (StatedProj (StatedSU (r + 1) (q.p ^ q.exponent)
      (GaloisField q.p (2 * q.exponent)))) ≤ 2) : Excluded433 (.lie ⟨.twistedA r q, hv⟩) :=
  fun _ _ _ hG e => hG.false_of_localRank_three_le_two
    (e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv)) h

theorem excluded433_twistedA_of_four_le (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    [Fact q.p.Prime] {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (h : 4 ≤ localRank s (StatedProj (StatedSU (r + 1) (q.p ^ q.exponent)
      (GaloisField q.p (2 * q.exponent))))) : Excluded433 (.lie ⟨.twistedA r q, hv⟩) :=
  fun _ _ _ hG e => hG.false_of_four_le_localRank
    (e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv)) hs hs2 h

theorem excluded433_twistedA_of_three_le (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    [Fact q.p.Prime] {s : ℕ} (hs : s.Prime) (hs3 : 3 < s)
    (h : 3 ≤ localRank s (StatedProj (StatedSU (r + 1) (q.p ^ q.exponent)
      (GaloisField q.p (2 * q.exponent))))) : Excluded433 (.lie ⟨.twistedA r q, hv⟩) :=
  fun _ _ _ hG e => hG.false_of_three_le_localRank
    (e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv)) hs hs3 h

end Bridges

theorem unitaryFieldData_galoisField_two {f : ℕ} (hf : 0 < f) :
    UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
  ⟨Nat.prime_two, hf, GaloisField.card 2 (2 * f) (by omega)⟩

theorem card_units_galoisField_two {f : ℕ} (hf : 0 < f) :
    Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by
  rw [Nat.card_units, GaloisField.card 2 f (by omega)]

theorem item433Case_A_even (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq : q.p = 2) :
    Item433Case (.lie ⟨.A r q, hv⟩) := by
  obtain ⟨p, f, hp, hf⟩ := q
  obtain rfl : p = 2 := hq
  have hr1 : 1 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp hv.1).1
  have hK := card_units_galoisField_two hf
  have h2f : ∀ g, 2 ≤ g → 4 ≤ 2 ^ g := fun g hg =>
    (Nat.pow_le_pow_right (by norm_num) hg).trans' (by norm_num)
  have hodd : 2 ≤ f → ∃ s, s.Prime ∧ s ≠ 2 ∧ s ≠ 5 ∧ s ∣ Nat.card (GaloisField 2 f)ˣ := by
    intro hf2
    rw [hK]
    exact exists_prime_ne_five_dvd_two_pow_sub_one hf2
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ 7 ≤ r by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | hr7
  ·
    exact (excluded433_A_of_localRank_three_le 1 _ hv localRank_three_PSL_two_le).item433Case
  ·
    exact (excluded433_A_of_localRank_three_le 2 _ hv localRank_three_PSL_three_le).item433Case
  ·
    rcases (show f = 1 ∨ f = 2 ∨ 3 ≤ f by omega) with rfl | rfl | hf3
    · exact absurd ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).mpr
        (Or.inr (Or.inr ⟨rfl, rfl⟩))) hv.2
    · exact item433Case_A_three_four _ hv rfl rfl
    · obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_sub_one hf3
      have hsd' : s ∣ Nat.card (GaloisField 2 f)ˣ := by
        rw [hK]
        exact hsd
      refine (excluded433_A_of_three_le 3 _ hv hs (by omega)
        (le_localRank_PSL_torus hs hsd' (by norm_num) (by norm_num)
          (Or.inr fun h4 => ?_))).item433Case
      have := Nat.le_of_dvd (by norm_num) h4
      omega
  ·
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · exact (excluded433_A_of_localRank_three_le 4 _ hv
        localRank_three_PSL_five_two_le).item433Case
    · obtain ⟨s, hs, hs2, hs5, hsd⟩ := hodd hf2
      refine (excluded433_A_of_four_le 4 _ hv hs hs2
        (le_localRank_PSL_torus hs hsd (by norm_num) (by norm_num)
          (Or.inr fun h5 => hs5 ?_))).item433Case
      exact (Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h5
  ·
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · exact item433Case_A_five_two _ hv rfl rfl
    · obtain ⟨s, hs, hs2, -, hsd⟩ := hodd hf2
      exact (excluded433_A_of_four_le 5 _ hv hs hs2
        (le_localRank_PSL_torus hs hsd (by norm_num) (by norm_num)
          (Or.inl (by norm_num)))).item433Case
  ·
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · exact item433Case_A_six_two _ hv rfl rfl
    · obtain ⟨s, hs, hs2, -, hsd⟩ := hodd hf2
      exact (excluded433_A_of_four_le 6 _ hv hs hs2
        (le_localRank_PSL_torus hs hsd (by norm_num) (by norm_num)
          (Or.inl (by norm_num)))).item433Case
  ·
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · exact (excluded433_A_of_four_le r _ hv Nat.prime_three (by norm_num)
        (four_le_localRank_PSL_of_eight_le (by omega))).item433Case
    · obtain ⟨s, hs, hs2, -, hsd⟩ := hodd hf2
      exact (excluded433_A_of_four_le r _ hv hs hs2
        (le_localRank_PSL_torus (m := 4) hs hsd (by omega) (by omega)
          (Or.inl (by omega)))).item433Case

theorem item433Case_twistedA_even (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.p = 2) :
    Item433Case (.lie ⟨.twistedA r q, hv⟩) := by
  obtain ⟨p, f, hp, hf⟩ := q
  obtain rfl : p = 2 := hq
  have hr2 : 2 ≤ r := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange hv.1
  have h := unitaryFieldData_galoisField_two hf
  rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ 6 ≤ r by omega) with rfl | rfl | rfl | rfl | hr6
  ·
    exact (excluded433_twistedA_of_localRank_three_le 2 _ hv
      (localRank_three_statedSU_three_le h)).item433Case
  ·
    exact (excluded433_twistedA_of_localRank_three_le 3 _ hv
      (localRank_three_statedSU_four_le h)).item433Case
  ·
    rcases (show f = 1 ∨ f = 2 ∨ f = 3 ∨ 4 ≤ f by omega) with rfl | rfl | rfl | hf4
    · exact item433Case_twistedA_four_two _ hv rfl rfl
    · exact (excluded433_twistedA_of_localRank_three_le 4 _ hv
        (localRank_three_statedSU_five_four_le h)).item433Case
    · exact item433Case_twistedA_four_eight _ hv rfl rfl
    · obtain ⟨s, hs, hs7, hsd⟩ := exists_prime_seven_le_dvd_two_pow_add_one hf4
      refine (excluded433_twistedA_of_three_le 4 _ hv hs (by omega)
        (le_localRank_statedSU_torus (k := 2) h hs hsd (by norm_num)
          (Or.inr fun h5 => ?_))).item433Case
      have := Nat.le_of_dvd (by norm_num) h5
      omega
  ·
    rcases (show f = 1 ∨ f = 3 ∨ (2 ≤ f ∧ f ≠ 3) by omega) with rfl | rfl | ⟨hf2, hf3⟩
    · exact item433Case_twistedA_five_two _ hv rfl rfl
    · exact (excluded433_twistedA_of_three_le 5 _ hv (by norm_num) (by norm_num)
        (three_le_localRank_statedSU_six_eight h)).item433Case
    · obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_add_one hf2 hf3
      exact (excluded433_twistedA_of_three_le 5 _ hv hs (by omega)
        (le_localRank_statedSU_torus (k := 2) h hs hsd (by norm_num)
          (Or.inl (by norm_num)))).item433Case
  ·
    obtain ⟨s, hs, hs2, hsd⟩ := exists_odd_prime_dvd_two_pow_add_one hf
    exact (excluded433_twistedA_of_four_le r _ hv hs hs2
      (le_localRank_statedSU_torus (k := 3) h hs hsd (by omega)
        (Or.inl (by omega)))).item433Case

theorem item433Case_B2_even (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    (hq : q.p = 2) : Item433Case (.lie ⟨.B 2 q, hv⟩) := by
  set K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)
  have : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card K = 2 ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder, hq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card, hcard])
  refine Excluded433.item433Case fun _ _ _ hG e => hG.false_of_localRank_three_le_two
    (e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)) ?_
  exact localRank_three_statedSp_two_le

end CFSG.RankThree.PartTwo.Census
