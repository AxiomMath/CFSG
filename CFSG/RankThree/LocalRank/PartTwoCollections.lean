module

public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.LocalRank.InvariantPrimeComplementOdd

public section

namespace CFSG.RankThree.LocalRank

open CFSG.Assembly.RankThreeEven

@[expose] def partTwoE (G : Type*) [Group G] : Set (Subgroup G) :=
  {E | CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G)}

@[expose] def partTwoF (G : Type*) [Group G] : Set (Subgroup G) :=
  {A | CFSG.Assembly.IsElemAbelian 3 A ∧
    (∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) ∧
    ∃ E ∈ partTwoE G, E ≤ A}

@[expose] def partTwoS (G : Type*) [Group G] : Set (Subgroup G) :=
  {A | A ∈ partTwoF G ∧
    (∀ a ∈ A, a ≠ 1 → Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)), A⁆ : Subgroup G))) ∧
    ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 → Odd (Nat.card (thetaT 3 B))}

@[expose] noncomputable def partTwoT (G : Type*) [Group G] [Finite G] : Set (Subgroup G) :=
  {E | E ∈ partTwoE G ∧ ∃ H : Subgroup G, CFSG.Assembly.IsTwoLocal H ∧ aschCore 2 3 E ≤ H}

theorem partTwoS_of_mem_partTwoF_not_mem_partTwoE {G : Type*} [Group G] [Finite G]
    (h3 : localRank 3 G ≤ 3) {A : Subgroup G} (hF : A ∈ partTwoF G) (hE : A ∉ partTwoE G) :
    A ∈ partTwoS G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAab, hAmax, E, hEmem, hEA⟩ := hF
  have hApg : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hApg
  have hEcard : Nat.card E = 27 := hEmem.2.1
  have hk4 : 4 ≤ k := by
    have hdvd : 3 ^ 3 ∣ 3 ^ k := by
      rw [← hk, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hEcard]
      exact Subgroup.card_dvd_of_le hEA
    have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    by_contra hlt
    have hkeq : k = 3 := by omega
    apply hE
    have hEA' : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hk, hkeq, hEcard]; norm_num)
    exact hEA' ▸ hEmem
  have hrankA : 4 ≤ CFSG.Assembly.pRank 3 A :=
    hk4.trans (le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3
      Nat.prime_three A) ⟨A, le_rfl, hAab, hk⟩)
  have hrank : localRank 3 G < CFSG.Assembly.pRank 3 A := by omega
  have hodd : ∀ a ∈ A, a ≠ 1 →
      Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))))
      ∧ A ≤ Subgroup.normalizer
        (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) : Set G) := by
    intro a ha _
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf Nat.prime_three]
    have hnorm : A ≤ Subgroup.normalizer
        (CFSG.RankThreeEvenClassification.Helpers.thetaCoreOf 3
          (Subgroup.centralizer ({a} : Set G)) : Set G) :=
      CFSG.RankThreeEvenClassification.Helpers.commutative_plane_normalizes_element_theta 3
        Nat.prime_three A hAab.1 a ha
    exact ⟨above_two_local_rank_invariant_prime_complement_odd Nat.prime_three hApg hrank hnorm
      (CFSG.RankThreeEvenClassification.Helpers.thetaCoreOf_prime_complement 3 Nat.prime_three _),
      hnorm⟩
  refine ⟨⟨hAab, hAmax, E, hEmem, hEA⟩, fun a ha ha1 => ?_, fun B hBA hBcard => ?_⟩
  · obtain ⟨hRodd, hRnorm⟩ := hodd a ha ha1
    exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_le
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hRnorm))
  · have hBne : B ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hBcard
      omega
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨hRodd, -⟩ := hodd b (hBA hb) hb1'
    have hle : thetaT 3 B ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) :=
      iInf_le_of_le b (iInf_le_of_le hb (iInf_le_of_le hb1' le_rfl))
    exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem part_two_empty_odd_collection_rank_three_reduction {G : Type*} [Group G] [Finite G]
    (h3 : localRank 3 G ≤ 3) :
    partTwoF G \ partTwoE G ⊆ partTwoS G ∧
    (∀ A ∈ partTwoF G \ partTwoS G, A ∈ partTwoE G ∧ Nat.card A = 27) ∧
    (partTwoS G = ∅ → partTwoF G = partTwoE G) ∧
    (partTwoS G = ∅ → localRank 3 G = 3 → (partTwoF G).Nonempty ∧ (partTwoE G).Nonempty) := by
  have hsub : partTwoF G \ partTwoE G ⊆ partTwoS G := fun A hA =>
    partTwoS_of_mem_partTwoF_not_mem_partTwoE h3 hA.1 hA.2
  have hcomp : ∀ A ∈ partTwoF G \ partTwoS G, A ∈ partTwoE G ∧ Nat.card A = 27 := by
    rintro A ⟨hF, hS⟩
    have hE : A ∈ partTwoE G := by
      by_contra hE
      exact hS (hsub ⟨hF, hE⟩)
    exact ⟨hE, hE.2.1⟩
  have heq : partTwoS G = ∅ → partTwoF G = partTwoE G := by
    intro hS
    apply Set.Subset.antisymm
    · intro A hF
      exact (hcomp A ⟨hF, by rw [hS]; exact Set.notMem_empty A⟩).1
    · intro E hE
      obtain ⟨A, hEA, hmax⟩ := Finite.exists_le_maximal
        (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hE.1
      have hF : A ∈ partTwoF G :=
        ⟨hmax.prop, fun B hB hAB => le_antisymm (hmax.2 hB hAB) hAB, E, hE, hEA⟩
      obtain ⟨-, hAcard⟩ := hcomp A ⟨hF, by rw [hS]; exact Set.notMem_empty A⟩
      have hEA' : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hAcard, hE.2.1])
      exact hEA' ▸ hF
  refine ⟨hsub, hcomp, heq, fun hS h3eq => ?_⟩
  have hEne : (partTwoE G).Nonempty := by
    have hpos : 0 < CFSG.RankThreeEvenClassification.Helpers.twoLocalRank 3 G := by
      change 0 < localRank 3 G
      omega
    obtain ⟨H, hH, hHrank⟩ := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained 3
      Nat.prime_three G hpos
    obtain ⟨U, hU, hU2, rfl⟩ := hH
    obtain ⟨E, hEH, hEab, hEcard⟩ := CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3
      Nat.prime_three (Subgroup.normalizer (U : Set G))
    have hrank3 : CFSG.Open.pRank 3 (Subgroup.normalizer (U : Set G)) = 3 := hHrank.trans h3eq
    refine ⟨E, hEab, ?_, U, hU, hU2, hEH⟩
    rw [hEcard, hrank3]
    norm_num
  exact ⟨heq hS ▸ hEne, hEne⟩

end CFSG.RankThree.LocalRank
