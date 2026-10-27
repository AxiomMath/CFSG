module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FifteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapTransvSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3RankLeTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3TenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c167_two_lt_rk_corr (D : Data G) (h13 : R16_13_1 D) (h13b : R16_13_2 D)
    (hcorr : R16_14Corr D) (hT : S16GapTransvectionSmall D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) {A : Subgroup G}
    (hA : Choice1613 D ⊥ V hV L A) : 2 < rk ↥(barSub ⊥ V hV A) := by
  by_contra hle
  push Not at hle
  obtain ⟨hle', hres⟩ := hcorr V L hV hc
  have hA' : A ∈ E3.gammaSet V D.k D.T := by
    unfold Choice1613 at hA
    exact hA.1
  obtain ⟨hAT, g, hAg, hmQ⟩ := E3.mem_gammaSet_iff.1 hA'
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAel : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono hAg (E3.isElemAbelian_conjSubgroup hV g)
  obtain ⟨hVg, himp⟩ := (h13 ⊥ V L hV hc).2 A hA g hAg
  by_cases hstrict : ((D.k + 2 : ℕ) : ℕ∞) < rMV D.M V
  · obtain ⟨-, hVM⟩ := s16c167_le_conj_of_rk_le D hV hc hstrict hAM hAg hmQ hle
    have hS := s16c167_twenty_two_small D hc (h13b ⊥ V L hV hc) (himp hVM)
    have hU := hT V L hV hc hS A hA g hAg hVM hVg hle
    exact hVg (s16c167_conj_le_of_mQuot_le D hstrict hU)
  · have hr : rMV D.M V = ((D.k + 2 : ℕ) : ℕ∞) := le_antisymm (not_lt.1 hstrict) hle'
    rcases hres hr with ⟨h3, -⟩ | ⟨h11, -⟩
    · exact s16c167_false_of_case168_3 D hcorr hV hc h3 hr hAM hAel hAg hmQ hVg himp hle
    · have hrk1 : rk ↥(barSub ⊥ V hV A) ≤ 1 :=
        s16c167_rk_le_one_of_case168_11 D hV hc h11 (barSub_mono ⊥ V hV hAM)
          (isElemAbelian2_barSub hV hAel)
      have hlt : ((D.k + 1 : ℕ) : ℕ∞) < rMV D.M V := by
        rw [hr]
        exact_mod_cast (by omega : D.k + 1 < D.k + 2)
      have hVM := (s16c167_le_conj_of_rk_le_gen D hV hc hlt hAM hAg hmQ hrk1).2
      have h2 := himp hVM
      have h37 : D.sig = {7} := h11.2.2.2
      have h33 : D.sig = {3} := h2.2.2
      rw [h33] at h37
      simp at h37

theorem s16c167_rk_le_two_of_cases (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV)
    (hcase : Case168_3 D ⊥ V hV L ∨ Case168_4At D ⊥ V hV L 7 3 ∨ Case168_10At D ⊥ V hV L 7 ∨
      Case168_11 D ⊥ V hV L)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V D.k D.T) : rk ↥(barSub ⊥ V hV A) ≤ 2 := by
  obtain ⟨hAT, g, hAg, -⟩ := E3.mem_gammaSet_iff.1 hA
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAel : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono hAg (E3.isElemAbelian_conjSubgroup hV g)
  have hXM : barSub ⊥ V hV A ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hAM
  have hXel : IsElemAbelian2 (barSub ⊥ V hV A) := isElemAbelian2_barSub hV hAel
  rcases hcase with h | h | h | h
  · exact s16c167_rk_le_two_of_case168_3 D hV hc h hXM hXel
  · exact s16c167_rk_le_two_of_case168_4_seven D hV hc h hXM hXel
  · exact s16c167_rk_le_two_of_case168_10_seven D hV hc h hXM hXel
  · exact s16c167_rk_le_two_of_case168_11 D hV hc h hXM hXel

theorem r16_14_of_corr (D : Data G) (h12 : R16_12 D) (h13 : R16_13_1 D) (h13b : R16_13_2 D)
    (hcorr : R16_14Corr D) (hT : S16GapTransvectionSmall D) : R16_14 D := by
  intro V₀ V L hV hc
  obtain ⟨-, rfl, -⟩ := h12 V₀ V L hV hc
  obtain ⟨hle', hres⟩ := hcorr V L hV hc
  refine lt_of_le_of_ne hle' fun heq => ?_
  obtain ⟨A, hA⟩ := (h13 ⊥ V L hV hc).1
  have hrk := s16c167_two_lt_rk_corr D h13 h13b hcorr hT hV hc hA
  have hA' : A ∈ E3.gammaSet V D.k D.T := by
    unfold Choice1613 at hA
    exact hA.1
  rcases hres heq.symm with ⟨h3, -⟩ | ⟨h11, -⟩
  · exact absurd (s16c167_rk_le_two_of_cases D hV hc (Or.inl h3) hA') (not_le.2 hrk)
  · exact absurd (s16c167_rk_le_two_of_cases D hV hc (Or.inr (Or.inr (Or.inr h11))) hA')
      (not_le.2 hrk)

theorem r16_15_of_corr (D : Data G) (h12 : R16_12 D) (h13 : R16_13_1 D) (h13b : R16_13_2 D)
    (hcorr : R16_14Corr D) (hT : S16GapTransvectionSmall D) : R16_15 D := by
  intro V₀ V L hV hc A hA
  obtain ⟨-, rfl, -⟩ := h12 V₀ V L hV hc
  have hrk : 2 < rk ↥(barSub ⊥ V hV A) := s16c167_two_lt_rk_corr D h13 h13b hcorr hT hV hc hA
  refine ⟨hrk, ?_⟩
  have hA' : A ∈ E3.gammaSet V D.k D.T := by
    unfold Choice1613 at hA
    exact hA.1
  have hbad : ∀ h : Case168_3 D ⊥ V hV L ∨ Case168_4At D ⊥ V hV L 7 3 ∨
      Case168_10At D ⊥ V hV L 7 ∨ Case168_11 D ⊥ V hV L, False := fun h =>
    absurd (s16c167_rk_le_two_of_cases D hV hc h hA') (not_le.2 hrk)
  rcases h13b ⊥ V L hV hc with h | ⟨p, hp, h⟩ | h | h | h | ⟨p, hp, h⟩ | h
  · exact Or.inl (Case168_2Small.case168_2 D ⊥ V hV L h)
  · rcases hp with rfl | rfl
    · exact Or.inr (Or.inl h)
    · exact (hbad (Or.inr (Or.inl h))).elim
  · exact (hbad (Or.inl h)).elim
  · exfalso
    obtain ⟨hAT, g, hAg, -⟩ := E3.mem_gammaSet_iff.1 hA'
    have hAM : A ≤ D.M := hAT.trans D.sylowM.le
    have hAel : IsElemAbelian 2 A :=
      B2F.isElemAbelian_mono hAg (E3.isElemAbelian_conjSubgroup hV g)
    exact absurd (s16c167_rk_le_two_of_case168_8 D hV h
      (barSub_mono ⊥ V hV hAM) (isElemAbelian2_barSub hV hAel)) (not_le.2 hrk)
  · exact Or.inr (Or.inr (Or.inr h))
  · rcases hp with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl h))
    · exact (hbad (Or.inr (Or.inr (Or.inl h)))).elim
  · exact (hbad (Or.inr (Or.inr (Or.inr h)))).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
