module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
import CFSG.CGT.T75N.L29Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {Y : Type} [Group Y] [Finite Y]

private theorem w183_one_le_of_card {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) : 1 ≤ a := by
  by_contra h
  have h0 : a = 0 := by omega
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [h0, pow_zero] at hK
  omega

private theorem w183_subsingleton_specialLinear_of_lt_two {K : Type} [Field K] {m : ℕ}
    (hm : m < 2) : Subsingleton (Matrix.SpecialLinearGroup (Fin m) K) := by
  refine ⟨fun A B => Subtype.ext (Matrix.ext fun i j => ?_)⟩
  have hi := i.isLt
  obtain rfl : m = 1 := by omega
  have hA := A.2
  have hB := B.2
  rw [Matrix.det_unique] at hA hB
  rw [Subsingleton.elim i default, Subsingleton.elim j default, hA, hB]

private theorem w183_two_le_of_isSLn {X : Type} [Group X] {n a : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (hshape : IsSLn X n a) : 2 ≤ n := by
  by_contra hlt
  have hn : n < 2 := by omega
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hshape
  letI := hKf
  haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin n) K) :=
    w183_subsingleton_specialLinear_of_lt_two hn
  haveI : Subsingleton ↥(StatedSL n K) :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).toEquiv.symm.subsingleton
  have hnt : Nontrivial X := by
    haveI : Nontrivial (X ⧸ Subgroup.center X) := hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  exact (not_subsingleton_iff_nontrivial (α := X)).mpr hnt e.toEquiv.subsingleton

private theorem w183_sq_not_dvd_six {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ 6 := by
  intro hdiv
  have hle : q ^ 2 ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
  have hq3 : 3 ≤ q := by
    have h2q : 2 ≤ q := hq.two_le
    by_contra h
    have : q = 2 := by omega
    exact hq2 this
  have h9 : 9 ≤ q ^ 2 := by
    have h := Nat.pow_le_pow_left hq3 2
    norm_num at h
    exact h
  exact absurd (h9.trans hle) (by norm_num)

private theorem w183_sq_not_dvd_168 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ 168 := by
  intro hdiv
  have hle : q ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) hdiv
  have hq3 : 3 ≤ q := by
    have h2q : 2 ≤ q := hq.two_le
    by_contra h
    have : q = 2 := by omega
    exact hq2 this
  have hqle : q ≤ 12 := by
    by_contra h
    have h13 : 13 ≤ q := by omega
    have h169 : 13 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h13 2
    norm_num at h169
    exact absurd (h169.trans hle) (by norm_num)
  interval_cases q <;> exact absurd hdiv (by norm_num)

private theorem w183_statedClassicalModel_psl_two_of_isSLn {X : Type} [Group X] {m : ℕ}
    (hm : 2 ≤ m) (h : IsSLn X 2 m) : StatedClassicalModel X .PSL 2 2 m := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 := (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hbot : (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
  let q : StatedProj (StatedSL 2 K) ≃* ↥(StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hadm : StatedLieAdmissible .PSL 2 2 m := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
    · intro hh
      have h2 : 2 ^ m = 2 := congrArg Prod.snd hh
      rw [h2] at h4
      omega
    · intro hh
      have h3 : 2 ^ m = 3 := congrArg Prod.snd hh
      rw [h3] at h4
      omega
  exact ⟨hadm, K, hKf, hKfin, hKcard, ⟨e.trans q.symm⟩⟩

theorem s16nt_range_sl {n a : ℕ} (hq : CFSG.Open.IsQuasisimple Y)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup Y))
    (h : IsSLn Y n a) : 4 ≤ n ∨ (n = 3 ∧ 2 ≤ a) := by
  by_contra hcon
  have hnle : n ≤ 3 := by omega
  have hnot : ¬ (n = 3 ∧ 2 ≤ a) := fun hh => hcon (Or.inr hh)
  have h2 : 2 ≤ n := w183_two_le_of_isSLn hq h
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have ha1 : 1 ≤ a := w183_one_le_of_card hKcard
  rcases lt_or_eq_of_le ha1 with ha2 | ha1eq
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn : n = 2 := by omega
      subst hn
      have hSL2 : IsSLn Y 2 a := ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩
      obtain ⟨q, hqp, hq2, hqr⟩ := hnt
      have hSCM := w183_statedClassicalModel_psl_two_of_isSLn (by omega) hSL2
      have hle := CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even hSCM hqp hq2
      omega
    · exact hnot ⟨by omega, by omega⟩
  · have hK2 : Nat.card K = 2 := by simpa [← ha1eq] using hKcard
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn : n = 2 := by omega
      subst hn
      have hcardY : Nat.card Y = 6 := by
        rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two K, hK2]
        norm_num
      obtain ⟨q, hqp, hq2, hqr⟩ := hnt
      have hsq : ¬ q ^ 2 ∣ Nat.card Y := by
        rw [hcardY]
        exact w183_sq_not_dvd_six hqp hq2
      have hle := CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hqp hsq
      omega
    · have hn : n = 3 := by omega
      subst hn
      have hcardY : Nat.card Y = 168 := by
        rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three K, hK2]
        norm_num
      obtain ⟨q, hqp, hq2, hqr⟩ := hnt
      have hsq : ¬ q ^ 2 ∣ Nat.card Y := by
        rw [hcardY]
        exact w183_sq_not_dvd_168 hqp hq2
      have hle := CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hqp hsq
      omega

theorem s16nt_false_l32
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup Y))
    (h : IsL3 Y 1) : False := by
  obtain ⟨q, hqp, hq2, hqr⟩ := hnt
  have hSCM : StatedClassicalModel Y .PSL 3 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSCM
  letI := hKf
  letI := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have e' : Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 K hK2)
  have hcardY : Nat.card Y = 168 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.CGT.T75N.card_SL_three_two (F := ZMod 2) (by rw [Nat.card_zmod])
  have hsq : ¬ q ^ 2 ∣ Nat.card Y := by
    rw [hcardY]
    exact w183_sq_not_dvd_168 hqp hq2
  have hle := CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hqp hsq
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
