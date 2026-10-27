module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGK1ScFinal
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Linear
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418Block
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLLiftP
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem not_three_dvd_two_pow_add_one_of_sub_one {f : ℕ}
    (h : 3 ∣ 2 ^ f - 1) : ¬ 3 ∣ 2 ^ f + 1 := by
  rintro ⟨k, hk⟩
  obtain ⟨l, hl⟩ := h
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  omega

private theorem not_three_dvd_two_pow_sub_one_of_add_one {f : ℕ}
    (h : 3 ∣ 2 ^ f + 1) : ¬ 3 ∣ 2 ^ f - 1 := by
  rintro ⟨k, hk⟩
  obtain ⟨l, hl⟩ := h
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  omega

private theorem ggE6Opp_three_dvd_two_pow_sub_one_or_add_one (f : ℕ) :
    3 ∣ 2 ^ f - 1 ∨ 3 ∣ 2 ^ f + 1 := by
  have h1 : ((2 : ZMod 3) ^ f = 1) ∨ ((2 : ZMod 3) ^ f = 2) := by
    induction f with
    | zero => left; decide
    | succ k ih =>
      rw [pow_succ]
      rcases ih with h | h <;> rw [h] <;> decide
  rcases h1 with h | h
  · left
    have h' : ((2 : ℕ) : ZMod 3) ^ f = 1 := by simpa using h
    apply (ZMod.natCast_eq_zero_iff (2 ^ f - 1) 3).mp
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, h']
    decide
  · right
    have h' : ((2 : ℕ) : ZMod 3) ^ f = 2 := by simpa using h
    apply (ZMod.natCast_eq_zero_iff (2 ^ f + 1) 3).mp
    rw [Nat.cast_add, Nat.cast_pow, h']
    decide

private theorem not_three_dvd_center_of_generic_label
    {lab : LargeEvenLabel} {X : Type}
    [Group X] [Finite X] (hX : commutator X = ⊤) (hlab : LargeEvenInLambda2 lab)
    (hgen : GGKacGenericCl lab 3) (hl : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  have hAll := largeEvenLabelAll_centerPrime_cl hlab hgen
  have hmain := hAll (fun R _ _ _ => Nonempty ((X ⧸ Subgroup.center X) ≃* R)) hl
  obtain ⟨R, _, I, F, hQe, hcentR⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨e⟩ := hQe
  let ψ : X →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hsurj : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : QuotientGroup.mk' (Subgroup.center X) x = 1 := by
      apply e.injective
      rw [map_one]
      exact hx
    exact (QuotientGroup.eq_one_iff x).1 hx1
  exact hcentR X ψ hsurj hker hX

private theorem exists_elemAbelian_three_cube_of_model {X G : Type} [Group X] [Finite X]
    [Group G] [Finite G] (hZ : ¬ 3 ∣ Nat.card (Subgroup.center X))
    (e : X ⧸ Subgroup.center X ≃* G) (hp : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) :
    ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
  obtain ⟨E, -, hEab, hEcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank
      (G := G) (p := 3) (H := ⊤) (k := 3) Nat.prime_three hp
  have hE'ab : CFSG.Open.IsElemAbelian 3 (E.map e.symm.toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hEab e.symm.toMonoidHom
  have hE'card : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hEcard]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQab, hQcard⟩ :=
    CFSG.RankThree.PartTwo.Sec21.exists_elemAbelian_of_quotient (Subgroup.center X) hZ hE'ab
  exact ⟨Q, hQab, by rw [hQcard, hE'card]⟩

theorem exists_elemAbelian_of_ggHasLabel_A5
    {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    (hl : GGHasLabel ⟨.A, 5, f⟩ (X ⧸ Subgroup.center X)) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) ∧
      ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
  have hlab : LargeEvenInLambda2 (⟨.A, 5, f⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2]; omega
  have hgen : GGKacGenericCl (⟨.A, 5, f⟩ : LargeEvenLabel) 3 := by
    refine ⟨Nat.prime_three, by norm_num, Or.inr h3, Or.inl rfl, ?_, ?_⟩
    · intro h
      exact not_three_dvd_two_pow_sub_one_of_add_one h3 h.2.2
    · intro h
      exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twA from h.1) (by decide)
  have hZ := not_three_dvd_center_of_generic_label hX hlab hgen hl
  refine ⟨hZ, ?_⟩
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨e⟩⟩ := statedClassicalModel_of_hasLabel_typeA hlab hl
  have : CharP K 2 := charP_two_of_card hKcard
  have hp := CFSG.SectionRank.ClassicalEven.psl_three_le_pRank_three (K := K) (n := 6) (by omega)
  exact exists_elemAbelian_three_cube_of_model hZ e hp

theorem exists_elemAbelian_of_ggHasLabel_twA5
    {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1)
    (hl : GGHasLabel ⟨.twA, 5, f⟩ (X ⧸ Subgroup.center X)) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) ∧
      ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
  have hlab : LargeEvenInLambda2 (⟨.twA, 5, f⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2]; omega
  have hgen : GGKacGenericCl (⟨.twA, 5, f⟩ : LargeEvenLabel) 3 := by
    refine ⟨Nat.prime_three, by norm_num, Or.inl h3, Or.inr (Or.inl rfl), ?_, ?_⟩
    · intro h
      exact absurd (show LargeEvenLieTag.twA = LargeEvenLieTag.A from h.1) (by decide)
    · intro h
      exact not_three_dvd_two_pow_add_one_of_sub_one h3 h.2.2
  have hZ := not_three_dvd_center_of_generic_label hX hlab hgen hl
  refine ⟨hZ, ?_⟩
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨e⟩⟩ := statedClassicalModel_of_hasLabel_typeTwA hlab hl
  have : CharP K 2 :=
    charP_two_of_card (m := 2 * f) (by rw [hKcard, ← pow_mul, Nat.mul_comm])
  have hp :=
    CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.psu_three_le_pRank_of_one_mod_three
      (K := K) (n := 6) (e := f) hKcard h3 (by omega)
  exact exists_elemAbelian_three_cube_of_model hZ e hp

theorem exists_elemAbelian_of_ggHasLabel_twD4
    {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {f : ℕ} (hf : 1 ≤ f)
    (hl : GGHasLabel ⟨.twD, 4, f⟩ (X ⧸ Subgroup.center X)) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) ∧
      ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
  have hlab : LargeEvenInLambda2 (⟨.twD, 4, f⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2]; omega
  have hgen : GGKacGenericCl (⟨.twD, 4, f⟩ : LargeEvenLabel) 3 := by
    refine ⟨Nat.prime_three, by norm_num, ggE6Opp_three_dvd_two_pow_sub_one_or_add_one f,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), ?_, ?_⟩
    · intro h
      exact absurd (show LargeEvenLieTag.twD = LargeEvenLieTag.A from h.1) (by decide)
    · intro h
      exact absurd (show LargeEvenLieTag.twD = LargeEvenLieTag.twA from h.1) (by decide)
  have hZ := not_three_dvd_center_of_generic_label hX hlab hgen hl
  refine ⟨hZ, ?_⟩
  obtain ⟨-, K, hK, hKfin, hKcard, b, c, -, ⟨e⟩⟩ :=
    statedClassicalModel_of_hasLabel_typeTwD (n := 4) (by omega) hl
  have : CharP K 2 := charP_two_of_card hKcard
  have hp :=
    CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three (K := K) (n := 4) (by omega) b c
  exact exists_elemAbelian_three_cube_of_model hZ e hp

end CFSG.StandardType

end
