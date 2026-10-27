module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V6
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpW
public import CFSG.Quasithin.H13.NQCatBNExc

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem fiveOverNorm614_of_lieOvergroup (hLO : LieOvergroupFact) {W : Type} [Group W] [Finite W]
    (hs : IsSimpleGroup W) (hbig : IsLieChar2Big W) : FiveOverNorm614 W := by
  intro S P hS hSP hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have hsolv : Group.IsSolvable P := by
    have : Fintype P := Fintype.ofFinite P
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := k)
      (b := 1) Nat.prime_two (by norm_num : Nat.Prime 5) (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard, hk]; ring)
  exact hLO W hs hbig S hS P hSP hsolv

theorem noFiveOver_of_not_dvd614 {W : Type} [Group W] [Finite W] (h : ¬ 5 ∣ Nat.card W) :
    FiveNorm.NoFiveOver W := by
  intro S P _ _ hcard
  apply h
  rw [← Subgroup.card_mul_index P, hcard, mul_assoc]
  exact dvd_mul_right 5 _

theorem sqtkCharTwoLie_cases614 {W : Type} [Group W] (h : Ch1.SQTKCharTwoLie W) :
    IsLieChar2Big W ∨ StatedClassicalModel W .PSL 3 2 1 ∨
      CFSG.Blueprint.ChevalleyExceptionalModel W .trialityD4 2 1 ∨
      CFSG.Blueprint.ReeTitsModel W .Tits 2 1 ∨ StatedClassicalModel W .PSL 4 2 1 ∨
      StatedClassicalModel W .PSL 5 2 1 := by
  rcases h with (⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨-, hf, h⟩ |
      ⟨-, hf, h⟩⟩ | h) | ⟨n, hn, h⟩
  · exact Or.inl ⟨f, hf, Or.inl h⟩
  · rcases Nat.lt_or_ge f 2 with h1 | h1
    · obtain rfl : f = 1 := by omega
      exact Or.inr (Or.inl h)
    · exact Or.inl ⟨f, h1, Or.inr (Or.inl h)⟩
  · exact Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inl h))⟩
  · exact Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
  · exact Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · rcases Nat.lt_or_ge f 2 with h1 | h1
    · obtain rfl : f = 1 := by omega
      exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl ⟨f, h1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
  · exact Or.inl ⟨f, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))⟩
  · exact Or.inl ⟨f, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem noFiveOver_psl32_614 {W : Type} [Group W] [Finite W]
    (h : StatedClassicalModel W .PSL 3 2 1) : FiveNorm.NoFiveOver W := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : W ≃* StatedProj (StatedSL 3 K) := e
  have e2 := e'.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 K
    (by simpa using hK))
  have e3 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  have hcard : Nat.card W = 168 := by
    rw [Nat.card_congr (e2.trans e3).toEquiv, Matrix.card_GL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  exact noFiveOver_of_not_dvd614 (by rw [hcard]; decide)

theorem noFiveOver_d42_614
    {W : Type} [Group W] [Finite W]
    (h : CFSG.Blueprint.ChevalleyExceptionalModel W .trialityD4 2 1) : FiveNorm.NoFiveOver W := by
  have h1 := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  norm_num [CFSG.Open.ordTrialityD4] at h1
  exact noFiveOver_of_not_dvd614 (by rw [h1]; decide)

theorem noFiveOver_psl42_614 {W : Type} [Group W] [Finite W]
    (h : StatedClassicalModel W .PSL 4 2 1) : FiveNorm.NoFiveOver W := by
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff W).mp
    (Or.inl ⟨by decide, h⟩)
  exact noFiveOver_of_mulEquiv614 e FiveNorm.noFiveOver_alt8

theorem kg614FiveChar2_of_lie
    (hLO : LieOvergroupFact)
    (hL52 : ∀ (W : Type) [Group W] [Finite W], StatedClassicalModel W .PSL 5 2 1 →
      FiveOverNorm614 W) : KG614FiveChar2 := by
  refine kg614FiveChar2_of (fun W _ _ hs hW => ?_) titsCenterFact614_holds
  rcases sqtkCharTwoLie_cases614 hW with h | h | h | h | h | h
  · exact Or.inl (fiveOverNorm614_of_lieOvergroup hLO hs h)
  · exact Or.inl (fiveOverNorm614_of_noFiveOver (noFiveOver_psl32_614 h))
  · exact Or.inl (fiveOverNorm614_of_noFiveOver (noFiveOver_d42_614 h))
  · exact Or.inr h
  · exact Or.inl (fiveOverNorm614_of_noFiveOver (noFiveOver_psl42_614 h))
  · exact Or.inl (hL52 W h)

theorem kg614FiveChar2_of_L52
    (hL52 : ∀ (W : Type) [Group W] [Finite W], StatedClassicalModel W .PSL 5 2 1 →
      FiveOverNorm614 W) : KG614FiveChar2 :=
  kg614FiveChar2_of_lie NQCat.lieOvergroupFact_holds hL52

end CFSG.Quasithin.H13
