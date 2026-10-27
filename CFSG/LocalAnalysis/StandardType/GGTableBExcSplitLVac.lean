module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMore
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreExc
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerBstar
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CorFourTwoOpen

namespace ExcSplitL


theorem mem_chevID_E6_of_pow {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : ¬ p ∣ f)
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenChevH TwistTag.E6.tag.cartan K false)))
    (hφ : φ ^ p = 1) :
    φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K
      (LargeEvenChevH TwistTag.E6.tag.cartan K false) := by
  have hQ := (RecipeFieldE6.e6QuotOn_isRoot K).of_eq
    (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  unfold RecipeFieldE6.E6QuotOn at hQ
  rw [← InndiagE6.diagHom_eq_markDiagUnit] at hQ
  have hcard : Nat.card (K ≃+* K) = f := by
    obtain ⟨-, -, -, -, hc, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two hf hK
    exact hc
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hcop : Nat.Coprime p (2 * f) := Nat.Coprime.mul_right
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpf)
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.chevH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K false →
      ∀ ψ : MulAut (LargeEvenCenterQuot H), ψ ^ p = 1 →
        ψ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K H from
    key _ (largeEvenChevH_eq _ K false) φ hφ
  intro H hH
  subst hH
  obtain ⟨Ψ, hker, -⟩ := hQ
  intro ψ hψ
  have h1 : Ψ ψ ^ p = 1 := by rw [← map_pow, hψ, map_one]
  have hall : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have h2 : Ψ ψ ^ (2 * f) = 1 := by
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst, Prod.fst_one, pow_mul', ← hcard, pow_card_eq_one', one_pow]
    · rw [Prod.pow_snd, Prod.snd_one, pow_mul]
      have h3 : (Ψ ψ).2 ^ 2 = 1 := hall _
      rw [h3, one_pow]
  have h3 : orderOf (Ψ ψ) = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  exact RecipeFieldE6.mem_chevID_iff_isInnDiagOn.mpr ((hker ψ).mp (orderOf_eq_one_iff.mp h3))

end ExcSplitL

open ExcSplitL

@[expose] def GGExcLVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ≠ 2 ∧ (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6) ∧
    ¬ p ∣ lab.n

@[expose] def GGExcLSplitVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .E6 ∧ p ≠ 3) ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧
    p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.n

theorem GGExcLSplitVacLabel.vac {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGExcLSplitVacLabel p lab) : GGExcLVacLabel p lab := by
  obtain ⟨htag, hpn, hpn'⟩ := h
  refine ⟨ne_two_of_dvd_two_pow_sub_one hlab.1 hpn, ?_, hpn'⟩
  rcases htag with ⟨h, -⟩ | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

section Labels


theorem largeEvenLabelAll_pow_mem_excLVac {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGExcLVacLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hp2, htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hpn hn
  rcases htag with rfl | rfl | rfl | rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_and (fun K _ _ hK => mem_chevID_E6_of_pow hn K hK hp hp2 hpn) hQ
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_and (fun K _ _ hK φ hφ => Subgroup.subset_closure
      (Or.inl (IOneRest.mem_range_conj_recipe_of_pow (τ := .E7) (Or.inl rfl) hn hK hp hpn hφ)))
      hQ
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_and (fun K _ _ hK φ hφ => Subgroup.subset_closure
      (Or.inl (IOneRest.mem_range_conj_recipe_of_pow (τ := .E8) (Or.inr rfl) hn hK hp hpn hφ)))
      hQ
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeChevalley_and (fun K _ _ hK φ hφ => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    exact Subgroup.subset_closure
      (Or.inl (IOneRest.mem_range_conj_recipeF4_of_pow hn hK hp hp2 hpn hφ))
  · exact TwE6Delta.labelAll (lab := ⟨.twE6, l, n⟩) rfl fun K _ _ hK φ hφ =>
      TwE6Per.mem_recipeI_of_pow_eq_one hn hK hp hp2 hpn hφ

theorem ggBstarInnerDiagLInputOn_excLVac (T : ℕ → LargeEvenLabel → Prop) :
    GGBstarInnerDiagLInputOn fun p lab => T p lab ∧ GGExcLVacLabel p lab :=
  ggBstarInnerDiagLInputOn_of_pow ggLNoncyclicInput_holds fun _ _ hp hlab h =>
    largeEvenLabelAll_pow_mem_excLVac hp hlab h.2

theorem ggBstarInnerDiagLInputOn_excLSplitVac : GGBstarInnerDiagLInputOn GGExcLSplitVacLabel :=
  ggBstarInnerDiagLInputOn_of_pow ggLNoncyclicInput_holds fun _ _ hp hlab h =>
    largeEvenLabelAll_pow_mem_excLVac hp hlab (h.vac hlab)

theorem ggTableBIrredInputOn_excLSplitVac : GGTableBIrredInputOn GGExcLSplitVacLabel :=
  (ggTableBIrredInputOn_excSplit.or ggTableBIrredInputOn_F4).mono fun _ _ h => by
    obtain ⟨htag, hpn, -⟩ := h
    rcases htag with h6 | h7 | h8 | h4
    · exact Or.inl ⟨Or.inl h6, hpn⟩
    · exact Or.inl ⟨Or.inr (Or.inl h7), hpn⟩
    · exact Or.inl ⟨Or.inr (Or.inr h8), hpn⟩
    · exact Or.inr ⟨h4, hpn⟩

theorem ggTableBCxInputOn_excLSplitVac : GGTableBCxInputOn GGExcLSplitVacLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_excLSplitVac
    ggTableBIrredInputOn_excLSplitVac

theorem ggTableBModuleInputOn_excLSplitVac : GGTableBModuleInputOn GGExcLSplitVacLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_excLSplitVac
    ggTableBIrredInputOn_excLSplitVac

theorem ggTableBActionInputOn_excLSplitVac : GGTableBActionInputOn GGExcLSplitVacLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_excLSplitVac
    ggTableBIrredInputOn_excLSplitVac

theorem ggBstarInnerDiagLInputOn_of_not_excLVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInnerDiagLInputOn fun p lab => S p lab ∧ ¬ GGExcLVacLabel p lab) :
    GGBstarInnerDiagLInputOn S := by
  have h' := (ggBstarInnerDiagLInputOn_excLVac S).or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · by_cases h1 : GGExcLVacLabel p lab
    · exact Or.inl ⟨hlab, h1⟩
    · exact Or.inr ⟨hlab, h1⟩
  · rcases hlab with h1 | h1
    · exact h1.1
    · exact h1.1

theorem ggTableBCxInputOn_of_not_excLSplitVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGExcLSplitVacLabel p lab) :
    GGTableBCxInputOn S :=
  (ggTableBCxInputOn_excLSplitVac.or h).mono fun p lab hS => by
    by_cases h3 : GGExcLSplitVacLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩

theorem ggTableBModuleInputOn_of_not_excLSplitVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGExcLSplitVacLabel p lab) :
    GGTableBModuleInputOn S :=
  (ggTableBModuleInputOn_excLSplitVac.or h).mono fun p lab hS => by
    by_cases h3 : GGExcLSplitVacLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩

theorem ggTableBActionInputOn_of_not_excLSplitVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGExcLSplitVacLabel p lab) :
    GGTableBActionInputOn S :=
  (ggTableBActionInputOn_excLSplitVac.or h).mono fun p lab hS => by
    by_cases h3 : GGExcLSplitVacLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩

end Labels

end CFSG.StandardType

end
