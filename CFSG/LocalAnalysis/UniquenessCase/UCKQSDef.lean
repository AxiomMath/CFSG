module

public import CFSG.LocalAnalysis.UniquenessCase.UCKQSDispatch
public import CFSG.RankThree.PartOne.CTP.StrongPCharP
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.DefG2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Order

theorem pcaLieDef_PSL : PCALieDefAt .PSL := by
  intro K _ _ hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hrank⟩ := CFSG.SectionRank.classical_model_rank (by omega)
    (hmodel.statedClassicalModel (by decide))
  have hord := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K .PSL n p f
    hadm hmodel).2.2
  by_cases h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)
  · exact PCentralAbelianAt.of_four_le_pRank hp h4
  · apply PCentralAbelianAt.of_factorization_le (by omega)
    rw [hord]
    rcases hrank with ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]
      omega
    · simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]
      omega
    · exact absurd h h4
    · cases h
    · cases h
    · exact absurd h h4

theorem pcaLieDef_PSU : PCALieDefAt .PSU := by
  intro K _ _ hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hrank⟩ := CFSG.SectionRank.classical_model_rank (by omega)
    (hmodel.statedClassicalModel (by decide))
  have hord := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K .PSU n p f
    hadm hmodel).2.2
  by_cases h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)
  · exact PCentralAbelianAt.of_four_le_pRank hp h4
  · apply PCentralAbelianAt.of_factorization_le (by omega)
    rw [hord]
    rcases hrank with ⟨h, -⟩ | ⟨-, ⟨rfl, h⟩ | h⟩ | ⟨h, -⟩ | h
    · cases h
    · simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]
      omega
    · exact absurd h h4
    · cases h
    · exact absurd h h4

end Order

theorem pcaLieDef_of_orthogonal (t : StatedLieTag) (ht : t ∈ classicalTags)
    (h1 : t ≠ .PSL) (h2 : t ≠ .PSU) (h3 : t ≠ .PSp) : PCALieDefAt t := by
  intro K _ _ hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  subst hpℓ
  obtain ⟨-, -, hrank⟩ := CFSG.SectionRank.classical_model_rank (by omega)
    (hmodel.statedClassicalModel ht)
  apply PCentralAbelianAt.of_four_le_pRank hp (H := ⊤)
  rcases hrank with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact h

theorem pcaLieDef_POmegaOdd : PCALieDefAt .POmegaOdd :=
  pcaLieDef_of_orthogonal .POmegaOdd (by decide) (by decide) (by decide) (by decide)

theorem pcaLieDef_POmegaPlus : PCALieDefAt .POmegaPlus :=
  pcaLieDef_of_orthogonal .POmegaPlus (by decide) (by decide) (by decide) (by decide)

theorem pcaLieDef_POmegaMinus : PCALieDefAt .POmegaMinus :=
  pcaLieDef_of_orthogonal .POmegaMinus (by decide) (by decide) (by decide) (by decide)

section Psp4

theorem pcaPsp4_holds (K : Type) [Group K] [Finite K] (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hmodel : LieModel K .PSp 2 p 1) : PCentralAbelianAt K p := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hmodel.statedClassicalModel_of_ne_zero (by norm_num)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hcard, pow_one])
  haveI : Finite (StatedProj (StatedSp 2 F)) := Finite.of_equiv K e.toEquiv
  exact PCentralAbelianAt.of_mulEquiv e (PCentralAbelianAt.of_hasNoncommPair
    (CFSG.RankThree.PartOne.StrongP.noncentralPair_sp4 (K := F) (by omega)).hasNoncommPair)

end Psp4

theorem pcaLieDef_PSp : PCALieDefAt .PSp := by
  intro K _ _ hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  subst hpℓ
  obtain ⟨-, hf, hrank⟩ := CFSG.SectionRank.classical_model_rank (by omega)
    (hmodel.statedClassicalModel (by decide))
  by_cases h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)
  · exact PCentralAbelianAt.of_four_le_pRank hp h4
  · rcases hrank with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨rfl, h⟩ | h⟩ | h
    · cases h
    · cases h
    · have hf1 : f = 1 := by omega
      subst hf1
      exact pcaPsp4_holds K p hp h5 hmodel
    · exact absurd h h4
    · exact absurd h h4

theorem pcaLieDef_twistedB2 : PCALieDefAt .twistedB2 := by
  intro K _ _ _ _ n ℓ f hadm _ p _ h5 hpℓ _
  obtain ⟨_, _, _, h2, _⟩ := hadm
  omega

theorem pcaLieDef_twistedG2 : PCALieDefAt .twistedG2 := by
  intro K _ _ _ _ n ℓ f hadm _ p _ h5 hpℓ _
  obtain ⟨_, _, _, h3, _⟩ := hadm
  omega

theorem pcaLieDef_twistedF4 : PCALieDefAt .twistedF4 := by
  intro K _ _ _ _ n ℓ f hadm _ p _ h5 hpℓ _
  obtain ⟨_, _, _, h2, _⟩ := hadm
  omega

theorem pcaLieDef_Tits : PCALieDefAt .Tits := by
  intro K _ _ _ _ n ℓ f hadm _ p _ h5 hpℓ _
  obtain ⟨_, _, _, h2, _⟩ := hadm
  omega

section Rank

open CFSG.SectionRank

theorem pcaLieDef_F4 : PCALieDefAt .F4 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inl rfl) hm
  exact PCentralAbelianAt.of_four_le_pRank hp (H := ⊤) (by omega)

theorem pcaLieDef_E6 : PCALieDefAt .E6 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inl rfl)) hm
  exact PCentralAbelianAt.of_four_le_pRank hp (H := ⊤) (by omega)

theorem pcaLieDef_E7 : PCALieDefAt .E7 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inl rfl))) hm
  exact PCentralAbelianAt.of_four_le_pRank hp (H := ⊤) (by omega)

theorem pcaLieDef_E8 : PCALieDefAt .E8 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inr rfl))) hm
  exact PCentralAbelianAt.of_four_le_pRank hp (H := ⊤) (by omega)

theorem pcaLieDef_twistedE6 : PCALieDefAt .twistedE6 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact PCentralAbelianAt.of_four_le_pRank hp (four_le_pRank_of_twistedE6Model hf hm)

theorem pcaLieDef_trialityD4 : PCALieDefAt .trialityD4 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact PCentralAbelianAt.of_four_le_pRank hp (four_le_pRank_of_trialityD4Model hf hm)

end Rank

section G2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.G2Radical

theorem qsG2_pca_adjoint (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (hF : Nat.card F = p) [Finite (adjointGroup .G2 F)] : PCentralAbelianAt (adjointGroup .G2 F) p := by
  have hpow := radG2_pow F (Fact.out : p.Prime) (by omega) hF
  refine PCentralAbelianAt.of_exponent (U := radG2 F) ?_ hpow ?_
  · intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hpow g g.2)⟩
  · have := radG2_card F
    rw [hF] at this
    exact this

theorem pcaG2p_holds (K : Type) [Group K] [Finite K] (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hmodel : LieModel K .G2 0 p 1) : PCentralAbelianAt K p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel.chevalleyExceptionalModel (by decide)
  have hZ : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  let e2 : AdjointQuotient .G2 F ≃* ↥(adjointGroup .G2 F) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e3 : K ≃* ↥(adjointGroup .G2 F) := e.trans e2
  haveI : Finite ↥(adjointGroup .G2 F) := Finite.of_equiv K e3.toEquiv
  exact PCentralAbelianAt.of_mulEquiv e3 (qsG2_pca_adjoint F h5 (by simpa using hF))

theorem pcaLieDef_G2 : PCALieDefAt .G2 := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h3 := CFSG.SectionRank.three_mul_le_pRank_of_G2Model hm
  by_cases hf1 : f = 1
  · subst hf1
    obtain ⟨_, _, hn0, _⟩ := hadm
    subst hn0
    exact pcaG2p_holds K p hp h5 hmodel
  · exact PCentralAbelianAt.of_four_le_pRank hp (H := ⊤) (by omega)

end G2

section Assembly

theorem pcaLieDef_holds : ∀ t, PCALieDefAt t := fun t => by
  cases t
  · exact pcaLieDef_PSL
  · exact pcaLieDef_PSU
  · exact pcaLieDef_PSp
  · exact pcaLieDef_POmegaOdd
  · exact pcaLieDef_POmegaPlus
  · exact pcaLieDef_POmegaMinus
  · exact pcaLieDef_G2
  · exact pcaLieDef_F4
  · exact pcaLieDef_E6
  · exact pcaLieDef_E7
  · exact pcaLieDef_E8
  · exact pcaLieDef_twistedE6
  · exact pcaLieDef_trialityD4
  · exact pcaLieDef_twistedB2
  · exact pcaLieDef_twistedG2
  · exact pcaLieDef_twistedF4
  · exact pcaLieDef_Tits

end Assembly

end CFSG.LocalAnalysis.UniquenessCase.UCK
