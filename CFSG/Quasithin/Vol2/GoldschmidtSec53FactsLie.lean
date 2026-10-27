module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsExt
public import CFSG.Quasithin.Vol2.Ch5Sec3PerType
public import CFSG.Quasithin.Vol2.Ch5Sec3Facts533
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsTwo

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

@[expose] def LieModelFacts (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] (f : ℕ), IsSec53Param t m f → LieModel Y t m 2 f →
    Finite Y ∧ ∀ TY P₁ P₂ : Subgroup Y, IsYAmalgamPair TY P₁ P₂ →
      TransFacts P₁ P₂ ∧ P₁ ⊓ P₂ ≤ Subgroup.normalizer (TY : Set Y) ∧
        TY ≤ perfectCore P₁ ∧ TY ≤ perfectCore P₂

@[expose] def LieAutFacts (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (f : ℕ), IsSec53Param t m f → LieModel Y t m 2 f →
    ∀ A : LieAmalgamExt Y, A.P1 ⊓ A.P2 ≤ Subgroup.normalizer (A.TD : Set Y) →
      A.TD ≤ perfectCore A.P1 → Group.IsSolvable ↥(A.N1 ⊓ A.N2) ∧
        pCoreOf 2 (A.N1 ⊓ A.N2) ≤ perfectCore A.N1

@[expose] def LieFactsAt (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  LieModelFacts t m ∧ LieAutFacts t m

theorem stmt5_3_3_factsAt_of_lieFacts {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (ht : t ≠ .PSp) (hL : LieFactsAt t m) (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (h532 : Stmt5_3_2At t m) : Stmt5_3_3_factsAt t m := by
  obtain ⟨hM, hA⟩ := hL
  intro G _ _ T M L V H B D L₂ n f hyp hty hpar
  obtain ⟨Y, _, hY, TY, M₁, M₂, hpair, ⟨Φ⟩⟩ := hty.1
  obtain ⟨hfin, hT⟩ := hM Y f hpar hY
  obtain ⟨Y', _, hY', hE⟩ := h532 G T M L V H B D L₂ n f hyp hty hpar
  obtain ⟨E⟩ := isExtensionOfLieAmalgam_iff.mp hE
  obtain ⟨hfin', hT'⟩ := hM Y' f hpar hY'
  have : Finite Y' := hfin'
  obtain ⟨-, hP, hU1, -⟩ := hT' E.TD E.P1 E.P2 E.yam
  have hX := hA Y' f hpar hY' E.toLieAmalgamExt hP hU1
  have hii := facts_ii Φ h527 hyp hty (hT TY M₁ M₂ hpair).1
  exact ⟨facts_i_of_ext h531 hyp hty hpar E ⟨hX.1, hX.2⟩, hii.1, hii.2, fun h => absurd h ht⟩

end CFSG.Quasithin.H13.Sec53F
