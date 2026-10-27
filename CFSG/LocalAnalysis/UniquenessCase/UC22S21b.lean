module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise

section Section21b

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_5 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, c.B ≤ normalizer (L : Set G)

@[expose] def S21_6 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, (∃ s : TauCeti.SporadicName, IsSpor (Bar2 L) s) →
    IsJ1 (Bar2 L) ∧
      (⁅CFSG.Quasithin.opResidual 3 c.B, L⁆ ≤ CFSG.Open.pCoreOf 2 L ∨ 7 ∈ piSet c.B)

@[expose] def S21_13 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, IsAlt (BarInf L) n → n = 5

@[expose] def S21_18 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch,
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M → Hinf D.M = Hinf (oTwoEOf D.M)

@[expose] def Hyp2120 (D : Data G) {Ch : Choice2011 G} (c : Ctx21 D Ch) : Prop :=
  ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M ∧
  (∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal ∧
    ¬ ∃ n : ℕ, Odd n ∧ (IsSp4 (Bar2 L) n ∨ IsSU3 (Bar2 L) n)) ∧
  (∀ p ∈ D.sig, ∃ P : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M)) ∧
      P ≤ normalizer (c.B : Set G)) ∧
  (∀ p ∈ D.sig, 1 < CFSG.Open.pRank p (barPreimage D.M (centE D.M)) → ¬ InvertedIn D.M c.B)

@[expose] def S21_23 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ p ∈ D.sig, ∀ P : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M)) →
    IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))) →
      IsCyclic ↥⁅centE D.M, centE D.M⁆ ∧
      CFSG.perfectResidual (Bar2 D.M) = CFSG.layer (Bar2 D.M) ∧
      barImage D.M P ≤ centE D.M ⊓ commutator (Bar2 D.M) ∧ (barImage D.M P).Normal ∧ IsCyclic ↥P

end Section21b

end CFSG.LocalAnalysis.UniquenessCase.UC22
