module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec20.One

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

noncomputable abbrev sTwenty {G : Type} [Group G] (M N : Subgroup G) (c : G) (T : Subgroup G) :
    Subgroup G :=
  CFSG.Open.pCoreOf 2 ((kTwenty M c ⊔ T) ⊓ N)

@[expose] def Step208X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
      ∃ x ∈ L ⊓ Subgroup.normalizer (T : Set G), x ∉ M ∧ IsPGroup 2 (Subgroup.zpowers x) ∧
        x ∈ Subgroup.normalizer (sTwenty M N c T : Set G)

@[expose] def Step208MSPair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    (∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G)) →
    (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) →
      CFSG.Quasithin.IsMSPair (kTwenty M c ⊔ T) (sTwenty M N c T) ∧
        kTwenty M c ∈ CFSG.Quasithin.cComp (kTwenty M c ⊔ T) ∧
        ((kTwenty M c ⊔ T : Subgroup G) : Set G) =
          (kTwenty M c : Set G) * (sTwenty M N c T : Set G) ∧
        ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
          (α : ↥(kTwenty M c) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
          Fintype.card F = 2 ^ n ∧ CFSG.Quasithin.IsModO2Surj (kTwenty M c) α

@[expose] def Step208Cases : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M} →
    kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    ∀ i : ℕ, CFSG.Quasithin.IsC134Case i (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) →
      IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
        ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n

theorem item208One_of_AS (hAS : CFSG.Quasithin.ASInputs.AS_C_1_34) (h204 : Item204One)
    (h2051 : Step2051) (h2053 : Step2053) (h207 : Item207) (hMS : Step208MSPair)
    (hC : Step208Cases) : Item208One := by
  intro G _ _ A M L N c T hT hTN
  have h1 := h2051 G A M L N c T hT
  have h2 := rank3II_20_5_2_of h204 hT h1
  have h3 := h2053 G A M L N c T hT h2
  obtain ⟨hpair, hcomp, hmul, hα⟩ := hMS G A M L N c T hT hTN h2 h3
  obtain ⟨i, hi⟩ := hAS G (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) hpair hcomp hmul hα
  exact hC G A M L N c T hT hTN (h204 G A M L N c T hT) (h207 G A M L N c T hT.toCtx20 hTN) i hi

end CFSG.RankThree.PartTwo.Sec20
