module

public import CFSG.Quasithin.EmptyFaithful.S153DIn16
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Vocabulary

variable {G : Type} [Group G] [Finite G]

abbrev VL153 (T V₁ Yp L : Subgroup G) : Subgroup G :=
  omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp))

noncomputable abbrev LStar153 (T V₁ Yp L : Subgroup G) : Subgroup (MulAut ↥(VL153 T V₁ Yp L)) :=
  autOn L (VL153 T V₁ Yp L)

@[expose] def IsLin2Block (I L : Subgroup G) : Prop :=
  IsBlock2 I L ∧ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n

@[expose] def IsLin2Quot (L : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 < n ∧ Fintype.card F = 2 ^ n ∧
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)

@[expose] def IsSL3Quot (L : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 < n ∧ Fintype.card F = 2 ^ n ∧
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 F))

@[expose] def IsSp4Quot (L : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSp 2 F))

@[expose] def IsLnTwoQuot (L : Subgroup G) (n : ℕ) : Prop :=
  Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL n (ZMod 2)))

@[expose] def Concl15317 (T V₁ Yp I L : Subgroup G) : Prop :=
  (CFSG.Open.pRank 3 L = 1 ∧
    ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Even n ∧ Fintype.card F = 2 ^ n ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      IsLnTwoQuot L 3)) ∨
  (CFSG.Open.pRank 3 L = 2 ∧ Yp ≤ thetaOf I ∧ thetaOf I = L) ∨
  (CFSG.Open.pRank 3 L = 2 ∧
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Even n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (↥(LStar153 T V₁ Yp L) ≃* ↥(StatedSL 3 F)))

end Vocabulary

structure Ctx15316 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop extends Ctx15313L T Mc M V₁ V₂ Yp I L t where
  c16 : Concl15316 T M V₁ Yp I L

@[expose] def Input15317 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L

@[expose] def Input15318 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L → ¬ IsLin2Block I L

@[expose] def Input15319 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L → ¬ IsLin2Block I L →
      ¬ IsLin2Quot L

@[expose] def Input15320 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L → ¬ IsLin2Block I L →
      ¬ IsLin2Quot L → ¬ IsSL3Quot L ∧ ¬ IsSp4Quot L

@[expose] def Input15321 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L → ¬ IsLin2Block I L →
      ¬ IsLin2Quot L → ¬ IsSL3Quot L → ¬ IsSp4Quot L →
        ¬ IsAltBlockType L 6 ∧ ¬ IsG2Block L ∧ ¬ IsHatA6Block L ∧ ¬ IsAltBlockType L 7 ∧
          ¬ IsExcA7Block L

@[expose] def Input15323 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → ¬ IsLnTwoQuot L 3

@[expose] def Input15324 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L →
      ¬ IsLnTwoQuot L 4 ∧ ¬ IsLnTwoQuot L 5

end CFSG.Quasithin
