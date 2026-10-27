module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.C124Offender
public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.Background.C2Defs

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure Entry (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V) : Prop where
  charTwo : CharTwo X
  sqtk : SQTKGroup ↥X
  red : IsTwoReducedIn X V
  sylow : IsSylowTwoOf T X
  prod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  comp : L ∈ cComp X
  charTwoL : CharTwo L
  VL : ⁅V, L⁆ ≠ ⊥
  alt : IsAltQuotient L (oTwoZIn L) m
  QR : pCoreOf 2 X ≤ R
  RT : R ≤ T
  mcase : m = 5 ∨ m = 7 ∨ (m = 6 ∧ R ≤ L ⊔ (X ⊓ Subgroup.centralizer (V : Set G))) ∨
    (m = 6 ∧ Nat.card ↥(autOn R V) = 2)
  normal : X ≤ Subgroup.normalizer (L : Set G)
  QC : pCoreOf 2 X = R ⊓ Subgroup.centralizer (V : Set G)
  hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G)
  fstarX : quasithinGenFitting (autI hV X) = autI hV L
  stab : IsStableFF (autI hV X) (offenderImagesConjIn hV X R)
  ffJP_le : ffJP (offenderImagesConjIn hV X R) (autI hV X) ≤ ffJ (autI hV X)
  fstar : quasithinGenFitting (ffJP (offenderImagesConjIn hV X R) (autI hV X)) = autI hV L
  quasi : CFSG.IsQuasisimple ↥(autI hV L)
  o2 : pCoreOf 2 (autI hV L) = ⊥
  card : ∃ z : ℕ, Odd z ∧ Nat.card ↥(autI hV L) = Nat.card (alternatingGroup (Fin m)) * z
  case1i : B51Case1i (ffJP (offenderImagesConjIn hV X R) (autI hV X)) (autI hV L)

section Cases

variable {V : Subgroup G} (hV : IsElemAbelian 2 V) (L : Subgroup G) (m : ℕ)

@[expose] def CaseL2 : Prop :=
  m = 5 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    ∃ π : ↥(StatedSL 2 F) →* ↥(autI hV L),
      (FFModel.nat (StatedSL 2 F)).RealizesVia (autI hV L) (commV (autI hV L))
        (fixV (autI hV L) ⊓ commV (autI hV L)) π ∧ Function.Injective π

@[expose] def CaseAlt5 : Prop :=
  m = 5 ∧ ∃ π : ↥(alternatingGroup (Fin 5)) →* ↥(autI hV L),
    (FFModel.altDn 5).RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π ∧ Function.Injective π

@[expose] def CaseAlt6 : Prop :=
  m = 6 ∧ ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥(autI hV L),
    (FFModel.altDn 6).RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π ∧ Function.Injective π

@[expose] def CaseAlt7 : Prop :=
  m = 7 ∧ ∃ π : ↥(alternatingGroup (Fin 7)) →* ↥(autI hV L),
    (FFModel.altDn 7).RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π ∧ Function.Injective π

@[expose] def CaseHat6 : Prop :=
  m = 6 ∧ TripleA6Six (autI hV L) (commV (autI hV L)) (fixV (autI hV L) ⊓ commV (autI hV L)) ∧
    IsHat ↥(autI hV L) ↥(alternatingGroup (Fin 6))

@[expose] def CaseA7Four : Prop :=
  m = 7 ∧ A7Four (autI hV L) (commV (autI hV L)) (fixV (autI hV L) ⊓ commV (autI hV L)) ∧
    Nonempty (↥(autI hV L) ≃* ↥(alternatingGroup (Fin 7)))

end Cases

section Star

variable (X V L R : Subgroup G) (hV : IsElemAbelian 2 V) (Ys : Subgroup (MulAut (IntMod V hV)))

structure StarCommon : Prop where
  le_L : Ys ≤ autI hV L
  not_cent : ¬ fixV (autI hV (thompsonJ R)) ≤ fixV Ys
  gen : autI hV X = Ys ⊔ (autI hV X ⊓
    Subgroup.normalizer (autI hV (baum R) : Set (MulAut (IntMod V hV))))

structure StarL2 : Prop extends StarCommon X V L R hV Ys where
  sylow : IsSylowTwoOf (autI hV (baum R)) Ys
  sl2 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧ Nonempty (↥Ys ≃* SL(2, F))

structure StarZ3 : Prop extends StarCommon X V L R hV Ys where
  card : Nat.card ↥Ys = 3
  S_norm : autI hV (baum R) ≤ Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV)))

end Star

structure BlockData (V L : Subgroup G) : Prop where
  short : IsShort2 L
  ker : pCoreOf 2 L = L ⊓ Subgroup.centralizer (V : Set G)
  VL_le : ⁅V, L⁆ ≤ blockU L
  U_eq : blockU L = ⁅V, L⁆ ⊔ blockZ L

end CFSG.Quasithin.C124
