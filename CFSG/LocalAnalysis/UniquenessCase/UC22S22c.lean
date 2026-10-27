module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (calCGS)
open scoped Pointwise

section Section22c

variable {G : Type} [Group G] [Finite G]

structure Ctx22c (D : Data G) (Ch : Choice2011 G) extends Ctx22 D Ch where
  hCle : centralizer (D.Z : Set G) ≤ D.M

omit [Finite G] in
@[expose] def omegaZJ22 (X : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup (fun K _ => CFSG.elemThompsonCenterTorsion K 2) X

@[expose] def proofE (D : Data G) : Subgroup G := omegaZJ22 D.T

@[expose] def proofS (D : Data G) : Subgroup G := D.T ⊓ centralizer (proofE D : Set G)

@[expose] def proofN (D : Data G) : Subgroup G := jOf D.M

@[expose] def modI (D : Data G) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) : Submodule (ZMod 2) Umod :=
  commOn ρ (mbarImage D.M D.U (proofN D)) ⊤

@[expose] def modCI (D : Data G) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) : Submodule (ZMod 2) Umod :=
  modI D ρ ⊓ fixSub ρ (mbarImage D.M D.U (proofN D))

@[expose] def IsL2Ev (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (X ≃* ↥(StatedSL 2 F))

@[expose] def IsS5 (X : Type) [Group X] : Prop := Nonempty (X ≃* Equiv.Perm (Fin 5))

@[expose] def FactorShape22 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, IsL2Ev X n) ∨ IsL3 X 1 ∨ IsS5 X

@[expose] def NbarSplit (D : Data G) {m : ℕ} (Nb : Fin m → Subgroup (MBar D.M D.U)) : Prop :=
  IsInternalDirect (mbarImage D.M D.U (proofN D)) Nb ∧ ∀ i, FactorShape22 ↥(Nb i)

@[expose] def preN (D : Data G) (Y : Subgroup (MBar D.M D.U)) : Subgroup G :=
  proofN D ⊓ (Y.comap (QuotientGroup.mk' (kerAct D.M D.U).normalCore)).map D.M.subtype

@[expose] def Cl22_5_1 (D : Data G) {m : ℕ} (Nb : Fin m → Subgroup (MBar D.M D.U)) : Prop :=
  ∀ i, ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2

@[expose] def S22_3_1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch,
    mbarImage D.M D.U (proofN D) ≠ ⊥ ∧ ¬ calCGS (proofS D) ≤ D.M

@[expose] def S22_3_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch,
    ∃ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)), NbarSplit D Nb

@[expose] def S22_3_3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
    NbarSplit D Nb →
    ∀ (Umod : Type) [AddCommGroup Umod] [Module (ZMod 2) Umod] [Finite Umod]
      (e : ↥D.U ≃* Multiplicative Umod)
      (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod),
      ConjModule D.M D.U e ρ →
      IsDirectSumMod (modI D ρ) (modCI D ρ) (fun i => commOn ρ (Nb i) (modI D ρ)) ∧
      ∀ i, Shape148 ρ (Nb i) (commOn ρ (Nb i) (modI D ρ)) (modCI D ρ)

@[expose] def S22_4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, D.sig = D.sig1

@[expose] def S22_5_1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
    NbarSplit D Nb → Cl22_5_1 D Nb

@[expose] def S22_5_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ p ∈ D.sig, p ∈ piSet (proofN D)

@[expose] def S22_7 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, normalizer (proofS D : Set G) ≤ D.M

end Section22c

end CFSG.LocalAnalysis.UniquenessCase.UC22
