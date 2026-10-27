module

public import CFSG.LocalAnalysis.StandardType.GGKD2Spec1615
public import CFSG.Open.StatedDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open S2MathAs3_1615

noncomputable section

@[expose] def QuotientInner {R : Type} [Group R] (C : Subgroup R) (beta : MulAut R) : Prop :=
  ∃ z : ↥C ⧸ Subgroup.center ↥C,
    ∀ c c' : ↥C, beta (c : R) = (c' : R) →
      (c' : ↥C ⧸ Subgroup.center ↥C) =
        z * (c : ↥C ⧸ Subgroup.center ↥C) * z⁻¹

@[expose] def ClassicalModelAction (H : Type) [Group H] : Prop :=
  ∀ x : H, x ≠ 1 → x ^ 3 = 1 →
    ∀ C : Subgroup H, CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({x} : Set H)) →
      GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥C ⧸ Subgroup.center ↥C) →
      ∀ y : H, x * y = y * x → (∀ c ∈ C, MulAut.conj y c ∈ C) →
        QuotientInner C (MulAut.conj y)

@[expose] def RawActionAt (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ phi ∈ I, phi ≠ 1 → phi ^ 3 = 1 →
    ∀ C : Subgroup R, CFSG.Assembly.IsComponentOf C (ggFixSub phi) →
      GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥C ⧸ Subgroup.center ↥C) →
      ∀ beta ∈ I, beta * phi = phi * beta → (∀ c ∈ C, beta c ∈ C) →
        QuotientInner C beta

@[expose] def NoSetupAt (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
      GGRankOneSetup I ψ 3 e J 3 a → False

@[expose] def NoSetupTag (t : LargeEvenLieTag) : Prop :=
  ∀ lab : LargeEvenLabel, lab.tag = t → LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (fun R _ I _ => NoSetupAt R I)

@[expose] def ActionTag (t : LargeEvenLieTag) : Prop :=
  ∀ lab : LargeEvenLabel, lab.tag = t → LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (fun R _ I _ => RawActionAt R I)

@[expose] def NoSetupTriD4 : Prop := NoSetupTag .triD4
@[expose] def NoSetupG2 : Prop := NoSetupTag .G2

@[expose] def SpRawRealization (lab : LargeEvenLabel) (R : Type) [Group R]
    (I : Set (MulAut R)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ lab.n ∧
    ∃ theta : R ≃* ↥(StatedSp lab.rank K),
      ∀ beta ∈ I, ∃ y : ↥(StatedSp lab.rank K), ∀ r : R,
        theta (beta r) = y * theta r * y⁻¹

@[expose] def OrthRawRealization (lab : LargeEvenLabel) (R : Type) [Group R]
    (I : Set (MulAut R)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ lab.n ∧
    ∃ (Phi : QuadraticForm K (Fin (2 * lab.rank) → K)),
      (QuadraticMap.polarBilin Phi).Nondegenerate ∧
      ∃ theta : R ≃* ↥(StatedOmega ⇑Phi),
        ∀ beta ∈ I, ∃ y : ↥(StatedOmega ⇑Phi), ∀ r : R,
          theta (beta r) = y * theta r * y⁻¹

open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def ReeWitness (f : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  Odd f ∧ 3 ≤ f ∧
    ∀ phi ∈ I, phi ≠ 1 → phi ^ 3 = 1 →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
        Nat.card K = 2 ^ (2 * f) ∧
        ∃ (_ : UnitaryFieldData 2 f K),
          Nonempty (↥(ggFixSub phi) ≃* ↥(unitarySU 2 f K 3))

@[expose] def SU3NoA1Eight (f : ℕ) : Prop :=
  3 ≤ f →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (_ : UnitaryFieldData 2 f K)
      (C : Subgroup ↥(unitarySU 2 f K 3)),
      CFSG.Assembly.IsComponentOf C ⊤ →
        ¬ GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥C ⧸ Subgroup.center ↥C)

end

end S2MathAs3_1619Final

end
