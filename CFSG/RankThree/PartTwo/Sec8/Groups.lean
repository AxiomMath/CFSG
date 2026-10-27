module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.LieType.Ree.FixedSubgroupData
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

variable {G : Type} [Group G]

@[expose] noncomputable def barCentralizer [Finite G] (X L : Subgroup G) :
    Subgroup (L ⧸ aschbacherSolvableCore 3 L) :=
  FixedPoints.subgroup (Sec4.autThetaQuot X L) (L ⧸ aschbacherSolvableCore 3 L)

@[expose] def IsoTrialityD4 (X : Type) [Group X] (m : ℕ) : Prop :=
  ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    q.p = 2 ∧ q.exponent = m ∧ Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def IsoGTwoEven (X : Type) [Group X] (m : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧
    Nonempty (X ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 K)

@[expose] def IsoReeF4 (X : Type) [Group X] (m : ℕ) : Prop :=
  ∃ (k : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
    (_ : CharP K CFSG.LieType.Ree.ReeTag.F4.prime), 2 * k + 1 = m ∧ Nat.card K = 2 ^ m ∧
      Nonempty (X ≃* CFSG.LieType.Ree.ReeTag.F4.reeGamma K k)

@[expose] def IsoPGUThree (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧
    Nonempty (X ≃* projImage (Sec4.glPi false 3 q K))

@[expose] def IsZ3LThreePi (X : Type) [Group X] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
    ((p ^ e % 3 = 1 ∧ Nonempty (X ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField p e))) ∨
      (p ^ e % 3 = 2 ∧ Nonempty (X ≃* Multiplicative (ZMod 3) × projSU 3 p e)))

@[expose] def IsZ3PGLThreePi (X : Type) [Group X] : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧
    Sec4.ModThree π (p ^ f) ∧
      Nonempty (X ≃* Multiplicative (ZMod 3) × projImage (Sec4.glPi π 3 (p ^ f) K))

end CFSG.RankThree.PartTwo.Sec8
