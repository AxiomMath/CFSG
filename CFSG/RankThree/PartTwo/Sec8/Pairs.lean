module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

@[expose] def IsoSUThree (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = q ^ 2 ∧ Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 q K)

@[expose] noncomputable def imageModTheta [Finite G] (L X : Subgroup G) :
    Subgroup (L ⧸ aschbacherSolvableCore 3 L) :=
  (X.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))

@[expose] def IsGammaIndex [Finite G] (A Le : Subgroup G) (d : G) (m : ℕ) : Prop :=
  d ∈ A ∧ d ≠ 1 ∧ 1 ≤ m ∧
    ((∃ (k : ℕ) (hk : (TauCeti.LieTypeIndex.reeF4 k).Valid), 2 * k + 1 = 3 * m ∧
        Nonempty (Le ⧸ aschbacherSolvableCore 3 Le ≃*
          (TauCeti.CFSGIndex.lie ⟨.reeF4 k, hk⟩).Group) ∧
        IsoSUThree (imageModTheta Le
          (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)))) (2 ^ (3 * m))) ∨
      (((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
            q.p = 2 ∧ q.exponent = m ∧
              Nonempty (Le ⧸ aschbacherSolvableCore 3 Le ≃*
                (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
          (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 * m ∧
            Sec4.IsoGTwo (Le ⧸ aschbacherSolvableCore 3 Le) q) ∨
          Nonempty (Le ⧸ aschbacherSolvableCore 3 Le ≃* projSU 3 2 (3 * m)) ∨
          IsoSUThree (Le ⧸ aschbacherSolvableCore 3 Le) (2 ^ (3 * m)) ∨
          Nonempty (Le ⧸ aschbacherSolvableCore 3 Le ≃* projSp 2 (GaloisField 2 (3 * m)))) ∧
        Nonempty (imageModTheta Le
            (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
          projSL 2 (GaloisField 2 (3 * m)))))

@[expose] def gammaSet [Finite G] (A Le : Subgroup G) : Set G :=
  {d | ∃ m : ℕ, IsGammaIndex A Le d m}

@[expose] def pairOmega [Finite G] (A : Subgroup G) : Set (G × Subgroup G) :=
  {p | p.1 ∈ A ∧ p.1 ≠ 1 ∧ p.2 ∈ thetaComponentsAt 3 p.1 ∧
    (∃ x ∈ A, KFacts.InducesStdKind p.2 x .field ∨ KFacts.InducesStdKind p.2 x .graphField) ∧
    (∃ E₁ : Subgroup G, E₁ ≤ A ∧ Nat.card A = 3 * Nat.card E₁ ∧
      ∃ U ∈ invariantPiSubgroups p.2 E₁ (piOf 2), U ≠ ⊥) ∧
    (gammaSet A p.2).Nonempty}

@[expose] def PairRel [Finite G] (A : Subgroup G) (e : G) (Le : Subgroup G) (f : G)
    (Lf : Subgroup G) : Prop :=
  (e, Le) ∈ pairOmega A ∧ f ∈ gammaSet A Le ∧ Lf ∈ thetaComponentsAt 3 f ∧
    inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({f} : Set G)) ≤ Lf ∧
    Lf ≠ inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({f} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) Lf

end CFSG.RankThree.PartTwo.Sec8
