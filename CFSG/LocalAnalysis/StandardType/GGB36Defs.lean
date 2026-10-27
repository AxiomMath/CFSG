module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList
public import CFSG.LocalAnalysis.StandardType.GGTPNI1Gen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGB36JLabel (labL labJ : LargeEvenLabel) : Prop :=
  let n := labL.n
  (labL.tag = .E6 ∧ 3 ∣ 2 ^ n - 1 ∧
      (labJ = ⟨.D, 5, n⟩ ∨ labJ = ⟨.A, 5, n⟩ ∨ labJ = ⟨.D, 4, n⟩ ∨ labJ = ⟨.triD4, 0, n⟩ ∨
        labJ = ⟨.A, 2, 3 * n⟩)) ∨
    (labL.tag = .E6 ∧ 3 ∣ 2 ^ n + 1 ∧
      (labJ = ⟨.A, 5, n⟩ ∨ labJ = ⟨.twD, 4, n⟩ ∨ (n = 1 ∧ labJ = ⟨.A, 2, 2⟩))) ∨
    (labL.tag = .twE6 ∧ 3 ∣ 2 ^ n - 1 ∧ (labJ = ⟨.twA, 5, n⟩ ∨ labJ = ⟨.twD, 4, n⟩)) ∨
    (labL.tag = .twE6 ∧ 3 ∣ 2 ^ n + 1 ∧
      (labJ = ⟨.twD, 5, n⟩ ∨ labJ = ⟨.twA, 5, n⟩ ∨ labJ = ⟨.D, 4, n⟩ ∨
        labJ = ⟨.triD4, 0, n⟩ ∨ labJ = ⟨.twA, 2, 3 * n⟩ ∨ (n = 1 ∧ labJ = ⟨.twA, 4, 1⟩)))

@[expose] def GGB36StepOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L → p = 3 →
    ∀ labL : LargeEvenLabel, LargeEvenInLambda2 labL → (labL.tag = .E6 ∨ labL.tag = .twE6) →
      GGHasLabel labL (L ⧸ Subgroup.center L) →
      ∃ labJ' : LargeEvenLabel, GGB36JLabel labL labJ' ∧ LargeEvenInLambda2 labJ' ∧
        GGHasLabel labJ' (J ⧸ Subgroup.center J)

@[expose] def GGPairE6Three (p : ℕ) (labL labJ : LargeEvenLabel) : Prop :=
  p = 3 ∧ (labL.tag = .E6 ∨ labL.tag = .twE6) ∧
    (labJ = ⟨.D, 5, labL.n⟩ ∨ labJ = ⟨.twD, 5, labL.n⟩ ∨ labJ = ⟨.A, 5, labL.n⟩ ∨
      labJ = ⟨.twA, 5, labL.n⟩ ∨ labJ = ⟨.triD4, 0, labL.n⟩ ∨ labJ = ⟨.twD, 4, labL.n⟩ ∨
      labJ = ⟨.A, 2, 3 * labL.n⟩ ∨ labJ = ⟨.twA, 2, 3 * labL.n⟩)

@[expose] def GGE6ThreeI1Rank : Prop := GGI1PairRankOn GGPairE6Three

@[expose] def GGB36KernelFail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K → p = 3 → Nat.card Bs = 3 ^ 6 →
    ∀ labL labJ : LargeEvenLabel, LargeEvenInLambda2 labL → LargeEvenInLambda2 labJ →
      (labL.tag = .E6 ∨ labL.tag = .twE6) → GGHasLabel labL (L ⧸ Subgroup.center L) →
      GGHasLabel labJ (J ⧸ Subgroup.center J) →
      (labJ = ⟨.A, 2, 2⟩ ∨ labJ = ⟨.twA, 4, 1⟩ ∨ labJ = ⟨.D, 4, labL.n⟩) →
      ∀ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
        (hx : x ∈ Subgroup.normalizer (K : Set G)),
        GGTPNKernel (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) ∨
          (labJ = ⟨.D, 4, labL.n⟩ ∧ ∃ labK : LargeEvenLabel,
            (labK.tag = .E6 ∨ labK.tag = .twE6) ∧ GGHasLabel labK (K ⧸ Subgroup.center K))

@[expose] def GGRegimeB36D4E6 : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ labX => p = 3 ∧ labJ.tag = .D ∧ labJ.rank = 4 ∧
    (labX.tag = .E6 ∨ labX.tag = .twE6)

@[expose] def GGE78LocalRankThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (lab : LargeEvenLabel), LargeEvenInLambda2 lab →
    (lab.tag = .E7 ∨ lab.tag = .E8) → GGHasLabel lab (X ⧸ Subgroup.center X) →
    commutator X = ⊤ → 6 + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤
      LargeEvenTwoLocalRank 3 X

@[expose] def GGRegimeB36J : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ _ => p = 3 ∧ n = 3 ^ 6 ∧ ∃ labL : LargeEvenLabel,
    (labL.tag = .E6 ∨ labL.tag = .twE6) ∧ GGB36JLabel labL labJ

@[expose] def GGRegimeB36JExc : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ labX => GGRegimeB36J p n labJ labX ∧
    (labX.tag = .F4 ∨ labX.tag = .E6 ∨ labX.tag = .twE6 ∨ labX.tag = .E7 ∨ labX.tag = .E8)

end CFSG.StandardType

end
