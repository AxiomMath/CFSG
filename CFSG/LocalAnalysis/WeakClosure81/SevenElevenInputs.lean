module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.Timmesfeld.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def transvectionCenterSet (m : ℕ) (F : Type) [Field F] (a : Fin m → F) :
    Set (StatedProj (StatedSL m F)) :=
  {x | ∃ g : ↥(StatedSL m F), (QuotientGroup.mk g : StatedProj (StatedSL m F)) = x ∧
    ∃ f : Fin m → F, f ⬝ᵥ a = 0 ∧
      ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 + Matrix.vecMulVec a f}

@[expose] def IsTransvectionCenterGroup (X : Type) [Group X] (m n : ℕ) (S : Subgroup X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    ∃ e : (X ⧸ Subgroup.center X) ≃* StatedProj (StatedSL m F), ∃ a : Fin m → F, a ≠ 0 ∧
      ∀ y : X ⧸ Subgroup.center X,
        (∃ x ∈ S, (QuotientGroup.mk x : X ⧸ Subgroup.center X) = y) ↔
          e y ∈ transvectionCenterSet m F a

@[expose] def IsSymplecticRootGroup (X : Type) [Group X] (m n : ℕ) (W : Subgroup X) : Prop :=
  Nat.card W = 2 ^ n ∧ ∃ k : ℕ, m = 2 * k ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = 2 ^ n ∧ ∃ e : (X ⧸ Subgroup.center X) ≃* ↥(StatedSp k F),
      ∀ w ∈ W, w ≠ 1 → IsSymplecticTransvectionIn k (e (QuotientGroup.mk w))

@[expose] def IsUnitaryRootGroup (X : Type) [Group X] (m n : ℕ) (W : Subgroup X) : Prop :=
  Nat.card W = 2 ^ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    ∃ e : (X ⧸ Subgroup.center X) ≃* StatedProj (StatedSU m (2 ^ n) F),
      ∀ w ∈ W, w ≠ 1 → IsUnitaryTransvectionIn m n (e (QuotientGroup.mk w))

@[expose] def IsSuzukiRootGroup (X : Type) [Group X] (W : Subgroup X) : Prop :=
  ∃ T : Sylow 2 X, ∀ x : X, x ∈ W ↔ x ∈ (T : Subgroup X) ∧ ∀ y ∈ (T : Subgroup X), x * y = y * x

@[expose] def IsRootGroupShape (X : Type) [Group X] (n : ℕ) (W : Subgroup X) : Prop :=
  (∃ m : ℕ, IsSpGp (X ⧸ Subgroup.center X) m n ∧ IsSymplecticRootGroup X m n W) ∨
    (∃ m : ℕ, IsPSUGp (X ⧸ Subgroup.center X) m n ∧ IsUnitaryRootGroup X m n W) ∨
    (IsSzGp (X ⧸ Subgroup.center X) n ∧ IsSuzukiRootGroup X W)

@[expose] def SevenElevenASixShape (X : Type) [Group X] (S : Subgroup X) : Prop :=
  Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) ∧ Nat.card S = 4 ∧
    ∃ T : Sylow 2 X, S ≤ T ∧ IsWeaklyClosedIn S T

@[expose] def SevenElevenLinearShape (X : Type) [Group X] (S : Subgroup X) : Prop :=
  ∃ m n : ℕ, 3 ≤ m ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL m 2 n ∧
    IsTransvectionCenterGroup X m n S ∧ ∃ T : Sylow 2 X, S ≤ T ∧ IsWeaklyClosedIn S T

@[expose] def SevenElevenAlt (X : Type) [Group X] (S : Subgroup X) : Prop :=
  ((∃ n : ℕ, IsRootGroupShape X n S) ∧
      CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp (Group.conjugatesOfSet ((S : Set X) \ {1}))) ∨
    SevenElevenLinearShape X S ∨
    (Nat.card (Subgroup.center X) = 3 ∧ SevenElevenASixShape X S) ∨
    (Nat.card S = 2 ∧ ∃ m n : ℕ,
      (IsSpGp (X ⧸ Subgroup.center X) m n ∧ ∀ s ∈ S, s ≠ 1 → IsSymplecticTransvection X m n s) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m n ∧ ∀ s ∈ S, s ≠ 1 → IsUnitaryTransvection X m n s) ∨
      IsOrthGp (X ⧸ Subgroup.center X) m n ∨ IsL2WrSymGp (X ⧸ Subgroup.center X) n m) ∨
    (Nat.card S = 2 ∧ ∃ n : ℕ, IsSymGp (X ⧸ fusionOddCore X) n) ∨
    (Nat.card S = 2 ∧ IsThreeCoverOrth6Minus X)

@[expose] def TimmesfeldTIRootInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X),
    IsElemAbelian 2 S → 2 < Nat.card S → CFSG.CGT.Timmesfeld75.IsTI S →
    Subgroup.normalClosure (S : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    CFSG.Timmesfeld.IsRootInvolutionSet (Group.conjugatesOfSet ((S : Set X) \ {1})) →
    (∀ g : X, IsPGroup 2 ↥(S ⊔ conjSubgroup S g) →
      ∀ a ∈ S, ∀ b ∈ conjSubgroup S g, a * b = b * a) →
    (∀ s ∈ S, ∀ t ∈ S, s ≠ 1 → t ≠ 1 → IsConj s t) ∧
      (SevenElevenASixShape X S ∨ SevenElevenLinearShape X S ∨
        ∃ n : ℕ, 1 < n ∧ ∃ W : Subgroup X, S ≤ W ∧ IsElemAbelian 2 W ∧ Nat.card W = 2 ^ n ∧
          (∃ g : X, IsL2OrSz ↥(W ⊔ conjSubgroup W g) n) ∧ IsRootGroupShape X n W ∧
          CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp
            (Group.conjugatesOfSet ((W : Set X) \ {1})))

@[expose] def SevenElevenASixInput (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H E : Subgroup G, Hyp711 V H E →
    ∀ (X : Type) [Group X] (φ : ↥(kSub V H E) →* X),
      IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ →
      Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) →
      Nat.card (barSub (kSub V H E) φ V) = 4 →
      Nat.card (Subgroup.center X) = 3

@[expose] def OddTranspositionCoreInputSC : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    ¬ fusionOddCore X ≤ Subgroup.center X →
    (∃ n : ℕ, IsSymGp (X ⧸ fusionOddCore X) n) ∨
      (∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ Lh ∧
        ¬ Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ pCoreOf 2 Lh ∧
        (⨆ (y : X ⧸ fusionOddCore X)
            (_ : conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y ≤ Lh),
            conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y) = Lh ∧
        HasQuotShape Lh (pCoreOf 2 Lh : Set (X ⧸ fusionOddCore X)) (fun Y _ => IsSymGp Y 3) ∧
        4 ≤ Set.ncard {W : Subgroup (X ⧸ fusionOddCore X) | ∃ x ∈ pCoreOf 2 Lh,
            W = conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) x}) ∨
      ∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        ∃ hsLh : QuotientGroup.mk' (fusionOddCore X) s ∈ Lh,
        Subgroup.normalClosure ({⟨_, hsLh⟩} : Set ↥Lh) = ⊤ ∧
        ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥Lh ⧸ fusionZStar ↥Lh) n

@[expose] def SevenSevenOddCentral (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H E : Subgroup G, Hyp711 V H E →
    ∀ (X : Type) [Group X] (φ : ↥(kSub V H E) →* X),
      IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ →
      Nat.card (barSub (kSub V H E) φ V) = 2 →
      ∀ (Y : Type) [Group Y] (ι : Y →* X), Function.Injective ι →
        barSub (kSub V H E) φ V ≤ ι.range →
        (∀ y : Y, ι y ∈ barSub (kSub V H E) φ V → y ≠ 1 →
          Subgroup.normalClosure ({y} : Set Y) = ⊤) →
        ∀ n : ℕ, 1 < n → IsL2OrSz (Y ⧸ fusionZStar Y) n →
          fusionOddCore Y ≤ Subgroup.center Y

@[expose] def SevenSevenTwoInput (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H E : Subgroup G, Hyp711 V H E →
    ∀ (X : Type) [Group X] (φ : ↥(kSub V H E) →* X),
      IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ →
      Nat.card (barSub (kSub V H E) φ V) = 2 →
      fusionOddCore X ≤ Subgroup.center X →
      ∀ n : ℕ, 1 < n → ¬ CFSG.Quasithin.IsSz n (X ⧸ fusionZStar X)

end CFSG.LocalAnalysis.WeakClosure81
