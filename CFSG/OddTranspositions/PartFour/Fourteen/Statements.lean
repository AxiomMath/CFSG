module

public import CFSG.OddTranspositions.ClassificationStatement
public import CFSG.OddTranspositions.O4Minus5Pair
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.Sporadic.Co2Cert.Order

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

@[expose] def AscList (X : Type) [Group X] (E : Set X) : Prop :=
  (∀ d ∈ E, ∀ e ∈ E, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) ∨
    (∃ s ∈ E, ∃ m f : ℕ, 2 ≤ m ∧ 2 ≤ f ∧
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.IsSymplecticTransvection X m f s ∨
        CFSG.LocalAnalysis.WeakClosure81.SevenK.IsUnitaryTransvection X m f s ∨
        CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s)) ∨
    (∃ n : ℕ, 4 ≤ n ∧ ∃ b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5),
      (∀ x y, b x y = b y x) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      CFSG.Open.fischerCentralQuotientModel E
        (Subgroup.closure
          (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) ∨
    (∃ f n : ℕ, 2 ≤ f ∧ Nonempty (X ≃* L2Wreath f n)) ∨
    (∃ f : ℕ, CFSG.Quasithin.IsSz f X) ∨
    CFSG.BenderSuzuki.IsBenderGroup X ∨
    QZ.IsO4Minus5Pair X E

@[expose] def AscMainTheorem : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    derivedSeries G 1 = derivedSeries G 2 → AscList G D

@[expose] def HypEShape (X : Type) [Group X] (E : Set X) : Prop :=
  (∃ s ∈ E, ∃ m f : ℕ, 2 ≤ m ∧ 2 ≤ f ∧
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.IsSymplecticTransvection X m f s ∨
        CFSG.LocalAnalysis.WeakClosure81.SevenK.IsUnitaryTransvection X m f s ∨
        CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s)) ∨
    (∃ n : ℕ, 4 ≤ n ∧ ∃ b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5),
      (∀ x y, b x y = b y x) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      CFSG.Open.fischerCentralQuotientModel E
        (Subgroup.closure
          (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) ∨
    (∃ s ∈ E, ∃ f m : ℕ, 5 ≤ m ∧ CFSG.LocalAnalysis.WeakClosure81.IsWreathTransposition X f m s) ∨
    (∃ f : ℕ, CFSG.Quasithin.IsSz f X)

@[expose] def AscListTable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    commutator G = layer G → IsPGroup 2 (G ⧸ layer G) →
    (¬ ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) →
    ¬ CFSG.RankThree.GF2n.Tim79a.NoSqE1 D → AscList G D →
    ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)

end CFSG.OddTranspositions.PartFour
