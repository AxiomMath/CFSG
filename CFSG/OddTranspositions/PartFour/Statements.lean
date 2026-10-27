module

public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.Sporadic.Co2Cert.Order

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

@[expose] def HypothesisE {G : Type} [Group G] [Finite G] {D : Set G} (hC : HypothesisC D) :
    Prop :=
  (∃ s ∈ imageClass hC, ∃ m f : ℕ, 2 ≤ m ∧ 2 ≤ f ∧
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.IsSymplecticTransvection
          (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s ∨
        CFSG.LocalAnalysis.WeakClosure81.SevenK.IsUnitaryTransvection
          (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s ∨
        CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection
          (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s)) ∨
    (∃ n : ℕ, 4 ≤ n ∧ ∃ b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5),
      (∀ x y, b x y = b y x) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      CFSG.Open.fischerCentralQuotientModel (imageClass hC)
        (Subgroup.closure
          (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) ∨
    (∃ s ∈ imageClass hC, ∃ f m : ℕ, 5 ≤ m ∧
      CFSG.LocalAnalysis.WeakClosure81.IsWreathTransposition
        (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) f m s) ∨
    (∃ f : ℕ, CFSG.Quasithin.IsSz f
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))

@[expose] def Theorem5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    (¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n)) →
    HypothesisE hC →
    ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) →
    MeetsSq D

end CFSG.OddTranspositions.PartFour
