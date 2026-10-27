module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch3E213MDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 Ch3E213M

namespace E217R4

structure Setting4 {G : Type} [Group G] [Finite G] (H T M V K : Subgroup G) : Prop
    extends Setting H T M V K where
  V16 : Nat.card V = 2 ^ 4
  q32 : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hyp.elem H)
  res : twoResidual M ≤ Subgroup.centralizer (V : Set G)

@[expose] def R4PkgOdd4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting4 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case1 H T M K →
    ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → False

end E217R4

end CFSG.Quasithin
