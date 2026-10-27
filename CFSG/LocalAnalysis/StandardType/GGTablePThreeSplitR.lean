module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeDefs

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

abbrev proj {X : Type} [Group X] {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) :
    X →* R :=
  (θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' _)

structure RDatum {R : Type} [Group R] (A : Subgroup (MulAut R)) (δ : MulAut R)
    (J : Subgroup R) : Prop where
  elem : IsElemAbelian 3 A
  mem : δ ∈ A
  ne_one : δ ≠ 1
  comp : IsComponentOf J (ggAutFixedSubgroup δ)
  uniq : ∀ Q : Subgroup R, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J
  norm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J
  ker : ∀ a ∈ A, (∀ j ∈ J, a j = j) → a ∈ Subgroup.zpowers δ
  card : 3 ^ 3 ≤ Nat.card A

end CFSG.StandardType.TablePThreeKG

end
