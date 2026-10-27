module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End7ProofKGamma
public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofDefs
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Concl2129Fix {G : Type} [Group G] (A : Subgroup G) (d : G) (Lf F : G → Subgroup G)
    (Y P D : Subgroup G) : Prop :=
  CFSG.Open.thompsonSubgroup P = D ∧ IsElemAbelian 3 D ∧ Nat.card D = 81 ∧
    Y ≤ Subgroup.normalizer (D : Set G) ∧
    ∀ b ∈ A, b ∉ Subgroup.zpowers d → F b ⊓ Lf b ≤ D

structure Config2119Fix (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G)
    (L : Subgroup G) (d : G) (U₀ : Subgroup G) (a : G) (X : Subgroup G)
    (Lf F : G → Subgroup G) (D : Subgroup G) : Prop where
  cfg : Config2119End G A E U c L d U₀ a X
  c23 : Concl2123 L X c d
  c24 : Concl2124 A L X d
  lf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)
  l34 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2))
  f : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)
  syl : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
    CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))
  q : IsQOf2127 A d F
  extra : IsExtra2127 (q2127Of A d F)
  c28 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)
  c29 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
      Concl2129Fix A d Lf F (y2128Of (Lf e) (F e) (q2127Of A d F)) P D

@[expose] def Item2119FinalFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G) (Lf F : G → Subgroup G) (D : Subgroup G),
    Config2119Fix G A E U c L d U₀ a X Lf F D → False

open Item2119End7Proof

end CFSG.RankThree.PartTwo.Sec21
