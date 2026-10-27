module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofCommon

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item2119EndShare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d →
            CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
            Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P) →
          ∃ e₀ ∈ A, e₀ ∉ Subgroup.zpowers d ∧ ∃ e₁ ∈ A,
            e₁ ∉ Subgroup.zpowers e₀ ⊔ Subgroup.zpowers d ∧ ∃ P₀ P₁ : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P₀ (y2128Of (Lf e₀) (F e₀) (q2127Of A d F)) ∧
            CFSG.ABGLocalTools.IsSylowOf 3 P₁ (y2128Of (Lf e₁) (F e₁) (q2127Of A d F)) ∧
            CFSG.Open.thompsonSubgroup P₀ = CFSG.Open.thompsonSubgroup P₁ ∧
            ∃ y : G, y ^ 3 = 1 ∧
              y ∈ Subgroup.normalizer (CFSG.Open.thompsonSubgroup P₀ : Set G) ∧
              y ∉ CFSG.Open.thompsonSubgroup P₀ ∧
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers d) ∧
              y * e₀ * y⁻¹ * e₀⁻¹ ∈
                Subgroup.centralizer (CFSG.Open.thompsonSubgroup P₀ : Set G)

@[expose] def Item2119EndShared : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d →
            CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
            Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P) →
          ∀ e₀ ∈ A, e₀ ∉ Subgroup.zpowers d → ∀ e₁ ∈ A,
            e₁ ∉ Subgroup.zpowers e₀ ⊔ Subgroup.zpowers d → ∀ P₀ P₁ : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P₀ (y2128Of (Lf e₀) (F e₀) (q2127Of A d F)) →
            CFSG.ABGLocalTools.IsSylowOf 3 P₁ (y2128Of (Lf e₁) (F e₁) (q2127Of A d F)) →
            CFSG.Open.thompsonSubgroup P₀ = CFSG.Open.thompsonSubgroup P₁ →
            ∀ y : G, y ^ 3 = 1 →
              y ∈ Subgroup.normalizer (CFSG.Open.thompsonSubgroup P₀ : Set G) →
              y ∉ CFSG.Open.thompsonSubgroup P₀ →
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers d) →
              y * e₀ * y⁻¹ * e₀⁻¹ ∈
                Subgroup.centralizer (CFSG.Open.thompsonSubgroup P₀ : Set G) →
              False

@[expose] def Item2119EndSharedNA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d →
            CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
            Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P) →
          ∀ e₀ ∈ A, e₀ ∉ Subgroup.zpowers d → ∀ e₁ ∈ A,
            e₁ ∉ Subgroup.zpowers e₀ ⊔ Subgroup.zpowers d → ∀ P₀ P₁ : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P₀ (y2128Of (Lf e₀) (F e₀) (q2127Of A d F)) →
            CFSG.ABGLocalTools.IsSylowOf 3 P₁ (y2128Of (Lf e₁) (F e₁) (q2127Of A d F)) →
            CFSG.Open.thompsonSubgroup P₀ = CFSG.Open.thompsonSubgroup P₁ →
            ∀ y : G, y ^ 3 = 1 →
              y ∈ Subgroup.normalizer (CFSG.Open.thompsonSubgroup P₀ : Set G) →
              y ∉ Subgroup.centralizer (CFSG.Open.thompsonSubgroup P₀ : Set G) →
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers d) →
              y * e₀ * y⁻¹ * e₀⁻¹ ∈
                Subgroup.centralizer (CFSG.Open.thompsonSubgroup P₀ : Set G) →
              False

@[expose] def Item2119EndSharedA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d →
            CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
            Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P) →
          ∀ e₀ ∈ A, e₀ ∉ Subgroup.zpowers d → ∀ e₁ ∈ A,
            e₁ ∉ Subgroup.zpowers e₀ ⊔ Subgroup.zpowers d → ∀ P₀ P₁ : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P₀ (y2128Of (Lf e₀) (F e₀) (q2127Of A d F)) →
            CFSG.ABGLocalTools.IsSylowOf 3 P₁ (y2128Of (Lf e₁) (F e₁) (q2127Of A d F)) →
            CFSG.Open.thompsonSubgroup P₀ = CFSG.Open.thompsonSubgroup P₁ →
            ∀ y : G, y ^ 3 = 1 →
              y ∈ Subgroup.centralizer (CFSG.Open.thompsonSubgroup P₀ : Set G) →
              y ∉ CFSG.Open.thompsonSubgroup P₀ → False

theorem item2119EndShared_of_branches (hNA : Item2119EndSharedNA) (hA : Item2119EndSharedA) :
    Item2119EndShared := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL e₀ he₀ he₀d e₁
    he₁ he₁d P₀ P₁ hP₀ hP₁ hJ y hy3 hyN hyD hyc hye
  by_cases hyC : y ∈ Subgroup.centralizer (CFSG.Open.thompsonSubgroup P₀ : Set G)
  · exact hA G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL e₀ he₀ he₀d e₁ he₁
      he₁d P₀ P₁ hP₀ hP₁ hJ y hy3 hyC hyD
  · exact hNA G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL e₀ he₀ he₀d e₁
      he₁ he₁d P₀ P₁ hP₀ hP₁ hJ y hy3 hyN hyC hyc hye

theorem item2119EndLoc_of_share (h1 : Item2119EndShare) (h2 : Item2119EndShared) :
    Item2119EndLoc := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL
  obtain ⟨e₀, he₀, he₀d, e₁, he₁, he₁d, P₀, P₁, hP₀, hP₁, hJ, y, hy3, hyN, hyD, hyc, hye⟩ :=
    h1 G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL
  exact h2 G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL e₀ he₀ he₀d e₁ he₁
    he₁d P₀ P₁ hP₀ hP₁ hJ y hy3 hyN hyD hyc hye

end CFSG.RankThree.PartTwo.Sec21
