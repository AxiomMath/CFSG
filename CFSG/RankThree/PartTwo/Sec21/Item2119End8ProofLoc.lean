module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End7ProofAssembly
import CFSG.RankThree.PartTwo.Sec21.Item2119End7ProofFinal

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Concl2129Loc {G : Type} [Group G] (Le F Y P : Subgroup G) : Prop :=
  IsElemAbelian 3 (CFSG.Open.thompsonSubgroup P) ∧
    Nat.card (CFSG.Open.thompsonSubgroup P) = 81 ∧
    Y ≤ Subgroup.normalizer (CFSG.Open.thompsonSubgroup P : Set G) ∧
    F ⊓ Le ≤ CFSG.Open.thompsonSubgroup P

@[expose] def Item2129Loc : Prop :=
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
          ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
            Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P

@[expose] def Item2129Same : Prop :=
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
          ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ e' ∈ A, e' ∉ Subgroup.zpowers d →
            ∀ P P' : Subgroup G,
              CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
              CFSG.ABGLocalTools.IsSylowOf 3 P' (y2128Of (Lf e') (F e') (q2127Of A d F)) →
                CFSG.Open.thompsonSubgroup P = CFSG.Open.thompsonSubgroup P'

theorem item2129Fix_of_loc (hLoc : Item2129Loc) (hSame : Item2129Same) : Item2129Fix := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := hLoc G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28
  have hS := hSame G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL
  obtain ⟨haA, had⟩ := Item2119End7Proof.mem_a_not_mem hE
  obtain ⟨P₀, hP₀⟩ :=
    CFSG.ABGLocalTools.exists_isSylowOf 3 (y2128Of (Lf a) (F a) (q2127Of A d F))
  refine ⟨CFSG.Open.thompsonSubgroup P₀, fun e he hed P hP => ?_⟩
  have hJ : CFSG.Open.thompsonSubgroup P = CFSG.Open.thompsonSubgroup P₀ :=
    hS e he hed a haA had P P₀ hP hP₀
  obtain ⟨h1, h2, h3, -⟩ := hL e he hed P hP
  rw [hJ] at h1 h2 h3
  refine ⟨hJ, h1, h2, h3, fun b hb hbd => ?_⟩
  obtain ⟨Pb, hPb⟩ :=
    CFSG.ABGLocalTools.exists_isSylowOf 3 (y2128Of (Lf b) (F b) (q2127Of A d F))
  rw [← hS b hb hbd a haA had Pb P₀ hPb hP₀]
  exact (hL b hb hbd Pb hPb).2.2.2

end CFSG.RankThree.PartTwo.Sec21
