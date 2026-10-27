module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Item2119End7ProofFix
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2128Tools
public import CFSG.RankThree.PartTwo.Sec21.Item2119End4ProofGL2

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open Item2119EndProof Item2119End3Proof Item2119End4Proof

@[expose] def Item2129Fix : Prop :=
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
          ∃ D : Subgroup G, ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
            Concl2129Fix A d Lf F (y2128Of (Lf e) (F e) (q2127Of A d F)) P D

section Items

theorem item2119End_of_fix (h211 : Item211) (h214 : Item214) (h215 : Item215) (h2123 : Item2123)
    (h2124 : Item2124) (h2125 : Item2125) (h2126 : Item2126) (h2127 : Item2127)
    (h2127Q : Item2127Q) (h2127X : Item2127QExtra) (h2128 : Item2128) (h2129 : Item2129Fix)
    (hFin : Item2119FinalFix) : Item2119End := by
  intro G _ _ A E U c L hcfg d hd hd1 hdT hnorm
  obtain ⟨U₀, a, X, hE⟩ := exists_config2119End h211 h214 h215 hcfg hd hd1 hdT hnorm
  have h23 := h2123 G A E U c L d U₀ a X hE
  have h24 := h2124 G A E U c L d U₀ a X hE h23
  obtain ⟨Lf, hLf⟩ := exists_lf (h2125 G A E U c L d U₀ a X hE h23 h24)
  have h26 := h2126 G A E U c L d U₀ a X hE h23 h24 Lf hLf
  have h27 := h2127 G A E U c L d U₀ a X hE h23 h24 Lf hLf h26
  obtain ⟨F, hF, hQ⟩ := h2127Q G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 h27
  have hQX := h2127X G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF hQ
  have h27F : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)) :=
    fun e he hed => h27 e he hed (F e) (hF e he hed)
  have h28 := h2128 G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27F hQ hQX
  obtain ⟨D, h29⟩ := h2129 G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27F hQ hQX h28
  exact hFin G A E U c L d U₀ a X Lf F D
    ⟨hE, h23, h24, hLf, h26, hF, h27F, hQ, hQX, h28, h29⟩

end Items

end CFSG.RankThree.PartTwo.Sec21
