module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Res
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Good
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Inv
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_normalizer_le_of_involution_three (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree) (k : Sec7Core4 G)
    (hres : L34GFResidue k) (hp3 : k.p = 3) (h4 : 4 ≤ CFSG.Open.pRank k.p k.M) {Y : Subgroup G}
    (hY : Y ∈ calC k.M) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = q) (hrank : CFSG.Open.pRank q k.M ≤ 3)
    (hcase : F08.Thin8 Y ∨ ∃ n : ℕ, IsSU3 (Bar2 Y) n ∧ q ∣ 2 ^ n - 1) {B₁ : Subgroup G}
    (hB₁M : B₁ ≤ k.M) (hB₁ : IsElemAbelian k.p B₁) (hB₁c : Nat.card B₁ = k.p ^ 2)
    (hB₁X : B₁ ≤ centralizer (X : Set G))
    (hB₁Y : ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 k.M) {t : G}
    (ht : t ∈ Y ⊓ normalizer (X : Set G)) (ht2 : orderOf t = 2) :
    normalizer (X : Set G) ≤ k.M := by
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  have hYM : Y ≤ k.M := hY.1.le
  rcases uc22ine229_normalizer_le_or_card_le_two k hp3 hK3 hX1 (hXY.trans hYM) hB₁M hB₁ hB₁c
    hB₁X with h | hQ
  · exact h
  by_contra hnot
  have hB₁N : B₁ ≤ normalizer (X : Set G) :=
    hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hH := k.config_normalizer hX1 (hXY.trans hYM)
    (CFSG.SectionRank.le_pRank k.prime.one_lt (le_inf hB₁M hB₁N) hB₁ hB₁c) hnot
  have htC := uc22ine229_le_centralizer3 hB₁M hQ (by rwa [hp3] at hB₁) hB₁X hB₁Y ht
  have h75 := k.step75_of_stronglyEmbeddedThree hp3 hK3
  rcases (k.goodZ3_of_config hG3 hRee hp3 hH).2 with hC2 | hL
  · exact k.false_of_involution h75 hH hC2 (le_inf hB₁N hB₁M) hB₁ hB₁c ⟨ht.2, hYM ht.1⟩ ht2
      fun a ha => (Subgroup.mem_centralizer_iff.1 htC) a ha
  · exact hres hG3 hRee hK3 hp3 h4 Y hY X hXY q hq hq5 hXc hrank hcase hH B₁ hB₁M hB₁ hB₁c hB₁X
      hB₁Y t ht ht2 (fun b hb => ((Subgroup.mem_centralizer_iff.1 htC) b hb).symm) hL

end CFSG.LocalAnalysis.UniquenessCase.UC22
