module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeMinimal
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreClaim
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeNGeOneSyl
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSyl
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Defs
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCard
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIn
public import CFSG.LocalAnalysis.WeakClosure81.NineThreePSym
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeDischarge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}


theorem thm93Syl_of_core
    (h79 : ∀ (A K S X : Subgroup G) (p : ℕ) (g x : G), Nine3CoreMin V T A K S X p →
      Nine3Thm79 V T A K S X p g x) :
    Thm93Syl V T := by
  intro hTG hN h9 A hA hAT hsyl
  by_cases h1 : normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)
  · exact Or.inl h1
  · right
    rcases Set.eq_empty_or_nonempty (calPMTA V T A) with hne | ⟨K, hK⟩
    · exact hne
    · exfalso
      obtain ⟨K₀, hK₀, -, hmin⟩ := exists_nine3Minimal_le hK
      obtain ⟨p, S, X, hseed⟩ := nine3_extract h9 hA hAT hsyl hK₀
      obtain ⟨Y, hY, hYmin⟩ := hseed.exists_minimal
      have hcore : Nine3Core V T A (S ⊔ Y) S Y p :=
        ⟨hseed.h9, hseed.conj, hseed.leT, hseed.syl, hseed.ne, hseed.leS, hseed.tau,
          hseed.hyp hY hYmin h1,
          hseed.card (sevenSixThreeAbelian_holds V) hY hYmin h1⟩
      have hmem : (S ⊔ Y) ∈ calPMTA V T A :=
        nine3ReduceInP_holds V T A K₀ S X p hseed Y hY hYmin hcore
      have hSle : S ≤ K₀ := hseed.two.sylowTwo.le
      have hYle : Y ≤ K₀ := hY.1.trans hseed.two.sylowP.le
      have heq : S ⊔ Y = K₀ := Nine3Minimal.eq_of_mem_le hmin hmem (sup_le hSle hYle)
      have hcoreK : Nine3Core V T A K₀ S Y p := by
        rw [← heq]
        exact hcore
      have hcoreMin : Nine3CoreMin V T A K₀ S Y p := ⟨hcoreK, hmin⟩
      obtain ⟨g, x, hc, hc'⟩ := hcoreK.exists_choice_sym (sevenSixThreeAbelian_holds V)
      have hI := hcoreK.nine3_IFacts
      have hn : Nine3NGeOne V S := nine3NGeOne_of_isSylowIn_top hcoreK hTG hN
      have h35 := hc.card_nineDelta_eq_three_or_five hI hn
      have hc'' : Nine3Choice V T A K₀ S Y p g⁻¹⁻¹ x := by
        rw [inv_inv]
        exact hc
      have hg := nine3_coreClaim hc hc' hI h35
      have hg' := nine3_coreClaim hc' hc'' hI h35
      have hH := hc.nine_twelve_H_le_normalizer hg
      have hH' := hc'.nine_twelve_H_le_normalizer hg'
      exact h79 A K₀ S Y p g x hcoreMin hc hc' hI h35 (nine_H0_le_normalizer_sym hH hH')

end CFSG.LocalAnalysis.WeakClosure81
