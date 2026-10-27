module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FReduction
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FLinearField
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FSymplecticField
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FOrthogonalMinusField
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FExceptionalField
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FTwistedExceptionalField
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FUnitaryPreimage

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_14R4FFieldRest (D : Data G) (Ch : Choice2011 G) : Prop :=
  ∀ (_ : UC6S846.SigmaStd D) (_ : F07.R76Sig D) (_ : F07.R74Card D),
    H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ l f : ℕ, 4 ≤ l → PartTwo.S17.CHasLieRank (BarInf L) l f → 3 ≤ c.n →
    c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    (Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f)) →
    (∀ r : ℕ, r.Prime → 5 ≤ r → r ∣ 2 ^ c.n - 1 → r ∣ f) →
    ∀ (b : G), b ∈ c.B0 → ∀ (hbL : b ∈ normalizer (L : Set G)) (r : ℕ),
      r.Prime → 5 ≤ r → orderOf b = r → r ∣ 2 ^ c.n - 1 → r ∣ f →
      inducedBarInfAutHom L ⟨b, hbL⟩ ∉
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range →
      (¬ ∃ m : ℕ, 8 ≤ m ∧ LieModel (BarInf L) .PSU m 2 f ∧ Odd c.n) →
      (¬ ∃ m : ℕ, 8 ≤ m ∧ LieModel (BarInf L) .PSL m 2 f) →
      (¬ ∃ m : ℕ, 5 ≤ m ∧ LieModel (BarInf L) .PSL m 2 f ∧ (Even f ∨ 2 ≤ f / r)) →
      (¬ ∃ n : ℕ, 4 ≤ n ∧ LieModel (BarInf L) .PSp n 2 f) →
      (¬ ∃ n : ℕ, 4 ≤ n ∧ LieModel (BarInf L) .POmegaPlus n 2 f) →
      (¬ ∃ n : ℕ, 5 ≤ n ∧ LieModel (BarInf L) .POmegaMinus n 2 f) →
      ¬ LieModel (BarInf L) .F4 0 2 f → ¬ LieModel (BarInf L) .E6 0 2 f →
      ¬ LieModel (BarInf L) .E7 0 2 f →
      ¬ LieModel (BarInf L) .E8 0 2 f →
      ¬ LieModel (BarInf L) .twistedE6 0 2 f →
      (¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) ∧
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
        ∃ X : Subgroup (BarInf L), IsPGroup p ↥X ∧ ¬ IsCyclic ↥X ∧
          ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
      (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
        ¬ q ∣ Nat.card (CFSG.solvableRadical ↥L) ∧
        ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
          ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a))


theorem s21_14R4FFieldData_of_rest (hGA : GriessAllModelsStatement)
    {D : Data G} {Ch : Choice2011 G} (hRest : S21_14R4FFieldRest D Ch) :
    S21_14R4FFieldData D Ch := by
  intro hSg h76 h74 hH c L hL hX hpow l f hl hlr hn3 hBL hfaith hcase hall b hbB hbL r hr hr5 hbr hrn hrf hin
  by_cases hu : ∃ m : ℕ, 8 ≤ m ∧ LieModel (BarInf L) .PSU m 2 f ∧ Odd c.n
  · obtain ⟨m, hm, hmodel, hodd⟩ := hu
    exact (uc22s2114r4f_false_of_psu_odd hGA hSg h74 hH c hL hm hmodel hbB hbL
      hr hr5 hbr hrn hodd hin).elim
  · by_cases hlin : ∃ m : ℕ, 8 ≤ m ∧ LieModel (BarInf L) .PSL m 2 f
    · obtain ⟨m, hm, hmodel⟩ := hlin
      exact uc22s2114r4f_fieldDataBody_psl_of_ctx hSg hH c hL hm hmodel hbL
        hr hr5 hbr hrn hin
    · by_cases hlow : ∃ m : ℕ,
          5 ≤ m ∧ LieModel (BarInf L) .PSL m 2 f ∧ (Even f ∨ 2 ≤ f / r)
      · obtain ⟨m, hm, hmodel, hslice⟩ := hlow
        exact uc22s2114r4f_fieldDataBody_psl_of_ctx_of_even_or_fixed_gt_two
          hSg hH c hL hm hmodel hbL hr hr5 hbr hrn hcase hslice hin
      · by_cases hsp : ∃ n : ℕ, 4 ≤ n ∧ LieModel (BarInf L) .PSp n 2 f
        · obtain ⟨n, hn, hmodel⟩ := hsp
          exact uc22s2114r4f_fieldDataBody_psp hSg hL hn hmodel hbL hr hr5 hbr hin
        · by_cases hplus : ∃ n : ℕ, 4 ≤ n ∧ LieModel (BarInf L) .POmegaPlus n 2 f
          · obtain ⟨n, hn, hmodel⟩ := hplus
            exact uc22s2114r4f_fieldDataBody_pomegaPlus hSg hL hn hmodel hbL hr hr5 hbr hin
          · by_cases hminus : ∃ n : ℕ, 5 ≤ n ∧ LieModel (BarInf L) .POmegaMinus n 2 f
            · obtain ⟨n, hn, hmodel⟩ := hminus
              exact uc22s2114r4f_fieldDataBody_pomegaMinus hSg hL hn hmodel hbL hr hr5 hbr hin
            · by_cases hf4 : LieModel (BarInf L) .F4 0 2 f
              · exact uc22s2114r4f_fieldDataBody_f4 hSg hL hf4 hbL hr hr5 hbr hin
              · by_cases he6 : LieModel (BarInf L) .E6 0 2 f
                · exact uc22s2114r4f_fieldDataBody_e6 hSg hL he6 hbL hr hr5 hbr hin
                · by_cases he7 : LieModel (BarInf L) .E7 0 2 f
                  · exact uc22s2114r4f_fieldDataBody_e7 hSg hL he7 hbL hr hr5 hbr hin
                  · by_cases he8 : LieModel (BarInf L) .E8 0 2 f
                    · exact uc22s2114r4f_fieldDataBody_e8 hSg hL he8 hbL hr hr5 hbr hin
                    · by_cases htw : LieModel (BarInf L) .twistedE6 0 2 f
                      · exact uc22s2114r4f_fieldDataBody_twistedE6 hSg hL htw hbL hr hr5 hbr hin
                      · exact hRest hSg h76 h74 hH c L hL hX hpow l f hl hlr hn3 hBL hfaith hcase hall
                          b hbB hbL r hr hr5 hbr hrn hrf hin hu hlin hlow hsp hplus hminus hf4 he6 he7 he8 htw

end CFSG.LocalAnalysis.UniquenessCase.UC22
