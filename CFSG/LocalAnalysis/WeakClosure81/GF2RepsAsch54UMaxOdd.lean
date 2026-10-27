module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxChevOdd
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54OddDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallNarrow
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Ree

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SylowOver
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SL2Image
import CFSG.LocalAnalysis.UniquenessCase.UC22ListB
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Cases

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)


theorem asch80ThmA54Case_oddLie_of (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hSp : K_Asch511SylowOvergroupsPSp4) (hG2 : Asch80G2Prime)
    (hRest : Asch80ThmA54Case fun X _ => CFSG.Models.OddLieType X ∧
      (¬ ∃ (F : Type) (_ : Field F) (_ : Finite F), (2 : F) ≠ 0 ∧
        ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* X, Function.Surjective φ) ∧
      (¬ ∃ f : ℕ, CFSG.Models.LieModel X .twistedG2 0 3 f) ∧
      ¬ ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ Asch511SmallLie X r) :
    Asch80ThmA54Case fun X _ => CFSG.Models.OddLieType X := by
  intro Q _ _ L T M hK hLn hLs hnab hC hP hL0 hT hMt hM
  have := hLn
  by_cases hSL2 : ∃ (F : Type) (_ : Field F) (_ : Finite F), (2 : F) ≠ 0 ∧
      ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥L, Function.Surjective φ
  · obtain ⟨F, _, _, h2, φ, hφ⟩ := hSL2
    exact asch80ThmA54Case_psl2 hS Q L T M hK hLn hLs hnab hC
      (exists_lieModel_psl_two_of_surjective hLs hnab h2 hφ) hL0 hT hMt hM
  by_cases hree : ∃ f : ℕ, CFSG.Models.LieModel ↥L .twistedG2 0 3 f
  · exact absurd (lGen_eq_top_of_ree hC hree hT) (lGen_ne_top_of_forall_le hMt hM)
  by_cases hsm : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ Asch511SmallLie ↥L r
  · obtain ⟨r, hr, hr2, hG | hPSp | hL3 | hU3⟩ := hsm
    · exact (hG2 Q L T r hLn hr hr2 hG hC hT ⟨M, hMt, hM⟩).elim
    · have hTM : T ≤ M := hM T le_rfl
        (lt_top_of_isSylowIn_of_not_isSolvable hT (not_isSolvable_of_simple_normal L hLs hnab))
      refine Or.inr ⟨not_hasCompFactor_of_sylowOvergroups hS (fun X _ hX =>
          CFSG.LocalAnalysis.UniquenessCase.UC22.uc22lb_listB_facts
            CFSG.LocalAnalysis.UniquenessCase.UC22.listBExceptionalFacts
            ((isCalL0_iff_asc1930ListB X).1 hX)) hK hLn hLs hnab hC hL0 hT
          (hSp ↥L r hr hr2 hPSp) hTM,
        shape54_of_shape54Socle T hLs hnab hC
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, hr, hr2, hPSp⟩))))⟩
    all_goals
      have h4 : r % 4 = 1 ∨ r % 4 = 3 := by
        have := Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
        omega
    · rcases h4 with h4 | h4
      · exact asch80ThmA54Case_l3EpsWreathed Q L T M hK hLn hLs hnab hC
          ⟨r, 1, hr, hr2, Or.inl ⟨hL3, by rwa [pow_one]⟩⟩ hL0 hT hMt hM
      · exact asch80ThmA54Case_l3EpsSD hS Q L T M hK hLn hLs hnab hC
          ⟨r, hr, hr2, Or.inl ⟨h4, hL3⟩⟩ hL0 hT hMt hM
    · rcases h4 with h4 | h4
      · exact asch80ThmA54Case_l3EpsSD hS Q L T M hK hLn hLs hnab hC
          ⟨r, hr, hr2, Or.inr ⟨h4, hU3⟩⟩ hL0 hT hMt hM
      · exact asch80ThmA54Case_l3EpsWreathed Q L T M hK hLn hLs hnab hC
          ⟨r, 1, hr, hr2, Or.inr ⟨hU3, by rwa [pow_one]⟩⟩ hL0 hT hMt hM
  · exact hRest Q L T M hK hLn hLs hnab hC ⟨hP, hSL2, hree, hsm⟩ hL0 hT hMt hM

end CFSG.LocalAnalysis.WeakClosure81

end
