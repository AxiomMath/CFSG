module

public import CFSG.LocalAnalysis.WeakClosure81.W183Kern
public import CFSG.LocalAnalysis.WeakClosure81.W172Final
public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G]

@[expose] def Tail1812FourFree_AS (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i →
      ¬ Concl182 D V₀ V H i →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) → False

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem false_of_not_concl182_AS_free (h162 : W3Thm162Gt2 G) (h172 : W3Thm172Weak G)
    (h5_4 : Asch5_4) (h5_11 : Asch5_11AS) (h5_12 : Asch5_12) (h5_13 : Asch5_13AS)
    (b2 : Tail1812Two_AS G) (b4 : Tail1812FourFree_AS G) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) : False := by
  obtain ⟨g, hgT, hgK, hgi⟩ := c.exists_conj_inf_le_T
  rcases c.relIndex_cases hgK with hA | hA
  · exact b2 h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hgT hgK hgi hA
  · exact b4 h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hgT hgK hgi hA

end MinCex183

section Certified

theorem w3Thm183_of_branches_AS_free (h162 : W3Thm162Gt2 G) (h5_4 : Asch5_4)
    (h5_11 : Asch5_11AS) (h5_12 : Asch5_12) (h5_13 : Asch5_13AS)
    (hMult : OddMultiplierSocle185) (hO : LieOrderFormulasInput) (h66 : Asch6_6)
    (b1 : Tail189Two_AS G) (b3 : Tail1812Two_AS G) (b4 : Tail1812FourFree_AS G) :
    W3Thm183 G :=
  w3Thm183_of_no_minCex fun _ _ _ _ _ c => by
    rcases not_and_or.mp c.fail with h1 | h2
    · exact c.false_of_not_concl181_AS_kern h162 (w3Thm172Weak_of_thm162 h162) h5_4 h5_11 h5_12
        h5_13 hMult b1 (tail189Four_AS_of_inputs hO h66) h1
    · exact c.false_of_not_concl182_AS_free h162 (w3Thm172Weak_of_thm162 h162) h5_4 h5_11 h5_12
        h5_13 b3 b4 h2

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
