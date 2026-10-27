module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
public import CFSG.LocalAnalysis.WeakClosure81.W18PackG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def Tail189Two_AS (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i → ¬ Concl181 D V₀ V H →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) = 2 → False

@[expose] def Tail189Four_AS (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i → ¬ Concl181 D V₀ V H →
      kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) → False

@[expose] def Tail1812Two_AS (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i →
      ¬ Concl182 D V₀ V H i →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) = 2 → False

@[expose] def Tail1812Four_AS (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i →
      ¬ Concl182 D V₀ V H i →
      kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) → False

end CFSG.LocalAnalysis.WeakClosure81

end
