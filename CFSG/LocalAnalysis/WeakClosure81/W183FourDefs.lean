module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
public import CFSG.LocalAnalysis.WeakClosure81.W18PackG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)

@[expose] def Tail1812FourL24U34 (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i →
      ¬ Concl182 D V₀ V H i →
      kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) →
      (∃ L : Subgroup G, IsComponentModN (kerMV V H) H L ∧ L ⊔ D.T = H ∧
        HasQuotShape L (kerMV V H : Set G) (fun X _ => IsL2 X 2 ∨ IsU3 X 2)) →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) → False

@[expose] def FourU34Two (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i →
      ¬ Concl182 D V₀ V H i →
      kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) →
      (∃ L : Subgroup G, IsComponentModN (kerMV V H) H L ∧ L ⊔ D.T = H ∧
        HasQuotShape L (kerMV V H : Set G) (fun X _ => IsU3 X 2) ∧
        ∃ t ∈ D.T, conjSubgroup L t ≠ L) →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) → False

@[expose] def FourOdd (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i →
      ¬ Concl182 D V₀ V H i →
      kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) →
      (∃ L : Subgroup G, IsComponentModN (kerMV V H) H L ∧ L ⊔ D.T = H ∧
        ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧
            HasQuotShape L (kerMV V H : Set G) (fun X _ => CFSG.Quasithin.F6.IsL2 p e X)) ∨
          (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
            ((p % 4 = 3 ∧
                HasQuotShape L (kerMV V H : Set G) (fun X _ => LieModel X .PSL 3 p 1)) ∨
              (p % 4 = 1 ∧
                HasQuotShape L (kerMV V H : Set G) (fun X _ => LieModel X .PSU 3 p 1)))))) →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) → False

end CFSG.LocalAnalysis.WeakClosure81

end
