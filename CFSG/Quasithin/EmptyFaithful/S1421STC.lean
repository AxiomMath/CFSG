module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem not_le_of_inM_G0 (st : Setting1427 T M H K1) {M₁ : Subgroup G}
    (hM₁ : InM (K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1) M₁) : ¬ T ≤ M₁ := by
  intro hT
  have hYL : yOfL22 T M ≤ l2Of T H (yOfL22 T M) := le_sup_left
  have hYG : yOfL22 T M ≤ K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1 :=
    hYL.trans (le_sup_right.trans le_sup_left)
  have hInM : InM (yOfL22 T M ⊔ T) M₁ := ⟨hM₁.1, sup_le (hYG.trans hM₁.2) hT⟩
  have heq : M₁ = M := st.facts.unique.2 M₁ hInM
  have hK1G : K1 ≤ K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1 := le_sup_left.trans le_sup_left
  exact st.notation_.not_le (hK1G.trans (le_of_le_of_eq hM₁.2 heq))

end S1421

end CFSG.Quasithin
