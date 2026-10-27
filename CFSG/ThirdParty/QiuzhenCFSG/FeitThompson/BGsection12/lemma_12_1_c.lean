module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_1_c
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.1(c). -/
public theorem CFSG.lemma_12_1_c
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    E₂ = ⊥ → E₁ ≠ ⊥ := by
  classical
  intro hE2bot hE1bot
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3⟩
  have hE12bot : E₁₂ = ⊥ :=
    section12_E12_eq_bot_of_E1_E2_eq_bot hE12 hE1 hE2 hE1bot hE2bot
  have hE3eqE : E₃ = E :=
    section12_E3_eq_E_of_E12_eq_bot (M := M) (E := E) (E₁₂ := E₁₂) (E₃ := E₃)
      hM hcomp hE12 hE3 hE12bot
  have hE3_le_der : E₃ ≤ ambientDerivedSubgroup E :=
    (lemma_12_1_b (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      (E₃ := E₃) hM ⟨hcomp, hE12, hE1, hE2, hE3⟩).1
  have hE_le_der : E ≤ ambientDerivedSubgroup E := by
    simpa [hE3eqE] using hE3_le_der
  have hder_eq_E : ambientDerivedSubgroup E = E :=
    le_antisymm section12_ambientDerivedSubgroup_le hE_le_der
  have hder_lt_E : ambientDerivedSubgroup E < E :=
    section12_ambientDerivedSubgroup_lt hM hcomp
  exact hder_lt_E.ne hder_eq_E

end Section12
