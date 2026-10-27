module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Final

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

theorem lemma212 (h : NearAsolvAction p A G) (hsol : sol G = ⊥)
    (hmin : IsChiefFactorOf (G ⊔ A) (layerIn G) ⊥)
    (hG : (layerIn G : Set Γ) * (cenIn G A : Set Γ) = G) :
    ∃ B : Subgroup Γ, B ≤ A ∧ CyclicMod A B ∧
      ¬ Group.IsSolvable (cenIn (layerIn G) B) ∧
      IsChiefFactorOf (A ⊔ cenIn G B) (cenIn (layerIn G) B) ⊥ ∧
      A ⊔ cenIn G B = A ⊔ cenIn G A ⊔ cenIn (layerIn G) B ∧ sol (cenIn G B) = ⊥ := by
  have H : Lemma212.Hyp p A G := ⟨h, hsol, hmin, hG⟩
  obtain ⟨B, hB, hcyc⟩ := H.exists_B
  rw [H.layerIn_eq]
  exact ⟨B, hB.le, hcyc, Lemma212.GoodB.not_isSolvable_cenIn H hB,
    Lemma212.GoodB.isChiefFactor H hB, Lemma212.GoodB.sup_eq H hB,
    Lemma212.GoodB.sol_cenIn_eq_bot H hB⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near
