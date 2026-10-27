module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L511.Core
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Sol

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem lemma_5_11_sol_eq_bot
    {p : ℕ} (hp : p.Prime) {A G : Subgroup Γ} (hA : IsElemAbelian p A)
    (hrank : p ^ 2 ≤ Nat.card A) (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hB : signalizerMcBrideHypothesisB p G) (hsol : sol G = ⊥) :
    kOf G ≤ ⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer {a}) :=
  L511.kOf_le_Lgen_of_sol_eq_bot hp hA hrank hAG hB hsol

theorem lemma_5_11
    {p : ℕ} (hp : p.Prime) {A G : Subgroup Γ} (hA : IsElemAbelian p A)
    (hrank : p ^ 2 ≤ Nat.card A) (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hB : signalizerMcBrideHypothesisB p G) :
    kOf (⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer {a})) = kOf G := by
  have hK : KSetting p A G := ⟨hp, hA, hAG, hB⟩
  have hq := SolQuot.qSetting_sol hK
  have hK' := SolQuot.kSetting_qimg_sol hK
  have hrank' : p ^ 2 ≤ Nat.card (AChief.qimg (sol G) A) := by
    rw [hq.card_qimg (sol_le G)]
    exact hrank
  have hbar := lemma_5_11_sol_eq_bot hp hK'.elemAbelian hrank' hK'.normalizes hK'.hypB
    (SolQuot.sol_qimg_sol G)
  have hLG : (⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer {a})) ≤ G :=
    iSup_le fun a => iSup_le fun _ => iSup_le fun _ => (kOf_le _).trans inf_le_left
  exact kOf_eq_of_kOf_le hLG (SolQuot.kOf_le_iSup_kOf hK hrank hbar)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
