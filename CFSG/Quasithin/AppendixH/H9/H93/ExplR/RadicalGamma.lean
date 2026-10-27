module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplR.RadicalParam
public import CFSG.Quasithin.AppendixH.H9.H93.RankGeneric

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem card_fixers_pairVec (a b : Fin 4 → ZMod 2) :
    Nat.card {ε : Fin 4 → ZMod 2 //
      radicalHom (Multiplicative.ofAdd ε) (pairVec a b) = pairVec a b} =
    Nat.card {ε : Fin 4 → ZMod 2 // Rfst ε a b = a ∧ Rsnd ε a b = b} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun ε => ?_)
  rw [radicalHom_pairVec, pairVec_inj]

private theorem four_le_fixers_V1 (i : Fin 4) :
    4 ≤ Nat.card {ε : Fin 4 → ZMod 2 //
      radicalHom (Multiplicative.ofAdd ε) (pairVec (Pi.single i 1) 0) =
        pairVec (Pi.single i 1) 0} := by
  rw [card_fixers_pairVec, Nat.card_eq_fintype_card]
  fin_cases i <;> decide

private theorem four_le_fixers_V2 (j : Fin 4) :
    4 ≤ Nat.card {ε : Fin 4 → ZMod 2 //
      radicalHom (Multiplicative.ofAdd ε) (pairVec 0 (Pi.single j 1)) =
        pairVec 0 (Pi.single j 1)} := by
  rw [card_fixers_pairVec, Nat.card_eq_fintype_card]
  fin_cases j <;> decide

theorem eq_top_of_pairVec_single_mem (H : Subgroup (PairN 4))
    (h1 : ∀ i : Fin 4, pairVec (Pi.single i 1) 0 ∈ H)
    (h2 : ∀ j : Fin 4, pairVec 0 (Pi.single j 1) ∈ H) : H = ⊤ := by
  have hs1 : ∀ (i : Fin 4) (c : ZMod 2), pairVec (Pi.single i c) 0 ∈ H := by
    intro i c
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [Pi.single_zero]
      exact H.one_mem
    · exact h1 i
  have hs2 : ∀ (j : Fin 4) (c : ZMod 2), pairVec 0 (Pi.single j c) ∈ H := by
    intro j c
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [Pi.single_zero]
      exact H.one_mem
    · exact h2 j
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  have hdec : pairVec a b =
      pairVec (Pi.single 0 (a 0)) 0 * pairVec (Pi.single 1 (a 1)) 0 *
        pairVec (Pi.single 2 (a 2)) 0 * pairVec (Pi.single 3 (a 3)) 0 *
        pairVec 0 (Pi.single 0 (b 0)) * pairVec 0 (Pi.single 1 (b 1)) *
        pairVec 0 (Pi.single 2 (b 2)) * pairVec 0 (Pi.single 3 (b 3)) := by
    simp only [pairVec_mul, pairVec_inj]
    constructor <;> funext i <;> fin_cases i <;> simp [Pi.single_apply]
  rw [hdec]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (hs1 0 _) (hs1 1 _)) (hs1 2 _)) (hs1 3 _)) (hs2 0 _)) (hs2 1 _)) (hs2 2 _)) (hs2 3 _)

theorem gammaCheck_two_Rg4 : E3.gammaCheck 2 Rg4 = ⊤ := by
  have h := gammaCheck_two_range (W := PairN 4) radicalHom radicalHom_injective
  rw [← radicalHom_range]
  refine h.trans (eq_top_of_pairVec_single_mem _ (fun i => ?_) (fun j => ?_))
  · exact Subgroup.subset_closure (four_le_fixers_V1 i)
  · exact Subgroup.subset_closure (four_le_fixers_V2 j)

end CFSG.ASVolI.ChH
