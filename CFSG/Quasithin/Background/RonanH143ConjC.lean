module

public import CFSG.Quasithin.Background.RonanH143ConjB

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code

theorem H143Concl_of_conj {c : P24} (hc : c ∈ AutPerm) {a b : Fin 24} {O : Finset (Fin 24)}
    {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)} {T₀ Γ : Subgroup P24}
    (h : H143Concl (c a) (c b) (c • O) (c • S) (c • B) (conjSubg c T₀) (conjSubg c Γ)) :
    H143Concl a b O S B T₀ Γ := by
  unfold H143Concl at h ⊢
  have hS : (c • S).erase (c • B) = c • S.erase B := (smul_erase_finset_finset c S B).symm
  have hO : ((c • O).erase (c a)).erase (c b) = c • (O.erase a).erase b := by
    rw [← smul_erase_finset, ← smul_erase_finset]
  rw [hS, hO, MY_conjSubg, MY_conjSubg] at h
  simp only [KY_conjSubg, ← M22g_conj hc, ← conjSubg_inf, perfectCore_conjSubg,
    ConjIsoModel_conj, ConjSymNatural_conj, ne_eq, conjSubg_inj, card_conjSubg] at h
  obtain ⟨⟨h1a, h1b, h1c⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := h
  refine ⟨⟨h1a, ?_, ?_⟩, ⟨h2a, ?_⟩, ⟨h3a, h3b⟩⟩
  · intro A
    have hA := h1b (conjSubg c A)
    simp only [conjSubg_le_conjSubg_iff, IsE2k_conjSubg_iff, conjSubg_inj] at hA
    exact hA
  · intro hΓ A
    have hA := h1c hΓ (conjSubg c A)
    simp only [conjSubg_le_conjSubg_iff, IsE2k_conjSubg_iff, conjSubg_inj] at hA
    exact hA
  · intro hΓ
    obtain ⟨h2b1, h2b2, h2b3⟩ := h2b hΓ
    exact ⟨(exists_perm_surj_conj c (MY Γ (S.erase B)) (KY Γ (S.erase B)) 5).mp h2b1, h2b2,
      (indecomposable_conj c (MY Γ (S.erase B)) (KY Γ (S.erase B))).mp h2b3⟩

theorem H143Concl_swap {a b : Fin 24} {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))}
    {B : Finset (Fin 24)} {T₀ Γ : Subgroup P24} (h : H143Concl a b O S B T₀ Γ) :
    H143Concl b a O S B T₀ Γ := by
  unfold H143Concl at h ⊢
  rw [M22g_comm b a, Finset.erase_right_comm]
  exact h

end CFSG.Quasithin.RonanH143
