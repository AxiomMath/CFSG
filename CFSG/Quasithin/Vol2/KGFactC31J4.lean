module

public import CFSG.Quasithin.Vol2.KGFactC31J4B

public section

namespace CFSG.Quasithin.KGC31.J4

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31

@[expose] def M4Branch : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (S M₀ R M V : Subgroup A), Setup S M₀ R M V → S = ⊤ →
    ∀ κ : G₀ →* A, Iso κ → Subgroup.normalizer (R : Set A) ≤ CFSG.Quasithin.KGJ4.M4.map κ →
      (¬ ∃ B : Subgroup A, B ≤ R ∧ IsElemAbelian 2 B ∧ 2 ^ 11 ≤ Nat.card B) →
      Concl S M₀ R M V

theorem inspC31SporadicAtJ_j4_of
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW)
    (hD3 : Subgroup.centralizer ((pCoreOf 2 (Subgroup.centralizer
      ({CFSG.Quasithin.J4Loc.z0} : Set G₀)) : Subgroup G₀) : Set G₀) ≤
      Subgroup.zpowers CFSG.Quasithin.J4Loc.z0)
    {KL : Subgroup G₀} {v0 : Fin 3 → G₀} {hv0 : EBasis v0} (hM3 : M3Facts KL hv0)
    (hM4 : M4Branch) : CFSG.Quasithin.InspC31SporadicAtJ .J4 := by
  intro A _ _ S M₀ R M V hSn hSs hCS hM₀S hper hM₀ne hcomp hR2 hRM hMN hM₀R hsyl hVM₀ hVne hV
    hcomm hVc hNVM hNR hSM hJ4
  obtain ⟨hJ, hZ, hΩ⟩ := hJ4 rfl
  have h : Setup S M₀ R M V := ⟨hSn, hSs, hCS, hM₀S, hper, hM₀ne, hcomp, hR2, hRM, hMN, hM₀R,
    hsyl, hVM₀, hVne, hV, hcomm, hVc, hNVM, hNR, hSM, hJ, hZ, hΩ⟩
  obtain ⟨hStop, f, hf⟩ := exists_iso hSn hSs hCS
  by_cases hB : ∃ B : Subgroup A, B ≤ R ∧ IsElemAbelian 2 B ∧ 2 ^ 11 ≤ Nat.card B
  · exact caseA h hf hB
  obtain ⟨i, g, hg⟩ := kw1 hKW hf h.hR2 h.R_ne_bot
  rw [Subgroup.map_map] at hg
  have hκ := hf.conj g
  fin_cases i
  · exact absurd (branch_H h hκ hg) hB
  · exact (branch_M2 h hκ hg hD3).elim
  · exact branch_M3 h hStop hκ hg hM3
  · exact hM4 A S M₀ R M V h hStop _ hκ hg hB

end CFSG.Quasithin.KGC31.J4

end
