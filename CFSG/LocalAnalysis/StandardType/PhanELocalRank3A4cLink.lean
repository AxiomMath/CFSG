module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4cSkew
public import CFSG.LocalAnalysis.StandardType.PhanELocalLinkB

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private lemma plh_inf_eq_bot_of_point_not_le {a Y : Submodule K (Fin 4 → K)}
    (ha : finrank K a = 1) (h : ¬ a ≤ Y) : Y ⊓ a = ⊥ := by
  by_contra hne
  have h0 : finrank K ↥(Y ⊓ a) ≠ 0 := fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
  have hle1 : finrank K ↥(Y ⊓ a) ≤ 1 := ha ▸ Submodule.finrank_mono inf_le_right
  have h1 : finrank K ↥(Y ⊓ a) = 1 := by omega
  have heq : Y ⊓ a = a := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, ha])
  exact h (heq ▸ inf_le_left)

private lemma plh_skew_iff (hK : Nat.card K = (2 ^ f) ^ 2) {p L : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) (hL : finrank K L = 2) (hpL : p ≤ L) :
    L ⊓ sgS K f 4 L = ⊥ ↔
      (finrank K ↥(L ⊔ (p ⊔ sgS K f 4 p)) = 3 ∧
        sgS K f 4 (L ⊔ (p ⊔ sgS K f 4 p)) ≠ L ⊔ (p ⊔ sgS K f 4 p)) := by
  have hσp1 : finrank K (sgS K f 4 p) = 1 := by rw [finrank_sgS hK]; exact hp
  have hT_eq : L ⊔ (p ⊔ sgS K f 4 p) = L ⊔ sgS K f 4 p := by
    rw [← sup_assoc, sup_eq_left.mpr hpL]
  constructor
  · intro hMbot
    have hσpσL : sgS K f 4 p ≤ sgS K f 4 L := sgS_mono (f := f) hpL
    have hσpNotL : ¬ sgS K f 4 p ≤ L := by
      intro hle
      have hbot : sgS K f 4 p ≤ (⊥ : Submodule K (Fin 4 → K)) := by
        have hle' : sgS K f 4 p ≤ L ⊓ sgS K f 4 L := le_inf hle hσpσL
        rwa [hMbot] at hle'
      have h0 : finrank K (sgS K f 4 p) = 0 := by
        rw [le_bot_iff.mp hbot, finrank_bot]
      rw [hσp1] at h0
      omega
    have hInfBot : L ⊓ sgS K f 4 p = ⊥ := plh_inf_eq_bot_of_point_not_le hσp1 hσpNotL
    have hT3 : finrank K ↥(L ⊔ sgS K f 4 p) = 3 := by
      rw [finrank_sup_of_disjoint (disjoint_iff.mpr hInfBot), hL, hσp1]
    have hTne : sgS K f 4 (L ⊔ sgS K f 4 p) ≠ L ⊔ sgS K f 4 p := by
      intro hfix
      have hσLsup : sgS K f 4 L ⊔ p = L ⊔ sgS K f 4 p := by
        rw [← hfix, sgS_sup hK, sgS_sgS hK]
      have hle : L ⊔ sgS K f 4 L ≤ L ⊔ sgS K f 4 p := by
        apply sup_le le_sup_left
        rw [← hσLsup]
        exact le_sup_left
      have h4 : finrank K ↥(L ⊔ sgS K f 4 L) = 4 := by
        rw [finrank_sup_of_disjoint (disjoint_iff.mpr hMbot), hL, finrank_sgS hK, hL]
      have hle3 : finrank K ↥(L ⊔ sgS K f 4 L) ≤ 3 := by
        have hmono := Submodule.finrank_mono hle
        rwa [hT3] at hmono
      omega
    rw [hT_eq]
    exact ⟨hT3, hTne⟩
  · intro hT
    obtain ⟨hT3, hTne⟩ := hT
    have hT3' : finrank K ↥(L ⊔ sgS K f 4 p) = 3 := by
      rw [hT_eq] at hT3
      exact hT3
    have hσpNotL : ¬ sgS K f 4 p ≤ L := by
      intro hle
      have hUle : p ⊔ sgS K f 4 p ≤ L := sup_le hpL hle
      have hTeq : L ⊔ (p ⊔ sgS K f 4 p) = L := sup_eq_left.mpr hUle
      have h2 : finrank K L = 3 := by rw [← hTeq, hT_eq]; exact hT3'
      omega
    set M : Submodule K (Fin 4 → K) := L ⊓ sgS K f 4 L with hMdef
    have hMleL : M ≤ L := by rw [hMdef]; exact inf_le_left
    have hMleσL : M ≤ sgS K f 4 L := by rw [hMdef]; exact inf_le_right
    have hMstable : sgS K f 4 M = M := by
      rw [hMdef, sgS_inf, sgS_sgS hK, inf_comm]
    by_contra hMne
    have hMneL : M ≠ L := by
      intro hEq
      have hLleσL : L ≤ sgS K f 4 L := hEq ▸ hMleσL
      have hσLeq : sgS K f 4 L = L :=
        (Submodule.eq_of_le_of_finrank_eq hLleσL (by rw [finrank_sgS hK])).symm
      have hσpσL : sgS K f 4 p ≤ sgS K f 4 L := sgS_mono (f := f) hpL
      exact hσpNotL (hσLeq ▸ hσpσL)
    have hMle2 : finrank K ↥M ≤ 2 := by
      have hmono := Submodule.finrank_mono hMleL
      rwa [hL] at hmono
    have hMne2 : finrank K ↥M ≠ 2 := by
      intro h2
      exact hMneL (Submodule.eq_of_le_of_finrank_eq hMleL (by rw [h2, hL]))
    have hMge1 : 1 ≤ finrank K ↥M := by
      by_contra h
      have hlt : finrank K ↥M < 1 := not_le.1 h
      have h0 : finrank K ↥M = 0 := by omega
      exact hMne (Submodule.finrank_eq_zero.mp h0)
    have hMfin : finrank K ↥M = 1 := by omega
    have hMneP : M ≠ p := by
      intro hEq
      have hpσL : p ≤ sgS K f 4 L := hEq ▸ hMleσL
      have hmono := sgS_mono (f := f) hpσL
      rw [sgS_sgS hK] at hmono
      exact hσpNotL hmono
    have hLsup : p ⊔ M = L := by
      have hle : p ⊔ M ≤ L := sup_le hpL hMleL
      have hfr : finrank K ↥(p ⊔ M) = 2 := finrank_sup_of_ne_pts hp hMfin (Ne.symm hMneP)
      exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hL, hfr])
    have hσL : sgS K f 4 L = sgS K f 4 p ⊔ M := by
      rw [← hLsup, sgS_sup hK, hMstable]
    have hσTleT : sgS K f 4 (L ⊔ (p ⊔ sgS K f 4 p)) ≤ L ⊔ (p ⊔ sgS K f 4 p) := by
      rw [hT_eq, sgS_sup hK, sgS_sgS hK]
      apply sup_le
      · rw [hσL]
        exact sup_le le_sup_right (hMleL.trans le_sup_left)
      · exact hpL.trans le_sup_left
    have hfix : sgS K f 4 (L ⊔ (p ⊔ sgS K f 4 p)) = L ⊔ (p ⊔ sgS K f 4 p) :=
      Submodule.eq_of_le_of_finrank_eq hσTleT (by rw [finrank_sgS hK])
    exact hTne hfix

theorem adm4c_fibreConn (hK : Nat.card K = (2 ^ f) ^ 2) :
    AdmFibreConn (Adm4c (K := K) f) := by
  refine admFibreConn_of_dual_pencil (Adm4c (K := K) f)
    (fun p => p ⊔ sgS K f 4 p)
    (fun _ T => finrank K T = 3 ∧ sgS K f 4 T ≠ T) ?_ ?_ ?_
  · intro p L H h
    exact ⟨finrank_realLine (f := f) hK h.1.p1 (adm4c_nonreal (f := f) hK h), le_sup_left⟩
  · intro p L₀ H₀ _ L H hf
    have hsup : (p ⊔ sgS K f 4 p ≤ H) ↔ (sgS K f 4 p ≤ H) := by
      rw [sup_le_iff]
      exact ⟨fun h => h.2, fun h => ⟨hf.pL.trans hf.LH, h⟩⟩
    show (Adm4c (K := K) f p L H) ↔
      (¬ (p ⊔ sgS K f 4 p) ≤ H ∧ (finrank K ↥(L ⊔ (p ⊔ sgS K f 4 p)) = 3 ∧
        sgS K f 4 (L ⊔ (p ⊔ sgS K f 4 p)) ≠ L ⊔ (p ⊔ sgS K f 4 p)))
    rw [adm4c_iff_of_flag (f := f) hK hf]
    exact and_congr (not_congr hsup.symm) (plh_skew_iff (f := f) hK hf.p1 hf.L2 hf.pL)
  · intro p L₀ H₀ h₀
    obtain ⟨hf₀, hadm₀⟩ := h₀
    have hskew₀ : L₀ ⊓ sgS K f 4 L₀ = ⊥ :=
      ((adm4c_iff_of_flag (f := f) hK hf₀).mp hadm₀).2
    obtain ⟨hdim₀, hne₀⟩ := (plh_skew_iff (f := f) hK hf₀.p1 hf₀.L2 hf₀.pL).mp hskew₀
    refine ⟨L₀ ⊔ (p ⊔ sgS K f 4 p), sgS K f 4 (L₀ ⊔ (p ⊔ sgS K f 4 p)),
      Ne.symm hne₀, ⟨le_sup_right, hdim₀, hdim₀, hne₀⟩, ?_⟩
    have hUleσ : p ⊔ sgS K f 4 p ≤ sgS K f 4 (L₀ ⊔ (p ⊔ sgS K f 4 p)) := by
      have hmono := sgS_mono (f := f)
        (le_sup_right : p ⊔ sgS K f 4 p ≤ L₀ ⊔ (p ⊔ sgS K f 4 p))
      rw [sgS_realLine (f := f) hK p] at hmono
      exact hmono
    have hdimσ : finrank K ↥(sgS K f 4 (L₀ ⊔ (p ⊔ sgS K f 4 p))) = 3 := by
      rw [finrank_sgS hK]
      exact hdim₀
    have hneσ : sgS K f 4 (sgS K f 4 (L₀ ⊔ (p ⊔ sgS K f 4 p))) ≠
        sgS K f 4 (L₀ ⊔ (p ⊔ sgS K f 4 p)) := by
      rw [sgS_sgS hK]
      exact Ne.symm hne₀
    exact ⟨hUleσ, hdimσ, hdimσ, hneσ⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
