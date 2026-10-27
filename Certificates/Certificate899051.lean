module

public import Certificates.Data.FF81P51Fast
public import Certificates.Kernel.FF81P51Checks
public import CFSG.Certificates.Kernel.FF81P51WitSound

@[expose] public section

open CFSG.RankThree.PartTwo.Sec21.FF81.P51 Matrix

public section

open CFSG.RankThree.PartTwo.Sec21.FF81.P51 Matrix
open Certificates.Kernel.C899051

namespace Certificates

private theorem vecCount (m : Fin 7 → Bool) (hm : m = mA ∨ m = mB ∨ m = mC ∨ m = mD ∨ m = mE) :
    ((nonzeroL.filter fun v => m (tab v).1).toFinset).card = 2 * lineCount m := by
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact vecCount_mA
  · exact vecCount_mB
  · exact vecCount_mC
  · exact vecCount_mD
  · exact vecCount_mE

open CFSG.RankThree.PartTwo.Sec21.FF81.P51 Matrix in
theorem certificate899051 :
    (∀ v : V, v ≠ 0 → v ∈ nonzeroL)
    ∧ ((0 : V) ∉ nonzeroL)
    ∧ (∀ v : V, v ∈ allV)
    ∧ (∀ A ∈ H0L, mm A Aᵀ = 1 ∧ mm Aᵀ A = 1)
    ∧ (∀ A ∈ H0L, mm A T0 = mm T0 A)
    ∧ (∀ c₀ ∈ E0L, ∀ c₁ ∈ SU, ∀ c₂ ∈ SU, ∀ c₃ ∈ SU, ofCols ![c₀, c₁, c₂, c₃] ∈ H0L ∨ c₁ = c₂ ∨ c₁ = -c₂ ∨ c₁ = c₃ ∨ c₁ = -c₃ ∨ c₂ = c₃ ∨ c₂ = -c₃)
    ∧ (((H0L.filter fun A => decide (mv A (e 0) = e 0)).toFinset).card = 48)
    ∧ (∀ v ∈ nonzeroL, (tab v).2 ∈ H0L ∧ mv (tab v).2 (rep (tab v).1) = v)
    ∧ (∀ k : Fin 7, (tab (rep k)).1 = k)
    ∧ (∀ k : Fin 7, rep k ≠ 0)
    ∧ (nonzeroL = nonzeroD.map V4.toV)
    ∧ (allV = allD.map V4.toV)
    ∧ (H0L = H0D.map M16.toM)
    ∧ (∀ x : V4, x ∈ allD)
    ∧ (∀ x ∈ allD, tab x.toV = ((tabD x).1, (tabD x).2.toM))
    ∧ (∀ k : Fin 7, rep k = (repD k).toV)
    ∧ (∀ k : Fin 7, okL k = (okLD k).map V4.toV)
    ∧ (T0 = T0D.toM)
    ∧ (S1 = S1D.toM)
    ∧ (Tau = TauD.toM)
    ∧ (Cyc = CycD.toM)
    ∧ (Sig01 = Sig01D.toM)
    ∧ (e 0 = e0D.toV)
    ∧ (∀ a ∈ H0D, a ∈ H0WD)
    ∧ (∀ k : Fin 7, ∀ y ∈ allD, V4.dot y (repD k) = 1 → OkBD (repD k) y → y ∈ okLD k)
    ∧ (e 0 ≠ 0)
    ∧ (∀ i j : Fin 4, i ≠ j → e i ≠ e j ∧ e i ≠ -e j)
    ∧ (T0 = 1 + vecMulVec (e 0) (e 0))
    ∧ (mm T0 T0 = 1)
    ∧ (e 0 ⬝ᵥ e 0 = 1)
    ∧ (rep 0 = e 0)
    ∧ ((![1, 0, 0, 0] : V) = e 0)
    ∧ (mm Sig01 Cyc4 ∈ H0L)
    ∧ (mm Sig01 Sig01 = 1)
    ∧ (Sig01 *ᵥ e 1 = e 0)
    ∧ (∀ v ∈ nonzeroL, mA (tab v).1 = true → v ∈ Fr8)
    ∧ (∀ j : Fin 4, e j ∈ nonzeroL ∧ mA (tab (e j)).1 = true)
    ∧ (∀ v ∈ Fr8, v ≠ e 1 → v ≠ -e 1 → Sig01 *ᵥ v ∈ SU)
    ∧ (ofCols ![-e 0, e 1, e 2, e 3] = T0)
    ∧ (ofCols ![e 0, -e 1, e 2, e 3] = S1)
    ∧ (ofCols ![e 0, e 2, e 1, e 3] = Tau)
    ∧ (ofCols ![e 0, e 2, e 3, e 1] = Cyc)
    ∧ (Sig01 *ᵥ e 0 = e 1 ∧ Sig01 *ᵥ e 1 = e 0 ∧ Sig01 *ᵥ e 2 = e 2 ∧ Sig01 *ᵥ e 3 = e 3)
    ∧ (Cyc4 *ᵥ e 0 = e 1 ∧ Cyc4 *ᵥ e 1 = e 2 ∧ Cyc4 *ᵥ e 2 = e 3 ∧ Cyc4 *ᵥ e 3 = e 0)
    ∧ (T0 *ᵥ e 0 = -e 0)
    ∧ (rep 6 = e 0 + e 1 + e 2 + e 3)
    ∧ (∀ i : Fin 4, i ≠ 0 → e i 0 = 0)
    ∧ (∀ v ∈ nonzeroL, pos v = true ∨ pos (-v) = true)
    ∧ (∀ v ∈ nonzeroL, ¬(pos v = true ∧ pos (-v) = true))
    ∧ (∀ v ∈ nonzeroL, -v ∈ nonzeroL)
    ∧ (lineCount mA = 4)
    ∧ (lineCount mB = 12)
    ∧ (lineCount mC = 24)
    ∧ (lineCount mD = 15)
    ∧ (lineCount mE = 30)
    ∧ (∀ (m : Fin 7 → Bool) (hm : m = mA ∨ m = mB ∨ m = mC ∨ m = mD ∨ m = mE), ((nonzeroL.filter fun v => m (tab v).1).toFinset).card = 2 * lineCount m)
    ∧ (([false, true].all fun m₁ => [false, true].all fun m₂ => [false, true].all fun m₄ => [false, true].all fun m₅ => [false, true].all fun m₆ => (optLD 1 m₁).all fun p₁ => (optLD 2 m₂).all fun p₂ => (optLD 4 m₄).all fun p₄ => (optLD 5 m₅).all fun p₅ => (optLD 6 m₆).all fun p₆ => decide (C1D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) → C3D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) → C4D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) 2 → C4D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) 4 → GoodD (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆))) = true) :=
  ⟨mem_nonzeroL, not_zero_mem_nonzeroL, mem_allV, H0L_transpose, H0L_comm_T0,
    H0L_cols_of H0L_eq E0L_eqD SU_eqD H0L_colsD, card_stab, tab_spec, tab_rep, rep_ne_zero,
    nonzeroL_eq, allV_eq, H0L_eq, mem_allD, tab_eqD, rep_eqD, okL_eq, T0_eqD, S1_eqD, Tau_eqD,
    Cyc_eqD, Sig01_eqD, e0_eqD, H0D_sub_H0WD, okD, e0_ne_zero, e_ne, T0_eq, T0_sq, e0_dot,
    rep_zero, vec_e0, sig01_cyc4, sig01_sq, sig01_e1, mA_sub_Fr8, mA_e, sig01_Fr8, T0_cols,
    S1_cols, Tau_cols, Cyc_cols, Sig01_cols, Cyc4_cols, T0_e0, rep_six, e_succ_zero, pos_or,
    not_pos_and, neg_mem_nonzeroL, lineCount_mA, lineCount_mB, lineCount_mC, lineCount_mD,
    lineCount_mE, vecCount, classify_of_fwitsOK mem_nonzeroD fwitsOK_true⟩

end Certificates
