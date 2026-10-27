
module

public import CFSG.Sporadic.HNOddCore.CRecBase

public import CFSG.Sporadic.HNOddCore.Stab
public import CFSG.Sporadic.HNOddCore.CCheck
public import CFSG.Sporadic.HNSchreier.ThreeSpec
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.F5.Native Equiv

theorem c_parts : plettersOK 17 LocalData.innerWord = true ∧
    pisInv hnsData.n uTab (pinvCand hnsData.n uTab) = true ∧
    pisInv hnsData.n kTab (pinvCand hnsData.n kTab) = true ∧
    pisInv hnsData.n wTab (pinvCand hnsData.n wTab) = true ∧
    cRecOK hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta) parTab
      cABTab.1 cABTab.2 cRec = true := by
  have h := c_cert
  unfold cChecksO cChecks cChecksR cChecksH cChecksDU cChecksK at h
  simp only [Bool.and_eq_true] at h
  rw [← hRegs_eq, ← hStrongArr_eq, ← dTab_eq, ← uTab_eq, ← kTab_eq, ← wTab_eq, ← cABTab_eq,
    ← parTab_eq, ← cRec_eq] at h
  obtain ⟨h1, h2, ⟨h3, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem prep_dTab :
    PRep hnsData.n dTab (permJ (hWordJ LocalData.innerWord)) := by
  rw [dTab_eq]
  exact prep_hWord c_parts.1

theorem prep_kTab :
    PRep hnsData.n kTab (permJ dJ) := by
  rw [kTab_eq, dJ, map_mul, map_inv]
  exact prep_pcomp prep_dTab (prep_inv_of_pisInv prep_uTab c_parts.2.1)

theorem prep_cATab :
    PRep hnsData.n cABTab.1 (permJ (conjC aJ)) := by
  rw [cATab_eq, conjC_aJ, map_mul, map_mul, map_inv, mul_assoc]
  exact prep_pcomp prep_kTab (prep_pcomp prep_aTab (prep_inv_of_pisInv prep_kTab c_parts.2.2.1))

theorem prep_cBTab :
    PRep hnsData.n cABTab.2 (permJ (conjC bJ)) := by
  rw [cBTab_eq, conjC_bJ, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  have hki := prep_inv_of_pisInv prep_kTab c_parts.2.2.1
  have hwi := prep_inv_of_pisInv prep_wTab c_parts.2.2.2.1
  have := prep_pcomp prep_kTab (prep_pcomp hwi (prep_pcomp prep_bTab (prep_pcomp prep_wTab hki)))
  simpa only [mul_assoc] using this

theorem cRec_step {j : ℕ} (hj0 : 0 < j) (hj : j < hnsData.n) :
    cRecStep (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta) parTab
      cABTab.1 cABTab.2 cRec j = true := by
  have h := c_parts.2.2.2.2
  unfold cRecOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have := allBelowN_spec h.2 hj
  simpa [Nat.pos_iff_ne_zero.1 hj0] using this

theorem cRec_zero : cRec[0]! = 0 := by
  have h := c_parts.2.2.2.2
  unfold cRecOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem cR_smul_eq_cRec :
    ∀ j : X, ((cR • j : X) : ℕ) = cRec[(j : ℕ)]! := by
  intro ⟨j, hj⟩
  show ((cR • (⟨j, hj⟩ : X) : X) : ℕ) = cRec[j]!
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [cRec_zero]
      exact congrArg Fin.val cR_smul_x0
    · have hs := cRec_step hj0 hj
      unfold cRecStep at hs
      set p := parTab[j]! with hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨hlt, hs⟩ := hs
      have hi : p / 2 < hnsData.n := lt_trans hlt hj
      have ih' : ((cR • (⟨p / 2, hi⟩ : X) : X) : ℕ) = cRec[p / 2]! := ih (p / 2) hlt hi
      split_ifs at hs with hpar
      · simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨ha, hc⟩ := hs
        have hy : (⟨j, hj⟩ : X) = aJ • (⟨p / 2, hi⟩ : X) :=
          Fin.ext (by rw [smul_val_aJ]; exact ha.symm)
        rw [hy, cR_smul_conj, hc, ← ih', ← permJ_apply]
        exact (prep_cATab _).symm
      · simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨hb, hc⟩ := hs
        have hy : (⟨j, hj⟩ : X) = bJ • (⟨p / 2, hi⟩ : X) :=
          Fin.ext (by rw [smul_val_bJ]; exact hb.symm)
        rw [hy, cR_smul_conj, hc, ← ih', ← permJ_apply]
        exact (prep_cBTab _).symm

theorem prep_cRec :
    PRep hnsData.n cRec (permR cR) := fun x => by
  rw [permR_apply, cR_smul_eq_cRec]

end CFSG.Sporadic.HNOddCore
