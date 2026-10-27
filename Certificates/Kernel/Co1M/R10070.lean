
module

public import Certificates.Kernel.Co1M.K10070

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam
  CFSG.KC.Co1B CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative

theorem unpackR_ne_id {N : Nat} (hN : TwoBK.Canon N) (h : Nat.beq N (idF 24) = false) :
    (unpackR 24 N == idRows 24) = false := by
  cases e : (unpackR 24 N == idRows 24)
  · rfl
  · exfalso
    rw [beq_iff_eq, ← TwoBK.unpackR_idF] at e
    have := TwoBK.eq_of_unpackR hN TwoBK.canon_idF e
    rw [this, Nat.beq_refl] at h
    exact Bool.noConfusion h

theorem invLoop_steps {M : Nat} : ∀ (j fuel C Rs : Nat), j < fuel → stepsK M j C Rs = true →
    invRowsLoop (unpackR 24 M) fuel (unpackR 24 C) = unpackR 24 Rs
  | 0, fuel + 1, C, Rs, _, h => by
    obtain ⟨h1, h2⟩ := CFSG.KC.SortTree.andB_true_iff.1 h
    rw [invRowsLoop, CFSG.KC.F2W.mulRows_unpackR, Nat.eq_of_beq_eq_true h1, TwoBK.unpackR_idF,
      beq_self_eq_true]
    simp only [↓reduceIte, Nat.eq_of_beq_eq_true h2]
  | j + 1, fuel + 1, C, Rs, hj, h => by
    change CFSG.KC.M1F2.strictB (mulF 24 C M) (fun N =>
      andB (notB (Nat.beq N (idF 24))) (stepsK M j N Rs)) = true at h
    have hs : ∀ (y : Nat) (k : Nat → Bool), CFSG.KC.M1F2.strictB y k = k y := fun y k => by
      cases y <;> rfl
    rw [hs] at h
    obtain ⟨h1, h2⟩ := CFSG.KC.SortTree.andB_true_iff.1 h
    have hne : Nat.beq (mulF 24 C M) (idF 24) = false := notB_true' h1
    rw [invRowsLoop, CFSG.KC.F2W.mulRows_unpackR,
      unpackR_ne_id (TwoBK.canon_mulF C M) hne]
    exact invLoop_steps j fuel _ Rs (by omega) h2
where
  notB_true' {b : Bool} (h : notB b = true) : b = false := by
    cases b
    · rfl
    · exact absurd h Bool.false_ne_true

theorem invRows_of_steps {M Rs : Nat} {j : Nat} (hj : j < 100000) (h : stepsK M j M Rs = true) :
    invRows (unpackR 24 M) = unpackR 24 Rs :=
  invLoop_steps j 100000 M Rs hj h

theorem fixed_of {M c : Nat} (h : Nat.beq (vmF 24 (trK 24 M) c) c = true) :
    isFixedN (transposeRows 24 (unpackR 24 M)) c = true := by
  rw [tr_sound (Nat.beq_refl (trK 24 M)), isFixedN, CFSG.KC.F2W.vecMulN_unpackR,
    Nat.eq_of_beq_eq_true h]
  exact beq_self_eq_true c

theorem mulId_of {A B : Nat} (h : Nat.beq (mulF 24 A B) (idF 24) = true) :
    mulRows 24 (unpackR 24 A) (unpackR 24 B) = idRows 24 := by
  rw [CFSG.KC.F2W.mulRows_unpackR, Nat.eq_of_beq_eq_true h, TwoBK.unpackR_idF]

theorem repOK_of_packed {K1 K2 K1i K2i S c : Nat}
    (h : andB (Nat.beq (mulF 24 K1 K1i) (idF 24)) (andB (Nat.beq (mulF 24 K2 K2i) (idF 24))
      (andB (orderIsK 24 S 2) (andB (Nat.beq (vmF 24 (trK 24 S) c) c)
      (andB (Nat.beq (vmF 24 (trK 24 K1) c) c) (Nat.beq (vmF 24 (trK 24 K2) c) c))))) = true) :
    repOK #[unpackR 24 K1, unpackR 24 K2] #[unpackR 24 K1i, unpackR 24 K2i] (unpackR 24 S) c =
      true := by
  simp only [CFSG.KC.SortTree.andB_true_iff] at h
  obtain ⟨h1, h2, hS, fS, f1, f2⟩ := h
  simp only [repOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨rfl, rfl⟩, orderIs_sound hS⟩, fixed_of fS⟩, fun l hl => ?_⟩
  interval_cases l
  · exact ⟨mulId_of h1, fixed_of f1⟩
  · exact ⟨mulId_of h2, fixed_of f2⟩

theorem kGensInv_eq : kGensInv = #[unpackR 24 (w70.reg 2), unpackR 24 (w70.reg 12)] := by
  rw [kGensInv, kGens_eq]
  simp only [List.map_toArray, List.map_cons, List.map_nil]
  rw [invRows_of_steps (by norm_num) inv_k1, invRows_of_steps (by norm_num) inv_k2]

theorem nGensInv_eq : nGensInv = #[unpackR 24 (w70.reg 4), unpackR 24 (w70.reg 13)] := by
  rw [nGensInv, nGens_eq]
  simp only [List.map_toArray, List.map_cons, List.map_nil]
  rw [invRows_of_steps (by norm_num) inv_n1, invRows_of_steps (by norm_num) inv_n2]

theorem repOK_A70 : repOK kGens kGensInv rowsSA code3 = true := by
  rw [kGensInv_eq, kGens_eq, w70_sA]
  exact repOK_of_packed rep_A_chk

theorem repOK_B70 : repOK nGens nGensInv rowsSB code4 = true := by
  rw [nGensInv_eq, nGens_eq, w70_sB]
  exact repOK_of_packed rep_B_chk

theorem repOK_C70 : repOK nGens nGensInv rowsSC code4 = true := by
  rw [nGensInv_eq, nGens_eq, w70_sC]
  exact repOK_of_packed rep_C_chk

theorem witOK_of {w : List Bool} {S T Rs j n : Nat} (hj : j < 100000)
    (h : andB (stepsK (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 w oneK) j (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 w oneK) Rs)
      (andB (Nat.beq (mulF 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
        CertificateChecks.KernelCo1Cover.R1 w oneK) Rs) (idF 24))
      (orderIsK 24 (mulF 24 (mulF 24 (mulF 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
        CertificateChecks.KernelCo1Cover.R1 w oneK) S) Rs) T) n)) = true) :
    witOK w (unpackR 24 S) (unpackR 24 T) n = true := by
  simp only [CFSG.KC.SortTree.andB_true_iff] at h
  obtain ⟨hst, hid, hord⟩ := h
  rw [witOK, CertificateChecks.KernelCo1B.wordRows_eq, invRows_of_steps hj hst, mulId_of hid,
    CFSG.KC.F2W.mulRows_unpackR, CFSG.KC.F2W.mulRows_unpackR, CFSG.KC.F2W.mulRows_unpackR,
    orderIs_sound hord]
  simp

theorem wit_A70 : witOK [false, false, false, false] rowsSA rowsSA 3 = true := by
  rw [w70_sA]
  exact witOK_of (by norm_num) wit_A_chk

theorem wit_B70 : witOK [false] rowsSA rowsSB 10 = true := by
  rw [w70_sA, w70_sB]
  exact witOK_of (by norm_num) wit_B_chk

theorem wit_C70 : witOK [true, true, true, false] rowsSA rowsSC 12 = true := by
  rw [w70_sA, w70_sC]
  exact witOK_of (by norm_num) wit_C_chk

theorem q0_eq (x : Nat) : q0N (transposeRows 24 qRows) x = dotN x (vmF 24 Qt70 x) := by
  rw [CertificateChecks.KernelCo1Cover.qRows_eq, tr_sound qt_chk, q0N, CFSG.KC.F2W.vecMulN_unpackR]

theorem q0_code3_70 : q0N (transposeRows 24 qRows) code3 = true := by
  rw [q0_eq]
  exact q0_code3_chk

theorem q0_code4_70 : q0N (transposeRows 24 qRows) code4 = false := by
  rw [q0_eq]
  have h := q0_code4_chk
  cases e : dotN code4 (vmF 24 Qt70 code4)
  · rfl
  · rw [e] at h
    exact absurd h Bool.false_ne_true

theorem code4_word70 : vecMulN 24 (transposeRows 24 (wordRows code4Word)) 1 = code4 := by
  rw [CertificateChecks.KernelCo1B.wordRows_eq, tr_sound (Nat.beq_refl _),
    CFSG.KC.F2W.vecMulN_unpackR]
  exact Nat.eq_of_beq_eq_true code4_chk

end CertificateChecks.KernelCo1M

end
