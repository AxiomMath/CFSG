
module

public import Certificates.Kernel.Co1M.D10070
public import CFSG.Sporadic.Co1.Module.InvFamInputs
public import Certificates.Kernel.Co1B.C2046
public import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Certificates.Kernel.Co1BWordSound
public import CFSG.Certificates.Kernel.SortTreeChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam
  CFSG.KC.SortTree CFSG.KC.Co1B CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def w70 : InvFamW where
  R := R70
  RT := RT70
  P := P70
  a0 := a0v70
  a1 := a1v70
  w0 := w0v70
  w1 := w1v70
  K1 := K1x70
  K2 := K2x70
  K2i := K2ix70
  K3 := K3x70
  K3i := K3ix70
  K4 := K4x70
  K4i := K4ix70
  r1 := Rt1x70
  r2 := Rt2x70
  r3 := Rt3x70
  t1 := ⟨recT t1L70 5 595, 5, 12, 32, 89⟩
  t2 := ⟨recT t2L70 5 588, 3, 7, 32, 4⟩
  t3 := ⟨recT t3L70 5 591, 3, 10, 32, 17⟩
  v1 := ⟨recT v1L70 6 38, 4, 8, 64, 3⟩
  v0 := ⟨recT v0L70 6 38, 3, 9, 64, 5⟩
  uB := uBv70
  wB := wBv70
  uC := uCv70
  wC := wCv70
  KB := KBx70
  KC := KCx70
  vb := ⟨recT vbL70 6 41, 3, 11, 64, 32⟩
  vc := ⟨recT vcL70 6 41, 3, 11, 64, 32⟩

theorem w70_seeds : andB (Nat.beq (w70.reg 0) CertificateChecks.KernelCo1Cover.R0)
    (Nat.beq (w70.reg 1) CertificateChecks.KernelCo1Cover.R1) = true := by quickRfl

theorem w70_words : andB (Nat.beq (wordABFrom CertificateChecks.KernelCo1Cover.R0
    CertificateChecks.KernelCo1Cover.R1 kWord1 oneK) (w70.reg 2))
    (andB (Nat.beq (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 kWord2 oneK) (w70.reg 3))
    (andB (Nat.beq (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 nWord1 oneK) (w70.reg 4))
    (Nat.beq (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 nWord2 oneK) (w70.reg 5)))) = true := by quickRfl

theorem w70_reps : andB (Nat.beq (powWK (gwordFrom [w70.reg 2, w70.reg 3] wordA oneK) 7) (w70.reg 7))
    (andB (Nat.beq CFSG.KD.Co1B.SBK (w70.reg 9))
      (Nat.beq (powWK (gwordFrom [w70.reg 4, w70.reg 5] wordC oneK) 5) (w70.reg 11))) = true := by
  quickRfl

theorem wordA_lt : ∀ l ∈ wordA, l < 2 := by decide +kernel

theorem wordC_lt : ∀ l ∈ wordC, l < 2 := by decide +kernel

theorem w70_rA : dat.rowsA = unpackR 24 (w70.reg 0) := by
  rw [CertificateChecks.KernelCo1Cover.rowsA_eq,
    ← Nat.eq_of_beq_eq_true (CFSG.KC.SortTree.andB_true_iff.1 w70_seeds).1]

theorem w70_rB : dat.rowsB = unpackR 24 (w70.reg 1) := by
  rw [CertificateChecks.KernelCo1Cover.rowsB_eq,
    ← Nat.eq_of_beq_eq_true (CFSG.KC.SortTree.andB_true_iff.1 w70_seeds).2]

theorem w70_word (w : List Bool) {i : Nat}
    (h : Nat.beq (wordABFrom CertificateChecks.KernelCo1Cover.R0 CertificateChecks.KernelCo1Cover.R1
      w oneK) (w70.reg i) = true) : wordRows w = unpackR 24 (w70.reg i) := by
  rw [CertificateChecks.KernelCo1B.wordRows_eq, Nat.eq_of_beq_eq_true h]

theorem w70_gens : wordRows kWord1 = unpackR 24 (w70.reg 2) ∧ wordRows kWord2 = unpackR 24 (w70.reg 3) ∧
    wordRows nWord1 = unpackR 24 (w70.reg 4) ∧ wordRows nWord2 = unpackR 24 (w70.reg 5) := by
  have h := w70_words
  simp only [CFSG.KC.SortTree.andB_true_iff] at h
  exact ⟨w70_word _ h.1, w70_word _ h.2.1, w70_word _ h.2.2.1, w70_word _ h.2.2.2⟩

theorem kGens_eq : kGens = #[unpackR 24 (w70.reg 2), unpackR 24 (w70.reg 3)] := by
  rw [kGens, w70_gens.1, w70_gens.2.1]

theorem nGens_eq : nGens = #[unpackR 24 (w70.reg 4), unpackR 24 (w70.reg 5)] := by
  rw [nGens, w70_gens.2.2.1, w70_gens.2.2.2]

theorem gens_get {a b : Nat} : ∀ l < [a, b].length,
    (#[unpackR 24 a, unpackR 24 b] : Array (Array Nat))[l]! = unpackR 24 (getL 0 [a, b] l) := by
  intro l hl
  rcases l with _ | _ | l
  · rfl
  · rfl
  · simp at hl

theorem w70_sA : rowsSA = unpackR 24 (w70.reg 7) := by
  have h := w70_reps
  simp only [CFSG.KC.SortTree.andB_true_iff] at h
  rw [rowsSA, kGens_eq, genWordRows_eq gens_get wordA_lt CertificateChecks.KernelCo1B.idRows_eq,
    powRows_eq _ CertificateChecks.KernelCo1B.idRows_eq, Nat.eq_of_beq_eq_true h.1]

theorem w70_sB : rowsSB = unpackR 24 (w70.reg 9) := by
  have h := w70_reps
  simp only [CFSG.KC.SortTree.andB_true_iff] at h
  rw [CertificateChecks.KernelCo1B.rowsSB_eq, Nat.eq_of_beq_eq_true h.2.1]

theorem w70_sC : rowsSC = unpackR 24 (w70.reg 11) := by
  have h := w70_reps
  simp only [CFSG.KC.SortTree.andB_true_iff] at h
  rw [rowsSC, nGens_eq, genWordRows_eq gens_get wordC_lt CertificateChecks.KernelCo1B.idRows_eq,
    powRows_eq _ CertificateChecks.KernelCo1B.idRows_eq, Nat.eq_of_beq_eq_true h.2.2]

theorem w70_prog : progK 24 w70.R w70.P 2 = true := by quickRfl

theorem w70_tr : allN (lenL w70.R) (fun i => Nat.beq (trK 24 (w70.reg i)) (w70.regT i)) = true := by
  quickRfl

theorem w70_idx : bndK (lenL w70.R) w70.idxL = true := by quickRfl

theorem w70_fix3 : fixAllK w70.RT (w70.K1 ++ w70.K2 ++ w70.K3 ++ w70.K4 ++
    [getL 0 w70.r1 0, getL 0 w70.r2 0, getL 0 w70.r3 0]) [code3] = true := by quickRfl

theorem w70_fix1 : fixAllK w70.RT w70.K1 [w70.a0] = true := by quickRfl

theorem w70_fix2 : fixAllK w70.RT w70.K2 [w70.a0, w70.w0] = true := by quickRfl

theorem w70_fixK3 : fixAllK w70.RT w70.K3 [w70.a0, w70.a1] = true := by quickRfl

theorem w70_fix4 : fixAllK w70.RT w70.K4 [w70.a0, w70.a1, w70.w1] = true := by quickRfl

theorem w70_inv : andB (invPairsK w70.R w70.K2 w70.K2i) (andB (invPairsK w70.R w70.K3 w70.K3i)
    (invPairsK w70.R w70.K4 w70.K4i)) = true := by quickRfl

theorem w70_roots : andB (rootK w70.R w70.r1 7) (andB (rootK w70.R w70.r2 7)
    (rootK w70.R w70.r3 7)) = true := by quickRfl

theorem w70_rootAct : andB (Nat.beq (vmF 24 (w70.regT (getL 0 w70.r1 2)) w70.a0) w70.a0)
    (andB (Nat.beq (vmF 24 (w70.regT (getL 0 w70.r1 2)) w70.a1) w70.a1)
    (andB (Nat.beq (vmF 24 (w70.regT (getL 0 w70.r2 2)) w70.a0) w70.a0)
    (andB (Nat.beq (vmF 24 (w70.regT (getL 0 w70.r2 2)) w70.a1) w70.w1)
      (Nat.beq (vmF 24 (w70.regT (getL 0 w70.r3 2)) w70.a0) w70.w0)))) = true := by quickRfl

theorem w70_vecs : bndK (2 ^ 24) [w70.a0, w70.a1, w70.w0, w70.w1, w70.wB, w70.wC] = true := by
  quickRfl

theorem w70_mem : andB (notB (memK w70.v1.tab 162 24 w70.a1))
    (notB (memK w70.v0.tab 275 24 w70.a0)) = true := by quickRfl

theorem w70_fixB : fixAllK w70.RT w70.KB [code4, w70.uB] = true := by quickRfl

theorem w70_fixC : fixAllK w70.RT w70.KC [code4, w70.uC] = true := by quickRfl

theorem w70_img : andB (Nat.beq (vmF 24 (w70.regT 9) w70.uB) w70.wB)
    (Nat.beq (vmF 24 (w70.regT 11) w70.uC) w70.wC) = true := by quickRfl

theorem chunks_spec {act : Nat → Nat → Nat} {ng root : Nat} {rec : Nat → Nat}
    {n wv wl wp B lo cnt : Nat} (h : chunksK act ng root rec n wv wl wp B lo cnt = true) :
    ∀ j < cnt, chunkOK act ng (fun _ => true) root rec n wv wl wp B (lo + j) = true :=
  (CFSG.KC.SortTree.allN_iff _ _).1 h

theorem chunks_join {P : Nat → Prop} {a b : Nat} (ha : ∀ j < a, P (0 + j)) (hb : ∀ j < b, P (a + j)) :
    ∀ c < a + b, P c :=
  CFSG.KC.SortTree.forall_lt_add (fun c hc => by simpa using ha c hc) hb

theorem w70_t2 : chunksK (actC w70.R w70.K4 w70.K4i) (lenL w70.K4) (w70.reg (getL 0 w70.r2 2))
    w70.t2.tab 120 576 w70.t2.wl w70.t2.wp w70.t2.B 0 4 = true := by quickRfl

theorem w70_v1 : chunksK (actV w70.RT w70.K3) (lenL w70.K3) w70.w1 w70.v1.tab 162 24 w70.v1.wl
    w70.v1.wp w70.v1.B 0 3 = true := by quickRfl

theorem w70_v0 : chunksK (actV w70.RT w70.K1) (lenL w70.K1) w70.w0 w70.v0.tab 275 24 w70.v0.wl
    w70.v0.wp w70.v0.B 0 5 = true := by quickRfl

theorem w70_vb : chunksK (actV w70.RT w70.KB) (lenL w70.KB) w70.wB w70.vb.tab 2000 24 w70.vb.wl
    w70.vb.wp w70.vb.B 0 32 = true := by quickRfl

theorem w70_vc : chunksK (actV w70.RT w70.KC) (lenL w70.KC) w70.wC w70.vc.tab 2000 24 w70.vc.wl
    w70.vc.wp w70.vc.B 0 32 = true := by quickRfl

theorem tree_ok {act : Nat → Nat → Nat} {ng root wv n : Nat} {T : STree}
    (hcov : n ≤ T.C * T.B)
    (h : chunksK act ng root T.tab n wv T.wl T.wp T.B 0 T.C = true) : T.OK act ng root wv n :=
  ⟨hcov, fun c hc => by simpa using chunks_spec h c hc⟩

end CertificateChecks.KernelCo1M

end
