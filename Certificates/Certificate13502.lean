module

public import Certificates.Kernel.OmegaEight.Bridge3009
public import Certificates.Kernel.OmegaEight.D4Two13502K
public import Certificates.Certificate3119

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.HardMathSupport.Solomon.Coordinator

theorem d4_ok {i : Nat} (hi : i < 4) :
    lettersK 17 (d4W.getD i []) = true ∧ cn (d4K i) = true ∧ cn (ppw (d4K i) 0) = true ∧
      cn (ppw (d4K i) 1) = true ∧ Nat.beq (pc (d4K i) (d4K i)) pid = true ∧
      allN 4 (fun j => Nat.beq (pc (d4K i) (d4K j)) (pc (d4K j) (d4K i))) = true := by
  have hk := kD4
  simp only [bAnd_iff] at hk
  have h := allN_spec hk.1 i hi
  simp only [bAnd_iff] at h
  exact h

theorem d4_arr (i : Fin 4) : i1021D4Arr i = unpack 360 9 (d4K i) := by
  have hw : i1021D4Word i = d4W.getD i [] := by fin_cases i <;> rfl
  rw [i1021D4Arr, hw]
  exact omegaW_eq (d4_ok i.isLt).1

theorem d4_pw (i : Fin 4) (e : Fin 2) :
    powArr (i1021D4Arr i) e = unpack 360 9 (ppw (d4K i) e) ∧ cn (ppw (d4K i) e) = true := by
  refine ⟨by rw [d4_arr, powArr_pc (d4_ok i.isLt).2.1], ?_⟩
  rcases e with ⟨_ | _ | e, he⟩
  · exact (d4_ok i.isLt).2.2.1
  · exact (d4_ok i.isLt).2.2.2.1
  · omega

theorem d4_prod (a : Fin 4 → Fin 2) :
    i1021D4Prod a = unpack 360 9 (d4Prod (a 0) (a 1) (a 2) (a 3)) := by
  have e : i1021D4Prod a = compA 360 (powArr (i1021D4Arr 0) (a 0)) (compA 360
      (powArr (i1021D4Arr 1) (a 1)) (compA 360 (powArr (i1021D4Arr 2) (a 2))
        (compA 360 (powArr (i1021D4Arr 3) (a 3)) (idA 360)))) := by
    simp [i1021D4Prod, List.ofFn_succ]
  obtain ⟨e0, c0⟩ := d4_pw 0 (a 0)
  obtain ⟨e1, c1⟩ := d4_pw 1 (a 1)
  obtain ⟨e2, c2⟩ := d4_pw 2 (a 2)
  obtain ⟨e3, c3⟩ := d4_pw 3 (a 3)
  rw [e, e0, e1, e2, e3, idA_eq, compA_pc c3 cn_pid, compA_pc c2 (cn_pc c3 cn_pid),
    compA_pc c1 (cn_pc c2 (cn_pc c3 cn_pid)), compA_pc c0 (cn_pc c1 (cn_pc c2 (cn_pc c3 cn_pid)))]
  rfl

theorem d4_cn (a : Fin 4 → Fin 2) : cn (d4Prod (a 0) (a 1) (a 2) (a 3)) = true :=
  cn_pc (d4_pw 0 (a 0)).2 (cn_pc (d4_pw 1 (a 1)).2 (cn_pc (d4_pw 2 (a 2)).2
    (cn_pc (d4_pw 3 (a 3)).2 cn_pid)))

theorem d4_sq_k : ∀ i : Fin 4, eqA 360 (compA 360 (i1021D4Arr i) (i1021D4Arr i)) (idA 360) = true := by
  intro i
  have h := d4_ok i.isLt
  rw [d4_arr, compA_pc h.2.1 h.2.1, idA_eq, eqA_pc (cn_pc h.2.1 h.2.1) cn_pid]
  exact h.2.2.2.2.1

theorem d4_comm_k : ∀ i j : Fin 4, commArr (i1021D4Arr i) (i1021D4Arr j) = true := by
  intro i j
  rw [d4_arr, d4_arr, commArr_pc (d4_ok i.isLt).2.1 (d4_ok j.isLt).2.1]
  exact allN_spec (d4_ok i.isLt).2.2.2.2.2 j j.isLt

theorem d4_ker_k : ∀ a : Fin 4 → Fin 2, a ≠ 0 → eqA 360 (i1021D4Prod a) (idA 360) = false := by
  intro a ha
  have hk := kD4
  simp only [bAnd_iff] at hk
  have h0 := allN_spec hk.2 (a 0) (a 0).isLt
  beta_reduce at h0
  have h1 := allN_spec h0 (a 1) (a 1).isLt
  beta_reduce at h1
  have h2 := allN_spec h1 (a 2) (a 2).isLt
  beta_reduce at h2
  have h := allN_spec h2 (a 3) (a 3).isLt
  beta_reduce at h
  have hs : Nat.beq (Nat.add (Nat.add (a 0 : Nat) (a 1)) (Nat.add (a 2 : Nat) (a 3))) 0 = false := by
    rw [Bool.eq_false_iff]
    intro hb
    have h0 := Nat.eq_of_beq_eq_true hb
    have h0' : (a 0 : Nat) + a 1 + ((a 2 : Nat) + a 3) = 0 := h0
    obtain ⟨z0, z1, z2, z3⟩ : (a 0 : Nat) = 0 ∧ (a 1 : Nat) = 0 ∧ (a 2 : Nat) = 0 ∧
        (a 3 : Nat) = 0 := by omega
    apply ha
    funext i
    fin_cases i
    · exact Fin.ext z0
    · exact Fin.ext z1
    · exact Fin.ext z2
    · exact Fin.ext z3
  rw [hs] at h
  rw [d4_prod, idA_eq, eqA_pc (d4_cn a) cn_pid]
  revert h
  cases Nat.beq (d4Prod (a 0) (a 1) (a 2) (a 3)) pid <;> simp

end CertificateChecks.KernelO8

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Solomon.Coordinator in
theorem certificate13502 : (∀ i : Fin 4, eqA 360 (compA 360 (i1021D4Arr i) (i1021D4Arr i)) (idA 360) = true) ∧
    (∀ i j : Fin 4, CFSG.EvenSmallLie.OmegaEight.commArr (i1021D4Arr i) (i1021D4Arr j) = true) ∧
    ∀ a : Fin 4 → Fin 2, a ≠ 0 → eqA 360 (i1021D4Prod a) (idA 360) = false :=
  ⟨KernelO8.d4_sq_k, KernelO8.d4_comm_k, KernelO8.d4_ker_k⟩

end Certificates
