module

public import Certificates.Kernel.Co1M.K64
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Sporadic.Co1.Module.Co2StabLitInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.Co1.Module.InvFam
public import CFSG.Sporadic.Co1.Module.Forms

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam CFSG.KC.SortTree
  CFSG.KC.Co1M CFSG.KC.XorSel CFSG.KC.Syl64 CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Co2Stab CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def w64 : SylW where
  R := R64
  RT := RT64
  P := P64
  SI := [18, 19, 20, 21, 22]
  GI := 23
  GJ := 24
  RS := RS64
  RST := RST64
  PS := PS64
  Q := Q64
  QI := QI64
  BASE := BASE64
  LV := LV64
  SZ := SZ64
  T := [⟨recT l0L64 6 42, 3, 12, 64, 64⟩, ⟨recT l1L64 6 35, 3, 6, 64, 1⟩]
  E := E64
  CN := CN64
  CM := CM64
  L := L64
  CL := CL64
  CLG := CLG64
  PVL := PVL64
  PP := PP64
  CP := CP64
  PVP := PVP64
  U := U64

theorem c64_beq {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem c64_conjL_length (G Gi : Nat) : ∀ E : List Nat, (conjL G Gi E).length = E.length
  | [] => rfl
  | _ :: E => congrArg Nat.succ (c64_conjL_length G Gi E)

theorem c64_lenL : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (c64_lenL L)

theorem inO64_eq : inO64 = fun w =>
    orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
  funext fun w => cm_orb_inPts w

theorem c64_one {act : Nat → Nat → Nat} {ng root wv n : Nat} {T : STree} (hcov : n ≤ T.C * T.B)
    (h : chunksK act ng root T.tab n wv T.wl T.wp T.B 0 T.C = true) : T.OK act ng root wv n :=
  ⟨hcov, fun c hc => by simpa using (allN_iff _ _).1 h c hc⟩

theorem w64_prog : progK 24 R64 P64 2 = true := by quickRfl

theorem w64_progS : progK 24 RS64 PS64 5 = true := by quickRfl

theorem w64_small : andB (Nat.beq (getL 0 R64 0) CertificateChecks.KernelCo1Cover.R0)
    (andB (Nat.beq (getL 0 R64 1) CertificateChecks.KernelCo1Cover.R1)
    (andB (allN (lenL R64) (fun i => Nat.beq (trK 24 (getL 0 R64 i)) (getL 0 RT64 i)))
    (andB (bndK (lenL R64) [23, 24, 18, 19, 20, 21, 22])
    (andB (fixAllK RT64 [23, 18, 19, 20, 21, 22] [2])
    (andB (Nat.beq (mulF 24 (getL 0 R64 23) (getL 0 R64 24)) (idF 24))
    (andB (allN 5 (fun k => Nat.beq (getL 0 RS64 k) (getL 0 R64 (getL 0 [18, 19, 20, 21, 22] k))))
    (andB (allN (lenL RS64) (fun i => Nat.beq (trK 24 (getL 0 RS64 i)) (getL 0 RST64 i)))
    (andB (Nat.beq (mulF 24 Q64 QI64) (idF 24)) (andB (Nat.beq (mulF 24 QI64 Q64) (idF 24))
    (andB (allN 5 (fun k => uniK (mulF 24 (mulF 24 Q64 (getL 0 RS64 k)) QI64)))
    (andB (bndK (lenL RS64) LV64.flatten) (andB (bndK (2 ^ 24) BASE64)
    (andB (fixAllK RST64 (LV64.getD 0 []) (BASE64.take 0))
      (fixAllK RST64 (LV64.getD 1 []) (BASE64.take 1))))))))))))))) = true := by quickRfl

theorem ok64 : SylOK w64 := by
  obtain ⟨a0, r⟩ := andB_true_iff.1 w64_small
  obtain ⟨a1, r⟩ := andB_true_iff.1 r
  obtain ⟨tr, r⟩ := andB_true_iff.1 r
  obtain ⟨ix, r⟩ := andB_true_iff.1 r
  obtain ⟨fx, r⟩ := andB_true_iff.1 r
  obtain ⟨gi, r⟩ := andB_true_iff.1 r
  obtain ⟨sd, r⟩ := andB_true_iff.1 r
  obtain ⟨trS, r⟩ := andB_true_iff.1 r
  obtain ⟨q1, r⟩ := andB_true_iff.1 r
  obtain ⟨q2, r⟩ := andB_true_iff.1 r
  obtain ⟨un, r⟩ := andB_true_iff.1 r
  obtain ⟨ixS, r⟩ := andB_true_iff.1 r
  obtain ⟨bs, r⟩ := andB_true_iff.1 r
  obtain ⟨f0, f1⟩ := andB_true_iff.1 r
  obtain ⟨pl, pp⟩ := andB_true_iff.1 k64_piv
  exact {
    rA := by
      rw [CertificateChecks.KernelCo1Cover.rowsA_eq, ← c64_beq a0]
      rfl
    rB := by
      rw [CertificateChecks.KernelCo1Cover.rowsB_eq, ← c64_beq a1]
      rfl
    prog := w64_prog
    tr := tr
    lenSI := rfl
    idx := ix
    fix := fx
    ginv := c64_beq gi
    seed := sd
    progS := w64_progS
    trS := trS
    flag := ⟨c64_beq q1, c64_beq q2⟩
    uni := un
    lenLV := rfl
    idxS := ixS
    base := bs
    cfix := fun j hj => by
      have hj' : j < 2 := hj
      interval_cases j
      · exact f0
      · exact f1
    tree := fun j hj => by
      have hj' : j < 2 := hj
      interval_cases j
      · exact c64_one (by decide) k64_l0
      · exact c64_one (by decide) k64_l1
    prod := by decide
    cn := k64_cn
    cm := fun k hk => by
      interval_cases k
      · exact k64_cm0
      · exact k64_cm1
      · exact k64_cm2
      · exact k64_cm3
      · exact k64_cm4
    cl := k64_cl
    clg := k64_clg
    cp := k64_cp
    pvl := pl
    pvp := pp
    dim := by
      have h := Nat.le_of_ble_eq_true k64_len
      change E64.length + (conjL (getL 0 R64 23) (getL 0 R64 24) E64).length ≤
        PP64.length + L64.length
      rw [c64_conjL_length]
      rw [c64_lenL, c64_lenL, c64_lenL] at h
      exact h
    wit := by
      rw [inO64_eq]
      exact k64_wit }

end CertificateChecks.KernelCo1M

end
