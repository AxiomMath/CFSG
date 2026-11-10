module

public import Certificates.Kernel.LocalComp.HeFixBind
public import CFSG.Quasithin.Background.F7TwoInvSporHeInputs
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Chain.He7417

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.Quasithin.F7Two
open CertificateChecks.KernelLC.HeFix

noncomputable abbrev pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def commK (y yi x xi : Nat) : Nat := pc (pc y x) (pc yi xi)

@[expose] noncomputable def nonTwoK (c e f : Nat) : Bool :=
  bAnd(Nat.beq (powK 8330 14 c e) (pidn 8330 14),
    bIf(Nat.beq (powK 8330 14 c f) (pidn 8330 14), false, true))

noncomputable abbrev BA : Nat := pc (HG.F 1) (HG.F 0)

noncomputable abbrev IAB : Nat := pc G0I G1I

theorem kInv : bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (HG.F 0) G0I,
    bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (HG.F 1) G1I,
    bAnd(invEqK 8330 14 (mask 14) (8330 * 14) PT1 T1I,
    bAnd(cn G0I, bAnd(cn G1I, cn T1I))))) = true := by
  quickRfl

theorem k1 : nonTwoK (commK (HG.F 0) G0I BA IAB) 6 2 = true := by
  quickRfl

theorem k2 : nonTwoK (commK PT1 T1I (HG.F 0) G0I) 3 1 = true := by
  quickRfl

theorem k3 : nonTwoK (commK PT1 T1I BA IAB) 3 1 = true := by
  quickRfl

theorem k4 : Nat.beq (pc PU (HG.F 0)) (pc (HG.F 0) PU) = true := by
  quickRfl

theorem k5 : nonTwoK (commK PU PU BA IAB) 15 1 = true := by
  quickRfl

theorem powK_canon {p : Nat} (hp : cn p = true) (e : Nat) : cn (powK 8330 14 p e) = true :=
  canonK_powK hid hp e

theorem pc_eq {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    compA 8330 (unpack 8330 14 p) (unpack 8330 14 q) = unpack 8330 14 (pc p q) ∧
      cn (pc p q) = true :=
  ⟨compA_unpack hp hq, canonK_pcomp hp hq⟩

theorem comm_eq {y yi x xi : Array Nat} {Y YI X XI : Nat} (hy : y = unpack 8330 14 Y)
    (hyi : yi = unpack 8330 14 YI) (hx : x = unpack 8330 14 X) (hxi : xi = unpack 8330 14 XI)
    (cY : cn Y = true) (cYI : cn YI = true) (cX : cn X = true) (cXI : cn XI = true) :
    heComm y yi x xi = unpack 8330 14 (commK Y YI X XI) ∧ cn (commK Y YI X XI) = true := by
  obtain ⟨e1, c1⟩ := pc_eq cY cX
  obtain ⟨e2, c2⟩ := pc_eq cYI cXI
  obtain ⟨e3, c3⟩ := pc_eq c1 c2
  refine ⟨?_, c3⟩
  unfold heComm commK
  rw [hy, hyi, hx, hxi, e1, e2, e3]

theorem nonTwo_eq {c : Array Nat} {C : Nat} (hc : c = unpack 8330 14 C) (cC : cn C = true)
    {s m e f : Nat} (he : 2 ^ s * m = e) (hf : 2 ^ s = f) (h : nonTwoK C e f = true) :
    heNonTwo c s m = true := by
  subst he hf
  unfold nonTwoK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  unfold heNonTwo
  rw [hc, hePowA_unpack hid hidA cC, hePowA_unpack hid hidA cC, hidA,
    eqA_unpack (powK_canon cC _) hid, eqA_unpack (powK_canon cC _) hid, h1]
  cases h3 : Nat.beq (powK 8330 14 C (2 ^ s)) (pidn 8330 14)
  · rfl
  · rw [h3] at h2
    exact absurd h2 (by decide)

theorem check : heInvChk () = true := by
  obtain ⟨i0, i1, iT, cG0I, cG1I, cT1I⟩ := (by simpa only [bAnd_iff] using kInv :
    invEqK 8330 14 (mask 14) (8330 * 14) (HG.F 0) G0I = true ∧
    invEqK 8330 14 (mask 14) (8330 * 14) (HG.F 1) G1I = true ∧
    invEqK 8330 14 (mask 14) (8330 * 14) PT1 T1I = true ∧
    cn G0I = true ∧ cn G1I = true ∧ cn T1I = true)
  have ea := heGen_eq (k := 0) (by decide)
  have eb := heGen_eq (k := 1) (by decide)
  have cA : cn (HG.F 0) = true := by
    have h := kCanonG
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have cB : cn (HG.F 1) = true := by
    have h := kCanonG
    simp only [Bool.and_eq_true] at h
    exact h.1.2
  have cT := cnW.1
  have cU := cnW.2.1
  have eai : invCand 8330 (heGen 0) = unpack 8330 14 G0I := by
    rw [ea]
    exact (invEqK_sound i0).1
  have ebi : invCand 8330 (heGen 1) = unpack 8330 14 G1I := by
    rw [eb]
    exact (invEqK_sound i1).1
  have eti : invCand 8330 heT1Arr = unpack 8330 14 T1I := by
    rw [heT1_eq]
    exact (invEqK_sound iT).1
  obtain ⟨eba, cBA⟩ := pc_eq cB cA
  rw [← ea, ← eb] at eba
  obtain ⟨eiab, cIAB⟩ := pc_eq cG0I cG1I
  rw [← eai, ← ebi] at eiab
  obtain ⟨c1, cc1⟩ := comm_eq ea eai eba eiab cA cG0I cBA cIAB
  obtain ⟨c2, cc2⟩ := comm_eq heT1_eq eti ea eai cT cT1I cA cG0I
  obtain ⟨c3, cc3⟩ := comm_eq heT1_eq eti eba eiab cT cT1I cBA cIAB
  obtain ⟨c5, cc5⟩ := comm_eq heU_eq heU_eq eba eiab cU cU cBA cIAB
  have e4 : eqA 8330 (compA 8330 heUArr (heGen 0)) (compA 8330 (heGen 0) heUArr) = true := by
    rw [heU_eq, ea, (pc_eq cU cA).1, (pc_eq cA cU).1,
      eqA_unpack (pc_eq cU cA).2 (pc_eq cA cU).2]
    exact k4
  unfold heInvChk
  rw [nonTwo_eq (s := 1) (m := 3) c1 cc1 rfl rfl k1, nonTwo_eq (s := 0) (m := 3) c2 cc2 rfl rfl k2,
    nonTwo_eq (s := 0) (m := 3) c3 cc3 rfl rfl k3, e4,
    nonTwo_eq (s := 0) (m := 15) c5 cc5 rfl rfl k5]
  rfl

end CertificateChecks.KernelCo2Chain.He7417

end
