module

public import Certificates.Data.TabCo1ThreeMoore
public meta import Certificates.Data.TabCo1ThreeMoore
public import Certificates.Kernel.Co1ThreeK.MooreK
public import Certificates.Kernel.Co1ThreeK.LettersEq
public import Certificates.Kernel.Co1B.Cent2045
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Certificates.Kernel.SporSch.Co1StabSound
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.KC.Co1Moore
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeMoore

theorem one_unpack : one () = unpack 24 24 CFSG.KC.Co1B.oneK := by
  rw [CFSG.KC.Co1B.one_eq, unpackR_eq_unpack]

theorem beq_unpackW (A B : Nat) :
    (unpack 24 24 A == unpack 24 24 B) = CFSG.KC.Co1B.eqK A B := by
  rw [← unpackR_eq_unpack, ← unpackR_eq_unpack]
  exact CFSG.KC.Co1B.beq_unpack A B

theorem pow_unpackW (X : Nat) :
    ∀ e : Nat, pow (unpack 24 24 X) e = unpack 24 24 (CFSG.KC.Co1B.powWK X e)
  | 0 => one_unpack
  | e + 1 => by
    have h : CFSG.KC.Co1B.powWK X (e + 1) = CFSG.KC.Co1B.mulWK (CFSG.KC.Co1B.powWK X e) X :=
      CFSG.KC.F2W.strictN_eq _ _
    rw [pow, pow_unpackW X e, mul_unpackW, h]

theorem nd_unpack {M : Nat → Nat} {N : Nat} {L : List Rows} {b : Bool} (i : Nat) :
    nd ((List.range N).map (fun k => unpack 24 24 (M k)), L, b) i = unpack 24 24 (ndK M N i) := by
  unfold nd ndK
  dsimp only
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_range]
  · rename_i h
    rw [List.getD_eq_default _ _ (by simpa using h), one_unpack]

theorem moore_of {M MI : Nat → Nat} {X : Nat}
    (hD : kDag ext = ((List.range 94).map (fun k => unpack 24 24 (M k)),
      (List.range 94).map (fun k => unpack 24 24 (MI k)), true))
    (hX : rootRows3D () = unpack 24 24 X) (h : mooreK (fun j => ndK M 94 (87 + j)) X = true) :
    mooreCheck () = true := by
  unfold mooreCheck
  rw [hD, hX]
  unfold mooreK at h
  simp only [nd_unpack, mul_unpackW, pow_unpackW, one_unpack, beq_unpackW, bne,
    StabL.wf_unpack', Bool.true_and, Bool.and_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h ⊢
  exact h

theorem KM_base : [aR, bR] = (List.range 2).map fun i => unpack 24 24 (KM.M i) := by
  have h := kMB
  simp only [Bool.and_eq_true] at h
  have e0 : KM.M 0 = CertificateChecks.KernelSporSch.Co1Packed.PA :=
    (Nat.eq_of_beq_eq_true h.1).trans (Nat.eq_of_beq_eq_true CertificateChecks.KernelCo1B.Cent2045.kb0)
  have e1 : KM.M 1 = CertificateChecks.KernelSporSch.Co1Packed.PB :=
    (Nat.eq_of_beq_eq_true h.2).trans (Nat.eq_of_beq_eq_true CertificateChecks.KernelCo1B.Cent2045.kb1)
  have hr : List.range 2 = [0, 1] := rfl
  rw [hr, List.map_cons, List.map_cons, List.map_nil, e0, e1,
    ← CertificateChecks.KernelSporSch.Co1Packed.aR_u, ← CertificateChecks.KernelSporSch.Co1Packed.bR_u]

theorem kDagM_eq : kDag ext = ((List.range 94).map fun i => unpack 24 24 (KM.M i),
    (List.range 94).map fun i => unpack 24 24 (KM.MI i), true) := by
  rw [kDag, ← kMW]
  exact dagWK_sound KM_base kKM

theorem rootRows3D_eq : rootRows3D () = unpack 24 24 (R.M 2) := by
  unfold rootRows3D
  exact rootRows_eq (by decide)

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeMoore in
theorem c17331 : mooreCheck () = true := moore_of kDagM_eq rootRows3D_eq kM

end CertificateChecks.KernelCo1ThreeK

end
