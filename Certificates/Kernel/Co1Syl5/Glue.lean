module

public import Certificates.Kernel.Co1Syl5.Checks
public import Certificates.Kernel.Co1B.Iota
public import Certificates.Kernel.SporSch.Co1.Packed
public import CFSG.Certificates.Kernel.SporSch.Co1StabSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.RankThree.PartOne.SPOR.Co1SylowGenData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Syl5

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.RankThree.PartOne.SPOR
open CertificateChecks.KernelSporSch.Co1Packed
open CFSG.KC.Co1B (powWK mulWK oneK)

theorem base_eq : co1PlaneBase = (List.range 4).map fun i => unpack 24 24 (S.M i) := by
  have h := kB
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have ha : PA = CFSG.KD.Co1B.SA := rfl
  have hb : PB = CFSG.KD.Co1B.SB := rfl
  unfold co1PlaneBase
  rw [aR_u, bR_u, CertificateChecks.KernelCo1B.iotaA_eq, CertificateChecks.KernelCo1B.iotaC_eq,
    unpackR_eq_unpack, unpackR_eq_unpack, ha, hb, ← Nat.eq_of_beq_eq_true h0,
    ← Nat.eq_of_beq_eq_true h1, ← Nat.eq_of_beq_eq_true h2, ← Nat.eq_of_beq_eq_true h3]
  rfl

theorem rows_getD {N : Nat} {M : Nat → Nat} {j : Nat} (hj : j < N) :
    ((List.range N).map fun i => unpack 24 24 (M i)).getD j one = unpack 24 24 (M j) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

theorem one_u : one = unpack 24 24 oneK :=
  CFSG.KC.Co1B.one_eq.trans (unpackR_eq_unpack _)

theorem pow_u (M : Nat) : ∀ e : Nat, pow (unpack 24 24 M) e = unpack 24 24 (powWK M e)
  | 0 => by
    have h : powWK M 0 = oneK := rfl
    rw [h]
    exact one_u
  | e + 1 => by
    have h : powWK M (e + 1) = mulWK (powWK M e) M := CFSG.KC.F2W.strictN_eq _ _
    rw [pow, pow_u M e, mul_unpackW, h]

theorem hN : S.N = 42 := Nat.eq_of_beq_eq_true kN

theorem dag_eq : dag co1PlaneBase co1SylowDerivs =
    ((List.range S.N).map fun i => unpack 24 24 (S.M i),
      (List.range S.N).map fun i => unpack 24 24 (S.MI i), true) :=
  dagIK_sound base_eq kD

theorem check : co1SylowGenOK co1SylowDerivs 41 39 = true := by
  unfold co1SylowGenOK
  rw [dag_eq]
  dsimp only
  rw [rows_getD (by rw [hN]; decide), rows_getD (by rw [hN]; decide), pow_u, pow_u,
    CFSG.KC.Co1B.one_eq, ← unpackR_eq_unpack, ← unpackR_eq_unpack, CFSG.KC.Co1B.beq_unpack,
    CFSG.KC.Co1B.beq_unpack]
  exact kP

end CertificateChecks.KernelCo1Syl5

end
