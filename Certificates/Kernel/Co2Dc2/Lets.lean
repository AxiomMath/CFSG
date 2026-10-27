module

public import Certificates.Data.Kernel.Co2Dc2.Defs
public import Certificates.Kernel.Sporadic.Co2Inv.Gens
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Co2Dc2

@[expose] def sOK (j : Nat) : Bool :=
  (List.range 2300).all fun p => Nat.beq (L j p)
    (P (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (CertificateChecks.KernelSpor.Co2Inv.PT j) (Q p)))

@[expose] def aOK (k : Nat) : Bool :=
  (List.range 2300).all fun p => Nat.beq (L (6 + k) p)
    (P (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (CertificateChecks.KernelSporSch.Co2M.AP k) (Q p)))

end CFSG.KD.Co2Dc2

#kss_each CFSG.KD.Co2Dc2.LS CFSG.KD.Co2Dc2.sOK 5

#kss_each CFSG.KD.Co2Dc2.LA CFSG.KD.Co2Dc2.aOK 2

namespace CFSG.KD.Co2Dc2

theorem lets_S (hQ : ∀ p < 2300, Q p < 2300) : ∀ j < 5, ∀ p < 2300,
    L j p = P ((CFSG.Sporadic.Co2Inv.genPermWith CFSG.Sporadic.Co2Cert.co2PosTable j)[Q p]!) := by
  intro j hj p hp
  rw [CertificateChecks.KernelSpor.Co2Inv.genPerm_eq hj,
    CertificateChecks.KernelSpor.Co2Inv.unpack_get (hQ p hp)]
  have h : sOK j = true := LS.all j hj
  unfold sOK at h
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 h p (List.mem_range.2 hp))

theorem lets_ab (hQ : ∀ p < 2300, Q p < 2300) : ∀ k < 2, ∀ p < 2300,
    L (6 + k) p = P ((CFSG.Sporadic.Co2Cert.co2OrigArrs[k]!)[Q p]!) := by
  intro k hk p hp
  have e : CFSG.Sporadic.Co2Cert.co2OrigArrs[k]! = CFSG.Sporadic.Co2Schreier.aArrs[k]! := rfl
  rw [e, CertificateChecks.KernelSporSch.Co2M.aArrs_get hk,
    CertificateChecks.KernelSpor.Co2Inv.unpack_get (hQ p hp)]
  have h : aOK k = true := LA.all k hk
  unfold aOK at h
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 h p (List.mem_range.2 hp))

end CFSG.KD.Co2Dc2

end
