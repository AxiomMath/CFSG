module

public import CFSG.Sporadic.HNOddCore.CRec
public import Certificates.Certificate2083
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native Matrix Equiv

theorem ctuc_hn_extended_faithful_action :
    (∀ (g : JH) (i : X), jR g • i = g • i) ∧
    (∀ (r : RH) (i : X), vL ((r • i : X) : ℕ) = matR r *ᵥ vL i) ∧
    FaithfulSMul RH X ∧ cR • x0 = x0 ∧
    (∀ r : RH, r ∈ RV ↔ (∃ h ∈ HJ, r = jR h) ∨ ∃ h ∈ HJ, r = jR h * cR) ∧
    RV = HR ⊔ Subgroup.zpowers cR ∧
    (∃ θR : RV ≃* Perm (Fin 12),
      (∀ (h : JH) (hh : h ∈ HJ),
        θR ⟨jR h, (jR_mem_RV_iff h).2 hh⟩ = (thetaJ ⟨h, hh⟩ : Perm (Fin 12))) ∧
      θR ⟨cR, cR_mem_RV⟩ = swap 0 1) ∧
    ∀ i : X, ((cR • i : X) : ℕ) = cRec[(i : ℕ)]! :=
  ⟨jR_smul, vL_smul, faithful_R, cR_smul_x0, mem_RV_iff, RV_eq_sup,
    ⟨thetaR, fun _ hh => thetaR_jR hh, thetaR_cR⟩, cR_smul_eq_cRec⟩

end CFSG.Sporadic.HNOddCore
