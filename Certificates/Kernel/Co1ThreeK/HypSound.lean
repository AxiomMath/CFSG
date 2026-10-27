
module

public import Certificates.Kernel.Co1ThreeK.Hyp
public import Certificates.Kernel.Co1ThreeK.GlueNodes
public import Certificates.Kernel.Co1ThreeK.ForestSound
public import CFSG.Certificates.Kernel.Co1Three.DualSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.Sporadic.Co1Schreier

theorem RTH_eq : CH.RT = [243, 81, 190] := by decide +kernel

section Hyp

theorem hyp_conjK {c : Nat} (h1 : 1 ≤ c) (h2 : c < 729) :
    ∃ r ∈ ([243, 81, 190] : List Nat), ∃ h : ↥GA, ∀ v, dotK 3 6 r v = 0 →
      ∃ w, dotK 3 6 c w = 0 ∧ h⁻¹ * eQ nodeK v * h = eQ nodeK w := by
  have h := kHyp
  simp only [Bool.and_eq_true] at h
  have hnorm : normK TS 3 EG NZ = true := by
    have h' := kNorm
    simp only [Bool.and_eq_true] at h'
    exact h'.2
  obtain ⟨r, hr, hh⟩ := forest_hyp (eQ nodeK) nodeK (p := 3) (n := 6) (by norm_num) h.2 h.1.1.2
    (fun x hx v => norm_conj qHypK hnorm (NF_sub x hx) (by have := NF_lt x hx; omega) v) c h1 h2
  exact ⟨r, RTH_eq ▸ hr, hh⟩

end Hyp

end CertificateChecks.KernelCo1ThreeK

end
