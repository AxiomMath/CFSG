module

public import CFSG.Quasithin.Recognition.M22UniqueData
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import CFSG.Quasithin.Vol2.Ch5Sec2M23L34DataInputs
public import Certificates.Certificate7058

public section

namespace CFSG.Quasithin.H13

open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem hex01_mem : ∀ h ∈ m22Hex01L, h.toFinset ∈ hexadList :=
  Certificates.certificate7058.1

theorem hex01_zero_one : ∀ h ∈ m22Hex01L, (0 : Fin 22) ∈ h ∧ (1 : Fin 22) ∈ h := by decide

theorem hex01_cover : ∀ x : Fin 22, x ≠ 0 → x ≠ 1 → ∃ h ∈ m22Hex01L, x ∈ h := by decide

theorem count_kernel_point : m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
    ∀ h ∈ m22Hex01L, ∀ p ∈ h, σ p ∈ h) = 16 :=
  Certificates.certificate7058.2.1

theorem count_kernel_hexad :
    m22Count (fun σ => ∀ p ∈ m22HexadL, σ p = p) = 16 :=
  Certificates.certificate7058.2.2.1

theorem count_two_hexads :
    ∀ h ∈ m22Hex01Others, m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
    (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ ∀ p ∈ h, σ p ∈ h) = 48 :=
  Certificates.certificate7058.2.2.2

end CFSG.Quasithin.H13
