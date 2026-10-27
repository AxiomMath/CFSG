module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
public import CFSG.Sporadic.Mathieu.M22
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Sporadic.Mathieu.M22
public import CFSG.Quasithin.Recognition.M22UniqueDataInputs
public import Certificates.Certificate7041

public section

namespace CFSG.Quasithin.Asc94

open CFSG.ComponentClassification.WittDesign CFSG.Sporadic.Mathieu

theorem mem_m22HexadL_iff (p : Fin 22) : p ∈ m22HexadL ↔ p ∈ m22HexadF := by
  simp [m22HexadL, m22HexadF]

theorem m22Fix_spec :
    ((m22Fix2 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix2 : Equiv.Perm (Fin 22)) 1 = 2 ∧
      PresHex m22Fix2) ∧
    ((m22Fix9 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix9 : Equiv.Perm (Fin 22)) 1 = 9 ∧
      PresHex m22Fix9) ∧
    ((m22Fix17 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix17 : Equiv.Perm (Fin 22)) 1 = 17 ∧
      PresHex m22Fix17) ∧
    ((m22Fix19 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix19 : Equiv.Perm (Fin 22)) 1 = 19 ∧
      PresHex m22Fix19) :=
  Certificates.certificate7041.2.2.2.1

theorem count_two_point :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1) = 960 :=
  Certificates.certificate7041.2.2.2.2.2.2.2.1

theorem count_two_point_hexad :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
    ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) = 192 :=
  Certificates.certificate7041.2.2.2.2.2.2.2.2.1

end CFSG.Quasithin.Asc94
