module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M12Pinned
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12Pinned
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12Derivs
public import Certificates.Certificate2207
public import Certificates.Certificate2193
public import Certificates.Certificate2194

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th.Native

theorem m12_sylowAut_check :
    sylowAutOK 12 (toTable m12gA) (toTable m12gB) m12Derivs
      m12SylowExprs (natTbl 12 m12SylowZ) 80 95040 6 = true :=
  Certificates.certificate2207.1

theorem m12_survivors_check :
    survivorsOK 12 (toTable m12gA) (toTable m12gB) (natTbl 12 m12SylowZ)
      m12Derivs m12SylowExprs 11 6 3
      (orderTables m12Certificate 3) = true :=
  Certificates.certificate2207.2

theorem m12_sylow_pointwise_inner :
    ∀ (T : Sylow 2 NativeSporadic.M12) (α : MulAut NativeSporadic.M12),
      (∀ t ∈ (T : Subgroup NativeSporadic.M12), α t = t) →
      ∃ z : (T : Subgroup NativeSporadic.M12),
        z ∈ Subgroup.center (T : Subgroup NativeSporadic.M12) ∧
        ∀ g : NativeSporadic.M12,
          α g = (z : NativeSporadic.M12) * g * (z : NativeSporadic.M12)⁻¹ := by
  obtain ⟨ha, hb, hab, hc, -⟩ := at_m12_image_pair_count
  exact sylow_pointwise_inner_of_checks (by norm_num) NativeSporadic.M12 m12_eq
    m12Certificate m12Certificate_check m12Certificate_originalSubgroup m12_card
    (by norm_num) (by norm_num) (by norm_num)
    ((Subgroup.orderOf_coe m12a).trans ha) ((Subgroup.orderOf_coe m12b).trans hb)
    ((Subgroup.orderOf_coe (m12a * m12b)).trans hab)
    ((Subgroup.orderOf_coe (m12a * m12b * m12a⁻¹ * m12b⁻¹)).trans hc) _ _ _
    80 6 m12_sylowAut_check m12_survivors_check

end CFSG.Sporadic.Schreier
