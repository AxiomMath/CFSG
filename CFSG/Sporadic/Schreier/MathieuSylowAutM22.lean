module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Monster.B.Mathieu.M22Check
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M22
public meta import CFSG.Monster.B.Mathieu.M22Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Derivs
public import Certificates.Certificate2208
public import Certificates.Certificate2195
public import Certificates.Certificate3157

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th.Native

theorem m22_sylowAut_check :
    sylowAutOK 22 (toTable m22gA) (toTable m22gB) m22Derivs
      m22SylowExprs (natTbl 22 m22SylowZ) 150 443520 7 = true :=
  Certificates.certificate2208.1

theorem m22_survivors_check :
    survivorsOK 22 (toTable m22gA) (toTable m22gB) (natTbl 22 m22SylowZ)
      m22Derivs m22SylowExprs 11 6 4
      (orderTables m22Certificate 4) = true :=
  Certificates.certificate2208.2

theorem m22_sylow_pointwise_inner :
    ∀ (T : Sylow 2 NativeSporadic.M22) (α : MulAut NativeSporadic.M22),
      (∀ t ∈ (T : Subgroup NativeSporadic.M22), α t = t) →
      ∃ z : (T : Subgroup NativeSporadic.M22),
        z ∈ Subgroup.center (T : Subgroup NativeSporadic.M22) ∧
        ∀ g : NativeSporadic.M22,
          α g = (z : NativeSporadic.M22) * g * (z : NativeSporadic.M22)⁻¹ := by
  obtain ⟨ha, hb, hab, hc, -⟩ := at_m22_image_pair_count
  exact sylow_pointwise_inner_of_checks (by norm_num) NativeSporadic.M22 m22_eq
    m22Certificate m22Certificate_check m22Certificate_originalSubgroup m22_card
    (by norm_num) (by norm_num) (by norm_num)
    ((Subgroup.orderOf_coe m22a).trans ha) ((Subgroup.orderOf_coe m22b).trans hb)
    ((Subgroup.orderOf_coe (m22a * m22b)).trans hab)
    ((Subgroup.orderOf_coe (m22a * m22b * m22a⁻¹ * m22b⁻¹)).trans hc) _ _ _
    150 7 m22_sylowAut_check m22_survivors_check

end CFSG.Sporadic.Schreier
