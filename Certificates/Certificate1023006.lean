module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Foundations.Basic
public import Mathlib.GroupTheory.Sylow
public import Certificates.Certificate3120
import Certificates.Kernel.SporCovPerm.M11Glue

public section

namespace Certificates

theorem certificate1023006 : 
    ∃ S₀ : Sylow 3 ↥CFSG.Blueprint.NativeSporadic.M11,
      (∀ Y : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11,
        Subgroup.normalizer ((S₀ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11) :
            Set ↥CFSG.Blueprint.NativeSporadic.M11) ≤ Y →
          Y = Subgroup.normalizer ((S₀ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11) :
              Set ↥CFSG.Blueprint.NativeSporadic.M11) ∨ Y = ⊤) ∧
      IsPGroup 3 ↥(CFSG.generalizedFitting
        ↥(Subgroup.normalizer ((S₀ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11) :
            Set ↥CFSG.Blueprint.NativeSporadic.M11))) :=
  CFSG.KD.SporCovPerm.M11.m11_exists_sylow

end Certificates
