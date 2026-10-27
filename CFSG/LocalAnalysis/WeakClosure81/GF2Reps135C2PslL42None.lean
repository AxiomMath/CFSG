module

public import Certificates.Certificate705102

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native

theorem w135c2_psl_l42_no_irred {d : ℕ} (hd : d ∈ noneDims)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = d) {ρ : SL4 →* (V ≃ₗ[ZMod 2] V)} (hirr : IsIrredGen ρ) : False :=
  Certificates.certificate705102 d hd V hV ρ hirr

end CFSG.LocalAnalysis.WeakClosure81
