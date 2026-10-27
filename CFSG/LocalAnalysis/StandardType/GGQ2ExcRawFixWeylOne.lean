module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawFixWeylOneCheck

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

theorem FixWeylOne.allOK_eq_true : FixWeylOne.allOK = true := by
  decide +kernel

theorem mem_weyl_one_of_occurs {U : Submodule (ZMod 3) (V 1)} {c : Finset (Root 1)}
    (hc : occurs 1 U c) {g : V 1 ≃ₗ[ZMod 3] V 1} (hg : g ∈ ambientNormalizer 1)
    (hfix : ∀ v ∈ cent 1 c, g v = v) : g ∈ weyl 1 c :=
  mem_weyl_of_fixWeylCert hc hg (FixWeylOne.fixWeylCert_of_allOK FixWeylOne.allOK_eq_true hg)
    hfix

theorem mem_weyl_one_of_fix_cent {c : Finset (Root 1)} (hc : admissible 1 c)
    {g : V 1 ≃ₗ[ZMod 3] V 1} (hg : g ∈ ambientNormalizer 1) (hfix : ∀ v ∈ cent 1 c, g v = v) :
    g ∈ weyl 1 c :=
  let ⟨_, hU⟩ := hc.1
  mem_weyl_one_of_occurs hU hg hfix

end CFSG.StandardType.GGQ2Frame.ExcRaw
