module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCF4Cent
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCF4Comp
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCSplit

public section

namespace CFSG.StandardType.TBCF4

open CFSG.Blueprint.Chevalley

section Core


theorem ggTBCReflCore_F4Two {K : Type} [Field K] [Finite K] [CharP K 2]
    [Finite ↥(adjointGroup .F4 K)] (hK : Nat.card K = 2) :
    GGTBCReflCore ↥(adjointGroup .F4 K) 4 := by
  intro H hH hcard d hdH hd1 J hJ φ hφ hφr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hH.2 d hdH) hd1
  obtain ⟨hAB, hdec⟩ := ggTBC_F4Two_comp_split hK hd3 hJ
  have hHC : H ≤ Subgroup.centralizer {d} := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hH.1.is_comm.comm ⟨h, hh⟩ ⟨d, hdH⟩))
  refine ggTBC_refl_split (C := Subgroup.centralizer {d}) (A := J)
    (B := Subgroup.centralizer {d} ⊓ Subgroup.centralizer (J : Set ↥(adjointGroup .F4 K)))
    (Ω := ⊤) hH hHC hJ.1 inf_le_left
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 a ha) hAB hdec
    (fun g _ hg => ggTBC_F4Two_centralizer_le hK hH hcard
      (Subgroup.mem_centralizer_iff.mpr fun h hh => (hg h hh).symm))
    le_top (Or.inl ⟨le_rfl, inf_le_right⟩) (by rwa [top_inf_eq]) hφr

end Core

end CFSG.StandardType.TBCF4

end
