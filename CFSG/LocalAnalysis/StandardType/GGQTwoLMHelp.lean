module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeProp1010

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_x_mem_Bs {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs) : x ∈ Bs :=
  hBs.1 (CFSG.GGQ2Prime.ggThmIHyp_unpack hG).2.1

theorem qTwoLMSkel_prime_hord {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs) : orderOf x = 3 := by
  obtain ⟨hab, hxB, hx1, -⟩ := CFSG.GGQ2Prime.ggThmIHyp_unpack hG
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (hab.2 x hxB) hx1

theorem qTwoLMSkel_route_noTransvection {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G}
    {x : G} {D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hrt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) : GGNoTransvection 3 Bs :=
  hrt.1.2.2.2.1

end CFSG.StandardType.QTwo

end
