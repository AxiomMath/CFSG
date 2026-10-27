module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_zl_weyl_normalizes {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Z : Subgroup ↥L} {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup ↥L} {w : Fin 6 → ↥L}
    (hmodel : GGE6ThreeWeylModelWith Z (ggGamma L hBsN).range Φ T w) (i : Fin 6) :
    ((w i : ↥L) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  obtain ⟨-, -, -, -, hAT, -, hwAT, -⟩ := hmodel
  refine mem_normalizer_of_ggTorusWeylElt hBsN hcfg.2.1.2.2.2 ?_
  intro a ha
  obtain ⟨hT, h3⟩ := hwAT i a ha
  exact ⟨h3, fun a' ha' => hAT a' ha' _ hT⟩

end ZL

end E6Dep

end CFSG.StandardType

end
