module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWPhi
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWCent
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWFrob
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Rest
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48RestZp
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseQuot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

theorem frobeniusOuter_of_automizer_at {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    (hcyc : ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁)
    (h1 : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) ≤
      ggL48H0 x U₁ ⊔ Subgroup.centralizer (Bs : Set G))
    (hW : GGL48AutomizerMetaAt p Bs x)
    (R : Subgroup G) (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hUR : U ≤ R) (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁)
    (hcent : x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁)
    (hhom : ¬ GGL48Homocyclic p U₁)
    (hidx : (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).relIndex
      (Subgroup.normalizer (U₁ : Set G)) = p)
    (hnn : ¬ ((ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).subgroupOf
      (Subgroup.normalizer (U₁ : Set G))).Normal) :
    ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1 := by
  obtain ⟨hp, hxp, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  exact exists_monoidHom_zmod_ne_one_of_not_mem_commutator' hxN hxp
    (not_mem_commutator_of_automizer hS h46 hcyc h1 hW hRp hRmax hUR hA hcent hhom hidx hnn)

end CFSG.StandardType
