module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

namespace HSRuLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]

theorem isSylowTwoOf_map [Finite G] (L S : Subgroup G) {H : Type} [Group H] [Finite H]
    (π : ↥L →* H) (hπ : Function.Surjective π) (hker : π.ker = CFSG.pCore 2 ↥L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    IsSylowTwoOf (((S ⊓ L).subgroupOf L).map π) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, h2, hidx⟩ := hsyl
  set A := (S ⊓ L).subgroupOf L with hA
  have hA2 : IsPGroup 2 ↥A :=
    IsPGroup.of_injective h2 (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).injective
  have hN2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  have hNA : CFSG.pCore 2 ↥L ≤ A := by
    have hsup : IsPGroup 2 ↥(A ⊔ CFSG.pCore 2 ↥L) := IsPGroup.to_sup_of_normal_right hA2 hN2
    let S' : Sylow 2 ↥L := hA2.toSylow hidx
    have heq : A ⊔ CFSG.pCore 2 ↥L = A := S'.is_maximal' hsup le_sup_left
    exact heq ▸ le_sup_right
  refine K1.isSylowTwoOf_top_iff.mpr ⟨?_, ?_⟩
  · exact IsPGroup.of_surjective hA2 (π.subgroupMap A) (π.subgroupMap_surjective A)
  · have hidx' : (A.map π).index = A.index := Subgroup.index_map_eq A hπ (by rw [hker]; exact hNA)
    rw [hidx']
    exact hidx

end HSRuLoc

end CFSG.Quasithin
