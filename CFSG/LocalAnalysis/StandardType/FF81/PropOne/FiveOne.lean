module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.FiveOneFusion
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.FiveOneSylow

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

theorem not_sylow_le_cen_b1 {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ A : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hA : AStar b z B₂ A) (hτc : TauC z τ c)
    (hS : SylowData b B₂ A c) :
    ∀ P : Sylow 3 G, ¬ ((P : Subgroup G) ≤ Subgroup.centralizer ({GGFF.zs z 0} : Set G)) :=
  fun P hP => not_conj_z0 h hB₂ hA hτc hS (exists_conj_z0 h hB₂ hA hτc hS P hP)

end CFSG.StandardType.FF81.PropOne

end
