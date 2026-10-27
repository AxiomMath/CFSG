module

public import CFSG.RankThree.PartOne.S10.PlaneSemidirect
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

namespace PlaneRestrict

theorem evenRank_le_of_embedding {D D' K K' : Type} [Group D] [Group D'] [Group K] [Group K']
    [Finite D] [Finite D'] [Finite K] [Finite K'] {β : K →* MulAut D} {β' : K' →* MulAut D'}
    (ι : D' →* D) (f : K' →* K) (hι : Function.Injective ι) (hf : Function.Injective f)
    (h : ∀ k, ι.comp (β' k).toMonoidHom = (β (f k)).toMonoidHom.comp ι) :
    evenRank (D' ⋊[β'] K') ≤ evenRank (D ⋊[β] K) := by
  refine PlaneAux.evenRank_le_of_injective (SemidirectProduct.map ι f h) fun x y hxy => ?_
  have hl : (SemidirectProduct.map ι f h x).left = (SemidirectProduct.map ι f h y).left :=
    congrArg SemidirectProduct.left hxy
  have hr : (SemidirectProduct.map ι f h x).right = (SemidirectProduct.map ι f h y).right :=
    congrArg SemidirectProduct.right hxy
  exact SemidirectProduct.ext (hι hl) (hf hr)

theorem evenRank_restrict_le {D K : Type} [Group D] [Group K] [Finite D] [Finite K]
    (β : K →* MulAut D) (D' : Subgroup D) (h : ∀ k : K, ∀ d ∈ D', β k d ∈ D') :
    evenRank (D' ⋊[PlaneSemidirect.restrictHom β D' h] K) ≤ evenRank (D ⋊[β] K) :=
  evenRank_le_of_embedding D'.subtype (MonoidHom.id K) D'.subtype_injective Function.injective_id
    fun _ => MonoidHom.ext fun _ => rfl

theorem map_actionCommutator_subtype {B S : Type} [Group B] [Group S] [MulDistribMulAction B S]
    (X : Subgroup S) [MulDistribMulAction B X]
    (hsmul : ∀ (b : B) (x : X), ((b • x : X) : S) = b • (x : S)) :
    (actionCommutator B (⊤ : Subgroup X)).map X.subtype = actionCommutator B X := by
  unfold actionCommutator
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨h, -, a, rfl⟩, rfl⟩
    refine ⟨h, h.2, a, ?_⟩
    simp [hsmul]
  · rintro ⟨h, hh, a, rfl⟩
    refine ⟨⟨h, hh⟩⁻¹ * (a • ⟨h, hh⟩), ⟨⟨h, hh⟩, Subgroup.mem_top _, a, rfl⟩, ?_⟩
    simp [hsmul]

end PlaneRestrict

end CFSG.RankThree.PartOne
