module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

@[expose] public section

open LinearMap (BilinForm)
open Module

namespace LinearMap

namespace BilinForm

open Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_inf_orthogonal_of_restrict_nondegenerate (B : BilinForm K V)
    {W U : Submodule K V} (hUW : U ≤ W) (hW : (B.restrict W).Nondegenerate) :
    finrank K ↥(W ⊓ B.orthogonal U) = finrank K W - finrank K U := by
  have hmap : ((B.restrict W).orthogonal (U.comap W.subtype)).map W.subtype =
      W ⊓ B.orthogonal U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun u hu => hy ⟨u, hUW hu⟩ hu⟩
    · rintro ⟨hxW, hxU⟩
      exact ⟨⟨x, hxW⟩, fun n hn => hxU n hn, rfl⟩
  rw [← hmap, Submodule.finrank_map_subtype_eq,
    finrank_orthogonal hW (U.comap W.subtype),
    (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq]

end BilinForm

end LinearMap

end
