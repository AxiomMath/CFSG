module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveOpm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

section Dimension

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem finrank_range_le_seven (Tv Tw W Lm : Submodule K E) (u : E →ₗ[K] E)
    (h6 : Module.finrank K Tv = 6) (h6' : Module.finrank K Tw = 6)
    (h2 : 2 ≤ Module.finrank K ↥(Tv ⊓ Tw))
    (hS : 2 ≤ Module.finrank K ↥((Tv ⊔ Tw).map W.mkQ))
    (hu : LinearMap.range u ≤ (Tv ⊔ Tw) ⊓ W ⊓ Lm) (hnot : ¬ ((Tv ⊔ Tw) ⊓ W ≤ Lm)) :
    Module.finrank K (LinearMap.range u) ≤ 7 := by
  have hG := Submodule.finrank_sup_add_finrank_inf_eq Tv Tw
  have hSle : Module.finrank K ↥(Tv ⊔ Tw) ≤ 10 := by omega
  have hrk := LinearMap.finrank_range_add_finrank_ker (W.mkQ.comp (Tv ⊔ Tw).subtype)
  have hrange : LinearMap.range (W.mkQ.comp (Tv ⊔ Tw).subtype) = (Tv ⊔ Tw).map W.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker (W.mkQ.comp (Tv ⊔ Tw).subtype) =
      Submodule.comap (Tv ⊔ Tw).subtype W := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hkerdim : Module.finrank K ↥(Submodule.comap (Tv ⊔ Tw).subtype W) =
      Module.finrank K ↥((Tv ⊔ Tw) ⊓ W) := by
    rw [← Submodule.map_comap_subtype (Tv ⊔ Tw) W, Submodule.finrank_map_subtype_eq]
  rw [hrange, hker, hkerdim] at hrk
  have hWle : Module.finrank K ↥((Tv ⊔ Tw) ⊓ W) ≤ 8 := by omega
  have hlt : (Tv ⊔ Tw) ⊓ W ⊓ Lm < (Tv ⊔ Tw) ⊓ W :=
    lt_of_le_of_ne inf_le_left (fun h => hnot (inf_eq_left.1 h))
  have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
  have hfin : Module.finrank K ↥((Tv ⊔ Tw) ⊓ W ⊓ Lm) ≤ 7 := by omega
  have hmono := Submodule.finrank_mono hu
  omega

theorem two_mul_finrank_le_of_isotropic (B : LinearMap.BilinForm K E) (hnd : B.Nondegenerate)
    (hrefl : B.IsRefl) (W : Submodule K E) (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    2 * Module.finrank K W ≤ Module.finrank K E := by
  have hle : W ≤ B.orthogonal W := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 (fun n hn => hW n hn x hx)
  have h1 : Module.finrank K W ≤ Module.finrank K (B.orthogonal W) := Submodule.finrank_mono hle
  have h2 : Module.finrank K (B.orthogonal W) = Module.finrank K E - Module.finrank K W :=
    LinearMap.BilinForm.finrank_orthogonal hnd W
  omega

end Dimension

end CFSG.RankThree.GF2n.Stroth80
