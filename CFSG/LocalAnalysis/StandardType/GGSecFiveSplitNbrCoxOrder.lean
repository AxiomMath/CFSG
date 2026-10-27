module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
import CFSG.LocalAnalysis.StandardType.GGKGPosRootPairs
import CFSG.LocalAnalysis.StandardType.GGWeylCartan

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem

private theorem conj_simple_sq {ι : Type} (M : CoxeterMatrix ι) (w : M.Group) (i : ι) :
    (w * M.simple i * w⁻¹) ^ 2 = 1 := by
  rw [conj_pow, show M.simple i ^ 2 = 1 from M.toCoxeterSystem.simple_sq i, mul_one,
    mul_inv_cancel]

theorem ggCoxRefl_mul_orderOf_le_three {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    (hM : GGIsWeylMatrix M) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {r r' : MulAut ↥Bs}
    (hr : r ∈ ggCoxRefl M e) (hr' : r' ∈ ggCoxRefl M e) :
    (r * r') ^ 2 = 1 ∨ (r * r') ^ 3 = 1 := by
  haveI : Finite ι := ggIsWeylMatrix_finite hM
  haveI : Fintype ι := Fintype.ofFinite ι
  classical
  obtain ⟨C, hC, -, rfl⟩ := ggWeylCartan hM hle3
  obtain ⟨w, i, rfl⟩ := hr
  obtain ⟨w', j, rfl⟩ := hr'
  let φ : (coxeterMatrix hC).Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
  have hφ : ∀ x, ((e x : ↥A) : MulAut ↥Bs) = φ x := fun _ => rfl
  rw [hφ, hφ, ← map_mul, ← map_pow, ← map_pow]
  by_cases hc : Commute (w * (coxeterMatrix hC).simple i * w⁻¹)
      (w' * (coxeterMatrix hC).simple j * w'⁻¹)
  · left
    rw [hc.mul_pow, conj_simple_sq, conj_simple_sq, mul_one, map_one]
  · right
    rw [ggWeyl_refl_order3 hC (ggSimplyLacedConnected_of_weyl hM hle3) w w' i j hc, map_one]

end CFSG.StandardType

end
