module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def ev (s : Fin 5) : Fin 5 → K := Pi.single s 1

@[expose] def wvec (ι : HypIndex 2 1 ≃ Fin 5) (u c : K) : HypIndex 2 1 → (Fin 5 → K)
  | .inl a => ev (ι (.inl a)) + u • ev (ι (.inr (.inr a)))
  | .inr (.inl k) => ev (ι (.inr (.inl k)))
  | .inr (.inr a) => (1 + c) • ev (ι (.inl a)) + (c * u) • ev (ι (.inr (.inr a)))

@[expose] def wmat (ι : HypIndex 2 1 ≃ Fin 5) (u c : K) : Matrix (Fin 5) (HypIndex 2 1) K :=
  Matrix.of fun t x => wvec ι u c x t

theorem stdHermForm_ev (ι : HypIndex 2 1 ≃ Fin 5) (x y : HypIndex 2 1) :
    stdHermForm h 5 (ev (ι x)) (ev (ι y)) = if x = y then 1 else 0 := by
  rw [stdHermForm_apply]
  simp only [ev, Pi.single_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · have hyx : y ≠ x := Ne.symm hxy
    simp [hxy, hyx]

theorem stdHermForm_wvec (ι : HypIndex 2 1 ≃ Fin 5) {u c : K} (hu : h.bar u * u = -1)
    (hc : c + h.bar c = -1) (x y : HypIndex 2 1) :
    stdHermForm h 5 (wvec ι u c x) (wvec ι u c y) = hypGram 2 1 K x y := by
  rcases x with i | k | i <;> rcases y with j | l | j <;>
    simp only [wvec, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, stdHermForm_ev h ι, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false,
      mul_ite, mul_one, mul_zero, add_zero, zero_add, map_mul, map_one, RingHom.id_apply,
      hypGram_inl_inl, hypGram_inl_inr_inl, hypGram_inl_inr_inr, hypGram_inr_inl_inl,
      hypGram_inr_inl_inr_inl, hypGram_inr_inl_inr_inr, hypGram_inr_inr_inl,
      hypGram_inr_inr_inr_inl, hypGram_inr_inr_inr_inr] <;>
    split_ifs <;>
    first | linear_combination | linear_combination hu | linear_combination c * hu |
      linear_combination h.bar c * hu | linear_combination hc + c * h.bar c * hu

theorem isHypTransport_wmat (ι : HypIndex 2 1 ≃ Fin 5) {u c : K} (hu : h.bar u * u = -1)
    (hc : c + h.bar c = -1) : IsHypTransport (r := 2) (ε := 1) h (wmat ι u c) := by
  ext x y
  rw [← stdHermForm_wvec h ι hu hc x y, stdHermForm_apply, mul_apply]
  rfl

end CFSG.RankThree.PartOne.U5K.Kf
