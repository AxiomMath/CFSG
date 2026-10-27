module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmMoves

public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module Multiplicative QuadraticMap ChoiceTwo Polynomial
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Polar

variable {K : Type} [Field K] [CharP K 2]

@[expose] def pn (c c' : K × K) : K := c.1 * c'.2 + c.2 * c'.1

theorem nrm_add (c c' : K × K) : nrm (c + c') = nrm c + nrm c' + pn c c' := by
  simp only [nrm, pn, Prod.fst_add, Prod.snd_add]
  linear_combination (c.1 * c'.1 + c.2 * c'.2) * add_self_K (1 : K)

omit [CharP K 2] in
theorem pn_one_zero (c : K × K) : pn c (1, 0) = c.2 := by simp [pn]

omit [CharP K 2] in
theorem pn_zero_one (c : K × K) : pn c (0, 1) = c.1 := by simp [pn]

omit [CharP K 2] in
theorem pn_zero_right (c : K × K) : pn c 0 = 0 := by simp [pn]

omit [CharP K 2] in
theorem pn_zero_left (c : K × K) : pn 0 c = 0 := by simp [pn]

omit [CharP K 2] in
theorem eq_zero_of_pn (c : K × K) (h : ∀ c', pn c c' = 0) : c = 0 :=
  Prod.ext (by rw [← pn_zero_one c]; exact h _) (by rw [← pn_one_zero c]; exact h _)

end Polar

namespace OmCoord

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} (C : OmCoord K Q A)

theorem polar_Φ (d d' : Fin C.s → K × K) (x x' : C.W0) :
    polar Q (C.Φ (d, x)) (C.Φ (d', x')) = (∑ i, pn (d i) (d' i)) + polar Q (x : V) (x' : V) := by
  have h : C.Φ (d, x) + C.Φ (d', x') = C.Φ (d + d', x + x') := by
    rw [← map_add, Prod.mk_add_mk]
  rw [QuadraticMap.polar, h, C.form, C.form, C.form]
  simp only [Pi.add_apply, nrm_add, Finset.sum_add_distrib, Submodule.coe_add, QuadraticMap.polar]
  ring

theorem coord_eq_zero_of_perp {d : Fin C.s → K × K} {x : C.W0} {i : Fin C.s}
    (h : ∀ c, polar Q (C.Φ (d, x)) (C.Φ (Pi.single i c, 0)) = 0) : d i = 0 := by
  refine eq_zero_of_pn _ fun c => ?_
  have h1 := h c
  rw [polar_Φ] at h1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), Finset.sum_eq_zero, zero_add,
    Pi.single_eq_same] at h1
  · simpa using h1
  · intro l hl
    rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hl), pn_zero_right]

theorem polar_single (d : Fin C.s → K × K) (x : C.W0) (i : Fin C.s) (c : K × K) :
    polar Q (C.Φ (d, x)) (C.Φ (Pi.single i c, 0)) = pn (d i) c := by
  rw [polar_Φ, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), Finset.sum_eq_zero, zero_add,
    Pi.single_eq_same]
  · simp
  · intro l hl
    rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hl), pn_zero_right]

theorem tor_Φ (f : Fin C.s → ZMod 3) (d : Fin C.s → K × K) (x : C.W0) :
    C.tor f (C.Φ (d, x)) = C.Φ (torC f d, x) := C.tor_acts f d x

theorem tor_Φ_eq_iff (β : Fin C.s → ZMod 3) (d : Fin C.s → K × K) (x : C.W0) :
    C.tor β (C.Φ (d, x)) = C.Φ (d, x) ↔ ∀ i, β i ≠ 0 → d i = 0 := by
  rw [tor_Φ, C.Φ.injective.eq_iff, Prod.mk.injEq, and_iff_left rfl]
  constructor
  · intro h i hi
    exact eq_zero_of_zpow_eq (β i) hi (d i) (congrFun h i)
  · intro h
    funext i
    by_cases hi : β i = 0
    · rw [torC_apply, hi, zpow_zero]
      rfl
    · rw [torC_apply, h i hi, map_zero]

theorem zpow_sq_add (a : ZMod 3) (ha : a ≠ 0) (c : K × K) :
    zpow a (zpow a c) + zpow a c + c = 0 := by
  rcases zpow_val_cases (K := K) a with ⟨h0, -⟩ | h1 | h2
  · exact absurd h0 ha
  · rw [h1]
    refine Prod.ext ?_ ?_
    · show c.1 + c.2 + c.2 + c.1 = 0
      linear_combination (c.1 + c.2) * add_self_K (1 : K)
    · show c.2 + (c.1 + c.2) + (c.1 + c.2) + c.2 = 0
      linear_combination (c.1 + 2 * c.2) * add_self_K (1 : K)
  · rw [h2]
    simp only [LinearEquiv.mul_apply, zL_three]
    refine Prod.ext ?_ ?_
    · show c.2 + (c.1 + c.2) + c.1 = 0
      linear_combination (c.1 + c.2) * add_self_K (1 : K)
    · show c.1 + c.2 + (c.2 + (c.1 + c.2)) + c.2 = 0
      linear_combination (c.1 + 2 * c.2) * add_self_K (1 : K)

theorem phi3_Φ_eq_zero_iff (β : Fin C.s → ZMod 3) (d : Fin C.s → K × K) (x : C.W0) :
    C.tor β (C.tor β (C.Φ (d, x))) + C.tor β (C.Φ (d, x)) + C.Φ (d, x) = 0 ↔
      x = 0 ∧ ∀ i, β i = 0 → d i = 0 := by
  simp only [tor_Φ]
  rw [← map_add, ← map_add, Prod.mk_add_mk, Prod.mk_add_mk, C.Φ.map_eq_zero_iff, Prod.mk_eq_zero]
  have hx : x + x + x = x := by rw [ChoiceTwo.add_self_eq_zero_of_charTwo (K := K), zero_add]
  rw [hx]
  constructor
  · rintro ⟨hd, rfl⟩
    refine ⟨rfl, fun i hi => ?_⟩
    have := congrFun hd i
    simp only [Pi.add_apply, torC_apply, hi, zpow_zero, Pi.zero_apply] at this
    have h3 : d i + d i + d i = d i := by
      rw [show d i + d i = 0 from Prod.ext (add_self_K _) (add_self_K _), zero_add]
    rwa [LinearEquiv.coe_one, id, id, h3] at this
  · rintro ⟨rfl, h⟩
    refine ⟨funext fun i => ?_, rfl⟩
    simp only [Pi.add_apply, torC_apply, Pi.zero_apply]
    by_cases hi : β i = 0
    · rw [h i hi, map_zero, map_zero, add_zero, add_zero]
    · exact zpow_sq_add (β i) hi (d i)

end OmCoord

end ChoiceTwoOm

end CFSG.StandardType
