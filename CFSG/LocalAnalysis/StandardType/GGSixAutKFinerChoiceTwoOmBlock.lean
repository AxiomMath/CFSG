module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmCent

public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module Multiplicative QuadraticMap ChoiceTwo Polynomial
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace OmCoord

section Blocks

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} (C : OmCoord K Q A)

omit [Finite K] [FiniteDimensional K V] in
theorem tor_mem_O (f : Fin C.s → ZMod 3) : C.tor f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
  rw [C.tor_acts, C.form, C.form]
  simp only [torC_apply, nrm_zpow]

omit [Finite K] [FiniteDimensional K V] in
theorem tor_pow_three (f : Fin C.s → ZMod 3) : C.tor f ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one, ← C.tor_add, ← C.tor_add,
    show f + f + f = 0 from funext fun i => by
      simp only [Pi.add_apply, Pi.zero_apply]
      have : (3 : ZMod 3) = 0 := rfl
      linear_combination f i * this, C.tor_zero]

omit [Finite K] [FiniteDimensional K V] in
theorem tor_comm (f f' : Fin C.s → ZMod 3) : C.tor f * C.tor f' = C.tor f' * C.tor f := by
  rw [← C.tor_add, ← C.tor_add, add_comm]

omit [Finite K] [FiniteDimensional K V] in
theorem oddOrderIsometry (hQ : (polarBilin Q).Nondegenerate) (β : Fin C.s → ZMod 3) :
    OddOrderIsometry Q 3 (C.tor β) :=
  ⟨C.tor_mem_O β, C.tor_pow_three β, by
    have h : ((3 : ℕ) : K) = 1 := by
      have := add_self_K (1 : K)
      push_cast
      linear_combination this
    rw [h]
    exact one_ne_zero, fun v hv => hQ.1 v fun w => hv w⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem aeval_phi3_apply' (T : Module.End K V) (v : V) :
    aeval T (phi3 K) v = T (T v) + T v + v := by
  simp [phi3, _root_.sq]

omit [Finite K] [FiniteDimensional K V] in
theorem toLinearMap_pow_three (β : Fin C.s → ZMod 3) :
    (C.tor β).toLinearMap ^ 3 = 1 := by
  have h := C.tor_pow_three β
  ext v
  have := congrArg (fun g : V ≃ₗ[K] V => g v) h
  simpa [pow_succ, LinearEquiv.mul_apply] using this

variable (hK : Nat.card K = 2)
include hK

theorem mem_fixedBlock_of {β : Fin C.s → ZMod 3} {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgc : g * C.tor β = C.tor β * g)
    (h : ∀ v, C.tor β (C.tor β v) + C.tor β v + v = 0 → g v = v) :
    g ∈ supportedBlock Q (C.tor β) (X - 1) := by
  refine mem_supportedBlock.mpr ⟨Subgroup.mem_inf.mpr ⟨hgO,
    Subgroup.mem_centralizer_singleton_iff.mpr hgc⟩, fixes_othersSpace_iff.mpr ?_⟩
  intro k hk hk1 _ v hv
  rcases primaryFactor_cases hK (C.toLinearMap_pow_three β) hk with rfl | rfl
  · exact absurd rfl hk1
  · refine h v ?_
    have := mem_primaryComponent.mp hv
    rwa [aeval_phi3_apply'] at this

theorem mem_phi3Block_of {β : Fin C.s → ZMod 3} {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgc : g * C.tor β = C.tor β * g)
    (h : ∀ v, C.tor β v = v → g v = v) :
    g ∈ supportedBlock Q (C.tor β) (phi3 K) := by
  refine mem_supportedBlock.mpr ⟨Subgroup.mem_inf.mpr ⟨hgO,
    Subgroup.mem_centralizer_singleton_iff.mpr hgc⟩, fixes_othersSpace_iff.mpr ?_⟩
  intro k hk hk1 _ v hv
  rcases primaryFactor_cases hK (C.toLinearMap_pow_three β) hk with rfl | rfl
  · refine h v ?_
    have := mem_primaryComponent.mp hv
    simp only [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero] at this
    exact this
  · exact absurd rfl hk1

theorem tor_mem_fixedBlock {β f : Fin C.s → ZMod 3} (hf : ∀ i, β i ≠ 0 → f i = 0) :
    C.tor f ∈ supportedBlock Q (C.tor β) (X - 1) := by
  refine C.mem_fixedBlock_of hK (C.tor_mem_O f) (C.tor_comm f β) fun v hv => ?_
  obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
  obtain ⟨rfl, hd⟩ := (C.phi3_Φ_eq_zero_iff β d x).mp hv
  rw [C.tor_acts]
  congr 2
  funext i
  by_cases hi : β i = 0
  · rw [torC_apply, hd i hi, map_zero]
  · rw [torC_apply, hf i hi, zpow_zero]
    rfl

theorem tor_mem_phi3Block {β f : Fin C.s → ZMod 3} (hf : ∀ i, β i = 0 → f i = 0) :
    C.tor f ∈ supportedBlock Q (C.tor β) (phi3 K) := by
  refine C.mem_phi3Block_of hK (C.tor_mem_O f) (C.tor_comm f β) fun v hv => ?_
  obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
  have hd := (C.tor_Φ_eq_iff β d x).mp hv
  rw [C.tor_acts]
  congr 2
  funext i
  by_cases hi : β i = 0
  · rw [torC_apply, hf i hi, zpow_zero]
    rfl
  · rw [torC_apply, hd i hi, map_zero]

theorem swap_mem_fixedBlock {β : Fin C.s → ZMod 3} {i j : Fin C.s} (bsw : Bool) (hi : β i = 0)
    (hj : β j = 0) : C.move (Equiv.swap i j) (swapSgn i j bsw) ∈
      supportedBlock Q (C.tor β) (X - 1) := by
  refine C.mem_fixedBlock_of hK (C.move_mem_O _ _)
    (C.swap_commute_tor bsw (by rw [hi, hj, sgnZ_zero])) fun v hv => ?_
  obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
  obtain ⟨rfl, hd⟩ := (C.phi3_Φ_eq_zero_iff β d x).mp hv
  rw [C.move_apply]
  congr 2
  funext l
  rw [monoC_apply]
  by_cases hli : l = i
  · subst hli
    rw [Equiv.swap_apply_left, hd j hj, map_zero, hd l hi]
  · by_cases hlj : l = j
    · subst hlj
      rw [Equiv.swap_apply_right, hd i hi, map_zero, hd l hj]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
      simp [swapSgn, hli, hlj, sgnC_false]

theorem swap_mem_phi3Block {β : Fin C.s → ZMod 3} {i j : Fin C.s} (bsw : Bool) (hi : β i ≠ 0)
    (hj : β j ≠ 0) (hij : β i = sgnZ bsw (β j)) :
    C.move (Equiv.swap i j) (swapSgn i j bsw) ∈ supportedBlock Q (C.tor β) (phi3 K) := by
  refine C.mem_phi3Block_of hK (C.move_mem_O _ _) (C.swap_commute_tor bsw hij) fun v hv => ?_
  obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
  have hd := (C.tor_Φ_eq_iff β d x).mp hv
  rw [C.move_apply]
  congr 2
  funext l
  rw [monoC_apply]
  by_cases hli : l = i
  · subst hli
    rw [Equiv.swap_apply_left, hd j hj, map_zero, hd l hi]
  · by_cases hlj : l = j
    · subst hlj
      rw [Equiv.swap_apply_right, hd i hi, map_zero, hd l hj]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
      simp [swapSgn, hli, hlj, sgnC_false]

end Blocks

end OmCoord

end ChoiceTwoOm

end CFSG.StandardType
