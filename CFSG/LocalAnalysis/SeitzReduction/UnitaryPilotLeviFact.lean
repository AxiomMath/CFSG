module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotLeviFact
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTorusBasic

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSpecialLinear_mono fixAll
  mem_fixAll fixAll_comp_of_surjective centralizerPerfectCore_eq_map_of_le)

section Torus

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] noncomputable def unitaryTorusSL (I : Finset (Fin n)) :
    Subgroup (SpecialLinearGroup (Fin n) K) :=
  ((unitaryTorusParam h I).subgroupOf (unitaryTorusParam h ∅)).map
    ((toSL h n).comp (torusDiagSU h))

theorem mem_unitaryTorusSL {I : Finset (Fin n)} {x : SpecialLinearGroup (Fin n) K} :
    x ∈ unitaryTorusSL h I ↔ ∃ c : unitaryTorusParam h (∅ : Finset (Fin n)),
      c.1 ∈ unitaryTorusParam h I ∧ toSL h n (torusDiagSU h c) = x := by
  simp only [unitaryTorusSL, mem_map, mem_subgroupOf, MonoidHom.comp_apply]

theorem coe_toSL_torusDiagSU (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    ((toSL h n (torusDiagSU h c) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => ((c.1 i : Kˣ) : K) :=
  rfl

theorem unitaryTorusSL_apply_of_ne {I : Finset (Fin n)} {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ unitaryTorusSL h I) {i j : Fin n} (hij : i ≠ j) :
    (x : Matrix (Fin n) (Fin n) K) i j = 0 := by
  obtain ⟨c, -, rfl⟩ := (mem_unitaryTorusSL h).1 hx
  rw [coe_toSL_torusDiagSU, diagonal_apply_ne _ hij]

theorem unitaryTorusSL_apply_const {I : Finset (Fin n)} {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ unitaryTorusSL h I) {i j : Fin n} (hi : i ∈ I) (hj : j ∈ I) :
    (x : Matrix (Fin n) (Fin n) K) i i = (x : Matrix (Fin n) (Fin n) K) j j := by
  obtain ⟨c, hc, rfl⟩ := (mem_unitaryTorusSL h).1 hx
  rw [coe_toSL_torusDiagSU, diagonal_apply_eq, diagonal_apply_eq, hc.2.2 i hi j hj]

theorem toSL_torusDiagSU_eq (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    toSL h n (torusDiagSU h c) =
      LinearPilot.torusDiagSL ⟨c.1, unitaryTorusParam_le_blockTorusParam h ∅ c.2⟩ :=
  rfl

theorem exists_eq_mul_of_unitaryProj_torusDiagSU_eq
    {c d : unitaryTorusParam h (∅ : Finset (Fin n))}
    (hcd : unitaryProj h n (torusDiagSU h c) = unitaryProj h n (torusDiagSU h d)) :
    ∃ s : Kˣ, ∀ i, d.1 i = s * c.1 i := by
  rw [MonoidHom.eq_iff, ker_unitaryProj, mem_unitaryScalars, ← map_inv, ← map_mul] at hcd
  obtain ⟨s, -, -, hs⟩ := hcd
  refine ⟨s⁻¹, fun i => ?_⟩
  have hi := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) hs
  simp only [coe_torusDiagSU, GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_apply_eq] at hi
  have hi' : (d⁻¹ * c).1 i = s := Units.ext hi
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply,
    inv_mul_eq_iff_eq_mul] at hi'
  rw [hi', mul_comm (d.1 i) s, inv_mul_cancel_left]

@[expose] noncomputable def unitaryBlockTorusLift {I : Finset (Fin n)}
    (d : unitaryBlockTorus h I) : unitaryTorusParam h (∅ : Finset (Fin n)) :=
  ((mem_unitaryBlockTorus h).1 d.2).choose

theorem unitaryBlockTorusLift_mem {I : Finset (Fin n)} (d : unitaryBlockTorus h I) :
    (unitaryBlockTorusLift h d).1 ∈ unitaryTorusParam h I :=
  ((mem_unitaryBlockTorus h).1 d.2).choose_spec.1

theorem unitaryProj_torusDiagSU_unitaryBlockTorusLift {I : Finset (Fin n)}
    (d : unitaryBlockTorus h I) :
    unitaryProj h n (torusDiagSU h (unitaryBlockTorusLift h d)) = d :=
  ((mem_unitaryBlockTorus h).1 d.2).choose_spec.2

theorem exists_unitaryBlockTorusLift_ne {I : Finset (Fin n)} {c : Fin n → Kˣ}
    (hc : c ∈ unitaryTorusParam h I) {i j : Fin n} (hcij : c i ≠ c j) :
    ∃ d : unitaryBlockTorus h I,
      (unitaryBlockTorusLift h d).1 i ≠ (unitaryBlockTorusLift h d).1 j := by
  set c₀ : unitaryTorusParam h (∅ : Finset (Fin n)) :=
    ⟨c, unitaryTorusParam_anti h (Finset.empty_subset I) hc⟩
  set d : unitaryBlockTorus h I := ⟨unitaryProj h n (torusDiagSU h c₀),
    unitaryProj_torusDiagSU_mem_unitaryBlockTorus h (c := c₀) hc⟩
  refine ⟨d, ?_⟩
  obtain ⟨s, hs⟩ := exists_eq_mul_of_unitaryProj_torusDiagSU_eq h (c := c₀)
    (d := unitaryBlockTorusLift h d) (unitaryProj_torusDiagSU_unitaryBlockTorusLift h d).symm
  rw [hs i, hs j]
  exact fun h' => hcij (mul_left_cancel h')

end Torus

section Conj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem toSL_torusDiagSU_apply_of_ne (c : unitaryTorusParam h (∅ : Finset (Fin n)))
    {i j : Fin n} (hij : i ≠ j) :
    ((toSL h n (torusDiagSU h c) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      0 := by
  rw [coe_toSL_torusDiagSU, diagonal_apply_ne _ hij]

@[expose] noncomputable def conjTorus (N : Finset (Fin n))
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) : MulAut (blockSpecialLinear (K := K) N) :=
  LinearPilot.conjDiagonal N (toSL h n (torusDiagSU h c))
    fun _ _ hij => toSL_torusDiagSU_apply_of_ne h c hij

theorem coe_conjTorus_apply (N : Finset (Fin n)) (c : unitaryTorusParam h (∅ : Finset (Fin n)))
    (x : blockSpecialLinear (K := K) N) :
    ((conjTorus h N c x : blockSpecialLinear (K := K) N) : SpecialLinearGroup (Fin n) K) =
      toSL h n (torusDiagSU h c) * x * (toSL h n (torusDiagSU h c))⁻¹ :=
  rfl

theorem conjTorus_eq_conjDiag (N : Finset (Fin n))
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    conjTorus h N c = LinearPilot.conjDiag (RingHom.id K) N
      ⟨c.1, unitaryTorusParam_le_blockTorusParam h ∅ c.2⟩ := by
  have hmap : Matrix.SpecialLinearGroup.map (RingHom.id K)
      (LinearPilot.torusDiagSL ⟨c.1, unitaryTorusParam_le_blockTorusParam h ∅ c.2⟩) =
      toSL h n (torusDiagSU h c) :=
    Subtype.ext (by ext i j; rfl)
  ext x
  rw [coe_conjTorus_apply, LinearPilot.coe_conjDiag_apply, hmap]

theorem perfectCore_fixAll_conjTorus [Finite K] {N I : Finset (Fin n)} (hIN : I ⊆ N)
    {ι' : Type*} (c : ι' → unitaryTorusParam h (∅ : Finset (Fin n)))
    (hc : ∀ j, (c j).1 ∈ unitaryTorusParam h I)
    (hsep : ∀ i ∈ N, ∀ k ∈ N, i ≠ k → (i ∉ I ∨ k ∉ I) → ∃ j, (c j).1 i ≠ (c j).1 k)
    (hperf : ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ =
      blockSpecialLinear I) :
    perfectCore (fixAll fun j => conjTorus h N (c j)) =
      (blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N) := by
  refine LinearPilot.perfectCore_fixAll_eq hIN _ (fun j => toSL h n (torusDiagSU h (c j)))
    (fun j x => rfl) (fun j i k hik => toSL_torusDiagSU_apply_of_ne h (c j) hik)
    (fun j i hi k hk => by
      rw [coe_toSL_torusDiagSU, diagonal_apply_eq, diagonal_apply_eq, (hc j).2.2 i hi k hk])
    (fun i hi k hk hik hIk => ?_) hperf
  obtain ⟨j, hj⟩ := hsep i hi k hk hik hIk
  refine ⟨j, ?_⟩
  rw [coe_toSL_torusDiagSU, diagonal_apply_eq, diagonal_apply_eq]
  exact fun h' => hj (Units.ext h')

include h in
theorem four_le_card_of_unitaryFieldData : 4 ≤ Nat.card K := by
  rw [h.card_eq_sq]
  calc 4 = 2 ^ 2 := rfl
    _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left h.one_lt_pow 2

include h in
theorem commutator_blockSpecialLinear_eq_of_unitaryFieldData {I : Finset (Fin n)}
    (hI : 2 ≤ I.card) :
    ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ = blockSpecialLinear I := by
  have := h.finite
  exact LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hI
    (four_le_card_of_unitaryFieldData h)

end Conj

section Even

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem exists_mem_unitaryTorusSL_ne {I : Finset (Fin n)} (hI : 2 ≤ Iᶜ.card) {i j : Fin n}
    (hij : i ≠ j) (hIJ : i ∉ I ∨ j ∉ I) :
    ∃ d ∈ unitaryTorusSL h I,
      (d : Matrix (Fin n) (Fin n) K) i i ≠ (d : Matrix (Fin n) (Fin n) K) j j := by
  obtain ⟨c, hc, hcij⟩ := exists_mem_unitaryTorusParam_ne h hI hij hIJ
  refine ⟨toSL h n (torusDiagSU h ⟨c, unitaryTorusParam_anti h (Finset.empty_subset I) hc⟩),
    (mem_unitaryTorusSL h).2 ⟨_, hc, rfl⟩, ?_⟩
  rw [coe_toSL_torusDiagSU, diagonal_apply_eq, diagonal_apply_eq]
  exact fun h' => hcij (Units.ext h')

theorem perfectCore_inf_centralizer_unitaryTorusSL {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card) :
    perfectCore (blockSpecialLinear (K := K) N ⊓
        centralizer (unitaryTorusSL h I : Set (SpecialLinearGroup (Fin n) K))) =
      blockSpecialLinear I := by
  have := h.finite
  exact LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear hIN _
    (fun d hd i j hij => unitaryTorusSL_apply_of_ne h hd hij)
    (fun d hd i hi j hj => unitaryTorusSL_apply_const h hd hi hj)
    (fun i _ j _ hij hIJ => exists_mem_unitaryTorusSL_ne h hIc hij hIJ)
    (commutator_blockSpecialLinear_eq_of_unitaryFieldData h hI2)

theorem perfectCore_fixAll_conjTorus_unitaryBlockTorusLift {N I : Finset (Fin n)}
    (hIN : I ⊆ N) (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card) :
    perfectCore (fixAll fun d : unitaryBlockTorus h I =>
        conjTorus h N (unitaryBlockTorusLift h d)) =
      (blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N) := by
  have := h.finite
  refine perfectCore_fixAll_conjTorus h hIN _ (unitaryBlockTorusLift_mem h)
    (fun i _ j _ hij hIJ => ?_) (commutator_blockSpecialLinear_eq_of_unitaryFieldData h hI2)
  obtain ⟨c, hc, hcij⟩ := exists_mem_unitaryTorusParam_ne h hIc hij hIJ
  exact exists_unitaryBlockTorusLift_ne h hc hcij

end Even

end CFSG.SeitzReduction.UnitaryPilot
