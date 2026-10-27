module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotLeviFact
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCores

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSpecialLinear_mono fixAll
  mem_fixAll)

section Torus

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] noncomputable def unitaryTorusSU (I : Finset (Fin n)) : Subgroup (unitarySU p f K n) :=
  ((unitaryTorusParam h I).subgroupOf (unitaryTorusParam h ∅)).map (torusDiagSU h)

theorem mem_unitaryTorusSU {I : Finset (Fin n)} {x : unitarySU p f K n} :
    x ∈ unitaryTorusSU h I ↔ ∃ c : unitaryTorusParam h (∅ : Finset (Fin n)),
      c.1 ∈ unitaryTorusParam h I ∧ torusDiagSU h c = x := by
  simp only [unitaryTorusSU, mem_map, mem_subgroupOf]

theorem map_unitaryTorusSU_unitaryProj (I : Finset (Fin n)) :
    (unitaryTorusSU h I).map (unitaryProj h n) = unitaryBlockTorus h I :=
  rfl

theorem map_unitaryTorusSU_toSL (I : Finset (Fin n)) :
    (unitaryTorusSU h I).map (toSL h n) = unitaryTorusSL h I := by
  rw [unitaryTorusSU, Subgroup.map_map]
  rfl

theorem unitaryTorusSU_anti {I I' : Finset (Fin n)} (hII' : I ⊆ I') :
    unitaryTorusSU h I' ≤ unitaryTorusSU h I := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_unitaryTorusSU h).1 hx
  exact (mem_unitaryTorusSU h).2 ⟨c, unitaryTorusParam_anti h hII' hc, rfl⟩

theorem torusDiagSU_mem_normalizer_unitaryBlock (N : Finset (Fin n))
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    torusDiagSU h c ∈ normalizer (unitaryBlock h N : Set (unitarySU p f K n)) := by
  have hD := LinearPilot.mem_normalizer_blockSpecialLinear_of_diag (N := N)
    (g := toSL h n (torusDiagSU h c)) fun _ _ hij => toSL_torusDiagSU_apply_of_ne h c hij
  rw [mem_normalizer_iff] at hD ⊢
  intro x
  rw [mem_unitaryBlock_iff_toSL, mem_unitaryBlock_iff_toSL, map_mul, map_mul, map_inv]
  exact hD (toSL h n x)

@[expose] noncomputable def conjTorusSU (N : Finset (Fin n))
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) : MulAut (unitaryBlock h N) :=
  (unitaryBlock h N).normalizerMonoidHom
    ⟨torusDiagSU h c, torusDiagSU_mem_normalizer_unitaryBlock h N c⟩

theorem coe_conjTorusSU_apply (N : Finset (Fin n)) (c : unitaryTorusParam h (∅ : Finset (Fin n)))
    (x : unitaryBlock h N) :
    ((conjTorusSU h N c x : unitaryBlock h N) : unitarySU p f K n) =
      torusDiagSU h c * x * (torusDiagSU h c)⁻¹ :=
  rfl

end Torus

section Levi

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem perfectCore_unitaryBlock_inf_centralizer_of_diag {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hI2 : 2 ≤ I.card) (D : Set (unitarySU p f K n))
    (hdiag : ∀ d ∈ D, ∀ i j, i ≠ j →
      ((d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0)
    (hconst : ∀ d ∈ D, ∀ i ∈ I, ∀ j ∈ I,
      ((d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
        ((d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j)
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) → ∃ d ∈ D,
      ((d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i ≠
        ((d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I) :
    perfectCore (unitaryBlock h N ⊓ centralizer D) = unitaryBlock h I := by
  have := h.finite
  set D' : Set (SpecialLinearGroup (Fin n) K) := toSL h n '' D with hD'
  have hLevi : perfectCore (blockSpecialLinear (K := K) N ⊓ centralizer D') =
      blockSpecialLinear I :=
    LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear hIN D'
      (by rintro _ ⟨d, hd, rfl⟩; exact hdiag d hd)
      (by rintro _ ⟨d, hd, rfl⟩; exact hconst d hd)
      (fun i hi j hj hij hIJ => by
        obtain ⟨d, hd, hne⟩ := hsep i hi j hj hij hIJ
        exact ⟨toSL h n d, ⟨d, hd, rfl⟩, hne⟩)
      (commutator_blockSpecialLinear_eq_of_unitaryFieldData h hI2)
  have hmap : (unitaryBlock h N ⊓ centralizer D).map (toSL h n) ≤
      blockSpecialLinear (K := K) N ⊓ centralizer D' := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxN, hxD⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨hxN, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hxD d hd]
  apply le_antisymm
  · intro x hx
    have h1 : toSL h n x ∈ perfectCore ((unitaryBlock h N ⊓ centralizer D).map (toSL h n)) := by
      rw [← CFSG.Quasithin.map_perfectCore]
      exact mem_map_of_mem _ hx
    have h2 := perfectCore_mono hmap h1
    rw [hLevi] at h2
    exact (mem_unitaryBlock_iff_toSL h).2 h2
  · refine le_perfectCore_of_perfect (le_inf (unitaryBlock_mono h hIN) ?_) hperf
    intro x hx
    rw [mem_centralizer_iff]
    intro d hd
    have hxC : toSL h n x ∈ centralizer D' := by
      have hx' : toSL h n x ∈ blockSpecialLinear (K := K) I := (mem_unitaryBlock_iff_toSL h).1 hx
      rw [← hLevi] at hx'
      exact (mem_inf.1 (perfectCore_le _ hx')).2
    apply toSL_injective h
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hxC (toSL h n d) ⟨d, hd, rfl⟩

theorem perfectCore_fixAll_conjTorusSU {N I : Finset (Fin n)} (hIN : I ⊆ N) (hI2 : 2 ≤ I.card)
    {ι' : Type*} (c : ι' → unitaryTorusParam h (∅ : Finset (Fin n)))
    (hc : ∀ j, (c j).1 ∈ unitaryTorusParam h I)
    (hsep : ∀ i ∈ N, ∀ k ∈ N, i ≠ k → (i ∉ I ∨ k ∉ I) → ∃ j, (c j).1 i ≠ (c j).1 k)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I) :
    perfectCore (fixAll fun j => conjTorusSU h N (c j)) =
      (unitaryBlock h I).subgroupOf (unitaryBlock h N) := by
  have := h.finite
  have hmap : (fixAll fun j => conjTorusSU h N (c j)).map (unitaryBlock h N).subtype =
      unitaryBlock h N ⊓ centralizer (Set.range fun j => torusDiagSU h (c j)) := by
    ext x
    simp only [mem_map, mem_inf, coe_subtype, mem_centralizer_iff, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun j => ?_⟩
      have h' := congrArg Subtype.val (mem_fixAll.1 hy j)
      rw [coe_conjTorusSU_apply] at h'
      calc torusDiagSU h (c j) * (y : unitarySU p f K n) =
            torusDiagSU h (c j) * (y : unitarySU p f K n) * (torusDiagSU h (c j))⁻¹ *
              torusDiagSU h (c j) := by group
        _ = (y : unitarySU p f K n) * torusDiagSU h (c j) := by rw [h']
    · rintro ⟨hxN, hx⟩
      refine ⟨⟨x, hxN⟩, mem_fixAll.2 fun j => Subtype.ext ?_, rfl⟩
      rw [coe_conjTorusSU_apply]
      change torusDiagSU h (c j) * x * (torusDiagSU h (c j))⁻¹ = x
      rw [hx j, mul_inv_cancel_right]
  apply Subgroup.map_injective (unitaryBlock h N).subtype_injective
  rw [CFSG.Quasithin.map_perfectCore, hmap, subgroupOf_map_subtype,
    inf_of_le_left (unitaryBlock_mono h hIN)]
  refine perfectCore_unitaryBlock_inf_centralizer_of_diag h hIN hI2 _
    (by rintro _ ⟨j, rfl⟩ i k hik; rw [coe_torusDiagSU, diagonal_apply_ne _ hik])
    (by
      rintro _ ⟨j, rfl⟩ i hi k hk
      rw [coe_torusDiagSU, diagonal_apply_eq, diagonal_apply_eq, (hc j).2.2 i hi k hk])
    (fun i hi k hk hik hIk => ?_) hperf
  obtain ⟨j, hj⟩ := hsep i hi k hk hik hIk
  refine ⟨torusDiagSU h (c j), ⟨j, rfl⟩, ?_⟩
  rw [coe_torusDiagSU, diagonal_apply_eq, diagonal_apply_eq]
  exact fun h' => hj (Units.ext h')

theorem commutator_unitaryBlock_eq_of_three_le {I : Finset (Fin n)} (hI3 : 3 ≤ I.card)
    (hIq : (I.card, p ^ f) ≠ (3, 2)) : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I := by
  have hP := (isQuasisimple_unitarySU h hI3 hIq).1
  exact Subgroup.isPerfect_iff.1
    (Group.IsPerfect.ofSurjective (f := (unitaryBlockEquiv h I).toMonoidHom)
      (unitaryBlockEquiv h I).surjective)

theorem commutator_unitaryBlock_eq_of_four_le {I : Finset (Fin n)} (hI4 : 4 ≤ I.card) :
    ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I :=
  commutator_unitaryBlock_eq_of_three_le h (by omega)
    (fun h3 => by have := congrArg Prod.fst h3; simp only at this; omega)

end Levi

section Even

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem perfectCore_unitaryBlock_inf_centralizer_unitaryTorusSU {N I : Finset (Fin n)}
    (hIN : I ⊆ N) (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I) :
    perfectCore (unitaryBlock h N ⊓
        centralizer (unitaryTorusSU h I : Set (unitarySU 2 f K n))) =
      unitaryBlock h I := by
  refine perfectCore_unitaryBlock_inf_centralizer_of_diag h hIN hI2 _
    (fun d hd i j hij => ?_) (fun d hd i hi j hj => ?_) (fun i _ j _ hij hIJ => ?_) hperf
  · obtain ⟨c, -, rfl⟩ := (mem_unitaryTorusSU h).1 hd
    rw [coe_torusDiagSU, diagonal_apply_ne _ hij]
  · obtain ⟨c, hc, rfl⟩ := (mem_unitaryTorusSU h).1 hd
    rw [coe_torusDiagSU, diagonal_apply_eq, diagonal_apply_eq, hc.2.2 i hi j hj]
  · obtain ⟨c, hc, hcij⟩ := exists_mem_unitaryTorusParam_ne h hIc hij hIJ
    refine ⟨torusDiagSU h ⟨c, unitaryTorusParam_anti h (Finset.empty_subset I) hc⟩,
      (mem_unitaryTorusSU h).2 ⟨_, hc, rfl⟩, ?_⟩
    rw [coe_torusDiagSU, diagonal_apply_eq, diagonal_apply_eq]
    exact fun h' => hcij (Units.ext h')

theorem perfectCore_unitaryBlock_compl_pair_inf_centralizer {a b : Fin n} (hab : a ≠ b)
    {I : Finset (Fin n)} (hI : I ⊆ {a, b}ᶜ) (hI2 : 2 ≤ I.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I) :
    perfectCore (unitaryBlock h ({a, b}ᶜ : Finset (Fin n)) ⊓
        centralizer (unitaryTorusSU h I : Set (unitarySU 2 f K n))) =
      unitaryBlock h I :=
  perfectCore_unitaryBlock_inf_centralizer_unitaryTorusSU h hI hI2
    (two_le_card_compl_of_subset_compl_pair hab hI) hperf

theorem perfectCore_unitaryBlock_inf_centralizer_unitaryTorusSU_of_four_le
    {N I : Finset (Fin n)} (hIN : I ⊆ N) (hI4 : 4 ≤ I.card) (hIc : 2 ≤ Iᶜ.card) :
    perfectCore (unitaryBlock h N ⊓
        centralizer (unitaryTorusSU h I : Set (unitarySU 2 f K n))) =
      unitaryBlock h I :=
  perfectCore_unitaryBlock_inf_centralizer_unitaryTorusSU h hIN (by omega) hIc
    (commutator_unitaryBlock_eq_of_four_le h hI4)

theorem perfectCore_fixAll_conjTorusSU_unitaryBlockTorusLift {N I : Finset (Fin n)}
    (hIN : I ⊆ N) (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I) :
    perfectCore (fixAll fun d : unitaryBlockTorus h I =>
        conjTorusSU h N (unitaryBlockTorusLift h d)) =
      (unitaryBlock h I).subgroupOf (unitaryBlock h N) := by
  refine perfectCore_fixAll_conjTorusSU h hIN hI2 _ (unitaryBlockTorusLift_mem h)
    (fun i _ j _ hij hIJ => ?_) hperf
  obtain ⟨c, hc, hcij⟩ := exists_mem_unitaryTorusParam_ne h hIc hij hIJ
  exact exists_unitaryBlockTorusLift_ne h hc hcij

end Even

end CFSG.SeitzReduction.UnitaryPilot
