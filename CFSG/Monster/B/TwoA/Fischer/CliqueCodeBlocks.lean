module

public import CFSG.Monster.B.TwoA.Fischer.CliqueCodeLocal

public section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.UnitarySix
  CFSG.Monster.B.TwoA.Unitary.Clique CFSG.Fischer CFSG.LinearGroups
  CFSG.LieType.Universal.Unitary
open scoped IsMulCommutative LinearAlgebra.Projectivization

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

section Supports

variable {C : Set V}

@[expose] noncomputable def indicWord (T : Finset C) : C →₀ ZMod 2 :=
  open _root_.Classical in
  Finsupp.onFinset T (fun z => if z ∈ T then 1 else 0) fun z hz => by
    by_contra h
    exact hz (ite_eq_right h)

theorem support_indicWord (T : Finset C) : (indicWord T).support = T := by
  classical
  ext z
  rw [indicWord, Finsupp.mem_support_iff, Finsupp.onFinset_apply]
  by_cases h : z ∈ T <;> simp [h]

variable [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]

theorem mem_cliqueBlocks_iff (B : Set V) :
    B ∈ cliqueBlocks lab C ↔ ∃ T : Finset C,
      ∑ z ∈ T, Additive.ofMul (cliqueGen (lab := lab) z) = 0 ∧ T.card = 6 ∧
        B = Subtype.val '' (T : Set C) := by
  constructor
  · rintro ⟨f, hf, hf6, rfl⟩
    exact ⟨f.support, (mem_cliqueCode_iff f).1 hf, hf6, rfl⟩
  · rintro ⟨T, hT, hT6, rfl⟩
    refine ⟨indicWord T, ?_, by rw [support_indicWord, hT6], by rw [support_indicWord]⟩
    rw [mem_cliqueCode_iff, support_indicWord]
    exact hT

theorem additive_add_self {G : Type*} [Group G] [CFSG.IsElementaryAbelian 2 G] (x : Additive G) :
    x + x = 0 := by
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (CFSG.IsElementaryAbelian.exponent_dvd_p 2 G) x.toMul
  apply Additive.toMul.injective
  rw [toMul_add, ← pow_two, h, toMul_zero]

theorem eq_of_add_eq_zero_additive {G : Type*} [Group G] [CFSG.IsElementaryAbelian 2 G]
    {x y : Additive G} (h : x + y = 0) : y = x := by
  calc y = x + y + x := by rw [add_comm x y, add_assoc, additive_add_self, add_zero]
    _ = x := by rw [h, zero_add]

end Supports

theorem mem_zpowers_iff_of_sq {G : Type*} [Group G] {g x : G} (hg : g ^ 2 = 1) :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · rintro ⟨k, rfl⟩
    have hg' : g ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hg]
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      change g ^ (2 * m) = 1
      rw [zpow_mul, hg', one_zpow]
    · right
      change g ^ (2 * m + 1) = g
      rw [zpow_add_one, zpow_mul, hg', one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem lab_sq_eq_one (hS : IsFischerSlice act lab Y) {u : V} (hu : u ∈ Y) : lab u ^ 2 = 1 := by
  rw [← hS.orderOf_lab u hu]
  exact pow_orderOf_eq_one _

open _root_.Classical in
theorem sum_eq_gen_of_insert {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {u : V} (hu : u ∈ C) {T : Finset C} (huT : (⟨u, hu⟩ : C) ∉ T)
    (h0 : ∑ z ∈ insert ⟨u, hu⟩ T, Additive.ofMul (cliqueGen (lab := lab) z) = 0) :
    ∑ z ∈ T, Additive.ofMul (cliqueGen (lab := lab) z) = Additive.ofMul (cliqueGen ⟨u, hu⟩) := by
  rw [Finset.sum_insert huT] at h0
  exact eq_of_add_eq_zero_additive h0


theorem ne_of_not_mem {C : Set V} {u : V} (hu : u ∈ C) {T : Finset C}
    (huT : (⟨u, hu⟩ : C) ∉ T) : ∀ z ∈ T, (z : V) ≠ u :=
  fun z hz h => huT (by rwa [show z = ⟨u, hu⟩ from Subtype.ext h] at hz)

namespace LocalChart

variable {u : V} (L : LocalChart act lab Y u) {C : Set V}

section Local

variable (hS : IsFischerSlice act lab Y) (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C)
  (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0))
  [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
include hS hC hu hWe

open _root_.Classical

theorem sum_R_eq_zero_of_insert {T : Finset C} (huT : (⟨u, hu⟩ : C) ∉ T)
    (h0 : ∑ z ∈ insert ⟨u, hu⟩ T, Additive.ofMul (cliqueGen (lab := lab) z) = 0) :
    ∑ z ∈ T, Plane.R (L.coordC g hWe z) = 0 := by
  refine (L.sum_mem_zpowers_iff hS hC hu g hWe T (ne_of_not_mem hu huT)).1 ?_
  rw [sum_eq_gen_of_insert hu huT h0, toMul_ofMul, coe_cliqueGen]
  exact Subgroup.mem_zpowers _

theorem sum_insert_ne_zero {T : Finset C} (huT : (⟨u, hu⟩ : C) ∉ T) (h4 : T.card ≤ 4) :
    ∑ z ∈ insert ⟨u, hu⟩ T, Additive.ofMul (cliqueGen (lab := lab) z) ≠ 0 := by
  intro h0
  by_cases hT0 : T.card = 0
  · have hT : T = ∅ := Finset.card_eq_zero.1 hT0
    have h := sum_eq_gen_of_insert hu huT h0
    rw [hT, Finset.sum_empty] at h
    have h1 : lab u = 1 := by
      have := congrArg (fun x => ((Additive.toMul x : Subgroup.closure (lab '' C)) : S)) h
      simpa [coe_cliqueGen] using this.symm
    have h2 := hS.orderOf_lab u (hC.1.1 hu)
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  · have h := (L.sum_coordC_eq_zero_iff hC hu g hWe T (ne_of_not_mem hu huT)
      (by omega) (by omega)).1 (L.sum_R_eq_zero_of_insert hS hC hu g hWe huT h0)
    omega

theorem exists_line_of_sum_eq_zero {T : Finset C} (huT : (⟨u, hu⟩ : C) ∉ T) (h5 : T.card = 5)
    (h0 : ∑ z ∈ insert ⟨u, hu⟩ T, Additive.ofMul (cliqueGen (lab := lab) z) = 0) :
    ∃ A : Submodule F4 UnitarySix.V, A ≤ smulSub g W0 ∧ Module.finrank F4 A = 2 ∧
      Subtype.val '' (T : Set C) = Subtype.val '' (L.τ ⁻¹' planePts A) :=
  ((L.sum_coordC_eq_zero_iff hC hu g hWe T (ne_of_not_mem hu huT) (by omega)
    (by omega)).1 (L.sum_R_eq_zero_of_insert hS hC hu g hWe huT h0)).2

end Local

end LocalChart

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem six_le_card_of_sum_eq_zero {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {T : Finset C} (hT : T.Nonempty)
    (h0 : ∑ z ∈ T, Additive.ofMul (cliqueGen (lab := lab) z) = 0) : 6 ≤ T.card := by
  open _root_.Classical in
  obtain ⟨⟨u, hu⟩, huT⟩ := hT
  obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 hu)
  obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC hu
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  by_contra hlt
  have hT' : T = insert ⟨u, hu⟩ (T.erase ⟨u, hu⟩) := (Finset.insert_erase huT).symm
  have hc := Finset.card_erase_of_mem huT
  rw [hT'] at h0
  exact L.sum_insert_ne_zero hS hC hu g hWe (Finset.notMem_erase _ _) (by omega) h0

end IsFischerSlice

namespace LocalChart

variable {u : V} (L : LocalChart act lab Y u) {C : Set V}

theorem image_preimage_subset (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0))
    {A : Submodule F4 UnitarySix.V} (hAW : A ≤ smulSub g W0) :
    Subtype.val '' (L.τ ⁻¹' planePts A) ⊆ C := by
  rintro _ ⟨z, hz, rfl⟩
  exact (L.mem_img_iff C z).1 (by rw [hWe]; exact planePts_mono hAW hz)

theorem ncard_image_preimage (g : SU frobeniusF4 6) {A : Submodule F4 UnitarySix.V}
    (hAW : A ≤ smulSub g W0) (hA : Module.finrank F4 A = 2) :
    (Subtype.val '' (L.τ ⁻¹' planePts A)).ncard = 5 := by
  rw [Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_preimage_of_injective_subset_range L.τ.injective (by
      rw [Equiv.range_eq_univ]
      exact Set.subset_univ _),
    ncard_planePts_line (isMaxIso_smulSub isMaxIso_W0 g) hAW hA]


section Local

variable (hS : IsFischerSlice act lab Y) (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C)
  (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0))
  [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
include hS hC hu hWe

open _root_.Classical

theorem exists_word_of_line {A : Submodule F4 UnitarySix.V} (hAW : A ≤ smulSub g W0)
    (hA : Module.finrank F4 A = 2) :
    ∃ T : Finset C, (⟨u, hu⟩ : C) ∉ T ∧ T.card = 5 ∧
      ∑ z ∈ insert ⟨u, hu⟩ T, Additive.ofMul (cliqueGen (lab := lab) z) = 0 ∧
      Subtype.val '' (T : Set C) = Subtype.val '' (L.τ ⁻¹' planePts A) := by
  set X := Subtype.val '' (L.τ ⁻¹' planePts A) with hX
  have hXC := L.image_preimage_subset g hWe hAW
  have : Finite C := (hS.finite.subset hC.1.1).to_subtype
  set T : Finset C := (Set.toFinite {z : C | (z : V) ∈ X}).toFinset with hTdef
  have hTX : Subtype.val '' (T : Set C) = X := by
    ext v
    rw [hTdef, Set.Finite.coe_toFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hv
      exact ⟨⟨v, hXC hv⟩, hv, rfl⟩
  have huX : u ∉ X := by
    rintro ⟨z, -, hz⟩
    exact z.2.2.2.1 hz.symm
  have huT : (⟨u, hu⟩ : C) ∉ T := by
    intro h
    apply huX
    rw [← hTX]
    exact ⟨_, h, rfl⟩
  have hT5 : T.card = 5 := by
    rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ Subtype.val_injective, hTX,
      L.ncard_image_preimage g hAW hA]
  have hR : ∑ z ∈ T, Plane.R (L.coordC g hWe z) = 0 :=
    (L.sum_coordC_eq_zero_iff hC hu g hWe T (ne_of_not_mem hu huT) (by omega)
      (by omega)).2 ⟨hT5, A, hAW, hA, hTX⟩
  have hmem := (L.sum_mem_zpowers_iff hS hC hu g hWe T
    (ne_of_not_mem hu huT)).2 hR
  rw [mem_zpowers_iff_of_sq (lab_sq_eq_one hS (hC.1.1 hu))] at hmem
  refine ⟨T, huT, hT5, ?_, hTX⟩
  rcases hmem with h1 | h1
  · exfalso
    have h0 : ∑ z ∈ T, Additive.ofMul (cliqueGen (lab := lab) z) = 0 := by
      apply Additive.toMul.injective
      rw [toMul_zero]
      exact Subtype.ext h1
    have := hS.six_le_card_of_sum_eq_zero hC (Finset.card_pos.1 (by omega)) h0
    omega
  · have h2 : ∑ z ∈ T, Additive.ofMul (cliqueGen (lab := lab) z) =
        Additive.ofMul (cliqueGen ⟨u, hu⟩) := by
      apply Additive.toMul.injective
      rw [toMul_ofMul]
      exact Subtype.ext h1
    rw [Finset.sum_insert huT, h2, additive_add_self]

theorem mem_cliqueBlocks_and_mem_iff (B : Set V) :
    (B ∈ cliqueBlocks lab C ∧ u ∈ B) ↔ ∃ A : Submodule F4 UnitarySix.V, A ≤ smulSub g W0 ∧
      Module.finrank F4 A = 2 ∧ B = insert u (Subtype.val '' (L.τ ⁻¹' planePts A)) := by
  constructor
  · rintro ⟨hB, huB⟩
    obtain ⟨T, hT0, hT6, rfl⟩ := (mem_cliqueBlocks_iff B).1 hB
    have huT : (⟨u, hu⟩ : C) ∈ T := by
      obtain ⟨z, hz, hzu⟩ := huB
      rwa [show z = ⟨u, hu⟩ from Subtype.ext hzu] at hz
    have hT' : T = insert ⟨u, hu⟩ (T.erase ⟨u, hu⟩) := (Finset.insert_erase huT).symm
    have hc := Finset.card_erase_of_mem huT
    rw [hT'] at hT0
    obtain ⟨A, hAW, hA, hTA⟩ := L.exists_line_of_sum_eq_zero hS hC hu g hWe
      (Finset.notMem_erase _ _) (by omega) hT0
    refine ⟨A, hAW, hA, ?_⟩
    rw [hT', Finset.coe_insert, Set.image_insert_eq, hTA]
  · rintro ⟨A, hAW, hA, rfl⟩
    obtain ⟨T, huT, hT5, hT0, hTA⟩ := L.exists_word_of_line hS hC hu g hWe hAW hA
    refine ⟨(mem_cliqueBlocks_iff _).2 ⟨insert ⟨u, hu⟩ T, hT0, by
      rw [Finset.card_insert_of_notMem huT, hT5], ?_⟩, Set.mem_insert u _⟩
    rw [Finset.coe_insert, Set.image_insert_eq, hTA]

end Local

end LocalChart

end CFSG.Monster.B.TwoA.Fischer
