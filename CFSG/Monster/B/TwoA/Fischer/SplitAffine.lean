module

public import CFSG.Monster.B.TwoA.Fischer.HexadFiber
public import CFSG.Monster.B.Classical.CosetLeaders
public import CFSG.Monster.B.Generic.ThreeTransposition

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical.CosetLeaders CFSG.Monster.B.Generic
open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem conj_mem_ptStab {C : Set V} {g r : S} (hg : g ∈ setStab act lab Y C)
    (hr : r ∈ ptStab act lab Y C) : g * r * g⁻¹ ∈ ptStab act lab Y C := by
  refine ⟨(sliceGroup lab Y).mul_mem ((sliceGroup lab Y).mul_mem hg.1 hr.1)
    ((sliceGroup lab Y).inv_mem hg.1), fun x hx => ?_⟩
  have h1 : act g⁻¹ x ∈ C := (((setStab act lab Y C).inv_mem hg).2 x).2 hx
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hr.2 _ h1, act_act_inv]

instance ptStab_subgroupOf_setStab_normal (C : Set V) :
    ((ptStab act lab Y C).subgroupOf (setStab act lab Y C)).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_ptStab g.2 hn

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem exists_short_prod {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (r : Subgroup.closure (lab '' C)) :
    ∃ T : Finset C, T.card ≤ 3 ∧ ∏ z ∈ T, cliqueGen (lab := lab) z = r := by
  classical
  obtain ⟨_, hsurj, hcard, hdim, hmin, -, -, hSt, -⟩ := hS.clique_code_steiner_design hC
  have : Finite C := (hS.finite.subset hC.1.1).to_subtype
  let _ : Fintype C := Fintype.ofFinite C
  set e := Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) C with he
  set K := (cliqueCode lab C).map (e : (C →₀ ZMod 2) →ₗ[ZMod 2] (C → ZMod 2)) with hKdef
  have hsupp : ∀ f : C →₀ ZMod 2, supp (e f) = f.support := by
    intro f
    ext z
    rw [mem_supp, Finsupp.mem_support_iff]
    rfl
  have hnorm : ∀ f : C →₀ ZMod 2, hammingNorm (e f) = f.support.card := fun f => by
    rw [hammingNorm_eq_card_supp, hsupp]
  have hK : Module.finrank (ZMod 2) K = 12 := by
    rw [hKdef, LinearEquiv.finrank_map_eq]
    exact hdim
  have hmin' : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x := by
    rintro _ ⟨f, hf, rfl⟩ hx0
    rw [show ((e : (C →₀ ZMod 2) →ₗ[ZMod 2] (C → ZMod 2)) f) = e f from rfl, hnorm]
    exact hmin f hf fun h => hx0 (by rw [h, map_zero])
  have hblocks : ∀ B : Finset C,
      B ∈ blocks K ↔ Subtype.val '' (B : Set C) ∈ cliqueBlocks lab C := by
    intro B
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, h6, hB⟩
      change hammingNorm (e f) = 6 at h6
      change supp (e f) = B at hB
      exact ⟨f, hf, by rw [← hnorm]; exact h6, by rw [← hB, hsupp]⟩
    · rintro ⟨f, hf, h6, hB⟩
      have hfB : f.support = B :=
        Finset.coe_injective (Set.image_injective.2 Subtype.val_injective hB.symm)
      exact ⟨e f, ⟨f, hf, rfl⟩, by rw [hnorm]; exact h6, by rw [hsupp, hfB]⟩
  have hS' : ∀ T : Finset C, T.card = 3 → ∃! B, B ∈ blocks K ∧ T ⊆ B := by
    intro T hT
    have hT'C : Subtype.val '' (T : Set C) ⊆ C := by
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    have hT'3 : (Subtype.val '' (T : Set C)).ncard = 3 := by
      rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset, hT]
    obtain ⟨B', ⟨hB', hTB'⟩, huniq⟩ := hSt _ hT'C hT'3
    obtain ⟨T₀, -, -, rfl⟩ := (mem_cliqueBlocks_iff B').1 hB'
    have hsub : ∀ {B : Finset C}, Subtype.val '' (T : Set C) ⊆ Subtype.val '' (B : Set C) →
        T ⊆ B := fun h z hz => by
      obtain ⟨z', hz', hzz⟩ := h ⟨z, hz, rfl⟩
      rwa [← Subtype.ext hzz]
    refine ⟨T₀, ⟨(hblocks T₀).2 hB', hsub hTB'⟩, fun B₂ ⟨hB₂, hTB₂⟩ => ?_⟩
    have h := huniq _ ⟨(hblocks B₂).1 hB₂, Set.image_mono (Finset.coe_subset.2 hTB₂)⟩
    exact Finset.coe_injective (Set.image_injective.2 Subtype.val_injective h)
  have hC22 : Fintype.card C = 22 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨hrep, -⟩ := binary_steiner_code_coset_leaders hC22 K hK hmin' hS'
  obtain ⟨f, hf⟩ := hsurj (Additive.ofMul r)
  obtain ⟨x, hx3, hxK⟩ := hrep (K.mkQ (e f))
  have hg : cliqueLabelMap lab C (e.symm x) = cliqueLabelMap lab C f := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hxK
    obtain ⟨d, hd, hde⟩ := hxK
    have h1 : e.symm x - f = d := e.injective (by
      rw [map_sub, LinearEquiv.apply_symm_apply]
      exact hde.symm)
    rw [← sub_eq_zero, ← map_sub, h1]
    exact hd
  refine ⟨(e.symm x).support, ?_, ?_⟩
  · rw [← hnorm, LinearEquiv.apply_symm_apply]
    exact hx3
  · apply Additive.ofMul.injective
    rw [ofMul_prod, ← cliqueLabelMap_apply, hg, hf]

theorem ptStab_eq_closure_of_isSliceMaxClique {C : Set V} (hC : IsSliceMaxClique lab Y C) :
    ptStab act lab Y C = Subgroup.closure (lab '' C) :=
  (hS.maximal_clique_stabilizer_kernel.2.2 C hC).2.2.1

theorem eq_one_of_act_eq {C : Set V} (hC : IsSliceMaxClique lab Y C) {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) {r : S} (hr : r ∈ ptStab act lab Y C) (hrx : act r x = x) :
    r = 1 := by
  classical
  have inst := hS.isElementaryAbelian_closure hC.1.1 hC.1.2
  have hr' : r ∈ Subgroup.closure (lab '' C) := hS.ptStab_eq_closure_of_isSliceMaxClique hC ▸ hr
  obtain ⟨T, hT3, hTr⟩ := hS.exists_short_prod hC ⟨r, hr'⟩
  by_contra hr1
  have hT1 : 1 ≤ T.card := by
    by_contra h0
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [hT0, Finset.prod_empty] at hTr
    exact hr1 (congrArg Subtype.val hTr).symm
  set e := T.equivFin
  set a : Fin T.card → S := fun i => lab (e.symm i : C) with ha
  have hzC : ∀ i, ((e.symm i : C) : V) ∈ C := fun i => (e.symm i : C).2
  have hainj : Function.Injective a := fun i j h => e.symm.injective (Subtype.ext
    (Subtype.ext (hS.injOn (hC.1.1 (hzC i)) (hC.1.1 (hzC j)) h)))
  have hcomm : ∀ i j, Commute (a i) (a j) := by
    intro i j
    by_cases hij : ((e.symm i : C) : V) = e.symm j
    · simp only [a, hij]
      exact Commute.refl _
    · exact (hC.1.2 (hzC i) (hzC j) hij).2.2.2
  have hinv : ∀ i, orderOf (a i) = 2 := fun i => hS.orderOf_lab _ (hC.1.1 (hzC i))
  have h3 : ∀ i, orderOf (lab x * a i) = 3 := by
    intro i
    refine hS.orderOf_mul x hx.1 _ (hC.1.1 (hzC i)) fun hc => ?_
    have hne : x ≠ (e.symm i : C) := fun h => hx.2.1 (h ▸ hzC i)
    have hmem : ((e.symm i : C) : V) ∈ C ∩ (sliceGraph lab Y).neighborSet x :=
      ⟨hzC i, hx.1, hC.1.1 (hzC i), hne, hc⟩
    rw [hx.2.2] at hmem
    exact hmem
  have hprod : (List.ofFn a).prod = r := by
    have h1 : List.ofFn a = (List.ofFn fun i => cliqueGen (lab := lab) (e.symm i : C)).map
        (Subgroup.closure (lab '' C)).subtype := by
      rw [List.map_ofFn]
      rfl
    rw [h1, ← map_list_prod, List.prod_ofFn,
      Equiv.prod_comp e.symm (fun z : T => cliqueGen (lab := lab) (z : C)),
      Finset.prod_coe_sort T (fun z => cliqueGen (lab := lab) z), hTr]
    rfl
  have hct : Commute (lab x) (List.ofFn a).prod := by
    rw [hprod]
    have h := hS.lab_act r x
    rw [hrx] at h
    change lab x * r = r * lab x
    conv_lhs => rw [h]
    group
  exact three_transpositions_short_commuting_products (hS.orderOf_lab x hx.1) hT1 hT3 a hainj
    hcomm hinv h3 hct

theorem existsUnique_act_eq {C : Set V} (hC : IsSliceMaxClique lab Y C) {x y : V}
    (hx : x ∈ hexadFiber lab Y C ∅) (hy : y ∈ hexadFiber lab Y C ∅) :
    ∃! r, r ∈ ptStab act lab Y C ∧ act r x = y := by
  obtain ⟨inst, -, -, -, -, -, -, -, -, -, hΩ, -, -⟩ := hS.clique_hexad_fibers hC
  have hR : Nat.card (ptStab act lab Y C) = 2 ^ 10 :=
    (hS.maximal_clique_stabilizer_kernel.2.2 C hC).2.2.2.2.1
  have hinj : Function.Injective fun r : ptStab act lab Y C => act (r : S) x := by
    intro r s h
    have h1 : act ((s⁻¹ * r : ptStab act lab Y C) : S) x = x := by
      change act ((s : S)⁻¹ * r) x = x
      rw [map_mul, Equiv.Perm.mul_apply]
      exact (congrArg (act (s : S)⁻¹) h).trans (act_inv_act _ _)
    have h2 := hS.eq_one_of_act_eq hC hx (s⁻¹ * r).2 h1
    have h3 : s⁻¹ * r = 1 := Subtype.ext h2
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  have hsub : Set.range (fun r : ptStab act lab Y C => act (r : S) x) ⊆
      hexadFiber lab Y C ∅ := by
    rintro _ ⟨r, rfl⟩
    exact hS.act_mem_hexadFiber r.2 hx
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [hΩ, Set.ncard_range_of_injective hinj, hR]; norm_num) (hS.finite.subset fun _ h => h.1)
  obtain ⟨r, hr⟩ : y ∈ Set.range fun r : ptStab act lab Y C => act (r : S) x := heq ▸ hy
  refine ⟨r, ⟨r.2, hr⟩, ?_⟩
  rintro s ⟨hs, hsy⟩
  exact congrArg Subtype.val (hinj (a₁ := ⟨s, hs⟩) (hsy.trans hr.symm))

theorem act_mem_hexadFiber_empty {C : Set V} {a : S} (ha : a ∈ setStab act lab Y C) {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) : act a x ∈ hexadFiber lab Y C ∅ := by
  have h := hS.image_hexadFiber ha ∅
  rw [Set.image_empty] at h
  exact h ▸ ⟨x, hx, rfl⟩

theorem clique_split_regular {C : Set V} (hC : IsSliceMaxClique lab Y C) :
    (∀ r ∈ ptStab act lab Y C, ∀ x ∈ hexadFiber lab Y C ∅, act r x ∈ hexadFiber lab Y C ∅) ∧
    (∀ x ∈ hexadFiber lab Y C ∅, ∀ y ∈ hexadFiber lab Y C ∅,
      ∃! r, r ∈ ptStab act lab Y C ∧ act r x = y) ∧
    ∀ x ∈ hexadFiber lab Y C ∅,
      ((ptStab act lab Y C).subgroupOf (setStab act lab Y C)).IsComplement'
        ((setStab act lab Y C ⊓ actStab act x).subgroupOf (setStab act lab Y C)) ∧
      Function.Bijective
        ((QuotientGroup.mk' ((ptStab act lab Y C).subgroupOf (setStab act lab Y C))).comp
          (Subgroup.inclusion (inf_le_left : setStab act lab Y C ⊓ actStab act x ≤
            setStab act lab Y C))) ∧
      ∀ r ∈ ptStab act lab Y C, ∀ k ∈ setStab act lab Y C ⊓ actStab act x,
        ∀ a ∈ ptStab act lab Y C, k * a * k⁻¹ ∈ ptStab act lab Y C ∧
          act (r * k) (act a x) = act (r * (k * a * k⁻¹)) x := by
  refine ⟨fun r hr x hx => hS.act_mem_hexadFiber hr hx,
    fun x hx y hy => hS.existsUnique_act_eq hC hx hy, fun x hx => ?_⟩
  have hdec : ∀ f ∈ setStab act lab Y C, ∃ r ∈ ptStab act lab Y C,
      r⁻¹ * f ∈ setStab act lab Y C ⊓ actStab act x := by
    intro f hf
    obtain ⟨r, ⟨hr, hrx⟩, -⟩ :=
      hS.existsUnique_act_eq hC hx (hS.act_mem_hexadFiber_empty hf hx)
    refine ⟨r, hr, (setStab act lab Y C).mul_mem
      ((setStab act lab Y C).inv_mem (ptStab_le_setStab C hr)) hf, ?_⟩
    change act (r⁻¹ * f) x = x
    rw [map_mul, Equiv.Perm.mul_apply, ← hrx, act_inv_act]
  have hfree : ∀ k ∈ setStab act lab Y C ⊓ actStab act x, k ∈ ptStab act lab Y C → k = 1 :=
    fun k hk hkR => hS.eq_one_of_act_eq hC hx hkR hk.2
  refine ⟨Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro k hkR hkx
    exact Subtype.ext (hfree k ⟨k.2, ((Subgroup.mem_subgroupOf).1 hkx).2⟩
      ((Subgroup.mem_subgroupOf).1 hkR))
  · refine Set.eq_univ_of_forall fun f => ?_
    obtain ⟨r, hr, hk⟩ := hdec f f.2
    refine Set.mem_mul.2 ⟨⟨r, ptStab_le_setStab C hr⟩, (Subgroup.mem_subgroupOf).2 hr,
      ⟨r⁻¹ * f, hk.1⟩, (Subgroup.mem_subgroupOf).2 hk, Subtype.ext ?_⟩
    change r * (r⁻¹ * (f : S)) = f
    group
  · rw [injective_iff_map_eq_one]
    intro k hk
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hk
    exact Subtype.ext (hfree k k.2 hk)
  · intro q
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨r, hr, hk⟩ := hdec f f.2
    refine ⟨⟨r⁻¹ * f, hk⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    change (r⁻¹ * (f : S))⁻¹ * f ∈ ptStab act lab Y C
    rw [show (r⁻¹ * (f : S))⁻¹ * f = (f : S)⁻¹ * r * f by group]
    have h := conj_mem_ptStab ((setStab act lab Y C).inv_mem f.2) hr
    rwa [inv_inv] at h
  · intro r _ k hk a ha
    refine ⟨conj_mem_ptStab hk.1 ha, ?_⟩
    have hk' : act k⁻¹ x = x := by
      conv_lhs => rw [← show act k x = x from hk.2]
      exact act_inv_act _ _
    simp only [map_mul, Equiv.Perm.mul_apply, hk']

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
