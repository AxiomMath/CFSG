module

public import CFSG.Monster.B.TwoA.Fischer.CliqueKernelLocal
public import CFSG.Monster.B.TwoA.Unitary.CliqueMain

public section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.UnitarySix
  CFSG.Monster.B.TwoA.Unitary.Clique CFSG.Fischer

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem perm_image_eq {α : Type*} (σ : Equiv.Perm α) {P : Set α} (h : ∀ p, σ p ∈ P ↔ p ∈ P) :
    σ '' P = P := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (h p).2 hp
  · intro hq
    exact ⟨σ.symm q, (h _).1 (by rwa [Equiv.apply_symm_apply]), Equiv.apply_symm_apply _ _⟩

theorem image_act_eq_of_forall {a : S} {C C' : Set V} (h : ∀ y, act a y ∈ C' ↔ y ∈ C) :
    act a '' C = C' := by
  ext v
  rw [mem_image_act_iff, ← h, act_act_inv]

theorem natCard_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem natCard_eq_ker_mul_range {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem natCard_comap_of_surjective {G G' : Type*} [Group G] [Group G'] [Finite G] {f : G →* G'}
    (hf : Function.Surjective f) (K : Subgroup G') :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  have : Finite G' := Finite.of_surjective f hf
  have h1 := Subgroup.card_mul_index (K.comap f)
  have h2 := Subgroup.card_mul_index K
  have h3 := natCard_eq_ker_mul_range f
  rw [Subgroup.index_comap_of_surjective K hf] at h1
  rw [MonoidHom.range_eq_top.2 hf, Subgroup.card_top] at h3
  have hi : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) ?_
  rw [h1, h3, ← h2]
  ring

theorem mem_neighborSet_of_isSliceMaxClique {C : Set V} (hC : IsSliceMaxClique lab Y C) {u : V}
    (hu : u ∈ C) : ∀ v ∈ C, v ≠ u → v ∈ (sliceGraph lab Y).neighborSet u :=
  fun _ hv hvu => mem_neighborSet_of_mem_clique hC.1.2 hu hv hvu

namespace LocalChart

variable {u : V} (L : LocalChart act lab Y u)

theorem act_mem_iff_of_img (hS : IsFischerSlice act lab Y) {D D' : Set V}
    (hD : ∀ v ∈ D, v ≠ u → v ∈ (sliceGraph lab Y).neighborSet u)
    (hD' : ∀ v ∈ D', v ≠ u → v ∈ (sliceGraph lab Y).neighborSet u)
    (huD : u ∈ D) (huD' : u ∈ D') (b : sliceStab act lab Y u)
    (hb : projAct (L.φ b) '' L.img D = L.img D') (y : V) :
    act b y ∈ D' ↔ y ∈ D := by
  have hbu : act (b : S) u = u := b.2.2
  by_cases hyu : y = u
  · rw [hyu, hbu]
    exact iff_of_true huD' huD
  by_cases hy : y ∈ (sliceGraph lab Y).neighborSet u
  · have e := L.tau_act hS b ⟨y, hy⟩
    have h1 := L.mem_img_iff D' ⟨act b y, hS.act_mem_neighborSet b.2 hy⟩
    have h2 := L.mem_img_iff D ⟨y, hy⟩
    rw [e, ← hb, (projAct (L.φ b)).injective.mem_set_image] at h1
    exact h1.symm.trans h2
  · have h1 : y ∉ D := fun h => hy (hD y h hyu)
    have h2 : act (b : S) y ∉ D' := by
      intro h
      by_cases hbyu : act (b : S) y = u
      · apply hyu
        have := congrArg (act (b : S)⁻¹) hbyu
        rw [act_inv_act] at this
        have h3 : act (b : S)⁻¹ u = u := by
          calc act (b : S)⁻¹ u = act (b : S)⁻¹ (act b u) := by rw [hbu]
            _ = u := act_inv_act _ _
        exact this.trans h3
      · exact hy ((hS.act_mem_neighborSet_iff b.2 y).1 (hD' _ h hbyu))
    exact iff_of_false h2 h1

theorem mem_setStab_iff (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C) {W : Submodule F4 UnitarySix.V}
    (hW : L.img C = planePts W) (b : sliceStab act lab Y u) :
    (b : S) ∈ setStab act lab Y C ↔ L.φ b ∈ stabL W := by
  constructor
  · intro hb p
    obtain ⟨z, rfl⟩ := L.τ.surjective p
    rw [← L.tau_act hS b z, ← hW, L.mem_img_iff, L.mem_img_iff]
    exact hb.2 z
  · intro hb
    refine ⟨b.2.1, L.act_mem_iff_of_img hS (mem_neighborSet_of_isSliceMaxClique hC hu)
      (mem_neighborSet_of_isSliceMaxClique hC hu) hu hu b ?_⟩
    rw [hW]
    exact perm_image_eq _ hb

theorem mem_ptStab_iff (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C) {W : Submodule F4 UnitarySix.V}
    (hW : L.img C = planePts W) (b : sliceStab act lab Y u) :
    (b : S) ∈ ptStab act lab Y C ↔ L.φ b ∈ kerL W := by
  constructor
  · intro hb p hp
    obtain ⟨z, rfl⟩ := L.τ.surjective p
    rw [← hW, L.mem_img_iff] at hp
    rw [← L.tau_act hS b z]
    congr 1
    exact Subtype.ext (hb.2 z hp)
  · intro hb
    refine ⟨b.2.1, fun x hx => ?_⟩
    by_cases hxu : x = u
    · rw [hxu]
      exact b.2.2
    · have hxn := mem_neighborSet_of_mem_clique hC.1.2 hu hx hxu
      have e := L.tau_act hS b ⟨x, hxn⟩
      rw [hb _ (by rw [← hW]; exact (L.mem_img_iff C ⟨x, hxn⟩).2 hx)] at e
      exact congrArg Subtype.val (L.τ.injective e)

theorem exists_sliceStab_image_eq (L : LocalChart act lab Y u) (hS : IsFischerSlice act lab Y)
    {C C' : Set V}
    (hC : IsSliceMaxClique lab Y C) (hC' : IsSliceMaxClique lab Y C') (hu : u ∈ C)
    (hu' : u ∈ C') : ∃ b : sliceStab act lab Y u, ∀ y, act b y ∈ C' ↔ y ∈ C := by
  obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC hu
  obtain ⟨W', hW', hWe'⟩ := L.exists_img_eq hS hC' hu'
  obtain ⟨x, hx⟩ := exists_projAct_image_planePts hW hW'
  obtain ⟨b, rfl⟩ := L.surj x
  exact ⟨b, L.act_mem_iff_of_img hS (mem_neighborSet_of_isSliceMaxClique hC hu)
    (mem_neighborSet_of_isSliceMaxClique hC' hu') hu hu' b (by rw [hWe, hWe', hx])⟩

theorem ker_φ : L.φ.ker = (Subgroup.zpowers (lab u)).subgroupOf (sliceStab act lab Y u) := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact L.ker b

end LocalChart

theorem ptStab_le_setStab (C : Set V) : ptStab act lab Y C ≤ setStab act lab Y C := by
  intro a ha
  refine ⟨ha.1, fun x => ⟨fun h => ?_, fun h => by rw [ha.2 x h]; exact h⟩⟩
  have h1 : act a (act a x) = act a x := ha.2 _ h
  rw [(act a).injective h1] at h
  exact h

theorem ker_setStabPerm (C : Set V) :
    (setStabPerm act lab Y C).ker = (ptStab act lab Y C).subgroupOf (setStab act lab Y C) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine ⟨a.2.1, fun x hx => ?_⟩
    have := congrArg (fun σ : Equiv.Perm C => ((σ ⟨x, hx⟩ : C) : V)) h
    exact this
  · intro h
    exact Equiv.ext fun x => Subtype.ext (h.2 x x.2)

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem exists_incident {u u' : V} {C C' : Set V} (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C)
    (hC' : IsSliceMaxClique lab Y C') (hu' : u' ∈ C') :
    ∃ a ∈ sliceGroup lab Y, act a u = u' ∧ act a '' C = C' := by
  obtain ⟨a₀, ha₀, hau⟩ := hS.transitive u (hC.1.1 hu) u' (hC'.1.1 hu')
  have hC'' : IsSliceMaxClique lab Y (act a₀⁻¹ '' C') :=
    hS.isSliceMaxClique_image ((sliceGroup lab Y).inv_mem ha₀) hC'
  have hu'' : u ∈ act a₀⁻¹ '' C' := by
    rw [mem_image_act_iff, inv_inv, hau]
    exact hu'
  obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 hu)
  obtain ⟨b, hb⟩ := L.exists_sliceStab_image_eq hS hC hC'' hu hu''
  refine ⟨a₀ * b, (sliceGroup lab Y).mul_mem ha₀ b.2.1, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.mul_apply, show act (b : S) u = u from b.2.2, hau]
  · rw [map_mul, Equiv.Perm.coe_mul, Set.image_comp, image_act_eq_of_forall hb]
    have := image_act_inv_image (act := act) a₀⁻¹ C'
    rwa [inv_inv] at this

theorem exists_setStab {C : Set V} (hC : IsSliceMaxClique lab Y C) {x y : V} (hx : x ∈ C)
    (hy : y ∈ C) : ∃ a ∈ setStab act lab Y C, act a x = y := by
  obtain ⟨a, ha, hax, haC⟩ := hS.exists_incident hC hx hC hy
  refine ⟨a, ⟨ha, fun v => ?_⟩, hax⟩
  constructor
  · intro h
    rw [← haC, mem_image_act_iff, act_inv_act] at h
    exact h
  · intro h
    rw [← haC]
    exact ⟨v, h, rfl⟩

theorem lab_mem_sliceStab_self {u : V} (hu : u ∈ Y) : lab u ∈ sliceStab act lab Y u :=
  hS.lab_mem_sliceStab hu hu (Commute.refl _)

theorem natCard_ker_φ {u : V} (hu : u ∈ Y) (L : LocalChart act lab Y u) :
    Nat.card L.φ.ker = 2 := by
  rw [L.ker_φ, natCard_subgroupOf, inf_eq_left.2 ((Subgroup.zpowers_le).2
    (hS.lab_mem_sliceStab_self hu)), Nat.card_zpowers, hS.orderOf_lab u hu]

theorem finite_sliceStab (u : V) : Finite (sliceStab act lab Y u) := by
  have := hS.finite_sliceGroup
  have hle : sliceStab act lab Y u ≤ sliceGroup lab Y := inf_le_left
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

theorem finite_setStab (C : Set V) : Finite (setStab act lab Y C) := by
  have := hS.finite_sliceGroup
  have hle : setStab act lab Y C ≤ sliceGroup lab Y := fun _ h => h.1
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

theorem isElementaryAbelian_closure {C : Set V} (hCY : C ⊆ Y)
    (hC : (sliceGraph lab Y).IsClique C) :
    CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C)) := by
  have hcomm : (lab '' C).Pairwise Commute := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    exact (hC hx hy fun h => hne (h ▸ rfl)).2.2.2
  have hcm := Subgroup.isMulCommutative_closure hcomm
  have hc : ∀ x ∈ Subgroup.closure (lab '' C), ∀ y ∈ Subgroup.closure (lab '' C),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine isElementaryAbelian_two_of _ hc fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [← hS.orderOf_lab z (hCY hz)]
    exact pow_orderOf_eq_one _
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [(show Commute x y from hc x hx y hy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem closure_le_ptStab {C : Set V} (hCY : C ⊆ Y) (hC : (sliceGraph lab Y).IsClique C) :
    Subgroup.closure (lab '' C) ≤ ptStab act lab Y C := by
  rw [Subgroup.closure_le]
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨lab_mem_sliceGroup (hCY hz), fun x hx => ?_⟩
  rw [hS.act_lab_eq_iff (hCY hz) (hCY hx)]
  by_cases hzx : z = x
  · rw [hzx]
  · exact (hC hz hx hzx).2.2.2

end IsFischerSlice

namespace LocalChart

variable {u : V} (L : LocalChart act lab Y u)

theorem ptStab_eq_closure (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C) {W : Submodule F4 UnitarySix.V}
    (hW : IsMaxIso W) (hWe : L.img C = planePts W) :
    ptStab act lab Y C = Subgroup.closure (lab '' C) := by
  refine le_antisymm (fun a ha => ?_) (hS.closure_le_ptStab hC.1.1 hC.1.2)
  have haH : a ∈ sliceStab act lab Y u := ⟨ha.1, ha.2 u hu⟩
  set A := Subgroup.closure (lab '' C)
  have hAu : A ≤ sliceStab act lab Y u := fun x hx =>
    ⟨(hS.closure_le_ptStab hC.1.1 hC.1.2 hx).1, (hS.closure_le_ptStab hC.1.1 hC.1.2 hx).2 u hu⟩
  have hgen : kerL W ≤ (A.subgroupOf (sliceStab act lab Y u)).map L.φ := by
    rw [hW.kerL_eq_closure, Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, rfl⟩ := L.τ.surjective p
    rw [← hWe, L.mem_img_iff] at hp
    refine ⟨⟨lab z, hS.lab_mem_sliceStab_of_mem z.2⟩, ?_, L.φ_lab hS z⟩
    exact (Subgroup.mem_subgroupOf).2 (Subgroup.subset_closure ⟨z, hp, rfl⟩)
  have hφa : L.φ ⟨a, haH⟩ ∈ kerL W := (L.mem_ptStab_iff hS hC hu hWe ⟨a, haH⟩).1 ha
  obtain ⟨a', ha', he⟩ := hgen hφa
  have hk : L.φ (a'⁻¹ * ⟨a, haH⟩) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have hk' := (L.ker _).1 hk
  have hlu : Subgroup.zpowers (lab u) ≤ A :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure ⟨u, hu, rfl⟩)
  have h1 : ((a'⁻¹ * ⟨a, haH⟩ : sliceStab act lab Y u) : S) ∈ A := hlu hk'
  have h2 : (a' : S) ∈ A := ha'
  have h3 : a = (a' : S) * ((a'⁻¹ * ⟨a, haH⟩ : sliceStab act lab Y u) : S) := by
    simp
  rw [h3]
  exact A.mul_mem h2 h1

end LocalChart

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem natCard_ptStab_of_chart {C : Set V} (hC : IsSliceMaxClique lab Y C) {u : V}
    (hu : u ∈ C) (L : LocalChart act lab Y u) {W : Submodule F4 UnitarySix.V}
    (hW : IsMaxIso W) (hWe : L.img C = planePts W) :
    Nat.card (ptStab act lab Y C) = 2 ^ 10 := by
  have := hS.finite_sliceStab u
  have hRu : ptStab act lab Y C ≤ sliceStab act lab Y u := fun a ha => ⟨ha.1, ha.2 u hu⟩
  have e : (ptStab act lab Y C).subgroupOf (sliceStab act lab Y u) = (kerL W).comap L.φ := by
    ext b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact L.mem_ptStab_iff hS hC hu hWe b
  have h := natCard_comap_of_surjective L.surj (kerL W)
  rw [← e, natCard_subgroupOf, inf_eq_left.2 hRu, hW.natCard_kerL,
    hS.natCard_ker_φ (hC.1.1 hu) L] at h
  rw [h]
  norm_num

theorem natCard_setStab_inf_of_chart {C : Set V} (hC : IsSliceMaxClique lab Y C) {u : V}
    (hu : u ∈ C) (L : LocalChart act lab Y u) {W : Submodule F4 UnitarySix.V}
    (hW : IsMaxIso W) (hWe : L.img C = planePts W) :
    Nat.card ↥(setStab act lab Y C ⊓ sliceStab act lab Y u) = 2 ^ 10 * 20160 := by
  have := hS.finite_sliceStab u
  have e : (setStab act lab Y C).subgroupOf (sliceStab act lab Y u) = (stabL W).comap L.φ := by
    ext b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact L.mem_setStab_iff hS hC hu hWe b
  have h := natCard_comap_of_surjective L.surj (stabL W)
  rw [← e, natCard_subgroupOf, hS.natCard_ker_φ (hC.1.1 hu) L] at h
  have hk : (restrL W).ker = (kerL W).subgroupOf (stabL W) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact restrL_eq_one_iff W x
  have h2 := natCard_eq_ker_mul_range (restrL W)
  rw [hk, natCard_subgroupOf, inf_eq_left.2 (kerL_le_stabL W), hW.natCard_kerL,
    natCard_range_restrL hW] at h2
  rw [h, h2]
  norm_num

theorem natCard_setStab_eq {C : Set V} (hC : IsSliceMaxClique lab Y C) {u : V} (hu : u ∈ C) :
    Nat.card (setStab act lab Y C) =
      22 * Nat.card ↥(setStab act lab Y C ⊓ sliceStab act lab Y u) := by
  let _ : MulAction (setStab act lab Y C) C := MulAction.compHom C (setStabPerm act lab Y C)
  have hsmul : ∀ (a : setStab act lab Y C) (x : C), ((a • x : C) : V) = act a x :=
    fun _ _ => rfl
  have horbit : MulAction.orbit (setStab act lab Y C) (⟨u, hu⟩ : C) = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨a, ha, hax⟩ := hS.exists_setStab hC hu x.2
    exact ⟨⟨a, ha⟩, Subtype.ext ((hsmul _ _).trans hax)⟩
  have hstab : MulAction.stabilizer (setStab act lab Y C) (⟨u, hu⟩ : C) =
      (sliceStab act lab Y u).subgroupOf (setStab act lab Y C) := by
    ext a
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_sliceStab]
    constructor
    · intro h
      exact ⟨a.2.1, (hsmul a _).symm.trans (congrArg Subtype.val h)⟩
    · intro h
      exact Subtype.ext ((hsmul a _).trans h.2)
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (setStab act lab Y C) (⟨u, hu⟩ : C))
  rw [MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_coe_set_eq,
    hS.ncard_eq_of_isSliceMaxClique hC, hstab, natCard_subgroupOf, inf_comm] at h1
  rw [← h1, mul_comm]

omit hS in
theorem natCard_setStab_eq_mul (C : Set V) :
    Nat.card (setStab act lab Y C) =
      Nat.card (ptStab act lab Y C) * Nat.card (setStabPerm act lab Y C).range := by
  rw [natCard_eq_ker_mul_range (setStabPerm act lab Y C), ker_setStabPerm, natCard_subgroupOf,
    inf_eq_left.2 (ptStab_le_setStab C)]

theorem maximal_clique_stabilizer_kernel :
    (∀ C : Set V, IsSliceMaxClique lab Y C → C.ncard = 22) ∧
    (∀ (u u' : V) (C C' : Set V), IsSliceMaxClique lab Y C → u ∈ C →
      IsSliceMaxClique lab Y C' → u' ∈ C' →
      ∃ a ∈ sliceGroup lab Y, act a u = u' ∧ act a '' C = C') ∧
    ∀ C : Set V, IsSliceMaxClique lab Y C →
      (∀ x ∈ C, ∀ y ∈ C, ∃ a ∈ setStab act lab Y C, act a x = y) ∧
      Nat.card (setStabPerm act lab Y C).range = 443520 ∧
      ptStab act lab Y C = Subgroup.closure (lab '' C) ∧
      CFSG.IsElementaryAbelian 2 (ptStab act lab Y C) ∧
      Nat.card (ptStab act lab Y C) = 2 ^ 10 ∧
      Nat.card (setStab act lab Y C) = 454164480 ∧
      11 ∣ Nat.card (setStabPerm act lab Y C).range ∧
      ∀ u ∈ C, ∀ L : LocalChart act lab Y u,
        ∃ W : Submodule F4 UnitarySix.V, IsMaxIso W ∧
          L.τ '' {z | (z : V) ∈ C} = planePts W ∧
          ((ptStab act lab Y C).subgroupOf (sliceStab act lab Y u)).map L.φ = kerL W ∧
          Subgroup.zpowers (lab u) ≤ ptStab act lab Y C ∧
          ∀ a : sliceStab act lab Y u, (a : S) ∈ ptStab act lab Y C →
            (L.φ a = 1 ↔ (a : S) ∈ Subgroup.zpowers (lab u)) := by
  refine ⟨fun C hC => hS.ncard_eq_of_isSliceMaxClique hC,
    fun u u' C C' hC hu hC' hu' => hS.exists_incident hC hu hC' hu', fun C hC => ?_⟩
  obtain ⟨u, hu⟩ := hS.nonempty_of_isSliceMaxClique hC
  obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 hu)
  obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC hu
  have hR := hS.natCard_ptStab_of_chart hC hu L hW hWe
  have hF : Nat.card (setStab act lab Y C) = 454164480 := by
    rw [hS.natCard_setStab_eq hC hu, hS.natCard_setStab_inf_of_chart hC hu L hW hWe]
    norm_num
  have hFC : Nat.card (setStabPerm act lab Y C).range = 443520 := by
    have h := natCard_setStab_eq_mul (act := act) (lab := lab) (Y := Y) C
    rw [hF, hR] at h
    omega
  have hcl := L.ptStab_eq_closure hS hC hu hW hWe
  refine ⟨fun x hx y hy => hS.exists_setStab hC hx hy, hFC, hcl, ?_, hR, hF,
    by rw [hFC]; norm_num, fun u' hu' L' => ?_⟩
  · rw [hcl]
    exact hS.isElementaryAbelian_closure hC.1.1 hC.1.2
  · obtain ⟨W', hW', hWe'⟩ := L'.exists_img_eq hS hC hu'
    refine ⟨W', hW', hWe', ?_, ?_, fun a _ => L'.ker a⟩
    · have e : (ptStab act lab Y C).subgroupOf (sliceStab act lab Y u') =
          (kerL W').comap L'.φ := by
        ext b
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
        exact L'.mem_ptStab_iff hS hC hu' hWe' b
      rw [e, Subgroup.map_comap_eq_self_of_surjective L'.surj]
    · rw [hcl]
      exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure ⟨u', hu', rfl⟩)

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
