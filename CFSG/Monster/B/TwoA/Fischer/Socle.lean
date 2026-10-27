module

public import CFSG.Monster.B.TwoA.Fischer.Primitive
public import CFSG.Monster.B.Generic.PrimitiveInvolution

public noncomputable section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical.UnitarySix MulAction

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem ne_two_mul_sq_64561751654400 (s : ℕ) : (64561751654400 : ℕ) ≠ 2 * s ^ 2 := by
  intro h
  have h1 : s ^ 2 = 32280875827200 := by omega
  have h13 : 13 ∣ s :=
    Nat.Prime.dvd_of_dvd_pow (by norm_num) (by rw [h1]; norm_num : 13 ∣ s ^ 2)
  obtain ⟨t, rfl⟩ := h13
  have h2 : 169 * t ^ 2 = 32280875827200 := by rw [← h1]; ring
  omega

theorem mem_zpowers_iff_of_injective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {g b : G} :
    f g ∈ Subgroup.zpowers (f b) ↔ g ∈ Subgroup.zpowers b := by
  rw [← MonoidHom.map_zpowers, Subgroup.mem_map_iff_mem hf]

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem card_sliceGroup_ne_two_mul_sq (s : ℕ) : Nat.card (sliceGroup lab Y) ≠ 2 * s ^ 2 := by
  rw [hS.card_sliceGroup]
  exact ne_two_mul_sq_64561751654400 s

theorem normalClosure_lab_eq_top {u : V} (hu : u ∈ Y) :
    Subgroup.normalClosure {(⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y)} = ⊤ := by
  have h : Subgroup.closure (((↑) : sliceGroup lab Y → S) ⁻¹' (lab '' Y)) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  intro g hg
  obtain ⟨y, hy, hgy⟩ := hg
  obtain ⟨b, hb, hbu⟩ := hS.transitive u hu y hy
  have hg : g = ⟨b, hb⟩ * ⟨lab u, lab_mem_sliceGroup hu⟩ * (⟨b, hb⟩ : sliceGroup lab Y)⁻¹ := by
    apply Subtype.ext
    rw [← hgy, ← hbu, hS.lab_act]
    rfl
  have hmem : (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y) ∈
      Subgroup.normalClosure {(⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y)} :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  have h2 := (Subgroup.normalClosure_normal (s := {(⟨lab u, lab_mem_sliceGroup hu⟩ :
    sliceGroup lab Y)})).conj_mem _ hmem ⟨b, hb⟩
  rw [← hg] at h2
  exact h2

def stabilizerToSliceStab (u : Y) :
    letI := hS.mulAction
    stabilizer (sliceGroup lab Y) u →* sliceStab act lab Y u :=
  letI := hS.mulAction
  { toFun := fun g => ⟨((g : sliceGroup lab Y) : S), (g : sliceGroup lab Y).2,
      congrArg Subtype.val (mem_stabilizer_iff.1 g.2)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

theorem lab_mem_stabilizer {u : V} (hu : u ∈ Y) :
    letI := hS.mulAction
    (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y) ∈
      stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y) :=
  Subtype.ext (hS.act_lab_self hu)

theorem commute_lab_stabilizer {u : V} (hu : u ∈ Y) :
    letI := hS.mulAction
    ∀ g : stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y),
      Commute g ⟨_, hS.lab_mem_stabilizer hu⟩ := by
  let _ := hS.mulAction
  intro g
  have h := (hS.act_eq_self_iff_commute hu (g : sliceGroup lab Y).2).1
    (congrArg Subtype.val (mem_stabilizer_iff.1 g.2))
  exact Subtype.ext (Subtype.ext h.eq)

theorem zpowers_lab_normal {u : V} (hu : u ∈ Y) :
    letI := hS.mulAction
    (Subgroup.zpowers (⟨_, hS.lab_mem_stabilizer hu⟩ :
      stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y))).Normal := by
  let _ := hS.mulAction
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  rw [((hS.commute_lab_stabilizer hu g).zpow_right k).eq, mul_inv_cancel_right]
  exact hn

theorem nonempty_stabilizerQuotientEquiv {u : V} (hu : u ∈ Y) :
    letI := hS.mulAction
    haveI := hS.zpowers_lab_normal hu
    Nonempty (stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y) ⧸
      Subgroup.zpowers (⟨_, hS.lab_mem_stabilizer hu⟩ :
        stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y)) ≃* ProjSU) := by
  let _ := hS.mulAction
  have := hS.zpowers_lab_normal hu
  obtain ⟨L⟩ := hS.nonempty_localChart hu
  let ψ := L.φ.comp (hS.stabilizerToSliceStab ⟨u, hu⟩)
  have hψ : Function.Surjective ψ := by
    intro m
    obtain ⟨b, rfl⟩ := L.surj m
    exact ⟨⟨⟨b, b.2.1⟩, Subtype.ext b.2.2⟩, rfl⟩
  have hker : ψ.ker = Subgroup.zpowers ⟨_, hS.lab_mem_stabilizer hu⟩ := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, L.ker]
    have hinj : Function.Injective ((sliceGroup lab Y).subtype.comp
        (stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y)).subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    exact mem_zpowers_iff_of_injective hinj (g := g) (b := ⟨_, hS.lab_mem_stabilizer hu⟩)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem socle_at {u : V} (hu : u ∈ Y) :
    (∀ N : Subgroup (sliceGroup lab Y), N.Normal → N ≠ ⊥ → N ≠ ⊤ → N.index = 2) ∧
    IsSimpleGroup (commutator (sliceGroup lab Y)) ∧
    ¬ IsMulCommutative (commutator (sliceGroup lab Y)) ∧
    (∀ N : Subgroup (sliceGroup lab Y), N.Normal → N ≠ ⊥ → commutator (sliceGroup lab Y) ≤ N) ∧
    (commutator (sliceGroup lab Y)).index ≤ 2 ∧
    Function.Injective (MulAut.conjNormal (H := commutator (sliceGroup lab Y))) ∧
    (commutator (sliceGroup lab Y) ≠ ⊤ →
      (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y) ∉ commutator (sliceGroup lab Y) ∧
      Subgroup.zpowers (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y) ⊓
        (commutator (sliceGroup lab Y) ⊓ (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y)) =
        ⊥ ∧
      Subgroup.zpowers (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y) ⊔
        (commutator (sliceGroup lab Y) ⊓ (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y)) =
        (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y) ∧
      Nonempty (↥(commutator (sliceGroup lab Y) ⊓
        (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y)) ≃* ProjSU)) := by
  let _ := hS.mulAction
  have := hS.finite_sliceGroup
  have := hS.faithfulSMul
  have := hS.isPreprimitive
  have := hS.zpowers_lab_normal hu
  obtain ⟨e⟩ := hS.nonempty_stabilizerQuotientEquiv hu
  have hsimple : IsSimpleGroup (stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y) ⧸
      Subgroup.zpowers (⟨_, hS.lab_mem_stabilizer hu⟩ :
        stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y))) := by
    have := isSimpleGroup_projSU
    exact e.isSimpleGroup
  have hΩ : Nat.card Y = 2 * 1755 := by rw [Nat.card_coe_set_eq, hS.ncard]
  have ha2 : orderOf (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y) = 2 := by
    rw [Subgroup.orderOf_mk, hS.orderOf_lab u hu]
  have hgen := hS.normalClosure_lab_eq_top hu
  have hax := hS.lab_mem_stabilizer hu
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ :=
    CFSG.Monster.B.Generic.primitive_central_involution_simple_stabilizer_quotient
      (K := sliceGroup lab Y) (Ω := Y) hΩ (by norm_num) (by decide) (⟨u, hu⟩ : Y)
      ⟨lab u, lab_mem_sliceGroup hu⟩ hax ha2 hgen hsimple hS.card_sliceGroup_ne_two_mul_sq
  refine ⟨h1, h2, h3, h4, h5, h6, fun hD => ?_⟩
  obtain ⟨i1, i2, i3, i4⟩ := h7 hD
  have hst := hS.stabilizer_eq_subgroupOf hu
  let f := (QuotientGroup.mk' (Subgroup.zpowers (⟨_, hS.lab_mem_stabilizer hu⟩ :
      stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y)))).comp
    (Subgroup.inclusion (inf_le_right : commutator (sliceGroup lab Y) ⊓
      stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y) ≤
        stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y)))
  have hf : Function.Bijective f := i4
  rw [hst] at i2 i3
  exact ⟨i1, i2, i3, ⟨(MulEquiv.subgroupCongr (by rw [hst])).trans
    ((MulEquiv.ofBijective f hf).trans e)⟩⟩

theorem simple_derived_socle :
    IsSimpleGroup (commutator (sliceGroup lab Y)) ∧
    ¬ IsMulCommutative (commutator (sliceGroup lab Y)) ∧
    (∀ N : Subgroup (sliceGroup lab Y), N.Normal → N ≠ ⊥ → commutator (sliceGroup lab Y) ≤ N) ∧
    (∀ N : Subgroup (sliceGroup lab Y), (N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup (sliceGroup lab Y),
      M.Normal → M ≠ ⊥ → M ≤ N → M = N) ↔ N = commutator (sliceGroup lab Y)) ∧
    ((commutator (sliceGroup lab Y)).index = 1 ∨ (commutator (sliceGroup lab Y)).index = 2) ∧
    Function.Injective (MulAut.conjNormal (H := commutator (sliceGroup lab Y))) ∧
    (Nat.card (commutator (sliceGroup lab Y)) = 64561751654400 ∨
      Nat.card (commutator (sliceGroup lab Y)) = 32280875827200) ∧
    (∀ N : Subgroup (sliceGroup lab Y), N.Normal → N ≠ ⊥ → N ≠ ⊤ → N.index = 2) ∧
    (commutator (sliceGroup lab Y) ≠ ⊤ → ∀ (u : V) (hu : u ∈ Y),
      (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y) ∉ commutator (sliceGroup lab Y) ∧
      (∀ g ∈ (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y),
        Commute g ⟨lab u, lab_mem_sliceGroup hu⟩) ∧
      Subgroup.zpowers (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y) ⊓
        (commutator (sliceGroup lab Y) ⊓ (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y)) =
        ⊥ ∧
      Subgroup.zpowers (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y) ⊔
        (commutator (sliceGroup lab Y) ⊓ (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y)) =
        (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y) ∧
      Nonempty (↥(commutator (sliceGroup lab Y) ⊓
        (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y)) ≃* ProjSU)) := by
  have := hS.finite_sliceGroup
  obtain ⟨u, hu⟩ : Y.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hS.ncard]; norm_num)
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hS.socle_at hu
  have hDbot : commutator (sliceGroup lab Y) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).1 (IsSimpleGroup.toNontrivial (self := h2))
  have hidx : (commutator (sliceGroup lab Y)).index = 1 ∨
      (commutator (sliceGroup lab Y)).index = 2 := by
    have := Subgroup.index_ne_zero_of_finite (H := commutator (sliceGroup lab Y))
    omega
  refine ⟨h2, h3, h4, fun N => ⟨fun ⟨hN, hNbot, hmin⟩ => ?_, ?_⟩, hidx, h6, ?_, h1,
    fun hD v hv => ?_⟩
  · exact (hmin _ inferInstance hDbot (h4 N hN hNbot)).symm
  · rintro rfl
    exact ⟨inferInstance, hDbot, fun M hM hMbot hle => le_antisymm hle (h4 M hM hMbot)⟩
  · have hc := (commutator (sliceGroup lab Y)).card_mul_index
    rw [hS.card_sliceGroup] at hc
    rcases hidx with h | h <;> rw [h] at hc <;> omega
  · obtain ⟨-, -, -, -, -, -, h7⟩ := hS.socle_at hv
    obtain ⟨i1, i2, i3, i4⟩ := h7 hD
    refine ⟨i1, fun g hg => ?_, i2, i3, i4⟩
    rw [Subgroup.mem_subgroupOf, hS.sliceStab_eq_inf_centralizer hv] at hg
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hg.2)

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
