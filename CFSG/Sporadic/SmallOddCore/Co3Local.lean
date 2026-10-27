module

public import CFSG.Sporadic.SmallOddCore.LocalTransport
public import CFSG.Sporadic.SmallOddCore.Co3Classes
public import CFSG.Sporadic.Schreier.Co3FirstAut
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Symplectic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem co3M_quot_simple :
    IsSimpleGroup (co3M ⧸ center co3M) := by
  have : IsSimpleGroup (StatedProj (StatedSp 3 (ZMod 2))) :=
    isSimpleGroup_statedProj_statedSp (ZMod 2) 3 (by norm_num)
      (Or.inr (Or.inr ⟨by simp, by norm_num⟩))
  exact co3MQuotProj.isSimpleGroup

theorem co3M_isQuasisimple :
    CFSG.IsQuasisimple co3M := by
  refine ⟨co3M_isPerfect, co3M_quot_simple, ?_⟩
  by_contra h
  push Not at h
  have hle : commutator co3M ≤ center co3M := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    have h1 : (QuotientGroup.mk' (center co3M)) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h _ _
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
  have htop : center co3M = ⊤ := by
    rw [eq_top_iff, ← co3M_isPerfect.commutator_eq_top]
    exact hle
  have hcard := card_co3M_center
  rw [htop, Subgroup.card_top, card_co3M] at hcard
  norm_num at hcard

theorem co3M_component
    {B : Subgroup (Equiv.Perm (Fin 276))}
    (hB : CFSG.Assembly.IsComponentOf B co3M) :
    Nat.card ↥(co3M ⊓ centralizer (B : Set (Equiv.Perm (Fin 276)))) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBM : B = co3M := isComponentOf_eq_of_isQuasisimple hB co3M_isQuasisimple
    (IsPGroup.of_card (n := 1) (by rw [card_co3M_center, pow_one]))
  rw [hBM, card_inf_centralizer_self, card_co3M_center]

theorem card_co3Z1 :
    Nat.card co3Z1 = 2 := by
  rw [co3Z1, Nat.card_zpowers, orderOf_co3TtM1]

theorem co3M1_centralizer_L1 :
    centralizer (co3L1 : Set co3M1) = co3Z1 := by
  apply le_antisymm
  · intro x hx
    have hZn : co3Z1.Normal := ⟨fun n hn g => by
      have := mem_center_iff.mp (co3Z1_le_center hn) g
      rw [this, mul_inv_cancel_right]
      exact hn⟩
    have hx' : x ∈ ((co3L1 ⊔ co3Z1 : Subgroup co3M1) : Set co3M1) := by
      rw [co3L1_sup_Z1]
      trivial
    rw [Subgroup.mul_normal, Set.mem_mul] at hx'
    obtain ⟨l, hl, z, hz, rfl⟩ := hx'
    have hc : (⟨l, hl⟩ : co3L1) ∈ center co3L1 := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have h1 := mem_centralizer_iff.mp hx (g : co3M1) g.2
      have h2 := mem_center_iff.mp (co3Z1_le_center hz) (g : co3M1)
      have h3 : (g : co3M1) * l * z = l * g * z := by
        calc (g : co3M1) * l * z = g * (l * z) := by group
          _ = l * z * g := h1
          _ = l * (z * g) := by group
          _ = l * (g * z) := by rw [h2]
          _ = l * g * z := by group
      exact mul_right_cancel h3
    rw [co3L1_center, mem_bot] at hc
    have hl1 : l = 1 := congrArg Subtype.val hc
    rw [hl1, one_mul]
    exact hz
  · intro x hx
    rw [mem_centralizer_iff]
    intro y _
    exact mem_center_iff.mp (co3Z1_le_center hx) y

theorem card_co3M1_centralizer_L :
    Nat.card ↥(co3M1 ⊓ centralizer (co3L : Set (Equiv.Perm (Fin 276)))) = 2 := by
  have h := map_centralizer_eq_inf co3M1.subtype_injective (co3L1 : Set co3M1)
  rw [co3M1_centralizer_L1, range_subtype] at h
  have hL : co3M1.subtype '' (co3L1 : Set co3M1) = (co3L : Set (Equiv.Perm (Fin 276))) := by
    rw [← Subgroup.coe_map, co3L1, map_subgroupOf_eq_of_le co3L_le_M1]
  rw [hL] at h
  rw [← h, Subgroup.card_map_of_injective co3M1.subtype_injective, card_co3Z1]

theorem co3M1_component
    {B : Subgroup (Equiv.Perm (Fin 276))}
    (hB : CFSG.Assembly.IsComponentOf B co3M1) :
    Nat.card ↥(co3M1 ⊓ centralizer (B : Set (Equiv.Perm (Fin 276)))) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn : co3M1 ≤ normalizer (co3L : Set (Equiv.Perm (Fin 276))) :=
    (normal_subgroupOf_iff_le_normalizer co3L_le_M1).1 co3L1_normal
  rcases isComponentOf_le_or_commute hB co3L_le_M1 hLn with hle | hcomm
  ·
    have : IsSimpleGroup co3L := by
      have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      exact co3LEquivM12.isSimpleGroup
    have hnab : ∃ a b : co3L, a * b ≠ b * a := by
      refine ⟨co3LEquivM12.symm CFSG.Sporadic.Mathieu.m12a,
        co3LEquivM12.symm CFSG.Sporadic.Mathieu.m12b, fun h => m12_not_comm ?_⟩
      have := congrArg co3LEquivM12 h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this
    obtain ⟨hLq, hLZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
    have hBL : B = co3L := isComponentOf_eq_of_isQuasisimple
      (isComponentOf_of_le hB hle co3L_le_M1) hLq (p := 2) (by rw [hLZ]; exact IsPGroup.of_bot)
    rw [hBL]
    exact card_co3M1_centralizer_L
  · exfalso
    have hle : B ≤ co3M1 ⊓ centralizer (co3L : Set (Equiv.Perm (Fin 276))) := by
      intro x hx
      refine mem_inf.mpr ⟨hB.1 hx, ?_⟩
      rw [mem_centralizer_iff]
      intro y hy
      have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
      rw [mem_centralizer_iff] at this
      exact this y hy
    exact not_le_of_isPGroup hB.2.2
      (isPGroup_two_of_card (k := 1) (by rw [card_co3M1_centralizer_L]; norm_num)) hle

theorem co3P_local_components
    {τ : Equiv.Perm (Fin 276)} (hτP : τ ∈ co3P) (hτ : orderOf τ = 2)
    {B : Subgroup (Equiv.Perm (Fin 276))}
    (hB : CFSG.Assembly.IsComponentOf B (co3P ⊓ centralizer ({τ} : Set _))) :
    Nat.card ↥(co3P ⊓ centralizer ({τ} : Set _) ⊓
      centralizer (B : Set (Equiv.Perm (Fin 276)))) = 2 := by
  obtain ⟨-, -, -, hcl, -, -⟩ := ctuc_co3_complete_inner_involution_classes
  have hrep : ∃ g ∈ co3P, ∃ r : Equiv.Perm (Fin 276), τ = g * r * g⁻¹ ∧
      ((co3P ⊓ centralizer ({r} : Set _) = co3M) ∨ (co3P ⊓ centralizer ({r} : Set _) = co3M1)) := by
    by_cases h : ∃ g ∈ co3P, τ = g * co3Z * g⁻¹
    · obtain ⟨g, hg, rfl⟩ := h
      exact ⟨g, hg, co3Z, rfl, Or.inl co3M_eq_centralizer.symm⟩
    · have h' : ∃ g ∈ co3P, τ = g * co3Tt * g⁻¹ := by
        by_contra h''
        exact h ((hcl τ hτP hτ).2 h'')
      obtain ⟨g, hg, rfl⟩ := h'
      exact ⟨g, hg, co3Tt, rfl, Or.inr co3M1_eq_centralizer.symm⟩
  obtain ⟨g, hg, r, rfl, hr⟩ := hrep
  have hfinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hgr : g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := by group
  have hBr : CFSG.Assembly.IsComponentOf (B.map (MulAut.conj g⁻¹).toMonoidHom)
      (co3P ⊓ centralizer ({r} : Set _)) := by
    have h := (isComponentOf_map_iff hfinj).2 hB
    rwa [Subgroup.map_inf _ _ _ hfinj, map_conj_self (co3P.inv_mem hg), map_conj_centralizer,
      Set.image_singleton, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgr] at h
  have hmap := map_conj_inf_inf_centralizer (co3P.inv_mem hg) (g * r * g⁻¹) B
  rw [hgr] at hmap
  rw [← Subgroup.card_map_of_injective hfinj, hmap]
  rcases hr with hM | hM1
  · rw [hM] at hBr ⊢
    exact co3M_component hBr
  · rw [hM1] at hBr ⊢
    exact co3M1_component hBr

theorem cti_co3_involution_local_component_centralizer_order_two
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.Co3)) {t : T} (ht : orderOf t = 2) {B : Subgroup T}
    (hB : CFSG.Assembly.IsComponentOf B (centralizer ({t} : Set T))) :
    Nat.card ↥(centralizer ({t} : Set T) ⊓ centralizer (B : Set T)) = 2 := by
  obtain ⟨e⟩ := hT
  set ι : T →* Equiv.Perm (Fin 276) := co3P.subtype.comp (e.trans co3PermEquiv).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (e.trans co3PermEquiv).injective
  have hrange : ι.range = co3P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (e.trans co3PermEquiv).surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hτP : ι t ∈ co3P := hrange ▸ ⟨t, rfl⟩
  have hτ : orderOf (ι t) = 2 := by rw [orderOf_injective ι hι, ht]
  have hB' : CFSG.Assembly.IsComponentOf (B.map ι)
      (co3P ⊓ centralizer ({ι t} : Set (Equiv.Perm (Fin 276)))) := by
    have := (isComponentOf_map_iff hι).2 hB
    rwa [map_centralizer_eq_inf hι, hrange, Set.image_singleton] at this
  have h2 := co3P_local_components hτP hτ hB'
  rw [← Subgroup.card_map_of_injective hι, map_inf_centralizer_of_injective hι, hrange]
  exact h2

end CFSG.Sporadic.SmallOddCore
