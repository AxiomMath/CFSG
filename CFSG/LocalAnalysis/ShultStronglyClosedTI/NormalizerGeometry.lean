module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

theorem map_conj_map_conj (U : Subgroup G) (g a : G) :
    (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      U.map (MulAut.conj (a * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mul_inv_rev]
  group

variable [Finite G]

theorem conjugate_eq_of_le_sylow (T : Sylow 2 G) (U : Subgroup G)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (g : G)
    (hconj : U.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    U.map (MulAut.conj g).toMonoidHom = U := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨u, hu, rfl⟩
    have hmem := hconj (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hu)
    change g * u * g⁻¹ ∈ (T : Subgroup G) at hmem
    change g * u * g⁻¹ ∈ (U : Set G)
    simpa only [inv_inv] using hclosed u hu g⁻¹ (by simpa only [inv_inv] using hmem)
  · exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

theorem sylow_le_normalizer (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G))
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) :
    (T : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
  intro t ht
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply conjugate_eq_of_le_sylow T U hclosed t
  rintro x ⟨u, hu, rfl⟩
  exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht (hUT hu))
    ((T : Subgroup G).inv_mem ht)

theorem normal_in_sylow (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G))
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) :
    (U.subgroupOf (T : Subgroup G)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mpr
    (sylow_le_normalizer T U hUT hclosed)

theorem inf_conjugate_normalizer_eq_bot (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (g : G)
    (hg : U.map (MulAut.conj g).toMonoidHom ≠ U) :
    U ⊓ Subgroup.normalizer
      (U.map (MulAut.conj g).toMonoidHom : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro u ⟨huU, huN⟩
  apply Subgroup.mem_bot.mpr
  by_contra hune
  let V : Subgroup G := U.map (MulAut.conj g).toMonoidHom
  have hUtwo : IsPGroup 2 U :=
    T.isPGroup'.of_injective (Subgroup.inclusion hUT) (Subgroup.inclusion_injective hUT)
  have huorder : orderOf u = 2 :=
    orderOf_eq_prime_iff.mpr ⟨hUel.2 u huU, hune⟩
  have hutwo : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using huorder)
  have hjoin : IsPGroup 2 (V ⊔ Subgroup.zpowers u : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (H := V) (K := Subgroup.zpowers u)
      (hUtwo.map (MulAut.conj g).toMonoidHom) hutwo
      (Subgroup.zpowers_le.mpr huN)
  obtain ⟨R, hR⟩ := hjoin.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G R T
  have hRmap : (R : Subgroup G).map (MulAut.conj a).toMonoidHom = T := by
    change (a • R : Sylow 2 G).toSubgroup = T.toSubgroup
    rw [ha]
  have hVmapT : V.map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G) := by
    rw [← hRmap]
    exact Subgroup.map_mono (le_sup_left.trans hR)
  have hVmapU : V.map (MulAut.conj a).toMonoidHom = U := by
    have hcomp := map_conj_map_conj U g a
    change V.map (MulAut.conj a).toMonoidHom =
      U.map (MulAut.conj (a * g)).toMonoidHom at hcomp
    rw [hcomp] at hVmapT ⊢
    exact conjugate_eq_of_le_sylow T U hclosed (a * g) hVmapT
  have humapT : (MulAut.conj a) u ∈ (T : Subgroup G) := by
    rw [← hRmap]
    exact Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom
      ((show Subgroup.zpowers u ≤ (R : Subgroup G) from le_sup_right.trans hR)
        (Subgroup.mem_zpowers u))
  have humapU : (MulAut.conj a) u ∈ U := by
    change a * u * a⁻¹ ∈ (U : Set G)
    have hmem : a * u * a⁻¹ ∈ (T : Subgroup G) := humapT
    simpa only [inv_inv] using hclosed u huU a⁻¹ (by simpa only [inv_inv] using hmem)
  have huV : u ∈ V := by
    have hmem : (MulAut.conj a) u ∈ V.map (MulAut.conj a).toMonoidHom :=
      hVmapU.symm ▸ humapU
    simpa only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using hmem
  have hinf : U ⊓ V = ⊥ := hTI g hg
  exact hune (Subgroup.mem_bot.mp (hinf ▸ (show u ∈ U ⊓ V from ⟨huU, huV⟩)))

theorem conjugate_eq_of_mem_normalizer (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) {u : G} (hu : u ∈ U) (hune : u ≠ 1) (g : G)
    (hnormalizes : u ∈ Subgroup.normalizer
      (U.map (MulAut.conj g).toMonoidHom : Set G)) :
    U.map (MulAut.conj g).toMonoidHom = U := by
  by_contra hne
  have hbot := inf_conjugate_normalizer_eq_bot T U hUT hUel hclosed hTI g hne
  exact hune (Subgroup.mem_bot.mp (hbot ▸ (show u ∈ U ⊓
    Subgroup.normalizer (U.map (MulAut.conj g).toMonoidHom : Set G) from
      ⟨hu, hnormalizes⟩)))

omit [Finite G] in
theorem centralizer_le_normalizer (U : Subgroup G) (hTI : fusionIsTI U)
    {u : G} (hu : u ∈ U) (hune : u ≠ 1) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (U : Set G) := by
  intro a ha
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp ha
  have hfixed : (MulAut.conj a) u = u := by
    change a * u * a⁻¹ = u
    rw [hcomm]
    group
  have humap : u ∈ U.map (MulAut.conj a).toMonoidHom := by
    rw [← hfixed]
    exact Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hu
  exact hune (Subgroup.mem_bot.mp ((hTI a hne) ▸
    (show u ∈ U ⊓ U.map (MulAut.conj a).toMonoidHom from ⟨hu, humap⟩)))

end CFSG.ShultStronglyClosedTI
