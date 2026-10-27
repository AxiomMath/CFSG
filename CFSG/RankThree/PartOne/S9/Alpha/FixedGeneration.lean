module

public import CFSG.RankThree.GroupTheory.SteinbergCDHyperplaneFixedGeneration
public import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.RankThree.PartOne.AlphaTheory

open CFSG CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem map_fixedPointSubgroup_conj {H B : Subgroup G} (hBH : B ≤ normalizer (H : Set G)) :
    letI : MulDistribMulAction B H := MulDistribMulAction.compHom H (Subgroup.inclusion hBH)
    (fixedPointSubgroup B H).map H.subtype = H ⊓ centralizer (B : Set G) := by
  let : MulDistribMulAction B H := MulDistribMulAction.compHom H (Subgroup.inclusion hBH)
  have hsmul : ∀ (b : B) (k : H), ((b • k : H) : G) = (b : G) * k * (b : G)⁻¹ := fun _ _ => rfl
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.coe_subtype, SetLike.mem_coe]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, fun b hb => ?_⟩
    have h := congrArg Subtype.val (hk ⟨b, hb⟩)
    rw [hsmul] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · rintro ⟨hxH, hx⟩
    refine ⟨⟨x, hxH⟩, fun b => Subtype.ext ?_, rfl⟩
    rw [hsmul]
    exact mul_inv_eq_iff_eq_mul.mpr (hx b b.2)

theorem map_fixedPointSubgroup_zpowers_conj {H B : Subgroup G} (hBH : B ≤ normalizer (H : Set G))
    (b : B) :
    letI : MulDistribMulAction B H := MulDistribMulAction.compHom H (Subgroup.inclusion hBH)
    (fixedPointSubgroup (zpowers b) H).map H.subtype = H ⊓ centralizer ({(b : G)} : Set G) := by
  let : MulDistribMulAction B H := MulDistribMulAction.compHom H (Subgroup.inclusion hBH)
  have hsmul : ∀ (b : B) (k : H), ((b • k : H) : G) = (b : G) * k * (b : G)⁻¹ := fun _ _ => rfl
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h := congrArg Subtype.val
      ((SolvableHall.mem_fixedPointSubgroup_zpowers_iff b k).mp hk)
    rw [hsmul] at h
    exact ⟨k.2, (mul_inv_eq_iff_eq_mul.mp h).symm⟩
  · rintro ⟨hxH, hx⟩
    refine ⟨⟨x, hxH⟩, (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b _).mpr
      (Subtype.ext ?_), rfl⟩
    rw [hsmul]
    exact mul_inv_eq_iff_eq_mul.mpr hx.symm

theorem nilpotent_fixed_generation_ambient [Finite G] {p : ℕ} (hp : p.Prime) {B H : Subgroup G}
    (hB : IsElementaryAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (hBH : B ≤ normalizer (H : Set G)) (hHnil : Group.IsNilpotent H) (hHp : ¬ p ∣ Nat.card H)
    (hHB : ⁅H, B⁆ = H) :
    H ⊓ centralizer (B : Set G) =
      ⨆ b ∈ B, ⨆ (_ : b ≠ 1),
        ⁅H ⊓ centralizer ({b} : Set G), B⁆ ⊓ centralizer (B : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hB
  let _ : MulDistribMulAction B H := MulDistribMulAction.compHom H (Subgroup.inclusion hBH)
  have hcomm : ∀ K : Subgroup H, (actionCommutator B K).map H.subtype =
      ⁅K.map H.subtype, B⁆ := fun K => SteinbergBM.map_actionCommutator_conj hBH K
  have htop : actionCommutator B (⊤ : Subgroup H) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hcomm, Subgroup.map_top, Subgroup.range_subtype, hHB]
  have hgen := (nilpotent_hyperplane_commutator_fixed_generation (p := p) (B := B)
    (by rw [hBcard]) hHnil hHp htop).2 hBcard
  have hmap := congrArg (Subgroup.map H.subtype) hgen
  rw [map_fixedPointSubgroup_conj hBH] at hmap
  have hHle : ∀ b : G, ⁅H ⊓ centralizer ({b} : Set G), B⁆ ≤ H := fun b =>
    (Subgroup.commutator_mono inf_le_left le_rfl).trans hHB.le
  have hsummand : ∀ b : B, ((actionCommutator B (fixedPointSubgroup (zpowers b) H) ⊓
      fixedPointSubgroup B H).map H.subtype) =
      ⁅H ⊓ centralizer ({(b : G)} : Set G), B⁆ ⊓ centralizer (B : Set G) := by
    intro b
    rw [Subgroup.map_inf_eq _ _ H.subtype H.subtype_injective, hcomm,
      map_fixedPointSubgroup_zpowers_conj hBH, map_fixedPointSubgroup_conj hBH, ← inf_assoc,
      inf_eq_left.mpr (hHle _)]
  simp only [Subgroup.map_iSup, hsummand] at hmap
  rw [hmap]
  apply le_antisymm
  · refine iSup_le fun b => iSup_le fun hb => ?_
    exact le_iSup₂_of_le (b : G) b.2 (le_iSup_of_le (fun h => hb (Subtype.ext h)) le_rfl)
  · refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
    exact le_iSup_of_le (⟨b, hb⟩ : B) (le_iSup_of_le (fun h => hb1 (congrArg Subtype.val h))
      le_rfl)

end CFSG.RankThree.PartOne.AlphaTheory
