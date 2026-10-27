module

public import CFSG.Monster.VisQuot.SylowT
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMRankVis
public import CFSG.Monster.Schur.GmatStructureVec

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.Monster CFSG.Monster.Visible CFSG.Monster.Schur CFSG.Monster.SpinLattice
  CFSG.Monster.VisQuot CFSG.Monster.Generated
open scoped IsMulCommutative

private theorem ker_comp_PhiV (A : Subgroup CFSG.Monster.Visible.Gvis) :
    (CFSG.Monster.Schur.PhiV.comp A.subtype).ker =
      CFSG.Monster.Visible.rhoQvis.subgroupOf A := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    CFSG.Monster.Schur.ker_PhiV, Subgroup.mem_subgroupOf]
  rfl

private theorem ker_comp_repVis (A : Subgroup CFSG.Monster.Visible.Gvis) :
    (CFSG.Monster.Visible.repVis.comp A.subtype).ker =
      CFSG.Monster.Visible.rhoQvis.subgroupOf A := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    CFSG.Monster.Visible.ker_repVis, Subgroup.mem_subgroupOf]
  rfl

private theorem range_comp_PhiV (A : Subgroup CFSG.Monster.Visible.Gvis) :
    (CFSG.Monster.Schur.PhiV.comp A.subtype).range =
      A.map CFSG.Monster.Schur.PhiV := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact Subgroup.mem_map_of_mem CFSG.Monster.Schur.PhiV x.2
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem range_comp_repVis (A : Subgroup CFSG.Monster.Visible.Gvis) :
    (CFSG.Monster.Visible.repVis.comp A.subtype).range =
      A.map CFSG.Monster.Visible.repVis := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact Subgroup.mem_map_of_mem CFSG.Monster.Visible.repVis x.2
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem natCard_eq_mul_natCard_map_PhiV (A : Subgroup CFSG.Monster.Visible.Gvis) :
    Nat.card A = Nat.card (CFSG.Monster.Visible.rhoQvis.subgroupOf A) *
      Nat.card (A.map CFSG.Monster.Schur.PhiV) := by
  have h := (Subgroup.card_ker_mul_card_range
    (CFSG.Monster.Schur.PhiV.comp A.subtype)).symm
  rw [ker_comp_PhiV, range_comp_PhiV] at h
  exact h

private theorem natCard_eq_mul_natCard_map_repVis (A : Subgroup CFSG.Monster.Visible.Gvis) :
    Nat.card A = Nat.card (CFSG.Monster.Visible.rhoQvis.subgroupOf A) *
      Nat.card (A.map CFSG.Monster.Visible.repVis) := by
  have h := (Subgroup.card_ker_mul_card_range
    (CFSG.Monster.Visible.repVis.comp A.subtype)).symm
  rw [ker_comp_repVis, range_comp_repVis] at h
  exact h

private theorem natCard_map_PhiV_eq_natCard_map_repVis (A : Subgroup CFSG.Monster.Visible.Gvis)
    (hK : Nat.card (CFSG.Monster.Visible.rhoQvis.subgroupOf A) ≠ 0) :
    Nat.card (A.map CFSG.Monster.Schur.PhiV) =
      Nat.card (A.map CFSG.Monster.Visible.repVis) := by
  have h := (natCard_eq_mul_natCard_map_PhiV A).symm.trans
    (natCard_eq_mul_natCard_map_repVis A)
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hK) h

theorem card_le_two_pow_fifteen_of_le_Tvis (hFB : CFSG.Monster.VisQuot.FixBound)
    {A : Subgroup CFSG.Monster.Visible.Gvis} (hAT : A ≤ CFSG.Monster.VisQuot.Tvis)
    (hA : CFSG.Open.IsElemAbelian 2 A) : Nat.card A ≤ 2 ^ 15 := by
  obtain ⟨D, hfix, hsing, hcard⟩ := exists_fixed_singular_card_le_Gvis hA
  set Â : Subgroup CFSG.Monster.VisQuot.MonoSD :=
    (A.map CFSG.Monster.Schur.PhiV).comap CFSG.Monster.VisQuot.monoHom with hÂ_def
  have hÂT : Â ≤ CFSG.Monster.VisQuot.Tsd := by
    intro m hm
    rw [hÂ_def, Subgroup.mem_comap, Subgroup.mem_map] at hm
    obtain ⟨a, ha, hma⟩ := hm
    obtain ⟨m', hm', hm'e⟩ := CFSG.Monster.VisQuot.exists_mem_Tsd_of_mem_Tvis (hAT ha)
    have hmeq : m' = m :=
      CFSG.Monster.VisQuot.monoHom_injective (hm'e.symm.trans hma)
    rwa [← hmeq]
  have hÂabel : CFSG.Open.IsElemAbelian 2 Â :=
    (hA.map CFSG.Monster.Schur.PhiV).comap CFSG.Monster.VisQuot.monoHom_injective
  have hfix' : ∀ m ∈ Â, ∀ w ∈ D,
      ((CFSG.Monster.VisQuot.monoHom m : LinearMap.GeneralLinearGroup (ZMod 2) L2) :
        L2 →ₗ[ZMod 2] L2) w = w := by
    intro m hm w hw
    rw [hÂ_def, Subgroup.mem_comap, Subgroup.mem_map] at hm
    obtain ⟨a, ha, hma⟩ := hm
    have h := CFSG.Monster.Schur.visModLat_repVis_PhiV a (visModLat.symm w)
    rw [hfix a ha w hw, LinearEquiv.apply_symm_apply] at h
    have hs : CFSG.Monster.Schur.PhiV a • w =
        ((CFSG.Monster.Schur.PhiV a : LinearMap.GeneralLinearGroup (ZMod 2) L2) :
          L2 →ₗ[ZMod 2] L2) w := Module.End.smul_def _ _
    rw [← hma, ← hs]
    exact h.symm
  have h14 : Nat.card Â * Nat.card D ≤ 2 ^ 14 :=
    CFSG.Monster.VisQuot.card_mul_card_le_of_fixBound hFB hÂT hÂabel hfix' hsing
  have hÂcard : Nat.card Â = Nat.card (A.map CFSG.Monster.Schur.PhiV) := by
    have hle : A.map CFSG.Monster.Schur.PhiV ≤ CFSG.Monster.VisQuot.monoHom.range := by
      rintro ν ⟨a, ha, rfl⟩
      obtain ⟨m, hm, hP⟩ := CFSG.Monster.VisQuot.exists_mem_Tsd_of_mem_Tvis (hAT ha)
      exact ⟨m, hP.symm⟩
    have hmap : Â.map CFSG.Monster.VisQuot.monoHom =
        A.map CFSG.Monster.Schur.PhiV := by
      rw [hÂ_def, Subgroup.map_comap_eq_self hle]
    rw [← hmap, Subgroup.card_map_of_injective CFSG.Monster.VisQuot.monoHom_injective]
  rcases eq_or_ne (Nat.card (CFSG.Monster.Visible.rhoQvis.subgroupOf A)) 0 with hK | hK
  · have hA0 : Nat.card A = 0 := by
      rw [natCard_eq_mul_natCard_map_PhiV A, hK, zero_mul]
    rw [hA0]
    exact Nat.zero_le _
  · have hcard_eq := natCard_map_PhiV_eq_natCard_map_repVis A hK
    calc Nat.card A ≤ 2 * Nat.card (A.map CFSG.Monster.Visible.repVis) * Nat.card D := hcard
      _ = 2 * (Nat.card Â * Nat.card D) := by rw [← hcard_eq, ← hÂcard]; ring
      _ ≤ 2 * 2 ^ 14 := Nat.mul_le_mul_left 2 h14
      _ = 2 ^ 15 := by norm_num

theorem card_le_two_pow_fifteen_of_le_Tmat (hFB : CFSG.Monster.VisQuot.FixBound)
    {B : Subgroup CFSG.Monster.Generated.Gmat} (hBT : B ≤ CFSG.Monster.VisQuot.Tmat)
    (hB : CFSG.Open.IsElemAbelian 2 B) : Nat.card B ≤ 2 ^ 15 := by
  obtain ⟨A, hAT, hBA⟩ := CFSG.Monster.VisQuot.exists_eq_toMat hBT
  have hA : CFSG.Open.IsElemAbelian 2 A :=
    (CFSG.Monster.VisQuot.isElemAbelian_toMat_iff).1 (hBA ▸ hB)
  rw [hBA, CFSG.Monster.VisQuot.natCard_toMat]
  exact card_le_two_pow_fifteen_of_le_Tvis hFB hAT hA

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
