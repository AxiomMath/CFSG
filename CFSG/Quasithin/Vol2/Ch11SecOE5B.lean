module

public import CFSG.Quasithin.Vol2.Ch11SecOE5A
public import CFSG.Open.StatedSUFieldChange

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.OE5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem mem_centralizer_of_proj (h : UnitaryFieldData 5 1 K) {g : unitarySU 5 1 K 3}
    (hg : unitaryProj h 3 g ∈ Subgroup.centralizer {unitaryProj h 3 (unitaryInvT h)}) :
    g ∈ Subgroup.centralizer {unitaryInvT h} := by
  obtain ⟨u, -, huniq⟩ :=
    existsUnique_unitaryProj_lift h (orderOf_unitaryProj_unitaryInvT h (by norm_num))
  have ht : unitaryInvT h = u := huniq _ ⟨rfl, orderOf_invT h⟩
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hconj : g * unitaryInvT h * g⁻¹ = u := huniq _ ⟨by
      rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right], by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_invT h]⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : g * unitaryInvT h * g⁻¹ = unitaryInvT h := hconj.trans ht.symm
  calc g * unitaryInvT h = g * unitaryInvT h * g⁻¹ * g := by group
    _ = unitaryInvT h * g := by rw [this]

theorem card_centralizer_projInvT_le (h : UnitaryFieldData 5 1 K) :
    Nat.card (Subgroup.centralizer {unitaryProj h 3 (unitaryInvT h)}) ≤ 240 := by
  have := h.finite
  set C := Subgroup.centralizer {unitaryInvT h} with hC
  have hle : Subgroup.centralizer {unitaryProj h 3 (unitaryInvT h)} ≤ C.map (unitaryProj h 3) := by
    intro x hx
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
    exact ⟨g, mem_centralizer_of_proj h hx, rfl⟩
  have hZC : unitaryScalars h 3 ≤ C := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp (unitaryScalars_le_center h 3 hz) (unitaryInvT h)).symm
  have hker : ((unitaryProj h 3).comp C.subtype).ker = (unitaryScalars h 3).subgroupOf C := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← MonoidHom.mem_ker,
      ker_unitaryProj, Subgroup.mem_subgroupOf]
  have hk3 : Nat.card ((unitaryProj h 3).comp C.subtype).ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv,
      card_unitaryScalars h (by norm_num)]
    decide
  have hrange : ((unitaryProj h 3).comp C.subtype).range = C.map (unitaryProj h 3) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 := Subgroup.card_mul_index ((unitaryProj h 3).comp C.subtype).ker
  rw [Subgroup.index_ker, hrange, hk3] at h1
  have h2 : Nat.card C ≤ 720 := card_centralizer_invT_le h
  calc Nat.card (Subgroup.centralizer {unitaryProj h 3 (unitaryInvT h)})
      ≤ Nat.card (C.map (unitaryProj h 3)) := Subgroup.card_le_of_le hle
    _ ≤ 240 := by omega

export CFSG.Open.StatedSUFieldChange (glEquiv glEquiv_coe statedSU_generator_iff map_statedSU
  glEquiv_scalar map_statedScalars statedSUEquiv statedSUEquiv_coe statedProjSUEquiv)

end CFSG.Quasithin.Vol2.Ch11.SecS.OE5
