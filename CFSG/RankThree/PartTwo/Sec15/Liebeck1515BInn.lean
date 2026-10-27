module

import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

variable {Q : Type*} [Group Q] {U V : Subgroup Q}

theorem mem_center_iff_of_mem_right [U.Normal] (hUV : U ⊔ V = ⊤) (hc : ⁅U, V⁆ = ⊥) {v : Q}
    (hv : v ∈ V) : v ∈ Subgroup.center Q ↔ (⟨v, hv⟩ : ↥V) ∈ Subgroup.center ↥V := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h w
    exact Subtype.ext (h w)
  · intro h g
    obtain ⟨y, hy, w, hw, rfl⟩ := Item148PtRes.exists_mul_eq hUV g
    have h1 : y * v = v * y := Item148PtRes.commute_of_commutator_eq_bot hc hy hv
    have h2 : w * v = v * w := congrArg Subtype.val (h ⟨w, hw⟩)
    calc y * w * v = y * (v * w) := by rw [mul_assoc, h2]
      _ = v * (y * w) := by rw [← mul_assoc, h1, mul_assoc]

theorem nonempty_mulEquiv_map_conj [U.Normal] (hUV : U ⊔ V = ⊤) (hc : ⁅U, V⁆ = ⊥)
    (hV : Nonempty (↥V ⧸ Subgroup.center ↥V ≃* alternatingGroup (Fin 6))) :
    Nonempty (↥(V.map (MulAut.conj : Q →* MulAut Q)) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := hV
  set φ : ↥V →* MulAut Q := (MulAut.conj : Q →* MulAut Q).comp V.subtype with hφ
  have hker : φ.ker = Subgroup.center ↥V := by
    ext ⟨v, hv⟩
    rw [MonoidHom.mem_ker, ← mem_center_iff_of_mem_right hUV hc hv, Subgroup.mem_center_iff]
    constructor
    · intro h g
      have := congrArg (fun σ : MulAut Q => σ g) h
      simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply,
        MulAut.one_apply] at this
      calc g * v = v * g * v⁻¹ * v := by rw [this]
        _ = v * g := by group
    · intro h
      ext g
      simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply,
        MulAut.one_apply]
      rw [← h g, mul_inv_cancel_right]
  have hrange : φ.range = V.map (MulAut.conj : Q →* MulAut Q) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange φ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans e))⟩

theorem center_le_inf [Finite Q] [U.Normal] (hUV : U ⊔ V = ⊤) (hc : ⁅U, V⁆ = ⊥)
    (h3 : Nat.card ↥(U ⊓ V) = 3) (hZU : Nat.card (Subgroup.center ↥U) = 3)
    (hZV : Nat.card (Subgroup.center ↥V) = 3) : Subgroup.center Q ≤ U ⊓ V := by
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Item148PtRes.exists_mul_eq hUV z
  have hzc := Subgroup.mem_center_iff.mp hz
  have huZ : u ∈ U ⊓ V := by
    rw [Item148PtRes.inf_eq_centerIn_left hc h3 hZU]
    refine Item148PtRes.mem_centerIn_iff.mpr ⟨hu, Subgroup.mem_center_iff.mpr fun y => ?_⟩
    apply Subtype.ext
    have h1 := hzc y
    have h2 : (y : Q) * v = v * y := Item148PtRes.commute_of_commutator_eq_bot hc y.2 hv
    simp only [Subgroup.coe_mul]
    have : (y : Q) * u * v = u * y * v := by
      calc (y : Q) * u * v = y * (u * v) := by rw [mul_assoc]
        _ = u * v * y := h1
        _ = u * (v * y) := by rw [mul_assoc]
        _ = u * (y * v) := by rw [h2]
        _ = u * y * v := by rw [mul_assoc]
    exact mul_right_cancel this
  have hvZ : v ∈ U ⊓ V := by
    rw [Item148PtRes.inf_eq_centerIn_right hc h3 hZV]
    refine Item148PtRes.mem_centerIn_iff.mpr ⟨hv, Subgroup.mem_center_iff.mpr fun y => ?_⟩
    apply Subtype.ext
    have h1 := hzc y
    have h2 : u * (y : Q) = y * u := Item148PtRes.commute_of_commutator_eq_bot hc hu y.2
    simp only [Subgroup.coe_mul]
    have : u * ((y : Q) * v) = u * (v * y) := by
      calc u * ((y : Q) * v) = u * y * v := by rw [mul_assoc]
        _ = y * u * v := by rw [h2]
        _ = y * (u * v) := by rw [mul_assoc]
        _ = u * v * y := h1
        _ = u * (v * y) := by rw [mul_assoc]
    exact mul_left_cancel this
  exact ⟨mul_mem huZ.1 hvZ.1, mul_mem huZ.2 hvZ.2⟩

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
