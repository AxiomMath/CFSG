module

public import CFSG.GH74.KGroups.PSL2
public import CFSG.GH74.GLS.C3.Layer1.Th2P64E

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Blueprint

theorem psl225_exists_conj_product {S : Type} [Group S] (h : LieModel S .PSL 2 5 2) {i : S}
    (hi : orderOf i = 2) : ∃ g : S, orderOf (i * (g * i * g⁻¹)) = 13 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let F := GaloisField 5 2
  have hFcard : Nat.card F = 5 ^ 2 := GaloisField.card 5 2 (by norm_num)
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := F) 5 2 (by norm_num) hFcard h
  obtain ⟨D, ⟨d⟩⟩ := CFSG.Glauberman.Dickson.exists_dihedral_subgroup (F := F) (p := 5) (f := 2)
    hFcard (z := 13) (Or.inl (by norm_num))
  have hconj : ∀ c x : S, orderOf (c * x * c⁻¹) = orderOf x := fun c x => by
    simpa [MulAut.conj_apply] using (MulAut.conj c).orderOf_eq x
  have hord : ∀ x : DihedralGroup 13, orderOf (e.symm (d.symm x).1) = orderOf x := fun x => by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have ha : orderOf (e.symm (d.symm (DihedralGroup.sr 0)).1) = 2 := by
    rw [hord, DihedralGroup.orderOf_sr]
  have hb : orderOf (e.symm (d.symm (DihedralGroup.sr 1)).1) = 2 := by
    rw [hord, DihedralGroup.orderOf_sr]
  have hab : orderOf (e.symm (d.symm (DihedralGroup.sr 0)).1 *
      e.symm (d.symm (DihedralGroup.sr 1)).1) = 13 := by
    have hmul : e.symm (d.symm (DihedralGroup.sr 0)).1 * e.symm (d.symm (DihedralGroup.sr 1)).1 =
        e.symm (d.symm (DihedralGroup.sr 0 * DihedralGroup.sr 1)).1 := by
      rw [map_mul d.symm, Subgroup.coe_mul, map_mul e.symm]
    rw [hmul, hord, DihedralGroup.sr_mul_sr, sub_zero, DihedralGroup.orderOf_r_one]
  have hone : ∀ u v : S, orderOf u = 2 → orderOf v = 2 → IsConj u v :=
    CFSG.GH74.GLS.Th2.Obs.isConj_of_hasL2Model_odd
      ⟨5, 2, by norm_num, by norm_num, by decide, h⟩
  generalize e.symm (d.symm (DihedralGroup.sr 0)).1 = a at ha hab
  generalize e.symm (d.symm (DihedralGroup.sr 1)).1 = b at hb hab
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone a i ha hi)
  have hcb : orderOf (c * b * c⁻¹) = 2 := by rw [hconj, hb]
  obtain ⟨g, hg⟩ := isConj_iff.1 (hone i (c * b * c⁻¹) hi hcb)
  refine ⟨g, ?_⟩
  have hprod : i * (g * i * g⁻¹) = c * (a * b) * c⁻¹ := by
    rw [hg, ← hc]
    group
  rw [hprod, hconj, hab]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
