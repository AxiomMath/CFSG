module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem fittingSubgroup_inf_bar_H0_eq_bot [(Q.subgroupOf M).Normal]
    (h44 : Stroth44Statement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    fittingSubgroup (Mbar M Q) ⊓ bar M Q (H0 M Z) = ⊥ := by
  classical
  haveI hFn : (fittingSubgroup (Mbar M Q)).Normal := CFSG.fittingSubgroup_normal
  haveI : Group.IsNilpotent ↥(fittingSubgroup (Mbar M Q)) := CFSG.fittingSubgroup_nilpotent
  have hodd : Odd (Nat.card ↥(fittingSubgroup (Mbar M Q))) :=
    odd_card_of_normal_nilpotent hc.pCore_two_Mbar _
  haveI hHn : (bar M Q (H0 M Z)).Normal := hc.normal_bar_H0
  let A : Subgroup (Mbar M Q) := fittingSubgroup (Mbar M Q) ⊓ bar M Q (H0 M Z)
  haveI hAn : A.Normal := inferInstance
  have hA0 : A = ⊥ := h44 G M Q Z B hc n hw hn hno hgen A inf_le_right
    (fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hAn]
      exact Subgroup.mem_top x)
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left))
  exact hA0

private theorem commute_of_mem_fittingSubgroup_of_mem_bar_H0 [(Q.subgroupOf M).Normal]
    (h44 : Stroth44Statement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) {f : Mbar M Q}
    (hf : f ∈ fittingSubgroup (Mbar M Q)) {h : Mbar M Q} (hh : h ∈ bar M Q (H0 M Z)) :
    f * h = h * f := by
  haveI hFn : (fittingSubgroup (Mbar M Q)).Normal := CFSG.fittingSubgroup_normal
  haveI hHn : (bar M Q (H0 M Z)).Normal := hc.normal_bar_H0
  have hA0 := fittingSubgroup_inf_bar_H0_eq_bot h44 hc hw hn hno hgen
  have hfF : f * h * f⁻¹ * h⁻¹ ∈ fittingSubgroup (Mbar M Q) := by
    have := (fittingSubgroup (Mbar M Q)).mul_mem hf
      (Subgroup.Normal.conj_mem inferInstance f⁻¹ ((fittingSubgroup (Mbar M Q)).inv_mem hf) h)
    simpa [mul_assoc] using this
  have hH1 : f * h * f⁻¹ * h⁻¹ ∈ bar M Q (H0 M Z) :=
    (bar M Q (H0 M Z)).mul_mem (hHn.conj_mem h hh f) ((bar M Q (H0 M Z)).inv_mem hh)
  have h2 : f * h * f⁻¹ * h⁻¹ ∈
      fittingSubgroup (Mbar M Q) ⊓ bar M Q (H0 M Z) := ⟨hfF, hH1⟩
  rw [hA0, Subgroup.mem_bot] at h2
  calc f * h = (f * h * f⁻¹ * h⁻¹) * (h * f) := by group
    _ = h * f := by rw [h2, one_mul]

theorem Ctx.eq_one_of_centralizes_layer [(Q.subgroupOf M).Normal] (h44 : Stroth44Statement)
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hgen : GenByB M Q B) {x : Mbar M Q} (hx : x ∈ bar M Q (H0 M Z))
    (hcomm : ∀ y ∈ layer (Mbar M Q), x * y = y * x) : x = 1 := by
  classical
  let F : Subgroup (Mbar M Q) := fittingSubgroup (Mbar M Q)
  let E : Subgroup (Mbar M Q) := layer (Mbar M Q)
  have hA0 : F ⊓ bar M Q (H0 M Z) = ⊥ :=
    fittingSubgroup_inf_bar_H0_eq_bot h44 hc hw hn hno hgen
  have hcommF : ∀ y ∈ F, y * x = x * y := fun y hy =>
    commute_of_mem_fittingSubgroup_of_mem_bar_H0 h44 hc hw hn hno hgen hy hx
  have hFE : F ⊔ E ≤ Subgroup.centralizer ({x} : Set (Mbar M Q)) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommF y hy
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm y hy).symm
  have hcommFstar : ∀ y ∈ generalizedFitting (Mbar M Q), y * x = x * y := by
    intro y hy
    rw [generalizedFitting.eq_sup] at hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hFE hy)
  have hxF : x ∈ generalizedFitting (Mbar M Q) :=
    CFSG.centralizer_generalizedFitting_le (Mbar M Q)
      (Subgroup.mem_centralizer_iff.mpr hcommFstar)
  let C : Subgroup (Mbar M Q) :=
    (Subgroup.center ↥(generalizedFitting (Mbar M Q))).map
      (generalizedFitting (Mbar M Q)).subtype
  have hxC : x ∈ C := by
    refine Subgroup.mem_map.mpr ⟨⟨x, hxF⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcommFstar y y.2)
  haveI hFchar : (generalizedFitting (Mbar M Q)).Characteristic :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := Mbar M Q)).1
  haveI hFn : (generalizedFitting (Mbar M Q)).Normal := inferInstance
  have hCn : C.Normal := ConjAct.normal_of_characteristic_of_normal
  have hCnil : Group.IsNilpotent ↥C :=
    (Group.isNilpotent_congr ((Subgroup.center ↥(generalizedFitting (Mbar M Q))).equivMapOfInjective
      (generalizedFitting (Mbar M Q)).subtype
      (generalizedFitting (Mbar M Q)).subtype_injective)).mp inferInstance
  have hCfit : C ∈ {N : Subgroup (Mbar M Q) | N.Normal ∧ Group.IsNilpotent N} :=
    ⟨hCn, hCnil⟩
  have hxA : x ∈ F ⊓ bar M Q (H0 M Z) := ⟨le_sSup hCfit hxC, hx⟩
  rwa [hA0, Subgroup.mem_bot] at hxA

theorem Ctx.layer_le_bar_H0 [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hgen : GenByB M Q B) : layer (Mbar M Q) ≤ bar M Q (H0 M Z) :=
  (layer_le_of_not_centralizes hc.normal_bar_Lgen (hc.noComm h34 hw hn hno hgen)).trans
    hc.bar_Lgen_le_bar_H0

end CFSG.RankThree.GF2n.Stroth80
