module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt

import CFSG.GroupTheory.ClassTwoCommutator
public import CFSG.RankThree.GF2n.Smith81.Sec1Types

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Centre95.comm_mem_Z_of_mem_Wt (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hcen : Centre95 hc t Z0) {z w : G} (hz : z ∈ Z0)
    (hw : w ∈ Wt Q (Vt M (LB M Q B) B Z t)) : ⁅z, w⁆ ∈ Z := by
  obtain ⟨hZ0LB, -, hV⟩ := hcen
  have hzLB : z ∈ LB M Q B := (Subgroup.mem_inf.mp (hZ0LB hz)).1
  by_cases hzQ : z ∈ Q
  · exact Smith81.comm_mem_Z hc.hyp hzQ hw.1
  · have hznorm : z ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 (hc.LB_le_M hzLB)
    have hzwQ : z * w * z⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hznorm w).mp hw.1
    have haQ : ⁅z, w⁆ ∈ Q := by
      have e : ⁅z, w⁆ = (z * w * z⁻¹) * w⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact Q.mul_mem hzwQ (Q.inv_mem hw.1)
    have hZQ : Z ≤ Subgroup.centralizer (Q : Set G) := fun ζ hζ =>
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (hc.hyp.toHyp79.V_central hζ hq).symm
    have hQQ : ⁅Q, Q⁆ ≤ Z :=
      Subgroup.commutator_le.mpr fun a ha b hb => hc.hyp.toHyp79.comm_mem_V ha hb
    have hsZ : z ∈ Subgroup.centralizer (Z : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun ζ hζ => by
        have h := hc.LB_centralizes_Z hzLB ζ hζ
        calc ζ * z = (z * ζ * z⁻¹) * z := by rw [h]
          _ = z * ζ := by group
    have hcentral : ⁅z, w⁆ ∈ Subgroup.centralizer (Q : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have hyV : ⁅z⁻¹, y⁆ ∈ Vt M (LB M Q B) B Z t := by
        have h1 : ⁅y, z⁻¹⁆ ∈ ⁅Q, Subgroup.zpowers z⁆ :=
          Subgroup.commutator_mem_commutator hy
            ((Subgroup.zpowers z).inv_mem (Subgroup.mem_zpowers z))
        have h2 : ⁅y, z⁻¹⁆ ∈ Vt M (LB M Q B) B Z t := by
          rw [← hV z hz hzQ]
          exact Subgroup.mem_sup_left h1
        simpa only [commutatorElement_inv] using (Vt M (LB M Q B) B Z t).inv_mem h2
      have hcomm : ⁅⁅z, w⁆, y⁆ = 1 := by
        rw [CFSG.GroupTheory.commutatorElement_commutatorElement_eq_of_classTwo
          hZQ hQQ hznorm hsZ hw.1 hy]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          ((Subgroup.mem_centralizer_iff.mp hw.2 _ hyV).symm)
      exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
    rw [hc.hyp.hZ, cen_eq]
    exact ⟨haQ, hcentral⟩

end HS9

end CFSG.RankThree.GF2n.Stroth80
