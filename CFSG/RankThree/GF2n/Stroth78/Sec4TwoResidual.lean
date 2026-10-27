module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual

import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.GroupTheory.ThreeTranspositions.FischerResidualAction
import CFSG.GroupTheory.PermFiveOverNormal

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.GroupTheory.ThreeTranspositions

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem stroth78_42_threeResidualQuot (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hd : (d : Hbar z) ∈ Eset S a) :
    IsEmpty (↥(threeResidualQuot d) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨N, hNn, hNc, hNW⟩ :=
    exists_normal_le_threeResidualQuot (X := ↥(Xsub S a))
      (E := Subtype.val ⁻¹' Eset S a) (pair_Xsub S h h217 h3)
      (twoCore_Xsub S) (threeCore_Xsub S h h217) (d := d) hd
  exact ⟨fun e => (stroth78_42 S h h217).false
    (CFSG.GroupTheory.nonempty_mulEquiv_perm_five e hNn hNW hNc).some⟩

end CFSG.RankThree.GF2n.Stroth78
