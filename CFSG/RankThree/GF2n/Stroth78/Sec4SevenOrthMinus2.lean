module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Six

import CFSG.Fischer.Classification.O4Minus2S5
import CFSG.RankThree.GF2n.Stroth78.Sec4TwoResidual
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem stroth78_47_orthMinus2 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    {Qf : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Qf x y = 0) → x = 0)
    (hminus : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Qf w = 0)
    (hO : fischerLinearModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => ∀ x, Qf (A *ᵥ x) = Qf x)
      (fischerTransvections (QuadraticMap.polar Qf) fun v => Qf v = 1)) : False := by
  obtain ⟨φ, -⟩ := hO
  obtain ⟨e, -⟩ := CFSG.Fischer.Classification.o4minus2_equiv_s5 (Q := Qf) hnd hminus
  exact (stroth78_42_threeResidualQuot S h h217 h3
    (d := ⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩) (Tset_subset_Eset S a hα)).false
    (φ.trans e)

end CFSG.RankThree.GF2n.Stroth78
