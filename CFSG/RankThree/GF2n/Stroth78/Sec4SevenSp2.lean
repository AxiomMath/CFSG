module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Six

import CFSG.LargeExtraspecial.S12InspFamSix
import CFSG.RankThree.GF2n.Stroth78.Sec3Six
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6
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

theorem stroth78_47_sp2 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    StrothCaseVIII z w := by
  have hd : (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)) ∈
      (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := Tset_subset_Eset S a hα
  have hH := hyp_threeResidualQuot (pair_Xsub S h h217 h3) (twoCore_Xsub S)
    (threeCore_Xsub S h h217) hd
  obtain ⟨-, ⟨e, hE⟩, -⟩ := hH.pair
  obtain ⟨φ, hφ⟩ := CFSG.LargeExtraspecial.S12Insp5.exists_perm_six_of_sp_two
    ⟨e, by rw [hE]; exact IsConj.refl e, fun d => by rw [hE]; rfl⟩ halt hnd hsp
  exact stroth78_47_s6 S h h217 h3 hα φ hφ

end CFSG.RankThree.GF2n.Stroth78
