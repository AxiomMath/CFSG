module


import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndCaseVI
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndCases
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndWidth
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth78.Sec2Six
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem stroth78_47_psu42 (S : Setting z E F) {a : G} {w : ℕ}
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
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0)) :
    StrothCaseV z w ∨ StrothCaseVI z w := by
  have hw := Sec4PSUEnd.eq_four S h h217 h3 hα hpsu
  rcases (Subgroup.centralizer (Xsub S a : Set (Hbar z))).bot_or_exists_ne_one with
    hC | ⟨ρ, hρC, hρ1⟩
  · exact Or.inl (Sec4PSUEnd.caseV S h h217 h3 hα hpsu hw hC)
  · exact Or.inr (Sec4PSUEnd.caseVI S h h217 h3 hα hpsu hw hρC hρ1)

end CFSG.RankThree.GF2n.Stroth78
