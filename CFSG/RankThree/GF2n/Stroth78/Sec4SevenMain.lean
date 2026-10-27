module

public import CFSG.RankThree.GF2n.Stroth78.Sec4Seven
public import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS3
public import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6
public import CFSG.RankThree.GF2n.Stroth78.Sec4SevenSp2
public import CFSG.RankThree.GF2n.Stroth78.Sec4SevenOrthMinus2

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification Matrix

namespace Sec4Seven

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}


theorem stroth78_47_of_psu42 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
        (fischerTransvections (fischerHermitianF4 4)
          fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0) →
      StrothCaseV z w ∨ StrothCaseVI z w) :
    StrothCaseV z w ∨ StrothCaseVI z w ∨ StrothCaseVIII z w :=
  stroth78_47_of_inputs S h h217 h3 hα (stroth78_47_s3 S h h217 h3 hα)
    (stroth78_47_s6 S h h217 h3 hα)
    (fun halt hnd hsp => stroth78_47_sp2 S h h217 h3 hα halt hnd hsp)
    (fun hnd hminus hO => stroth78_47_orthMinus2 S h h217 h3 hα hnd hminus hO) hpsu

end Sec4Seven

end CFSG.RankThree.GF2n.Stroth78
