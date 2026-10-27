module

public import CFSG.RankThree.GF2n.Stroth78.Sec4SevenR5
public import CFSG.RankThree.GF2n.Stroth78.Sec4SixWMain
public import CFSG.RankThree.GF2n.Stroth78.Sec4OneW
public import CFSG.RankThree.GF2n.Stroth78.Sec4TwoResidual
public import CFSG.RankThree.GF2n.Stroth78.Sec4PSU
public import CFSG.RankThree.GF2n.Stroth78.Sec3Six
public import CFSG.Fischer.Classification.Final
public import CFSG.Fischer.Classification.PartII.O2G.ThreeFinal

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification Matrix

namespace Sec4Seven

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem hasType_of_isConj {X : Type} [Group X] {d d₀ : X} (hc : IsConj d d₀) (k : Fin 3)
    (hk : HasType k ↥(threeResidualQuot d) (threeResidualClass d)) :
    HasType k ↥(threeResidualQuot d₀) (threeResidualClass d₀) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  refine (CFSG.Fischer.hasType_congr k (threeResidualQuotConjEquiv c d) ?_).1 hk
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_threeResidualClass_conj_iff c d x).2 hx
  · intro hy
    refine ⟨(threeResidualQuotConjEquiv c d).symm y, ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [← mem_threeResidualClass_conj_iff c d, MulEquiv.apply_symm_apply]
    exact hy

section Certificates


theorem stroth78_47_of_inputs (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
    (hs3 : ∀ _ : ↥(threeResidualQuot
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))) ≃*
        Equiv.Perm (Fin 3), False)
    (hs6 : ∀ φ : ↥(threeResidualQuot
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))) ≃* Equiv.Perm (Fin 6),
      (∀ g, g ∈ threeResidualClass
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)) ↔ (φ g).IsSwap) →
      StrothCaseVIII z w)
    (hsp2 : ∀ {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}, (∀ x, b x x = 0) →
      (∀ x, (∀ y, b x y = 0) → x = 0) →
      fischerLinearModel
        (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0) →
      StrothCaseVIII z w)
    (ho42 : ∀ {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)},
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) →
      (¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) →
      fischerLinearModel
        (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
        (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1) → False)
    (hpsu : fischerCentralQuotientModel
        (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
        (fischerTransvections (fischerHermitianF4 4)
          fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0) →
      StrothCaseV z w ∨ StrothCaseVI z w) :
    StrothCaseV z w ∨ StrothCaseVI z w ∨ StrothCaseVIII z w := by
  have hpsu' : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4)
        fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0) →
      StrothCaseV z w ∨ StrothCaseVI z w ∨ StrothCaseVIII z w := fun hU =>
    (hpsu hU).elim Or.inl (fun h6 => Or.inr (Or.inl h6))
  rcases stroth78_36 S h (statement_of_twinFour o2TwinFourInput) h217 h3 hα with
    hcl | ⟨k, hk⟩
  · rcases hcl with ⟨m, hm, φ, hφ⟩ | ⟨m, hm, b, halt, hnd, hsp⟩ |
      ⟨m, hm, Q, hnd, hno, hO⟩ | ⟨m, hm, hU⟩ | ⟨m, hm, f, hsymm, hnd, hmod⟩
    ·
      rcases hm with rfl | hm5
      · exact (hs3 φ).elim
      rcases Nat.lt_or_ge m 7 with hlt | hge
      · interval_cases m
        · exact ((stroth78_42_threeResidualQuot S h h217 h3
            (Tset_subset_Eset S a hα)).false φ).elim
        · exact Or.inr (Or.inr (hs6 φ hφ))
      · exact (stroth78_41 S h h217 h3 hα hge φ hφ).elim
    ·
      rcases Nat.lt_or_ge m 3 with hlt | hge
      · obtain rfl : m = 2 := by omega
        exact Or.inr (Or.inr (hsp2 halt hnd hsp))
      · exact Or.inr (Or.inr (stroth78_46 S h h217 h3 hα hge halt hnd hsp))
    ·
      rcases Nat.lt_or_ge m 3 with hlt | hge
      · obtain rfl : m = 2 := by omega
        exact (ho42 hnd (hno rfl) hO).elim
      · exact (stroth78_45 S h h217 h3 hα hge hnd hO).elim
    ·
      rcases Nat.lt_or_ge m 5 with hlt | hge
      · obtain rfl : m = 4 := by omega
        exact hpsu' hU
      · exact (stroth78_44 S h h217 h3 hα hge hU).elim
    ·
      rcases Nat.lt_or_ge m 6 with hlt | hge
      · obtain rfl : m = 5 := by omega
        exact hpsu' (stroth78_47_r5 S h h217 h3 hα hsymm hnd hmod)
      · obtain ⟨α₀, hα₀, hα₀1, hc⟩ := Sec4OneW.exists_mem_Rbar_isConj S h h217 h3 hα
        exact (stroth78_43_orthogonal S h h217 h3 hα₀ hα₀1 hge hsymm hnd
          (Sec4PSU.fischerCentralQuotientModel_of_isConj hc hmod)).elim
  ·
    obtain ⟨α₀, hα₀, hα₀1, hc⟩ := Sec4OneW.exists_mem_Rbar_isConj S h h217 h3 hα
    exact (stroth78_43_hasType S h h217 h3 hα₀ hα₀1 k (hasType_of_isConj hc k hk)).elim

end Certificates

end Sec4Seven

end CFSG.RankThree.GF2n.Stroth78
