module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSULift

import CFSG.Fischer.Classification.SymplecticTypeTransport
import CFSG.RankThree.GF2n.Stroth78.Sec4Bound
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeAct
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeStepA

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.GroupTheory.ThreeTranspositions
open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

theorem stroth78_44 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) {m : ℕ} (hm : 5 ≤ m)
    (hpsu : fischerCentralQuotientModel
      (CFSG.GroupTheory.ThreeTranspositions.threeResidualClass
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m) fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    False := by
  classical
  obtain ⟨d₀, hd₀R, hd₀1, φ₀, hφ₀⟩ := Sec4PSU.exists_mem_Rbar_mulEquiv_U2 S h h217 h3 hα hpsu
  have hns : ¬ IsSymplecticType (threeResidualClass d₀) := fun hs =>
    not_isSymplecticType_DU (m := m) (by omega) (by
      have := hs.image (φ₀ : ↥(threeResidualQuot d₀) →* U2 m)
      rwa [MonoidHom.coe_coe, hφ₀] at this)
  have hstep := derivedSeries_two_le_ker_rhoW S h h217 h3 hd₀R hd₀1 hns
  have hA : ∀ j ∈ ⁅⁅threeResidualJoin d₀, threeResidualJoin d₀⁆,
      ⁅threeResidualJoin d₀, threeResidualJoin d₀⁆⁆, rhoZ S (j : Hbar z) = 1 := by
    have htop : (⊤ : Subgroup ↥(threeResidualJoin d₀)).map (threeResidualJoin d₀).subtype =
        threeResidualJoin d₀ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have heq : ⁅⁅threeResidualJoin d₀, threeResidualJoin d₀⁆,
        ⁅threeResidualJoin d₀, threeResidualJoin d₀⁆⁆ =
        (derivedSeries ↥(threeResidualJoin d₀) 2).map (threeResidualJoin d₀).subtype := by
      rw [show derivedSeries ↥(threeResidualJoin d₀) 2 =
          ⁅⁅(⊤ : Subgroup ↥(threeResidualJoin d₀)), ⊤⁆, ⁅⊤, ⊤⁆⁆ from rfl,
        Subgroup.map_commutator, Subgroup.map_commutator, htop]
    intro j hj
    rw [heq] at hj
    obtain ⟨y, hy, rfl⟩ := hj
    exact MonoidHom.mem_ker.1 (hstep hy)
  have e : alphaInX S h hd₀R = d₀ := Subtype.ext rfl
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(threeResidualQuot (alphaInX S h hd₀R)) ≃* U2 m,
      φ '' threeResidualClass (alphaInX S h hd₀R) = DU m := by
    rw [e]
    exact ⟨φ₀, hφ₀⟩
  have hA' : ∀ j ∈ ⁅⁅threeResidualJoin (alphaInX S h hd₀R), threeResidualJoin (alphaInX S h hd₀R)⁆,
      ⁅threeResidualJoin (alphaInX S h hd₀R), threeResidualJoin (alphaInX S h hd₀R)⁆⁆,
      rhoZ S (j : Hbar z) = 1 := by
    rw [e]
    exact hA
  have hLC : Lbar S a ≤ Subgroup.centralizer {((alphaInX S h hd₀R : ↥(Xsub S a)) : Hbar z)} := by
    rw [coe_alphaInX]
    exact Lbar_le_centralizer S h hd₀R
  set c : MulAut ↥(threeResidualQuot (alphaInX S h hd₀R)) :=
    MulAut.conj ⟨QuotientGroup.mk (alphaInX S h hd₀R),
      mk_mem_threeResidualQuot_self (alphaInX S h hd₀R)⟩ with hc
  have hrange : ((actL S h hd₀R).range : Set (MulAut ↥(threeResidualQuot (alphaInX S h hd₀R)))) ⊆
      {1, c} := by
    rintro _ ⟨l, rfl⟩
    have hl : actL S h hd₀R l =
        residualConj (alphaInX S h hd₀R) (Subgroup.inclusion hLC l) := by
      apply MulEquiv.ext
      rintro ⟨y, hy⟩
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
      apply Subtype.ext
      rw [actL_apply S h hd₀R l n hy, residualConj_apply_mk]
      rfl
    rw [hl]
    rcases Sec4PSU.residualConj_eq_one_or_conj_of_mem_Lbar S h hd₀R hd₀1 hA' hm φ hφ
      (Subgroup.inclusion hLC l) l.2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hle2 : Nat.card (actL S h hd₀R).range ≤ 2 := by
    calc Nat.card (actL S h hd₀R).range
        = Nat.card ↥((actL S h hd₀R).range :
            Set (MulAut ↥(threeResidualQuot (alphaInX S h hd₀R)))) := rfl
      _ ≤ Nat.card ↥({1, c} : Set (MulAut ↥(threeResidualQuot (alphaInX S h hd₀R)))) :=
          Nat.card_mono (Set.toFinite _) hrange
      _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have hcount := card_Lbar_le_two_mul_card_range_actL S h h217 h3 hd₀R hd₀1
  exact false_of_card_Lbar_le_four S h (by omega)

end CFSG.RankThree.GF2n.Stroth78
