module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSULift

import CFSG.Fischer.Classification.SymplecticTypeTransport
import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.GroupTheory.PerfectSmallModule
import CFSG.GroupTheory.ThreeTranspositions.FischerResidualTop
import CFSG.RankThree.GF2n.Stroth78.Sec2Nineteen
import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeStepA
import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
public import CFSG.Timmesfeld.Bridge.RootStructR2ManySection

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

namespace Sec4PSUEnd

private theorem isSimpleGroup_U2_four_aux : IsSimpleGroup (U2 4) := by
  have : IsSimpleGroup CFSG.GH74.Exceptional.PSp43 :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 3) 2 (by norm_num)
      (Or.inr (Or.inl ⟨by rw [Nat.card_eq_fintype_card, ZMod.card], le_rfl⟩))
  exact CFSG.GH74.Exceptional.psp43EquivU2.symm.isSimpleGroup

private theorem commutator_eq_top_of_mulEquiv_U2_four {W : Type*} [Group W] (φ : W ≃* U2 4) :
    commutator W = ⊤ := by
  have := isSimpleGroup_U2_four_aux
  have hs : IsSimpleGroup W := φ.isSimpleGroup
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator W)).resolve_left fun hb => ?_
  have hc : IsMulCommutative W := (commutator_eq_bot_iff _).1 hb
  have hp := (Group.is_simple_iff_prime_card (α := W)).1 hs
  rw [Nat.card_congr φ.toEquiv, CFSG.GH74.Exceptional.card_U2_four] at hp
  norm_num at hp

theorem rhoZ_Xsub_eq_one (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
    ∀ x ∈ Xsub S a, rhoZ S x = 1 := by
  classical
  by_contra hX
  push Not at hX
  have hR := forall_Rbar_eq_one_of_rhoZ_Xsub S h h217 hX
  obtain ⟨d₀, hd₀R, hd₀1, φ₀, hφ₀⟩ := Sec4PSU.exists_mem_Rbar_mulEquiv_U2 S h h217 h3 hα hpsu
  have hns : ¬ IsSymplecticType (threeResidualClass d₀) := fun hs =>
    not_isSymplecticType_DU (m := 4) (by norm_num) (by
      have := hs.image (φ₀ : ↥(threeResidualQuot d₀) →* U2 4)
      rwa [MonoidHom.coe_coe, hφ₀] at this)
  have hstep := derivedSeries_two_le_ker_rhoW S h h217 h3 hd₀R hd₀1 hns
  have hcW : commutator ↥(threeResidualQuot d₀) = ⊤ := commutator_eq_top_of_mulEquiv_U2_four φ₀
  have hW2 : derivedSeries ↥(threeResidualQuot d₀) 2 = ⊤ := by
    rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_zero, ← commutator_def, hcW,
      ← commutator_def, hcW]
  have hmap : (derivedSeries ↥(threeResidualJoin d₀) 2).map (residualProj d₀) = ⊤ := by
    rw [map_derivedSeries_eq (residualProj_surjective d₀), hW2]
  have hmem : residualProj d₀ (residualSelf d₀) ∈
      (derivedSeries ↥(threeResidualJoin d₀) 2).map (residualProj d₀) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyd⟩ := Subgroup.mem_map.mp hmem
  have hk : y⁻¹ * residualSelf d₀ ∈ (residualProj d₀).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyd, inv_mul_cancel]
  have hWd : rhoW S a d₀ (residualSelf d₀) = rhoW S a d₀ (y⁻¹ * residualSelf d₀) := by
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp (hstep hy), inv_one, one_mul]
  have hd₀E : (d₀ : Hbar z) ∈ Eset S a :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hd₀R hd₀1)
  have hord : orderOf d₀ = 2 := (pair_Xsub S h h217 h3).2.2.1 d₀ hd₀E
  have hsq : residualSelf d₀ ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, residualSelf_coe, ← hord, pow_orderOf_eq_one]
    rfl
  have h2 : orderOf (rhoW S a d₀ (residualSelf d₀)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hsq, map_one])
  have hodd : Odd (orderOf (rhoW S a d₀ (residualSelf d₀))) := by
    rw [hWd]
    exact ((odd_card_ker_residualProj d₀ (odd_card_center_Xsub S a)).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hk)).of_dvd_nat (orderOf_map_dvd _ _)
  have h1 : rhoZ S (d₀ : Hbar z) = 1 := by
    show rhoW S a d₀ (residualSelf d₀) = 1
    rw [← orderOf_eq_one_iff]
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
    · exact h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  exact hd₀1 (hR _ hd₀R fun u => by rw [h1]; rfl)

theorem nonempty_mulEquiv_U2 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
    Nonempty (↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a) ≃* U2 4) := by
  obtain ⟨d₀, hd₀R, hd₀1, φ₀, -⟩ := Sec4PSU.exists_mem_Rbar_mulEquiv_U2 S h h217 h3 hα hpsu
  have := isSimpleGroup_U2_four_aux
  have hs : IsSimpleGroup ↥(threeResidualQuot d₀) := φ₀.isSimpleGroup
  have hd₀E : d₀ ∈ Subtype.val ⁻¹' Eset S a :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hd₀R hd₀1)
  have htop := threeResidualQuot_eq_top_of_isSimpleGroup (pair_Xsub S h h217 h3)
    (twoCore_Xsub S) (threeCore_Xsub S h h217) hd₀E hs
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans φ₀⟩

theorem commutator_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
    ⁅Xsub S a, Xsub S a⁆ = Xsub S a := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_U2 S h h217 h3 hα hpsu
  have hP := pair_Xsub S h h217 h3
  have hc := CFSG.RankThree.GF2n.Stroth80.commutator_eq_top_of_closure_sq_eq_one
    (Group.isPerfect_def.2 (commutator_eq_top_of_mulEquiv_U2_four φ)) (odd_card_center_Xsub S a)
    hP.2.2.2.2 fun s hs => by rw [← hP.2.2.1 s hs]; exact pow_orderOf_eq_one s
  exact Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hc)

theorem exists_rhoLin_aVec_ne (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
    ∃ x ∈ Xsub S a, rhoLin S x (aVec S h.mem_Q) ≠ aVec S h.mem_Q := by
  by_contra hfix
  push Not at hfix
  have hZ1 := rhoZ_Xsub_eq_one S h h217 h3 hα hpsu
  have hle : Xsub S a ≤ CHbar S a :=
    le_CHbar_of_perfect S h.mem_Q (commutator_Xsub S h h217 h3 hα hpsu) hfix
      fun y hy u => by rw [hZ1 y hy]; rfl
  obtain ⟨⟨α₀, hα₀R⟩, hα₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα₀1' : α₀ ≠ 1 := fun h1 => hα₀1 (Subtype.ext h1)
  have hα₀E : α₀ ∈ Eset S a := Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀R hα₀1')
  set d : ↥(Xsub S a) := ⟨α₀, subset_Xsub S a hα₀E⟩
  have hcent : d ∈ Subgroup.center ↥(Xsub S a) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_mem_CHbar_of_card_Rbar_eq_two S a (card_Rbar_eq_two S h h217 h3)
      hα₀R hα₀1' (hle g.2))
  have hord : orderOf d = 2 := (pair_Xsub S h h217 h3).2.2.1 d hα₀E
  have hdvd := Subgroup.orderOf_dvd_natCard _ hcent
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr (odd_card_center_Xsub S a)) (even_iff_two_dvd.mpr hdvd)

theorem rhoLin_eq_self_of_finrank_le_five (S : Setting z E F) {a : G} {w : ℕ}
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
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    {U : Submodule (ZMod 2) (Additive (QbarOf S))}
    (hU : ∀ x ∈ Xsub S a, ∀ u ∈ U, rhoLin S x u ∈ U)
    (hd : Module.finrank (ZMod 2) U ≤ 5) :
    ∀ x ∈ Xsub S a, ∀ u ∈ U, rhoLin S x u = u := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_U2 S h h217 h3 hα hpsu
  have := isSimpleGroup_U2_four_aux
  have hperf : commutator ↥(Xsub S a) = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 (commutator_Xsub S h h217 h3 hα hpsu))
  have h81 : 81 ∣ Nat.card (↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) := by
    rw [Nat.card_congr φ.toEquiv, CFSG.GH74.Exceptional.card_U2_four]
    norm_num
  have h1 : rhoLin S 1 = 1 := by simp [rhoLin]
  let π : ↥(Xsub S a) →* (↥U ≃ₗ[ZMod 2] ↥U) :=
    { toFun := fun x => LinearEquiv.ofLinear
        ((rhoLin S x : _ →ₗ[ZMod 2] _).restrict (hU x x.2))
        ((rhoLin S (x : Hbar z)⁻¹ : _ →ₗ[ZMod 2] _).restrict (hU _ (inv_mem x.2)))
        (LinearMap.ext fun u => Subtype.ext <| by
          show rhoLin S x (rhoLin S (x : Hbar z)⁻¹ u) = u
          rw [← LinearEquiv.mul_apply, ← rhoLin_mul, mul_inv_cancel, h1]
          rfl)
        (LinearMap.ext fun u => Subtype.ext <| by
          show rhoLin S (x : Hbar z)⁻¹ (rhoLin S x u) = u
          rw [← LinearEquiv.mul_apply, ← rhoLin_mul, inv_mul_cancel, h1]
          rfl)
      map_one' := LinearEquiv.ext fun u => Subtype.ext <| by
        show rhoLin S 1 u = u
        rw [h1]
        rfl
      map_mul' := fun x y => LinearEquiv.ext fun u => Subtype.ext <| by
        show rhoLin S ((x : Hbar z) * y) u = rhoLin S x (rhoLin S y u)
        rw [rhoLin_mul, LinearEquiv.mul_apply] }
  intro x hx u hu
  have hπ := CFSG.GroupTheory.eq_one_of_finrank_le_five π hd hperf φ.isSimpleGroup h81 ⟨x, hx⟩
  exact congrArg (fun f : ↥U ≃ₗ[ZMod 2] ↥U => ((f ⟨u, hu⟩ : ↥U) : Additive (QbarOf S))) hπ

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
