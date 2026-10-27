module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEnd

import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndAut
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndCenter
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusNotCentral

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

namespace Sec4PSUEnd

theorem commute_of_rhoZ_mk_eq_one (S : Setting z E F) {x : ↥(H z)}
    (hx : rhoZ S (QuotientGroup.mk x) = 1) {y : G} (hy : y ∈ ZQ z) :
    (x : G) * y = y * (x : G) := by
  have h2 := rhoZ_mk S x ⟨y, hy⟩
  rw [hx] at h2
  change y = (x : G) * y * (x : G)⁻¹ at h2
  calc (x : G) * y = (x : G) * y * (x : G)⁻¹ * (x : G) := by group
    _ = y * (x : G) := by rw [← h2]

theorem caseV (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
    (hw : w = 4) (hC : Subgroup.centralizer (Xsub S a : Set (Hbar z)) = ⊥) :
    StrothCaseV z w := by
  classical
  obtain ⟨φ⟩ := nonempty_Xsub_mulEquiv_U2 S h h217 h3 hα hpsu (by omega)
  have hZ := rhoZ_Xsub_eq_one S h h217 h3 hα hpsu
  have hne : Xsub S a ≠ ⊤ := by
    intro htop
    apply not_zq_le_centerIn_H S h
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨Q_le_H S (Subgroup.mem_inf.mp hy).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact commute_of_rhoZ_mk_eq_one S (x := ⟨x, hx⟩) (hZ _ (htop ▸ Subgroup.mem_top _)) hy
  have hKC : (⊤ : Subgroup (Hbar z)) ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z)) = ⊥ := by
    rw [hC, inf_bot_eq]
  obtain ⟨e⟩ := nonempty_mulEquiv_oMinusSixTwo_of_inf_centralizer_eq_bot φ le_top hne hKC
  have hH : Nat.card (Hbar z) = 51840 := by
    rw [← Subgroup.card_top, Nat.card_eq_of_bijective _
      (bijective_conjNormal_comp_subtype φ le_top hne hKC), card_mulAut_of_mulEquiv_U2 φ]
  have hX : Nat.card ↥(Xsub S a) = 25920 :=
    (Nat.card_congr φ.toEquiv).trans CFSG.GH74.Exceptional.card_U2_four
  have hq : Nat.card (Hbar z ⧸ Xsub S a) = 2 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Xsub S a)
    rw [hH, hX] at hc
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (Hbar z ⧸ Xsub S a) := isCyclic_of_prime_card hq
  have hder : commutator (Hbar z) ≤ Xsub S a :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hcomm : ∀ x ∈ ⁅H z, H z⁆, ∀ y ∈ ZQ z, Commute x y := by
    intro x hx y hy
    let T : Subgroup ↥(H z) := ⊤
    have hT : T.map (H z).subtype = H z := by
      rw [show T = ⊤ from rfl, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hx' : x ∈ (⁅T, T⁆ : Subgroup ↥(H z)).map (H z).subtype := by
      rw [Subgroup.map_commutator, hT]
      exact hx
    obtain ⟨x', hx'm, rfl⟩ := hx'
    have hmem : (QuotientGroup.mk x' : Hbar z) ∈ commutator (Hbar z) := by
      have h1 : QuotientGroup.mk' ((Q z).subgroupOf (H z)) x' ∈
          (⁅T, T⁆ : Subgroup ↥(H z)).map (QuotientGroup.mk' ((Q z).subgroupOf (H z))) :=
        Subgroup.mem_map_of_mem _ hx'm
      rw [Subgroup.map_commutator] at h1
      rw [commutator_def]
      exact Subgroup.commutator_mono le_top le_top h1
    exact commute_of_rhoZ_mk_eq_one S (hZ _ (hder hmem)) hy
  exact ⟨hw, ⟨inferInstance, ⟨Subgroup.topEquiv.symm.trans e⟩⟩, hcomm, not_zq_le_centerIn_H S h⟩

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
