module

public import CFSG.RankThree.PartTwo.Sec21.Item22Statements
public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

open Subgroup
open scoped MatrixGroups commutatorElement

theorem inSubgroup_layer_eq_of_commutator_mem {G : Type*} [Group G] {H N : Subgroup G}
    (hNH : N ≤ H) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ N)
    (hN : CFSG.IsQuasisimple N) : CFSG.inSubgroup CFSG.layer H = N := by
  have hcH : _root_.commutator H ≤ N.subgroupOf H := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf, commutatorElement_def]
    exact hcomm a a.2 b b.2
  have hnorm : (N.subgroupOf H).Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [e]
    refine mul_mem (hcH ?_) hn
    rw [_root_.commutator_def, show g * n * g⁻¹ * n⁻¹ = ⁅g, n⁆ from
      (commutatorElement_def g n).symm]
    exact Subgroup.commutator_mem_commutator (mem_top g) (mem_top n)⟩
  have hcomp : CFSG.IsComponent (N.subgroupOf H) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNH).symm hN,
      hnorm.isSubnormal⟩
  have hlayer : CFSG.layer H = N.subgroupOf H := by
    refine le_antisymm (sSup_le fun L hL => ?_) (CFSG.LocalCores.component_le_layer hcomp)
    have hLperf : L = ⁅L, L⁆ := (Subgroup.isPerfect_iff.1 hL.1.1).symm
    calc L = ⁅L, L⁆ := hLperf
      _ ≤ _root_.commutator H := Subgroup.commutator_mono le_top le_top
      _ ≤ N.subgroupOf H := hcH
  unfold CFSG.inSubgroup
  rw [hlayer]
  exact Subgroup.map_subgroupOf_eq_of_le hNH

theorem census_of_model {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (x : X) {N : Subgroup Y}
    (hxN : e x ∈ N) (hNC : N ≤ centralizer ({e x} : Set Y))
    (hcomm : ∀ a ∈ centralizer ({e x} : Set Y), ∀ b ∈ centralizer ({e x} : Set Y),
      a * b * a⁻¹ * b⁻¹ ∈ N)
    (hN : CFSG.IsQuasisimple N) {Q : Type*} [Group Q] (f : N ≃* Q) :
    x ∈ CFSG.inSubgroup CFSG.layer (centralizer ({x} : Set X)) ∧
      Nonempty (↥(CFSG.inSubgroup CFSG.layer (centralizer ({x} : Set X))) ≃* Q) := by
  have hK := inSubgroup_layer_eq_of_commutator_mem hNC hcomm hN
  have hmap := CFSG.AGLEmbeddingD2.Wilson.Proving.map_inSubgroup_layer_centralizer e x
  rw [hK] at hmap
  set Lx := CFSG.inSubgroup CFSG.layer (centralizer ({x} : Set X)) with hLx
  have hLxe : Lx = N.comap e.toMonoidHom := by
    rw [← hmap]
    exact (Subgroup.comap_map_eq_self_of_injective e.injective Lx).symm
  refine ⟨?_, ⟨?_⟩⟩
  · rw [hLxe]
    exact hxN
  · exact ((Subgroup.equivMapOfInjective Lx e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)).trans f

@[expose] noncomputable def slThreeCongr {K K' : Type} [Field K] [Field K'] (r : K ≃+* K') :
    SL(3, K) ≃* SL(3, K') where
  toFun := Matrix.SpecialLinearGroup.map r.toRingHom
  invFun := Matrix.SpecialLinearGroup.map r.symm.toRingHom
  left_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' A B := map_mul _ A B

@[expose] noncomputable def sl3EquivOfCard {K : Type} [Field K] [Finite K] {n : ℕ} (hn : n ≠ 0)
    (hK : Nat.card K = 2 ^ n) : SL(3, K) ≃* SL3 n :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite (GaloisField 2 n)
  slThreeCongr (FiniteField.ringEquivOfCardEq (K := K) (K' := GaloisField 2 n) (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card 2 n hn]))

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof
