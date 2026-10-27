module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def graphRel (V B : Subgroup G) : Prop :=
  ∃ F ∈ omegaA V, F ≤ B

@[expose] def reachE (V : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ partTwoE G ∧
    Relation.ReflTransGen (fun X Y => X ∈ partTwoE G ∧ Y ∈ partTwoE G ∧ graphRel X Y) V B}

@[expose] def HypR (A : Subgroup G) : Prop :=
  (∀ B ∈ reachE A, B ∉ partTwoT G) ∧ Chosen136 A

structure Sec15R (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop extends Sec14Std G A c L where
  hypR : HypR A

omit [Finite G] in
theorem isElemAbelian_sup_zpowers {p : ℕ} {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian p E)
    {x : G} (hxp : x ^ p = 1) (hxE : ∀ e ∈ E, e * x = x * e) :
    CFSG.Assembly.IsElemAbelian p (E ⊔ Subgroup.zpowers x) := by
  have hZc : Subgroup.zpowers x ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr hxE)
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set G) :=
    hZc.trans (Subgroup.centralizer_le_normalizer _)
  have hEE : E ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hE.1
  have hZZ : Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hcomm : IsMulCommutative (E ⊔ Subgroup.zpowers x : Subgroup G) := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mpr (sup_le hEE hZc)
    · exact Subgroup.le_centralizer_iff.mpr (sup_le (Subgroup.le_centralizer_iff.mpr hZc) hZZ)
  refine ⟨hcomm, fun y hy => ?_⟩
  have hy' : y ∈ ((E : Set G) * (Subgroup.zpowers x : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left E _ hle]
    exact hy
  obtain ⟨e, he, z, hz, rfl⟩ := hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hc : Commute e (x ^ k) := Commute.zpow_right (hxE e he) k
  rw [hc.mul_pow, hE.2 e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hxp, one_zpow]

omit [Finite G] in
theorem mem_of_mem_partTwoF {E : Subgroup G} (hE : E ∈ partTwoF G) {a : G} (ha3 : a ^ 3 = 1)
    (haE : E ≤ Subgroup.centralizer ({a} : Set G)) : a ∈ E := by
  have hsup := isElemAbelian_sup_zpowers hE.1 ha3 fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (haE he)
  rw [← hE.2.1 _ hsup le_sup_left]
  exact (le_sup_right : Subgroup.zpowers a ≤ E ⊔ Subgroup.zpowers a) (Subgroup.mem_zpowers a)

theorem hypT_of_mem_reachE (hG : TheoremFourHyp G) (hS : partTwoS G = ∅) {A : Subgroup G}
    (hR : HypR A) {V : Subgroup G} (hV : V ∈ reachE A) : HypT V := by
  have hFE : partTwoF G = partTwoE G := (hG.partTwoF_eq_partTwoE hS).1
  refine ⟨hV.1, hR.1 V hV, fun a ha => ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro E ⟨hET, hEa⟩
  have hEE : E ∈ partTwoE G := hET.1
  have ha3 : a ^ 3 = 1 := by
    have h := (zpowers_mem_omegaA_iff.mp ha).2.1
    rw [Nat.card_zpowers] at h
    rw [← h]
    exact pow_orderOf_eq_one a
  have haE : a ∈ E := mem_of_mem_partTwoF (hFE ▸ hEE) ha3 hEa
  have hVE : graphRel V E := ⟨Subgroup.zpowers a, ha, Subgroup.zpowers_le.mpr haE⟩
  exact hR.1 E ⟨hEE, hV.2.tail ⟨hV.1, hEE, hVE⟩⟩ hET

end CFSG.RankThree.PartTwo.Sec15
