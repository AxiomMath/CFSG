module

import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Lift
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y143

theorem mem_zpowers_sup_center_of_commute {A : Subgroup G} (hA : A ∈ partTwoF G)
    {B : Subgroup G} (hBA : IsHyperplane A B)
    {Yc : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))}
    {a : ↥(Subgroup.centralizer (B : Set G))} (haA : (a : G) ∈ A) (haB : (a : G) ∉ B) {x : ↥Yc}
    (hx : (x : ↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) a)
    {u : ↥Yc} (hux : u * x = x * u) (hu3 : u ^ 3 = 1) :
    u ∈ Subgroup.zpowers x ⊔ Subgroup.center ↥Yc := by
  let C : Subgroup G := Subgroup.centralizer (B : Set G)
  let N : Subgroup ↥C := CFSG.pPrimeCore 3 ↥C
  let Q := ↥C ⧸ N
  let π : ↥C →* Q := QuotientGroup.mk' N
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  haveI : IsMulCommutative A := hAab.1
  have hAC : A ≤ C := by
    intro y hy
    change y ∈ Subgroup.centralizer (B : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨b, hBA.1 hb⟩ ⟨y, hy⟩)
  have hN : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  let At : Subgroup Q := (A.subgroupOf C).map π
  have hAelQ : CFSG.Assembly.IsElemAbelian 3 At := (hAab.subgroupOf C).map π
  have hA3 : IsPGroup 3 (A.subgroupOf C) := (hAab.subgroupOf C).isPGroup
  let uQ : Q := (u : Q)
  let xQ : Q := (x : Q)
  have huxQ : uQ * xQ = xQ * uQ := by
    simpa [uQ, xQ] using congrArg (fun y : ↥Yc => (y : Q)) hux
  have hxQ : xQ = π a := by
    change (x : ↥C ⧸ N) = QuotientGroup.mk' N a
    exact hx
  have hupow : uQ ^ 3 = 1 := by
    simpa [uQ] using congrArg (fun y : ↥Yc => (y : Q)) hu3
  have hAsup : B ⊔ Subgroup.zpowers (a : G) = A :=
    Item148HJ.sup_zpowers_eq_of_isHyperplane hBA haA haB
  have hdecomp : ∀ y : G, y ∈ A → ∃ b ∈ B, ∃ k : ℤ, b * (a : G) ^ k = y := by
    intro y hy
    have hnorm : Subgroup.zpowers (a : G) ≤ Subgroup.normalizer (B : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro h hh z hz
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [Subgroup.mul_comm_of_mem_isMulCommutative A (Subgroup.zpow_mem A haA j)
        (hBA.1 hz), mul_assoc, mul_inv_cancel, mul_one]
      exact hz
    have hy' : y ∈ ((B ⊔ Subgroup.zpowers (a : G) : Subgroup G) : Set G) := by
      rw [hAsup]
      exact hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left B (Subgroup.zpowers (a : G)) hnorm] at hy'
    obtain ⟨b, hb, t, ht, hbt⟩ := Set.mem_mul.mp hy'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact ⟨b, hb, k, hbt⟩
  have hcentB : ∀ b : ↥C, (b : G) ∈ B → π b ∈ Subgroup.center Q := by
    intro b hbB
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N z
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.2 b hbB).symm
  have hcommA' : ∀ y ∈ A.subgroupOf C, π y * uQ = uQ * π y := by
    intro y hy
    have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨b, hbB, k, hbk⟩ := hdecomp (y : G) hyA
    have hbC : b ∈ C := by
      have hb_eq : b = (y : G) * ((a : G) ^ k)⁻¹ := by
        calc b = b * (a : G) ^ k * ((a : G) ^ k)⁻¹ := by group
          _ = (y : G) * ((a : G) ^ k)⁻¹ := by rw [hbk]
      rw [hb_eq]
      exact C.mul_mem y.2 (C.inv_mem (Subgroup.zpow_mem C a.2 k))
    let bC : ↥C := ⟨b, hbC⟩
    have hbCeq : bC * a ^ k = y := by
      apply Subtype.ext
      simpa [bC] using hbk
    have hdecompQ : π y = π bC * π (a ^ k) := by
      rw [← hbCeq, map_mul]
    have hbcent : π bC * uQ = uQ * π bC :=
      (Subgroup.mem_center_iff.mp (hcentB bC hbB) uQ).symm
    have hgu : π (a ^ k) * uQ = uQ * π (a ^ k) := by
      rw [map_zpow, ← hxQ]
      exact ((Commute.zpow_right huxQ k).eq).symm
    calc π y * uQ = (π bC * π (a ^ k)) * uQ := by rw [hdecompQ]
      _ = π bC * (π (a ^ k) * uQ) := by rw [mul_assoc]
      _ = π bC * (uQ * π (a ^ k)) := by rw [hgu]
      _ = (π bC * uQ) * π (a ^ k) := by rw [← mul_assoc]
      _ = (uQ * π bC) * π (a ^ k) := by rw [hbcent]
      _ = uQ * (π bC * π (a ^ k)) := by rw [mul_assoc]
      _ = uQ * π y := by rw [← hdecompQ]
  let E : Subgroup Q := At ⊔ Subgroup.zpowers uQ
  have hEel : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_sup_zpowers hAelQ hupow (by
      intro e he
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he
      exact hcommA' y hy)
  obtain ⟨S, hAS, hSE, hSel, -⟩ :=
    Sylow155T51.exists_elemAbelian_lift_le N hN hA3 hEel le_sup_left
  have hSmap : S.map C.subtype = A :=
    hA.2.1 (S.map C.subtype) (hSel.map C.subtype) (by
      intro y hy
      exact ⟨⟨y, hAC hy⟩, hAS (Subgroup.mem_subgroupOf.mpr hy), rfl⟩)
  have hSA : S = A.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [hSmap, Subgroup.map_subgroupOf_eq_of_le hAC]
  have huE : uQ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers uQ)
  have huS : uQ ∈ S.map π := by
    rw [hSE]
    exact huE
  obtain ⟨s, hsS, hsu⟩ := Subgroup.mem_map.mp huS
  have huAt : uQ ∈ At := by
    refine ⟨s, ?_, hsu⟩
    rwa [hSA] at hsS
  obtain ⟨y, hy, huy⟩ := Subgroup.mem_map.mp huAt
  have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
  obtain ⟨b, hbB, k, hbk⟩ := hdecomp (y : G) hyA
  have hbC : b ∈ C := by
    have hb_eq : b = (y : G) * ((a : G) ^ k)⁻¹ := by
      calc b = b * (a : G) ^ k * ((a : G) ^ k)⁻¹ := by group
        _ = (y : G) * ((a : G) ^ k)⁻¹ := by rw [hbk]
    rw [hb_eq]
    exact C.mul_mem y.2 (C.inv_mem (Subgroup.zpow_mem C a.2 k))
  let bC : ↥C := ⟨b, hbC⟩
  have hbCeq : bC * a ^ k = y := by
    apply Subtype.ext
    simpa [bC] using hbk
  have hbQ : π bC * xQ ^ k = uQ := by
    calc π bC * xQ ^ k = π bC * (π a) ^ k := by rw [hxQ]
      _ = π bC * π (a ^ k) := by rw [← map_zpow]
      _ = π (bC * a ^ k) := by rw [← map_mul]
      _ = π y := by rw [hbCeq]
      _ = uQ := huy
  let bY : ↥Yc := u * x ^ (-k)
  have hbYQ : (bY : Q) = π bC := by
    have hbYval : (bY : Q) = uQ * xQ ^ (-k) := by simp [bY, uQ, xQ]
    rw [hbYval]
    calc uQ * xQ ^ (-k) = (π bC * xQ ^ k) * xQ ^ (-k) := by rw [hbQ]
      _ = π bC * (xQ ^ k * xQ ^ (-k)) := by rw [mul_assoc]
      _ = π bC := by rw [← zpow_add]; simp
  have hbYcenter : bY ∈ Subgroup.center ↥Yc := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    show (z : Q) * (bY : Q) = (bY : Q) * (z : Q)
    rw [hbYQ]
    exact Subgroup.mem_center_iff.mp (hcentB bC hbB) (z : Q)
  have hu_eq : u = bY * x ^ k := by
    apply Subtype.ext
    show (u : Q) = (bY : Q) * (x : Q) ^ k
    rw [hbYQ, hbQ]
  rw [hu_eq]
  have hxpow : x ^ k ∈ Subgroup.zpowers x :=
    Subgroup.zpow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) k
  simpa [sup_comm] using Subgroup.mul_mem_sup hbYcenter hxpow

end Gagen155Y143

end CFSG.RankThree.PartTwo.Sec15
