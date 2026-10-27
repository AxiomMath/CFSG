module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentTau
import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorr
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
public import CFSG.RankThree.PartTwo.Sec14.Concrete

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

theorem res1340_le_of_inf_normalizer_le {p : ℕ} [Fact p.Prime] {R Z : Subgroup G}
    (hR : IsPGroup p R) (hZ : IsPGroup p Z) (hRZ : R ≤ Subgroup.normalizer (Z : Set G))
    (h : Z ⊓ Subgroup.normalizer (R : Set G) ≤ R) : Z ≤ R := by
  have hHp : IsPGroup p ↥(R ⊔ Z) := IsPGroup.to_sup_of_normal_right' hR hZ hRZ
  haveI : Group.IsNilpotent ↥(R ⊔ Z) := hHp.isNilpotent
  have hself : Subgroup.normalizer ((R.subgroupOf (R ⊔ Z) : Subgroup ↥(R ⊔ Z)) : Set ↥(R ⊔ Z)) =
      R.subgroupOf (R ⊔ Z) := by
    refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
    rw [← Subgroup.subgroupOf_normalizer_eq le_sup_left, Subgroup.mem_subgroupOf] at hx
    have hx' : (x : G) ∈ ((R ⊔ Z : Subgroup G) : Set G) := x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R Z hRZ] at hx'
    obtain ⟨r, hr, w, hw, hrw⟩ := hx'
    have hwN : w ∈ Subgroup.normalizer (R : Set G) := by
      have e : w = r⁻¹ * x := by rw [← hrw, inv_mul_cancel_left]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer (R.inv_mem hr)) hx
    rw [Subgroup.mem_subgroupOf, ← hrw]
    exact R.mul_mem hr (h ⟨hw, hwN⟩)
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    normalizerCondition_of_isNilpotent _ hself
  intro w hw
  have hmem : (⟨w, Subgroup.mem_sup_right hw⟩ : ↥(R ⊔ Z)) ∈ R.subgroupOf (R ⊔ Z) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

namespace Res1Tau

variable {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
  {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}

theorem le_pCoreOf_of_competing (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (h1444 : Item1444 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hN : n155 A K ≤ Subgroup.normalizer (K : Set G)) {M' Z : Subgroup G}
    (hC' : Ctx155 A X K Y M' T) (hZ2 : IsPGroup 2 Z) (hZQ : Z ∈ scriptQ A (lB A))
    (hYZ : Y ≤ Subgroup.normalizer (Z : Set G)) (hZM : Z ≤ M') : Z ≤ CFSG.Open.pCoreOf 2 Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 Y with hR
  have hY3 : Y ∈ scriptY3 A (lB A) := τ.ctx.isY.1
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hR1 : R ≠ ⊥ := hY3.1.2
  have hRY : R ≤ Y := Subgroup.map_subtype_le _
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) Y
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hY3.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) Y)
  set D := Z ⊓ Subgroup.normalizer (R : Set G) with hD
  have hND : ∀ H : Subgroup G, H ≤ Subgroup.normalizer (Z : Set G) →
      H ≤ Subgroup.normalizer (R : Set G) → H ≤ Subgroup.normalizer (D : Set G) :=
    fun H h1 h2 => Late.le_normalizer_inf h1 (h2.trans Subgroup.le_normalizer)
  have hD2 : IsPGroup 2 D := hZ2.to_le inf_le_left
  have hDQ : D ∈ scriptQ A (lB A) := mem_scriptQ_of_le hZQ inf_le_left (hND A hZQ.1.2.2 hAR)
  have hYD : Y ≤ Subgroup.normalizer (D : Set G) := hND Y hYZ hYR
  have hchar : (R.subgroupOf R).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hDK : D ≤ Subgroup.normalizer (K : Set G) :=
    (le_delta hDQ inf_le_right).trans ((τ.endN.claim R hR1 le_rfl hchar).trans hN)
  have hTD : T ⊔ D ∈ scriptQ A (lB A) :=
    sup_mem_scriptQ_of_item146 τ.sec15.isE27 τ.i146 τ.ctx.mem_t.prop.1.1 hDQ
      (τ.ctx.mem_t.prop.1.2.trans hYD)
  have hAY : A ⊔ Y ≤ M' := SetLike.coe_subset_coe.mp hC'.mem_m.2
  have hM' : M' ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (Y ⊔ D) : Subgroup G) : Set G) :=
    ⟨hC'.mem_m.1, SetLike.coe_subset_coe.mpr (sup_le (le_sup_left.trans hAY)
      (sup_le (le_sup_right.trans hAY) (inf_le_left.trans hZM)))⟩
  have hDR : D ≤ R := Proof155w.le_pCoreOf_of_ctx155w τ.std h1444 τ.i146 hbot τ.ctx τ.maxT
    τ.above hD2 hDQ hYD hDK hTD hM' hC'.not_le
  exact res1340_le_of_inf_normalizer_le hR2 hZ2 (hRY.trans hYZ) hDR

end Res1Tau

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
