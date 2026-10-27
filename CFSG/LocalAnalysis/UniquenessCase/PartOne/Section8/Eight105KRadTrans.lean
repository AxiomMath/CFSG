module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadSetup
import CFSG.HardMathSupport.Curtis.UnitaryLevi.NormalizerStab
import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LinearGroups (stdHermForm)

variable {K : Type} [Field K] {f n : ℕ}

theorem exists_transvection (h : UnitaryFieldData 2 f K) {a : Fin n → K}
    (ha : stdHermForm h n a a = 0) :
    ∃ t : StatedSU n (2 ^ f) K, ∀ x : Fin n → K,
      ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = x + stdHermForm h n a x • a := by
  have hchar : CharP K 2 := h.charP
  have hc : (1 : K) + h.bar 1 + stdHermForm h n 0 0 = 0 := by
    rw [map_one, map_zero, add_zero, CharTwo.add_self_eq_zero]
  obtain ⟨t, ht⟩ := CFSG.HardMathSupport.Curtis.UnitaryLevi.exists_statedSU_eichler h
    (b := 0) (c := 1) ha (map_zero _) hc
  refine ⟨t, fun x => ?_⟩
  rw [ht x, CFSG.LinearGroups.eichlerMap_apply]
  simp

private theorem mul_mulVec (y y' : StatedSU n (2 ^ f) K) (x : Fin n → K) :
    (((y * y' : StatedSU n (2 ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Subgroup.coe_mul, Units.val_mul]

private theorem inv_mulVec_mulVec (y : StatedSU n (2 ^ f) K) (x : Fin n → K) :
    (((y⁻¹ : StatedSU n (2 ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, Units.inv_mul, Matrix.one_mulVec]

private theorem mulVec_inv_mulVec (y : StatedSU n (2 ^ f) K) (x : Fin n → K) :
    ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((((y⁻¹ : StatedSU n (2 ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, Units.mul_inv, Matrix.one_mulVec]

private def radQ (W : Submodule K (Fin n → K)) : Subgroup (StatedSU n (2 ^ f) K) where
  carrier := {y | (∀ w ∈ W, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∧
    ∀ x, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x - x ∈ W}
  one_mem' := ⟨fun w _ => Matrix.one_mulVec w, fun x => by simp⟩
  mul_mem' := by
    rintro y y' ⟨hy₁, hy₂⟩ ⟨hy'₁, hy'₂⟩
    refine ⟨fun w hw => by rw [mul_mulVec, hy'₁ w hw, hy₁ w hw], fun x => ?_⟩
    have hfix := hy₁ _ (hy'₂ x)
    rw [Matrix.mulVec_sub] at hfix
    have heq : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) - x =
        (((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x - x) +
          (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x - x) := by
      rw [← hfix]
      abel
    rw [mul_mulVec, heq]
    exact W.add_mem (hy'₂ x) (hy₂ x)
  inv_mem' := by
    rintro y ⟨hy₁, hy₂⟩
    refine ⟨fun w hw => ?_, fun x => ?_⟩
    · calc _ = (((y⁻¹ : StatedSU n (2 ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) := by rw [hy₁ w hw]
        _ = w := inv_mulVec_mulVec y w
    · have hneg := W.neg_mem (hy₂ ((((y⁻¹ : StatedSU n (2 ^ f) K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ x))
      rwa [mulVec_inv_mulVec, neg_sub] at hneg

private theorem mem_radQ {W : Submodule K (Fin n → K)} {y : StatedSU n (2 ^ f) K} :
    y ∈ radQ W ↔ (∀ w ∈ W, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∧
      ∀ x, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x - x ∈ W :=
  Iff.rfl

private theorem conj_mem_radQ {W : Submodule K (Fin n → K)} {g y : StatedSU n (2 ^ f) K}
    (hg : g ∈ stabSU (2 ^ f) W) (hy : y ∈ radQ W) : g * y * g⁻¹ ∈ radQ W := by
  obtain ⟨hy₁, hy₂⟩ := mem_radQ.mp hy
  have hg' := mem_stabSU.mp ((stabSU (2 ^ f) W).inv_mem hg)
  refine mem_radQ.mpr ⟨fun w hw => ?_, fun x => ?_⟩
  · rw [mul_mulVec, mul_mulVec, hy₁ _ (hg' w hw), mulVec_inv_mulVec]
  · have hmem := mem_stabSU.mp hg _ (hy₂ ((((g⁻¹ : StatedSU n (2 ^ f) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ x))
    rwa [Matrix.mulVec_sub, mulVec_inv_mulVec, ← mul_mulVec, ← mul_mulVec] at hmem

private theorem mul_self_eq_one_of_mem_radQ (h : UnitaryFieldData 2 f K)
    {W : Submodule K (Fin n → K)} {y : StatedSU n (2 ^ f) K} (hy : y ∈ radQ W) :
    y * y = 1 := by
  have hchar : CharP K 2 := h.charP
  obtain ⟨hy₁, hy₂⟩ := mem_radQ.mp hy
  have hact : ∀ x, (((y * y : StatedSU n (2 ^ f) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ x = x := by
    intro x
    have hfix := hy₁ _ (hy₂ x)
    rw [Matrix.mulVec_sub] at hfix
    rw [mul_mulVec, sub_eq_iff_eq_add.mp hfix]
    calc _ = (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x - x) +
          (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x - x) + x := by abel
      _ = x := by rw [← two_smul K, CharTwo.two_eq_zero, zero_smul, zero_add]
  have hM : (((y * y : StatedSU n (2 ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    Matrix.toLin'.injective (LinearMap.ext fun x => by
      rw [Matrix.toLin'_apply, hact x, Matrix.toLin'_one, LinearMap.id_apply])
  exact Subtype.ext (Units.ext hM)

theorem exists_transvection_mem_pCoreOf (h : UnitaryFieldData 2 f K)
    {W : Submodule K (Fin n → K)} (hW : ∀ v ∈ W, ∀ w ∈ W, stdHermForm h n v w = 0)
    {a : Fin n → K} (ha : a ∈ W) :
    ∃ t ∈ pCoreOf 2 (stabSU (2 ^ f) W), ∀ x : Fin n → K,
      ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = x + stdHermForm h n a x • a := by
  obtain ⟨t, ht⟩ := exists_transvection h (hW a ha a ha)
  set S := stabSU (2 ^ f) W
  have hQS : radQ W ≤ S := fun y hy =>
    mem_stabSU.mpr fun w hw => by rw [(mem_radQ.mp hy).1 w hw]; exact hw
  have htQ : t ∈ radQ W := mem_radQ.mpr ⟨fun w hw => by rw [ht w, hW a ha w hw, zero_smul,
    add_zero], fun x => by rw [ht x, add_sub_cancel_left]; exact W.smul_mem _ ha⟩
  have hN : ((radQ W).subgroupOf S).Normal :=
    ⟨fun y hy g => Subgroup.mem_subgroupOf.mpr (conj_mem_radQ g.2 hy)⟩
  have hp : IsPGroup 2 ((radQ W).subgroupOf S) := fun y => ⟨1, by
    have h2 := mul_self_eq_one_of_mem_radQ h (Subgroup.mem_subgroupOf.mp y.2)
    apply Subtype.ext
    apply Subtype.ext
    simpa [pow_two] using h2⟩
  have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hN hp
  exact ⟨t, Subgroup.mem_map.mpr ⟨⟨t, hQS htQ⟩, hle (Subgroup.mem_subgroupOf.mpr htQ), rfl⟩, ht⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
