
module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8Real
public import CFSG.RankThree.Chevalley.SteinbergBIWE8CertsBase

@[expose] public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.WE8.Native

@[expose] def rootsV : Set V8 := castV '' {α | IsRoot .E8 α}

@[expose] def nInv (t : W8) : ℕ := (rootsV ∩ (negSpace t : Set V8)).ncard / 2

theorem rootsV_inter_negSpace (t : W8) :
    rootsV ∩ (negSpace t : Set V8) = castV '' {α : L8 | IsRoot .E8 α ∧ t • α = -α} := by
  ext x
  constructor
  · rintro ⟨⟨α, hα, rfl⟩, hx⟩
    rw [SetLike.mem_coe, mem_negSpace, realAct_castV, ← castV_neg] at hx
    exact ⟨α, ⟨hα, castV_injective hx⟩, rfl⟩
  · rintro ⟨α, ⟨hα, h⟩, rfl⟩
    refine ⟨⟨α, hα, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, mem_negSpace, realAct_castV, h, castV_neg]

theorem ncard_rootsV_negSpace (t : W8) :
    (rootsV ∩ (negSpace t : Set V8)).ncard = {α : L8 | IsRoot .E8 α ∧ t • α = -α}.ncard := by
  rw [rootsV_inter_negSpace, Set.ncard_image_of_injective _ castV_injective]

theorem ncard_neg_conj (u t : W8) :
    {α : L8 | IsRoot .E8 α ∧ (u * t * u⁻¹) • α = -α}.ncard =
      {α : L8 | IsRoot .E8 α ∧ t • α = -α}.ncard := by
  have e : {α : L8 | IsRoot .E8 α ∧ (u * t * u⁻¹) • α = -α} =
      (fun β => u • β) '' {α : L8 | IsRoot .E8 α ∧ t • α = -α} := by
    ext α
    constructor
    · rintro ⟨hα, h⟩
      refine ⟨u⁻¹ • α, ⟨IsRoot.smul hα _, ?_⟩, smul_inv_smul u α⟩
      rw [mul_smul, mul_smul] at h
      rw [← smul_neg, ← h, inv_smul_smul]
    · rintro ⟨β, ⟨hβ, h⟩, rfl⟩
      refine ⟨IsRoot.smul hβ u, ?_⟩
      rw [mul_smul, mul_smul, inv_smul_smul, h, smul_neg]
  rw [e, Set.ncard_image_of_injective _ (MulAction.injective u)]

@[expose] def frameF (i : ℕ) : Fin (frame i).length → L8 := (frame i).get

theorem frameF_orth {i : ℕ} (hi : i < 9) : IsOrthFrame (frameF i) := by
  refine ⟨fun j => frame_isRoot hi _ (List.get_mem _ _), fun a b hab => ?_⟩
  have hp := List.pairwise_iff_get.1 (frame_pairwise hi)
  change iform (frameF i a) (frameF i b) = 0
  rcases lt_or_gt_of_ne hab with h | h
  · exact hp a b h
  · rw [iform_comm]
    exact hp b a h

theorem rep_eq_prodRefl (i : ℕ) : rep i = prodRefl (frameF i) := by
  rw [rep, prodRefl, frameF]
  congr 1
  conv_lhs => rw [← List.ofFn_get (frame i)]
  rw [List.map_ofFn]
  rfl

@[expose] def nList : List ℕ := [1, 2, 3, 4, 12, 13, 30, 63, 120]

theorem negCounts_eq : ∀ i < 9, negCounts.getD i 0 / 2 = nList.getD i 0 := by
  decide

theorem nList_inj : ∀ i < 9, ∀ j < 9, nList.getD i 0 = nList.getD j 0 → i = j := by
  decide

theorem nInv_of_isConj {i : ℕ} (hi : i < 9) {t : W8} (h : IsConj (rep i) t) :
    nInv t = nList.getD i 0 := by
  obtain ⟨u, rfl⟩ := isConj_iff.1 h
  rw [nInv, ncard_rootsV_negSpace, ncard_neg_conj, ncard_neg_rep hi, negCounts_eq i hi]

theorem prodRefl_mul_self {k : ℕ} {β : Fin k → L8} (h : IsOrthFrame β) :
    prodRefl β * prodRefl β = 1 := by
  refine realAct_injective (LinearMap.ext fun v => ?_)
  rw [realAct_mul_apply, realAct_one, LinearMap.id_apply, realAct_prodRefl h, realAct_prodRefl h]
  have hB : ∀ i, e8Form (castV (β i)) (v - ∑ j, e8Form (castV (β j)) v • castV (β j)) =
      -e8Form (castV (β i)) v := by
    intro i
    rw [map_sub, map_sum]
    simp only [map_smul, h.form, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    ring
  simp only [hB, neg_smul, Finset.sum_neg_distrib, sub_neg_eq_add, sub_add_cancel]

theorem rep_mul_self {i : ℕ} (hi : i < 9) : rep i * rep i = 1 := by
  rw [rep_eq_prodRefl]
  exact prodRefl_mul_self (frameF_orth hi)

theorem rep_ne_one {i : ℕ} (hi : i < 9) : rep i ≠ 1 := by
  intro h
  have h1 := ncard_neg_rep hi
  rw [h] at h1
  have e : {α : L8 | IsRoot .E8 α ∧ (1 : W8) • α = -α} = ∅ := by
    ext α
    simp only [one_smul, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hα hneg
    exact hα.ne_zero (by
      funext k
      have := congrFun hneg k
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega)
  rw [e, Set.ncard_empty] at h1
  have : ∀ i < 9, negCounts.getD i 0 ≠ 0 := by decide
  exact this i hi h1.symm

theorem conj_mul_self {t : W8} (ht : t * t = 1) (u : W8) :
    (u * t * u⁻¹) * (u * t * u⁻¹) = 1 := by
  have : (u * t * u⁻¹) * (u * t * u⁻¹) = u * (t * t) * u⁻¹ := by group
  rw [this, ht, mul_one, mul_inv_cancel]

theorem realAct_z : realAct z = -LinearMap.id :=
  linearMap_ext_castV fun v => by
    rw [realAct_castV, z_smul, castV_neg, LinearMap.neg_apply, LinearMap.id_apply]

theorem z_mul_comm (w : W8) : z * w = w * z := by
  refine realAct_injective (LinearMap.ext fun v => ?_)
  rw [realAct_mul_apply, realAct_mul_apply, realAct_z, LinearMap.neg_apply, LinearMap.id_apply,
    LinearMap.neg_apply, LinearMap.id_apply, map_neg]

theorem z_mul_z : z * z = 1 := rep_mul_self (by decide)

theorem sum_classSizes : ((List.range 9).map fun i => classSizes.getD i 0).sum = 199951 := by
  decide

theorem conj_y0_sq (u : W8) : (u * y0 * u⁻¹) * (u * y0 * u⁻¹) = z := by
  have : (u * y0 * u⁻¹) * (u * y0 * u⁻¹) = u * (y0 * y0) * u⁻¹ := by group
  rw [this, y0_mul_y0, ← z_mul_comm u, mul_assoc, mul_inv_cancel, mul_one]

theorem sq_eq_z_smul {y : W8} (hy : y * y = z) (v : L8) : (y * y) • v = -v := by
  rw [hy, z_smul]

end CFSG.RankThree.Chevalley.WeylE8
