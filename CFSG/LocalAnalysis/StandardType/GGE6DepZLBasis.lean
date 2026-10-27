module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

private def zlb_phi {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] (h : Fin 6 → V) :
    Vec6 →ₗ[ZMod 3] V :=
  Fintype.linearCombination (ZMod 3) h

private lemma zlb_phi_apply {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (c : Vec6) : zlb_phi h c = ∑ i, c i • h i := rfl

private lemma zlb_cartanE6_symm : ∀ i j : Fin 6, cartanE6 i j = cartanE6 j i := by decide +kernel

private lemma zlb_sum_smul_cartanE6 (c : Vec6) :
    (∑ i, c i • cartanE6 i) = cartanM.mulVec c := by
  funext j
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [zlb_cartanE6_symm i j]
  exact mul_comm (c i) (cartanE6 j i)

private lemma zlb_Phi_phi {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    {Φ : V →+ Vec6} {h : Fin 6 → V} (hhΦ : ∀ i, Φ (h i) = cartanE6 i) (c : Vec6) :
    Φ (zlb_phi h c) = cartanM.mulVec c := by
  rw [zlb_phi_apply, map_sum]
  rw [Finset.sum_congr rfl (fun i _ => by rw [ZMod.map_smul, hhΦ i]),
    zlb_sum_smul_cartanE6]

private def zlb_Nmat : Mat6 :=
  !![0, 0, 0, 0, 0, 0; 0, 2, 0, 0, 1, 2; 0, 0, 2, 0, 1, 2; 0, 0, 0, 0, 2, 1;
     0, 1, 1, 2, 2, 1; 0, 2, 2, 1, 1, 1]

private lemma zlb_Nmat_spec (u : Vec6) (hu : kappa ⬝ᵥ u = 0) :
    cartanM.mulVec (zlb_Nmat.mulVec u) = u := by
  rw [Matrix.mulVec_mulVec]
  have hid : cartanM * zlb_Nmat = 1 - Matrix.vecMulVec ![1, 0, 0, 0, 0, 0] kappa := by
    decide +kernel
  rw [hid, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, hu,
    op_smul_eq_smul, zero_smul, sub_zero]

private lemma zlb_reflMat_mulVec (α h u : Vec6) :
    (reflMat α h).mulVec u = u - (α ⬝ᵥ u) • h := by
  simp only [reflMat, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul]

private lemma zlb_one_apply (i : Fin 6) : (1 : Mat6) i = Pi.single i 1 := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Pi.single_apply]

private lemma zlb_indepGens_mulVec (i : Fin 6) (c : Vec6) :
    (indepGens i).mulVec c = c - (cartanE6 i ⬝ᵥ c) • (Pi.single i 1) := by
  rw [show indepGens i = reflMat (cartanE6 i) ((1 : Mat6) i) from rfl, zlb_reflMat_mulVec,
    zlb_one_apply i]

private lemma zlb_phi_single {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (i : Fin 6) : zlb_phi h (Pi.single i 1) = h i := by
  rw [zlb_phi_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma zlb_cartanM_mulVec_apply (u : Vec6) (i : Fin 6) :
    (cartanM.mulVec u) i = cartanE6 i ⬝ᵥ u := rfl

private lemma zlb_val_smul {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (a : ZMod 3) (w : V) : a.val • w = a • w := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3) a.val w, ZMod.natCast_zmod_val]

theorem zl_frame_basis {V : Type} [AddCommGroup V] [Finite V] (hcard : Nat.card V = 3 ^ 6)
    (hexp : ∀ v : V, 3 • v = 0) {Φ : V →+ Vec6} {σ : Fin 6 → V →+ V} {x : V} {h : Fin 6 → V}
    (hΦ1 : ∀ v, kappa ⬝ᵥ Φ v = 0) (hΦ3 : ∀ v, Φ v = 0 ↔ v ∈ AddSubgroup.zmultiples x)
    (hx : x ≠ 0) (hhΦ : ∀ i, Φ (h i) = cartanE6 i)
    (hσ : ∀ i v, σ i v = v - (Φ v i).val • h i)
    (hcob : x ∈ AddSubgroup.closure {u | ∃ (i : Fin 6) (v : V), u = σ i v - v}) :
    ∃ ι : V ≃+ Vec6, (∃ a : ZMod 3, a ≠ 0 ∧ ι x = a • kappa) ∧
      (∀ v, Φ v = cartanM.mulVec (ι v)) ∧ ∀ i v, ι (σ i v) = (indepGens i).mulVec (ι v) := by
  classical
  letI : Module (ZMod 3) V := AddCommGroup.zmodModule (n := 3) hexp
  let S : AddSubgroup V := AddSubgroup.closure (Set.range h)
  have hxS : x ∈ S := by
    have hsub : ({u : V | ∃ (i : Fin 6) (v : V), u = σ i v - v} : Set V) ⊆ S := by
      rintro u ⟨i, v, rfl⟩
      have h1 : σ i v - v = -((Φ v i).val • h i) := by
        rw [hσ i v]; abel
      rw [h1, zlb_val_smul]
      exact S.neg_mem (ZMod.smul_mem
        (AddSubgroup.subset_closure (Set.mem_range_self (f := h) i)) (Φ v i))
    exact (AddSubgroup.closure_le S).mpr hsub hcob
  have hS_top : ∀ v : V, v ∈ S := by
    intro v
    obtain ⟨c, hc⟩ : ∃ c : Vec6, cartanM.mulVec c = Φ v :=
      ⟨zlb_Nmat.mulVec (Φ v), zlb_Nmat_spec (Φ v) (hΦ1 v)⟩
    have hker : Φ (v - zlb_phi h c) = 0 := by
      rw [map_sub, zlb_Phi_phi hhΦ c, hc, sub_self]
    have hzx : v - zlb_phi h c ∈ AddSubgroup.zmultiples x := (hΦ3 _).mp hker
    have hzS : v - zlb_phi h c ∈ S := AddSubgroup.zmultiples_le_of_mem hxS hzx
    have hphiS : zlb_phi h c ∈ S := by
      rw [zlb_phi_apply]
      exact AddSubmonoid.sum_mem S.toAddSubmonoid fun i _ =>
        ZMod.smul_mem (AddSubgroup.subset_closure (Set.mem_range_self (f := h) i)) (c i)
    have hdecomp : v = zlb_phi h c + (v - zlb_phi h c) := by abel
    rw [hdecomp]
    exact S.add_mem hphiS hzS
  have hsurj : Function.Surjective (zlb_phi h) := by
    intro v
    have hv : v ∈ S := hS_top v
    have hle : S ≤ (zlb_phi h).range.toAddSubgroup := by
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro u ⟨i, rfl⟩
      exact ⟨Pi.single i 1, zlb_phi_single h i⟩
    exact hle hv
  have hcardVec : Nat.card Vec6 = 3 ^ 6 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hbij : Function.Bijective (zlb_phi h) :=
    hsurj.bijective_of_nat_card_le (by rw [hcardVec, hcard])
  let e : Vec6 ≃+ V := AddEquiv.ofBijective (zlb_phi h) hbij
  let ι : V ≃+ Vec6 := e.symm
  have hφι : ∀ v, zlb_phi h (ι v) = v := fun v => AddEquiv.apply_symm_apply e v
  have hPhiι : ∀ v, Φ v = cartanM.mulVec (ι v) := by
    intro v
    conv_lhs => rw [← hφι v]
    rw [zlb_Phi_phi hhΦ (ι v)]
  have hsigma : ∀ i v, ι (σ i v) = (indepGens i).mulVec (ι v) := by
    intro i v
    have hgen : (indepGens i).mulVec (ι v)
        = ι v - (cartanE6 i ⬝ᵥ (ι v)) • (Pi.single i 1) :=
      zlb_indepGens_mulVec i (ι v)
    have hΦvi : Φ v i = cartanE6 i ⬝ᵥ (ι v) := by
      rw [hPhiι v, zlb_cartanM_mulVec_apply]
    apply hbij.1
    rw [hφι (σ i v), hgen, map_sub, map_smul, zlb_phi_single h i, hφι v, hσ i v, hΦvi,
      zlb_val_smul]
  have hxker : cartanM.mulVec (ι x) = 0 := by
    rw [← hPhiι x]
    exact (hΦ3 x).mpr (AddSubgroup.mem_zmultiples x)
  obtain ⟨a, ha⟩ := rad_eq (ι x) hxker
  refine ⟨ι, ⟨a, ?_, ha⟩, hPhiι, hsigma⟩
  intro ha0
  refine hx (ι.injective ?_)
  rw [ha, ha0, zero_smul, map_zero]

end ZL

end E6Dep

end CFSG.StandardType

end
