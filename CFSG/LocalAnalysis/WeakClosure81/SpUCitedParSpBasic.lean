module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpRoot
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

private theorem spUCited_spForm_single_inl (j : Fin r) (v : Fin r ⊕ Fin r → K) :
    spForm r K (Pi.single (Sum.inl j) (1 : K)) v = v (Sum.inr j) := by
  rw [spForm_apply]
  simp [dotProduct, Pi.single_apply,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, Matrix.fromBlocks_mulVec]

private theorem spUCited_spForm_single_inl_right (j : Fin r) (v : Fin r ⊕ Fin r → K) :
    spForm r K v (Pi.single (Sum.inl j) (1 : K)) = - v (Sum.inr j) := by
  have h := spForm_isAlt.neg_eq (Pi.single (Sum.inl j) (1 : K)) v
  rw [spUCited_spForm_single_inl] at h
  exact h.symm

private theorem spUCited_blockMat_one_smul_single (i : Fin r) (t : K) :
    blockMat (1 : Matrix (Fin r) (Fin r) K) (t • Matrix.single i i (1 : K)) =
      1 + t • Matrix.single (Sum.inl i) (Sum.inr i) (1 : K) := by
  ext x y
  rcases x with a | a <;> rcases y with b | b <;>
    simp [blockMat, Matrix.single_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply]

private theorem spUCited_spTransvection_eq_pairRootElt (i : Fin r) (t : K) :
    spTransvection (Pi.single (Sum.inl i) (1 : K)) t =
      pairRootElt (a := (Sum.inl i : Fin r ⊕ Fin r)) (b := Sum.inr i) (by simp) (-t) := by
  apply spLin_injective
  apply Units.ext
  apply LinearMap.ext
  intro y
  change spEnd (spTransvection (Pi.single (Sum.inl i) (1 : K)) t) y =
    spEnd (pairRootElt (a := (Sum.inl i : Fin r ⊕ Fin r)) (b := Sum.inr i) (by simp) (-t)) y
  rw [spEnd_spTransvection, spEnd_apply, coe_pairRootElt, pairRootMat_inl_inr_self,
    spUCited_spForm_single_inl_right]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.single_mulVec_eq,
    one_mul, smul_smul]
  have hs : t * (- y (Sum.inr i)) = (-t) * y (Sum.inr i) := by ring
  rw [hs]

private theorem spUCited_coe_pairRootElt_self (i : Fin r) (t : K) :
    (((pairRootElt (a := (Sum.inl i : Fin r ⊕ Fin r)) (b := Sum.inr i) (by simp) t :
        StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      blockMat 1 (t • Matrix.single i i (1 : K)) := by
  rw [coe_pairRootElt, pairRootMat_inl_inr_self]
  exact (spUCited_blockMat_one_smul_single i t).symm

private theorem spUCited_coe_spTransvection (i : Fin r) (t : K) :
    (((spTransvection (Pi.single (Sum.inl i) (1 : K)) t : StatedSp r K) :
        GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      blockMat 1 ((-t) • Matrix.single i i (1 : K)) := by
  rw [spUCited_spTransvection_eq_pairRootElt]
  exact spUCited_coe_pairRootElt_self i (-t)

private theorem spUCited_spEnd_injective (g : StatedSp r K) :
    Function.Injective (spEnd g) := by
  intro x y h
  have h1 := congrArg (spEnd g⁻¹) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
    Module.End.one_apply, Module.End.one_apply] at h1

private theorem spUCited_single_inl_ne_zero (i : Fin r) :
    (Pi.single (Sum.inl i) (1 : K) : Fin r ⊕ Fin r → K) ≠ 0 := by
  intro h
  simpa using congrFun h (Sum.inl i)

private theorem spUCited_spTransvection_injective (i : Fin r) :
    Function.Injective (fun t : K => spTransvection (Pi.single (Sum.inl i) (1 : K)) t) := by
  intro s t h
  have h1 := congrArg (fun g => spEnd g (Pi.single (Sum.inr i) (1 : K))) h
  rw [spEnd_spTransvection, spEnd_spTransvection] at h1
  have h2 := add_left_cancel h1
  have hc : spForm r K (Pi.single (Sum.inr i) (1 : K)) (Pi.single (Sum.inl i) (1 : K)) = -1 := by
    rw [spUCited_spForm_single_inl_right]
    simp
  have h3 : s * spForm r K (Pi.single (Sum.inr i) (1 : K)) (Pi.single (Sum.inl i) (1 : K)) =
      t * spForm r K (Pi.single (Sum.inr i) (1 : K)) (Pi.single (Sum.inl i) (1 : K)) := by
    have := congrFun h2 (Sum.inl i)
    simpa using this
  exact mul_right_cancel₀ (by rw [hc]; exact neg_ne_zero.mpr one_ne_zero) h3

private theorem spUCited_flag_one_eq (hr : 2 ≤ r) :
    flag r K 1 = Submodule.span K
      {Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)} := by
  have hset : (fun j : Fin r =>
        (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K)) '' {j : Fin r | (j : ℕ) < 1} =
      {Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj0 : j = (⟨0, by omega⟩ : Fin r) := by
        ext
        simp
        omega
      rw [hj0]
    · rintro rfl
      exact ⟨⟨0, by omega⟩, by simp, rfl⟩
  rw [flag, ite_eq_left (by omega), isoFlag, hset]

private theorem spUCited_mem_stabilizer_flag_one_iff (hr : 2 ≤ r) (g : StatedSp r K) :
    g ∈ stabilizer r K (flag r K 1) ↔
      ∃ c : K, c ≠ 0 ∧
        spEnd g (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)) =
          c • (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) :
            Fin r ⊕ Fin r → K) := by
  have hflag := spUCited_flag_one_eq (r := r) (K := K) hr
  constructor
  · intro hg
    have hmem : spEnd g (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)) ∈ flag r K 1 := by
      have hmap := mem_stabilizer.mp hg
      rw [hflag] at hmap
      rw [hflag, ← hmap]
      refine Submodule.mem_map.mpr ⟨Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K),
        Submodule.subset_span (by simp), ?_⟩
      rw [spEnd_apply, Matrix.mulVecLin_apply]
    rw [hflag] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨c, ?_, hc.symm⟩
    intro hc0
    have hzero := spUCited_single_inl_ne_zero (r := r) (K := K) (⟨0, by omega⟩ : Fin r)
    exact hzero (spUCited_spEnd_injective g (by rw [← hc, hc0, zero_smul, map_zero]))
  · rintro ⟨c, hc0, hc⟩
    refine mem_stabilizer_of_mulVec_mem (fun v hv => ?_) (fun v hv => ?_)
    · rw [hflag, Submodule.mem_span_singleton] at hv
      obtain ⟨a, ha⟩ := hv
      rw [← ha, hflag, Matrix.mulVec_smul, ← spEnd_apply, hc, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [hflag, Submodule.mem_span_singleton] at hv
      obtain ⟨a, ha⟩ := hv
      have hinv : spEnd g⁻¹ (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)) =
          c⁻¹ • (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) :
            Fin r ⊕ Fin r → K) := by
        have h1 := congrArg (spEnd g⁻¹) hc
        rw [map_smul] at h1
        rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
          Module.End.one_apply] at h1
        have h2 := congrArg (fun w => c⁻¹ • w) h1
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h2
        exact h2.symm
      rw [← ha, hflag, Matrix.mulVec_smul, ← spEnd_apply, hinv, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

variable (r K) in
@[expose] noncomputable def spUCitedRoot (i : Fin r) : Subgroup ↥(StatedSp r K) :=
  spUFixRootSp (Pi.single (Sum.inl i) (1 : K))

variable (r K) in
@[expose] noncomputable def spUCitedPar : Subgroup ↥(StatedSp r K) :=
  flagStabilizer r K (Set.Icc 2 r)

theorem spUCited_root_le_unipotent (i : Fin r) : spUCitedRoot r K i ≤ unipotent r K := by
  intro x hx
  change x ∈ spUFixRootSp (Pi.single (Sum.inl i) (1 : K)) at hx
  rw [mem_spUFixRootSp] at hx
  obtain ⟨t, rfl⟩ := hx
  rw [mem_unipotent]
  refine ⟨1, (-t) • Matrix.single i i (1 : K), isUnitriangular_one, ?_, ?_⟩
  · simp [Matrix.transpose_smul, Matrix.transpose_single]
  · exact spUCited_coe_spTransvection i t

theorem spUCited_card_root [Finite K] (i : Fin r) :
    Nat.card (spUCitedRoot r K i) = Nat.card K := by
  let f : K → spUCitedRoot r K i := fun t =>
    ⟨spTransvection (Pi.single (Sum.inl i) (1 : K)) t, by
      change spTransvection (Pi.single (Sum.inl i) (1 : K)) t ∈
        spUFixRootSp (Pi.single (Sum.inl i) (1 : K))
      exact Subgroup.subset_closure ⟨t, rfl⟩⟩
  have hinj : Function.Injective f := fun s t h =>
    spUCited_spTransvection_injective i (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro x
    have hx : (x : StatedSp r K) ∈ spUFixRootSp (Pi.single (Sum.inl i) (1 : K)) := x.2
    obtain ⟨t, ht⟩ := mem_spUFixRootSp.mp hx
    exact ⟨t, Subtype.ext ht.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

theorem spUCited_mem_normalizer_root_iff (i : Fin r) (g : ↥(StatedSp r K)) :
    g ∈ Subgroup.normalizer (spUCitedRoot r K i : Set ↥(StatedSp r K)) ↔
      ∃ c : K, c ≠ 0 ∧ spEnd g (Pi.single (Sum.inl i) (1 : K)) =
        c • (Pi.single (Sum.inl i) (1 : K) : Fin r ⊕ Fin r → K) := by
  have h0 : (Pi.single (Sum.inl i) (1 : K) : Fin r ⊕ Fin r → K) ≠ 0 :=
    spUCited_single_inl_ne_zero i
  have hne : spEnd g (Pi.single (Sum.inl i) (1 : K)) ≠ 0 := fun h =>
    h0 (spUCited_spEnd_injective g (by rw [h, map_zero]))
  change g ∈ Subgroup.normalizer (spUFixRootSp (Pi.single (Sum.inl i) (1 : K)) :
    Set ↥(StatedSp r K)) ↔ _
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (spUFixRootSp (Pi.single (Sum.inl i) (1 : K))).map
      (MulAut.conj g).toMonoidHom = spUFixRootSp (Pi.single (Sum.inl i) (1 : K)) ↔
      ∃ c : K, c ≠ 0 ∧ spEnd g (Pi.single (Sum.inl i) (1 : K)) =
        c • (Pi.single (Sum.inl i) (1 : K) : Fin r ⊕ Fin r → K)
  rw [map_conj_spUFixRootSp]
  constructor
  · intro h
    have hc := exists_smul_of_spUFixRootSp_eq hne h0 h
    obtain ⟨c, hc⟩ := hc
    have hcne : c ≠ 0 := fun hc0 => h0 (by rw [hc, hc0, zero_smul])
    refine ⟨c⁻¹, inv_ne_zero hcne, ?_⟩
    have h2 := congrArg (fun w => c⁻¹ • w) hc
    rw [smul_smul, inv_mul_cancel₀ hcne, one_smul] at h2
    exact h2.symm
  · rintro ⟨c, hc, hc'⟩
    rw [hc', spUFixRootSp_smul hc]

theorem spUCited_normalizer_root_zero (hr : 2 ≤ r) :
    Subgroup.normalizer (spUCitedRoot r K ⟨0, by omega⟩ : Set ↥(StatedSp r K)) =
      stabilizer r K (flag r K 1) := by
  ext g
  rw [spUCited_mem_normalizer_root_iff]
  exact (spUCited_mem_stabilizer_flag_one_iff hr g).symm

theorem spUCited_conj_root_zero (hr : 2 ≤ r) :
    (spUCitedRoot r K ⟨0, by omega⟩).map
        (MulAut.conj (weylRep K ⟨0, by omega⟩)).toMonoidHom =
      spUCitedRoot r K ⟨1, by omega⟩ := by
  simp only [spUCitedRoot]
  rw [map_conj_spUFixRootSp]
  have hLP := isLinePerm_weylRep (K := K) (k := (⟨0, by omega⟩ : Fin r))
  have hlt : (↑(⟨0, by omega⟩ : Fin r)) + 1 < r := by
    simp
    omega
  have hσ : simpleRefl r (⟨0, by omega⟩ : Fin r) (Sum.inl (⟨0, by omega⟩ : Fin r)) =
      Sum.inl (⟨1, by omega⟩ : Fin r) := by
    rw [simpleRefl_inl]
    unfold simpleSnd
    rw [dif_pos hlt]
  have hmul := mulVec_single_of_isLinePerm hLP (Sum.inl (⟨0, by omega⟩ : Fin r))
  rw [hσ] at hmul
  have hc : (((weylRep K (⟨0, by omega⟩ : Fin r) : StatedSp r K) :
        GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      (Sum.inl (⟨1, by omega⟩ : Fin r)) (Sum.inl (⟨0, by omega⟩ : Fin r)) ≠ 0 := by
    have h := hLP.apply_ne_zero (Sum.inl (⟨0, by omega⟩ : Fin r))
    rwa [hσ] at h
  have hsp : spEnd (weylRep K (⟨0, by omega⟩ : Fin r))
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)) =
      ((((weylRep K (⟨0, by omega⟩ : Fin r) : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl (⟨1, by omega⟩ : Fin r)) (Sum.inl (⟨0, by omega⟩ : Fin r))) •
        (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) := by
    simp only [spEnd_apply, hmul]
  rw [hsp, spUFixRootSp_smul hc]

end CFSG.LocalAnalysis.WeakClosure81

end
