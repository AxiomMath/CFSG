module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LinearAlgebra.LinearGroups.Elementary

public section

namespace CFSG.StandardType

namespace IOneFieldCF

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {n : ℕ} {K : Type} [Field K]

@[expose] def suppSub (S : Set (Fin n)) : Submodule K (Fin n → K) where
  carrier := {x | ∀ i, i ∉ S → x i = 0}
  add_mem' := fun {a b} ha hb i hi => by simp only [Pi.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c x hx i hi => by simp only [Pi.smul_apply, hx i hi, smul_zero]

theorem mem_elationGenerators_iff' {L : Submodule K (Fin n → K)}
    {A : SpecialLinearGroup (Fin n) K} :
    A ∈ elationGenerators L ↔ (∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ L) ∧
      ∀ v ∈ L, (A : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
  simp only [mem_elationGenerators, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem coe_mulVec_mul (A B : SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    ((A * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      (A : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem sl_inv_mulVec (A : SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
  rw [← coe_mulVec_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem sl_mulVec_inv (A : SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    (A : Matrix (Fin n) (Fin n) K) *ᵥ
      (((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
  rw [← coe_mulVec_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem elationGenerators_mul {L : Submodule K (Fin n → K)} {A B : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ elationGenerators L) (hB : B ∈ elationGenerators L) :
    A * B ∈ elationGenerators L := by
  rw [mem_elationGenerators_iff'] at hA hB ⊢
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [coe_mulVec_mul]
    have h : (A : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) - v =
        ((A : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) -
          (B : Matrix (Fin n) (Fin n) K) *ᵥ v) +
          ((B : Matrix (Fin n) (Fin n) K) *ᵥ v - v) := by abel
    rw [h]
    exact L.add_mem (hA.1 _) (hB.1 v)
  · rw [coe_mulVec_mul, hB.2 v hv, hA.2 v hv]

theorem elationGenerators_inv {L : Submodule K (Fin n → K)} {A : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ elationGenerators L) : A⁻¹ ∈ elationGenerators L := by
  rw [mem_elationGenerators_iff'] at hA ⊢
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have h := hA.1 (((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
    rw [sl_mulVec_inv] at h
    have h' := L.neg_mem h
    rwa [neg_sub] at h'
  · calc ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v
        = ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) := by rw [hA.2 v hv]
      _ = v := sl_inv_mulVec A v

@[expose] def elSub (L : Submodule K (Fin n → K)) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := elationGenerators L
  mul_mem' := elationGenerators_mul
  one_mem' := one_mem_elationGenerators L
  inv_mem' := elationGenerators_inv

theorem mem_elSub {L : Submodule K (Fin n → K)} {A : SpecialLinearGroup (Fin n) K} :
    A ∈ elSub L ↔ A ∈ elationGenerators L := Iff.rfl

theorem elationGenerators_mul_self [CharP K 2] {L : Submodule K (Fin n → K)}
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ elationGenerators L) : A * A = 1 := by
  apply Subtype.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [coe_mulVec_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [mem_elationGenerators_iff'] at hA
  have hu := hA.2 _ (hA.1 v)
  rw [Matrix.mulVec_sub] at hu
  have h2 : ∀ x : Fin n → K, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  have h3 : (A : Matrix (Fin n) (Fin n) K) *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      ((A : Matrix (Fin n) (Fin n) K) *ᵥ v - v) + (A : Matrix (Fin n) (Fin n) K) *ᵥ v :=
    sub_eq_iff_eq_add.mp hu
  rw [h3]
  calc ((A : Matrix (Fin n) (Fin n) K) *ᵥ v - v) + (A : Matrix (Fin n) (Fin n) K) *ᵥ v
      = ((A : Matrix (Fin n) (Fin n) K) *ᵥ v + (A : Matrix (Fin n) (Fin n) K) *ᵥ v) - v := by
        abel
    _ = -v := by rw [h2, zero_sub]
    _ = v := neg_eq_of_add_eq_zero_right (h2 v)

theorem isPGroup_elSub [CharP K 2] (L : Submodule K (Fin n → K)) : IsPGroup 2 (elSub L) :=
  fun A => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, sq, Subgroup.coe_one]
    exact elationGenerators_mul_self A.2)⟩

@[expose] def elProj (L : Submodule K (Fin n → K)) : Subgroup (projectiveSL n K) :=
  (elSub L).map (proj n K)

theorem isPGroup_elProj [CharP K 2] (L : Submodule K (Fin n → K)) : IsPGroup 2 (elProj L) :=
  (isPGroup_elSub L).map _

theorem elProj_suppSub_ne_bot {S : Set (Fin n)} {i j : Fin n} (hi : i ∈ S) (hj : j ∉ S) :
    elProj (suppSub (K := K) S) ≠ ⊥ := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  set g : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.transvection hij 1 with hg
  have hgv : ∀ v : Fin n → K, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v + (v j) • Pi.single i 1 := by
    intro v
    rw [hg, CFSG.LinearGroups.coe_transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec_eq, one_mul]
  have hgS : g ∈ elSub (suppSub (K := K) S) := by
    rw [mem_elSub, mem_elationGenerators_iff']
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [hgv, add_sub_cancel_left]
      intro k hk
      have hki : k ≠ i := fun h => hk (h ▸ hi)
      simp [Pi.single_apply, hki]
    · rw [hgv, hv j hj, zero_smul, add_zero]
  intro hbot
  have hmem : proj n K g ∈ elProj (suppSub (K := K) S) := ⟨g, hgS, rfl⟩
  rw [hbot, Subgroup.mem_bot, proj_eq_one_iff] at hmem
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hmem
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) hc
  simp [hg, CFSG.LinearGroups.coe_transvection, Matrix.scalar_apply, Matrix.diagonal_apply,
    hij] at h1

theorem slConjugation_mem_elationGenerators {L : Submodule K (Fin n → K)} (M : GL (Fin n) K)
    (hM : ∀ v ∈ L, (M : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ L)
    (hM' : ∀ v ∈ L, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ L)
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ elationGenerators L) :
    CatalogueBHigherLinearAction.slConjugation n K M g ∈ elationGenerators L := by
  rw [mem_elationGenerators_iff'] at hg ⊢
  have hMM : ∀ v : Fin n → K, (M : Matrix (Fin n) (Fin n) K) *ᵥ
      (((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hmv : ∀ v : Fin n → K,
      ((CatalogueBHigherLinearAction.slConjugation n K M g : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v =
      (M : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ
        (((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) := fun v => by
    rw [coe_slConjugation, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [hmv]
    set x := ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v with hx
    have h : (M : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) - v =
        (M : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x - x) := by
      rw [Matrix.mulVec_sub, hx, hMM v]
    rw [h]
    exact hM _ (hg.1 x)
  · rw [hmv, hg.2 _ (hM' w hw), hMM w]

theorem slMap_mem_elationGenerators {L : Submodule K (Fin n → K)} (τ : K ≃+* K)
    (hτ : ∀ v ∈ L, (fun i => τ (v i)) ∈ L) (hτ' : ∀ v ∈ L, (fun i => τ.symm (v i)) ∈ L)
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ elationGenerators L) :
    SpecialLinearGroup.map τ.toRingHom g ∈ elationGenerators L := by
  rw [mem_elationGenerators_iff'] at hg ⊢
  have hmv : ∀ (v : Fin n → K) (i : Fin n),
      (((SpecialLinearGroup.map τ.toRingHom g : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v) i =
      τ (((g : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => τ.symm (v j))) i) := by
    intro v i
    have h := RingHom.map_mulVec τ.toRingHom (g : Matrix (Fin n) (Fin n) K)
      (fun j => τ.symm (v j)) i
    rw [SpecialLinearGroup.map_apply_coe]
    simpa [Function.comp_def] using h.symm
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · have h := hτ _ (hg.1 (fun j => τ.symm (v j)))
    convert h using 1
    funext i
    rw [Pi.sub_apply, hmv, Pi.sub_apply, map_sub, RingEquiv.apply_symm_apply]
  · funext i
    rw [hmv, hg.2 _ (hτ' w hw)]
    exact τ.apply_symm_apply (w i)

theorem conjAut_mem_elProj {L : Submodule K (Fin n → K)} (M : GL (Fin n) K)
    (hM : ∀ v ∈ L, (M : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ L)
    (hM' : ∀ v ∈ L, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ L) :
    ∀ u ∈ elProj L, conjAut n K M u ∈ elProj L := by
  rintro _ ⟨g, hg, rfl⟩
  rw [conjAut_proj]
  exact ⟨_, slConjugation_mem_elationGenerators M hM hM' hg, rfl⟩

theorem fieldAut_mem_elProj {L : Submodule K (Fin n → K)} (τ : K ≃+* K)
    (hτ : ∀ v ∈ L, (fun i => τ (v i)) ∈ L) (hτ' : ∀ v ∈ L, (fun i => τ.symm (v i)) ∈ L) :
    ∀ u ∈ elProj L, fieldAut n K τ u ∈ elProj L := by
  rintro _ ⟨g, hg, rfl⟩
  rw [fieldAut_proj]
  exact ⟨_, slMap_mem_elationGenerators τ hτ hτ' hg, rfl⟩

end IOneFieldCF

end CFSG.StandardType
