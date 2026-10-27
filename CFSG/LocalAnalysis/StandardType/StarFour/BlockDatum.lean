module

public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSL
public import CFSG.LinearAlgebra.RootGroupSL.DatumEquiv
public import CFSG.LinearAlgebra.RootGroupSL.Normalizer

public section

namespace CFSG.StandardType.StarFour

open CFSG.LinearAlgebra.RootGroupSL

variable {F : Type} [Field F] {P : Type} [CommGroup P] {V : Type} [AddCommGroup V] [Module F V]
  {ρ : P →* (V ≃ₗ[F] V)}

@[expose] def SemiFrame.blockIota (fr : SemiFrame F ρ) (i : Fin fr.r) (a : Fin (fr.m i)) :
    fr.E i →ₗ[F] V :=
  (fr.Φ.symm : (∀ j, Fin (fr.m j) → fr.E j) →ₗ[F] V) ∘ₗ
    LinearMap.single F (fun j => Fin (fr.m j) → fr.E j) i ∘ₗ
    LinearMap.single F (fun _ : Fin (fr.m i) => fr.E i) a

@[expose] def SemiFrame.blockPi (fr : SemiFrame F ρ) (i : Fin fr.r) (b : Fin (fr.m i)) :
    V →ₗ[F] fr.E i :=
  (LinearMap.proj b : (Fin (fr.m i) → fr.E i) →ₗ[F] fr.E i) ∘ₗ
    (LinearMap.proj i : (∀ j, Fin (fr.m j) → fr.E j) →ₗ[F] (Fin (fr.m i) → fr.E i)) ∘ₗ
    (fr.Φ : V →ₗ[F] (∀ j, Fin (fr.m j) → fr.E j))

private lemma phi_blockIota (fr : SemiFrame F ρ) (i : Fin fr.r) (a : Fin (fr.m i))
    (t : fr.E i) : fr.Φ (fr.blockIota i a t) = Pi.single i (Pi.single a t) := by
  rw [SemiFrame.blockIota, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.single_apply, LinearMap.single_apply]
  exact fr.Φ.apply_symm_apply _

private lemma blockPi_apply (fr : SemiFrame F ρ) (i : Fin fr.r) (b : Fin (fr.m i)) (v : V) :
    fr.blockPi i b v = fr.Φ v i b := by
  rw [SemiFrame.blockPi, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.proj_apply]
  rfl

theorem SemiFrame.blockPi_blockIota_ne (fr : SemiFrame F ρ) (i : Fin fr.r)
    {a b : Fin (fr.m i)} (hab : a ≠ b) (t : fr.E i) :
    fr.blockPi i b (fr.blockIota i a t) = 0 := by
  rw [blockPi_apply, phi_blockIota, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm]

theorem SemiFrame.blockPi_blockIota_self (fr : SemiFrame F ρ) (i : Fin fr.r)
    (a : Fin (fr.m i)) (t : fr.E i) : fr.blockPi i a (fr.blockIota i a t) = t := by
  rw [blockPi_apply, phi_blockIota, Pi.single_eq_same, Pi.single_eq_same]

theorem SemiFrame.blockIota_injective (fr : SemiFrame F ρ) (i : Fin fr.r) (a : Fin (fr.m i)) :
    Function.Injective (fr.blockIota i a) := by
  intro s t h
  have h' := congrArg (fr.blockPi i a) h
  simpa only [SemiFrame.blockPi_blockIota_self] using h'

theorem SemiFrame.blockPi_ne_zero (fr : SemiFrame F ρ) (i : Fin fr.r) (b : Fin (fr.m i)) :
    fr.blockPi i b ≠ 0 := by
  intro h
  have h1 : fr.blockPi i b (fr.blockIota i b 1) = 0 := by
    rw [h]
    rfl
  rw [SemiFrame.blockPi_blockIota_self] at h1
  exact one_ne_zero h1

@[expose] def SemiFrame.idx0 (fr : SemiFrame F ρ) (i : Fin fr.r) (hm : 2 ≤ fr.m i) :
    Fin (fr.m i) := ⟨0, by omega⟩

@[expose] def SemiFrame.idx1 (fr : SemiFrame F ρ) (i : Fin fr.r) (hm : 2 ≤ fr.m i) :
    Fin (fr.m i) := ⟨1, by omega⟩

theorem SemiFrame.idx0_ne_idx1 (fr : SemiFrame F ρ) (i : Fin fr.r) (hm : 2 ≤ fr.m i) :
    fr.idx0 i hm ≠ fr.idx1 i hm := by
  simp [SemiFrame.idx0, SemiFrame.idx1, Fin.ext_iff]

variable [Module.Finite F V]

private lemma blockDatum_proj_single (fr : SemiFrame F ρ) (i : Fin fr.r)
    {a b : Fin (fr.m i)} (hab : a ≠ b) :
    ∀ s : fr.E i, (LinearMap.proj b : (Fin (fr.m i) → fr.E i) →ₗ[fr.E i] fr.E i)
      ((LinearMap.single (fr.E i) (fun _ : Fin (fr.m i) => fr.E i) a) s) = 0 := by
  intro s
  show (Pi.single a s : Fin (fr.m i) → fr.E i) b = 0
  rw [Pi.single_eq_of_ne hab.symm]

private lemma blockDatum_iotaPi_zero (fr : SemiFrame F ρ) (i : Fin fr.r)
    {a b : Fin (fr.m i)} (hab : a ≠ b) :
    ∀ t, fr.blockPi i b (fr.blockIota i a t) = 0 := by
  intro t
  exact SemiFrame.blockPi_blockIota_ne fr i hab t

private lemma datumElt_single_proj_apply (fr : SemiFrame F ρ) (i : Fin fr.r)
    {a b : Fin (fr.m i)} (hab : a ≠ b) (t : fr.E i) (x : Fin (fr.m i) → fr.E i) :
    (datumElt (LinearMap.single (fr.E i) (fun _ : Fin (fr.m i) => fr.E i) a)
      (LinearMap.proj b) (blockDatum_proj_single fr i hab) t) x =
      x + Pi.single a (t * x b) := by
  simp only [datumElt_apply, LinearMap.single_apply, LinearMap.proj_apply]

private lemma phi_update_add_single (fr : SemiFrame F ρ) (i : Fin fr.r)
    (w : ∀ j, Fin (fr.m j) → fr.E j) (y : Fin (fr.m i) → fr.E i) :
    Function.update w i (w i + y) = w + Pi.single i y := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Function.update_self]
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

private lemma blockSpecialLinear_datumElt (fr : SemiFrame F ρ) (i : Fin fr.r)
    {a b : Fin (fr.m i)} (hab : a ≠ b) (t : fr.E i) :
    fr.blockSpecialLinear i
      (datumElt (LinearMap.single (fr.E i) (fun _ : Fin (fr.m i) => fr.E i) a)
        (LinearMap.proj b) (blockDatum_proj_single fr i hab) t) =
      datumElt (fr.blockIota i a) (fr.blockPi i b)
        (blockDatum_iotaPi_zero fr i hab) t := by
  apply SpecialLinearGroup.ext
  intro v
  apply fr.Φ.injective
  rw [SemiFrame.blockSpecialLinear_apply]
  have hB : (datumElt (LinearMap.single (fr.E i) (fun _ : Fin (fr.m i) => fr.E i) a)
      (LinearMap.proj b) (blockDatum_proj_single fr i hab) t) (fr.Φ v i) =
      fr.Φ v i + Pi.single a (t * (fr.Φ v i b)) :=
    datumElt_single_proj_apply fr i hab t (fr.Φ v i)
  rw [hB]
  simp only [datumElt_apply, map_add, phi_blockIota, blockPi_apply]
  exact phi_update_add_single fr i (fr.Φ v) (Pi.single a (t * (fr.Φ v i b)))

private lemma datumElt_mem_slOnBlock (fr : SemiFrame F ρ) (i : Fin fr.r)
    {a b : Fin (fr.m i)} (hab : a ≠ b) (t : fr.E i) :
    datumElt (fr.blockIota i a) (fr.blockPi i b)
      (blockDatum_iotaPi_zero fr i hab) t ∈
      fr.slOnBlock i := by
  refine ⟨datumElt (LinearMap.single (fr.E i) (fun _ : Fin (fr.m i) => fr.E i) a)
    (LinearMap.proj b) (blockDatum_proj_single fr i hab) t, fun v => ?_⟩
  rw [← blockSpecialLinear_datumElt fr i hab t]
  exact fr.blockSpecialLinear_apply i _ v

@[expose] def SemiFrame.blockRoot (fr : SemiFrame F ρ) (i : Fin fr.r) (hm : 2 ≤ fr.m i) :
    Subgroup (SpecialLinearGroup F V) :=
  datumRoot (fr.blockIota i (fr.idx0 i hm)) (fr.blockPi i (fr.idx1 i hm))
    (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm) t)

@[expose] def SemiFrame.blockJ0 (fr : SemiFrame F ρ) (i : Fin fr.r) (hm : 2 ≤ fr.m i) :
    Subgroup (SpecialLinearGroup F V) :=
  datumJ0 (fr.blockIota i (fr.idx0 i hm)) (fr.blockIota i (fr.idx1 i hm))
    (fr.blockPi i (fr.idx1 i hm)) (fr.blockPi i (fr.idx0 i hm))
    (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm) t)
    (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm).symm t)

theorem SemiFrame.blockRoot_le_blockJ0 (fr : SemiFrame F ρ) (i : Fin fr.r) (hm : 2 ≤ fr.m i) :
    fr.blockRoot i hm ≤ fr.blockJ0 i hm := by
  unfold SemiFrame.blockRoot SemiFrame.blockJ0
  exact datumRoot_le_datumJ0 _ _ _ _ _ _

theorem SemiFrame.blockJ0_le_slOnBlock (fr : SemiFrame F ρ) (i : Fin fr.r) (hm : 2 ≤ fr.m i) :
    fr.blockJ0 i hm ≤ fr.slOnBlock i := by
  unfold SemiFrame.blockJ0 datumJ0
  rw [Subgroup.closure_le]
  rintro g (hg | hg)
  · obtain ⟨t, rfl⟩ := hg
    exact datumElt_mem_slOnBlock fr i (fr.idx0_ne_idx1 i hm) t
  · obtain ⟨t, rfl⟩ := hg
    exact datumElt_mem_slOnBlock fr i (fr.idx0_ne_idx1 i hm).symm t

theorem SemiFrame.blockRoot_ne_bot (fr : SemiFrame F ρ) (i : Fin fr.r) (hm : 2 ≤ fr.m i) :
    fr.blockRoot i hm ≠ ⊥ := by
  unfold SemiFrame.blockRoot
  exact datumRoot_ne_bot _ _ _ (fr.blockIota_injective i (fr.idx0 i hm))
    (fr.blockPi_ne_zero i (fr.idx1 i hm))

theorem SemiFrame.isPGroup_blockRoot [CharP F 2] (fr : SemiFrame F ρ) (i : Fin fr.r)
    (hm : 2 ≤ fr.m i) : IsPGroup 2 (fr.blockRoot i hm) := by
  unfold SemiFrame.blockRoot
  exact isPGroup_datumRoot _ _ _

end CFSG.StandardType.StarFour
