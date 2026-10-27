module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinCent
public import Mathlib.GroupTheory.PGroup

import CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix

private noncomputable def o2_naturalRepEquiv (d : ℕ) :
    GL (Fin d) (ZMod 2) ≃*
      ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := ZMod 2)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin d → ZMod 2))

private noncomputable def o2_naturalRep (d : ℕ) :
    GL (Fin d) (ZMod 2) →*
      ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
  (o2_naturalRepEquiv d).toMonoidHom

private theorem o2_naturalRep_apply (d : ℕ) (g : GL (Fin d) (ZMod 2))
    (v : Fin d → ZMod 2) :
    o2_naturalRep d g v = (g : Matrix (Fin d) (Fin d) (ZMod 2)) *ᵥ v := by
  simp [o2_naturalRep, o2_naturalRepEquiv]

private theorem o2_transvection_mulVec (d : ℕ) (i j : Fin d) (h : i ≠ j)
    (v : Fin d → ZMod 2) :
    (Matrix.GeneralLinearGroup.transvection i j h (1 : ZMod 2) :
        Matrix (Fin d) (Fin d) (ZMod 2)) *ᵥ v = v + v j • Pi.single i (1 : ZMod 2) := by
  change (Matrix.transvection i j (1 : ZMod 2)) *ᵥ v = v + v j • Pi.single i (1 : ZMod 2)
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq,
    one_mul]

private theorem o2_naturalRep_irreducible (d : ℕ) :
    ∀ W : Submodule (ZMod 2) (Fin d → ZMod 2),
      (∀ g : GL (Fin d) (ZMod 2), ∀ w ∈ W, o2_naturalRep d g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).mp hbot
    have hj : ∃ j, v j ≠ 0 := by
      by_contra h
      apply hv0
      ext k
      by_contra hk
      exact h ⟨k, hk⟩
    obtain ⟨j, hj⟩ := hj
    have hsingle_ne : ∀ k : Fin d, k ≠ j → Pi.single k (1 : ZMod 2) ∈ W := by
      intro k hk
      have hT : o2_naturalRep d (Matrix.GeneralLinearGroup.transvection k j hk (1 : ZMod 2))
          v ∈ W := hW _ v hvW
      have hT' : v + v j • Pi.single k (1 : ZMod 2) ∈ W := by
        rwa [o2_naturalRep_apply, o2_transvection_mulVec d k j hk v] at hT
      have hsub := Submodule.sub_mem W hT' hvW
      have hsmul : (v j) • Pi.single k (1 : ZMod 2) ∈ W := by
        have h1 : (v + v j • (Pi.single k (1 : ZMod 2) : Fin d → ZMod 2)) - v =
            v j • (Pi.single k (1 : ZMod 2) : Fin d → ZMod 2) := by
          abel
        exact h1 ▸ hsub
      have hfin := Submodule.smul_mem W ((v j)⁻¹) hsmul
      simpa [smul_smul, inv_mul_cancel₀ hj] using hfin
    have hsingle_j : Pi.single j (1 : ZMod 2) ∈ W := by
      by_cases hex : ∃ k : Fin d, k ≠ j
      · obtain ⟨k, hk⟩ := hex
        have hek := hsingle_ne k hk
        have hT : o2_naturalRep d
            (Matrix.GeneralLinearGroup.transvection j k hk.symm (1 : ZMod 2))
            (Pi.single k (1 : ZMod 2)) ∈ W := hW _ _ hek
        have hT' : (Pi.single k (1 : ZMod 2) : Fin d → ZMod 2) +
            Pi.single j (1 : ZMod 2) ∈ W := by
          rw [o2_naturalRep_apply, o2_transvection_mulVec d j k hk.symm] at hT
          simpa using hT
        have hsub := Submodule.sub_mem W hT' hek
        have hsmul : (Pi.single j (1 : ZMod 2) : Fin d → ZMod 2) ∈ W := by
          have h1 : ((Pi.single k (1 : ZMod 2) : Fin d → ZMod 2) +
              (Pi.single j (1 : ZMod 2) : Fin d → ZMod 2)) -
              (Pi.single k (1 : ZMod 2) : Fin d → ZMod 2) =
              (Pi.single j (1 : ZMod 2) : Fin d → ZMod 2) := by
            abel
          exact h1 ▸ hsub
        exact hsmul
      · have hkj : ∀ k : Fin d, k = j := fun k => by
          by_contra hk
          exact hex ⟨k, hk⟩
        have hvj : v = (v j) • Pi.single j (1 : ZMod 2) := by
          ext k
          rw [hkj k]
          simp
        have heq : (v j)⁻¹ • v = Pi.single j (1 : ZMod 2) := by
          nth_rewrite 2 [hvj]
          rw [smul_smul, inv_mul_cancel₀ hj, one_smul]
        have hfin := Submodule.smul_mem W ((v j)⁻¹) hvW
        rwa [heq] at hfin
    have hsingle : ∀ i : Fin d, Pi.single i (1 : ZMod 2) ∈ W := by
      intro i
      by_cases hi : i = j
      · rw [hi]; exact hsingle_j
      · exact hsingle_ne i hi
    rw [Submodule.eq_top_iff']
    intro w
    rw [pi_eq_sum_univ' w]
    exact Submodule.sum_mem W fun i _ => Submodule.smul_mem W (w i) (hsingle i)

theorem eq_bot_of_isPGroup_of_normal (d : ℕ) (K : Subgroup (GL (Fin d) (ZMod 2))) [K.Normal]
    (hK : IsPGroup 2 K) : K = ⊥ := by
  have hρ : Function.Injective (o2_naturalRep d) := (o2_naturalRepEquiv d).injective
  have hpc : CFSG.pCore 2 (GL (Fin d) (ZMod 2)) = ⊥ :=
    @CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial.pCore_eq_bot
      2 (inferInstance) (GL (Fin d) (ZMod 2)) (Fin d → ZMod 2)
      (inferInstance) (inferInstance) (Pi.module (Fin d) (fun _ => ZMod 2) (ZMod 2))
      (inferInstance) (inferInstance) (o2_naturalRep d) hρ (o2_naturalRep_irreducible d)
  have hle : K ≤ CFSG.pCore 2 (GL (Fin d) (ZMod 2)) := by
    rw [CFSG.pCore]
    exact le_sSup ⟨inferInstance, hK⟩
  rw [hpc] at hle
  exact le_bot_iff.mp hle

variable (r m : ℕ)

private def o2_toMat (g : Cent r m) : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2) :=
  (g.1 : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2))

private def o2_pAmat (g : Cent r m) : Matrix (Fin r) (Fin r) (ZMod 2) :=
  fun i j => o2_toMat r m g (.inl i) (.inl j)

private def o2_pBmat (g : Cent r m) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun i j => o2_toMat r m g (.inr (.inl i)) (.inr (.inl j))

private theorem o2_cent_decomp (g : Cent r m) :
    ∃ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2))
      (a : Matrix (Fin r) (Fin m) (ZMod 2)) (b : Matrix (Fin m) (Fin r) (ZMod 2))
      (c : Matrix (Fin r) (Fin r) (ZMod 2)),
      o2_toMat r m g =
        blk (P : Matrix (Fin r) (Fin r) (ZMod 2)) a c
          (R : Matrix (Fin m) (Fin m) (ZMod 2)) b (P : Matrix (Fin r) (Fin r) (ZMod 2)) :=
  coe_eq_blk_of_mem_cent r m (g := g.1) g.2

private theorem o2_toMat_mul (g h : Cent r m) :
    o2_toMat r m (g * h) = o2_toMat r m g * o2_toMat r m h := by
  simp only [o2_toMat, Subgroup.coe_mul, Units.val_mul]

private theorem o2_pAmat_eq_of_decomp {g : Cent r m}
    {A : Matrix (Fin r) (Fin r) (ZMod 2)} {R : Matrix (Fin m) (Fin m) (ZMod 2)}
    {a : Matrix (Fin r) (Fin m) (ZMod 2)} {b : Matrix (Fin m) (Fin r) (ZMod 2)}
    {c : Matrix (Fin r) (Fin r) (ZMod 2)}
    (h : o2_toMat r m g = blk A a c R b A) :
    o2_pAmat r m g = A := by
  ext i j
  change o2_toMat r m g (.inl i) (.inl j) = A i j
  rw [h]
  simp [blk]

private theorem o2_pBmat_eq_of_decomp {g : Cent r m}
    {A : Matrix (Fin r) (Fin r) (ZMod 2)} {R : Matrix (Fin m) (Fin m) (ZMod 2)}
    {a : Matrix (Fin r) (Fin m) (ZMod 2)} {b : Matrix (Fin m) (Fin r) (ZMod 2)}
    {c : Matrix (Fin r) (Fin r) (ZMod 2)}
    (h : o2_toMat r m g = blk A a c R b A) :
    o2_pBmat r m g = R := by
  ext i j
  change o2_toMat r m g (.inr (.inl i)) (.inr (.inl j)) = R i j
  rw [h]
  simp [blk]

private theorem o2_pAmat_mul (g h : Cent r m) :
    o2_pAmat r m (g * h) = o2_pAmat r m g * o2_pAmat r m h := by
  obtain ⟨Pg, Rg, ag, bg, cg, hg⟩ := o2_cent_decomp r m g
  obtain ⟨Ph, Rh, ah, bh, ch, hh⟩ := o2_cent_decomp r m h
  have hgh : o2_toMat r m (g * h) =
      blk ((Pg : Matrix (Fin r) (Fin r) (ZMod 2)) * (Ph : Matrix (Fin r) (Fin r) (ZMod 2)))
        ((Pg : Matrix (Fin r) (Fin r) (ZMod 2)) * ah +
          ag * (Rh : Matrix (Fin m) (Fin m) (ZMod 2)))
        ((Pg : Matrix (Fin r) (Fin r) (ZMod 2)) * ch + ag * bh +
          cg * (Ph : Matrix (Fin r) (Fin r) (ZMod 2)))
        ((Rg : Matrix (Fin m) (Fin m) (ZMod 2)) * (Rh : Matrix (Fin m) (Fin m) (ZMod 2)))
        ((Rg : Matrix (Fin m) (Fin m) (ZMod 2)) * bh +
          bg * (Ph : Matrix (Fin r) (Fin r) (ZMod 2)))
        ((Pg : Matrix (Fin r) (Fin r) (ZMod 2)) * (Ph : Matrix (Fin r) (Fin r) (ZMod 2))) := by
    rw [o2_toMat_mul, hg, hh, blk_mul]
  rw [o2_pAmat_eq_of_decomp r m hgh, o2_pAmat_eq_of_decomp r m hg,
    o2_pAmat_eq_of_decomp r m hh]

private theorem o2_pBmat_mul (g h : Cent r m) :
    o2_pBmat r m (g * h) = o2_pBmat r m g * o2_pBmat r m h := by
  obtain ⟨Pg, Rg, ag, bg, cg, hg⟩ := o2_cent_decomp r m g
  obtain ⟨Ph, Rh, ah, bh, ch, hh⟩ := o2_cent_decomp r m h
  have hgh : o2_toMat r m (g * h) =
      blk ((Pg : Matrix (Fin r) (Fin r) (ZMod 2)) * (Ph : Matrix (Fin r) (Fin r) (ZMod 2)))
        ((Pg : Matrix (Fin r) (Fin r) (ZMod 2)) * ah +
          ag * (Rh : Matrix (Fin m) (Fin m) (ZMod 2)))
        ((Pg : Matrix (Fin r) (Fin r) (ZMod 2)) * ch + ag * bh +
          cg * (Ph : Matrix (Fin r) (Fin r) (ZMod 2)))
        ((Rg : Matrix (Fin m) (Fin m) (ZMod 2)) * (Rh : Matrix (Fin m) (Fin m) (ZMod 2)))
        ((Rg : Matrix (Fin m) (Fin m) (ZMod 2)) * bh +
          bg * (Ph : Matrix (Fin r) (Fin r) (ZMod 2)))
        ((Pg : Matrix (Fin r) (Fin r) (ZMod 2)) * (Ph : Matrix (Fin r) (Fin r) (ZMod 2))) := by
    rw [o2_toMat_mul, hg, hh, blk_mul]
  rw [o2_pBmat_eq_of_decomp r m hgh, o2_pBmat_eq_of_decomp r m hg,
    o2_pBmat_eq_of_decomp r m hh]

private theorem o2_pAmat_one : o2_pAmat r m (1 : Cent r m) = 1 := by
  ext i j
  change o2_toMat r m (1 : Cent r m) (.inl i) (.inl j) =
    (1 : Matrix (Fin r) (Fin r) (ZMod 2)) i j
  simp [o2_toMat, Matrix.one_apply]

private theorem o2_pBmat_one : o2_pBmat r m (1 : Cent r m) = 1 := by
  ext i j
  change o2_toMat r m (1 : Cent r m) (.inr (.inl i)) (.inr (.inl j)) =
    (1 : Matrix (Fin m) (Fin m) (ZMod 2)) i j
  simp [o2_toMat, Matrix.one_apply]

private theorem o2_pAmat_mul_inv (g : Cent r m) : o2_pAmat r m g * o2_pAmat r m g⁻¹ = 1 := by
  rw [← o2_pAmat_mul, mul_inv_cancel, o2_pAmat_one]

private theorem o2_pAmat_inv_mul (g : Cent r m) : o2_pAmat r m g⁻¹ * o2_pAmat r m g = 1 := by
  rw [← o2_pAmat_mul, inv_mul_cancel, o2_pAmat_one]

private theorem o2_pBmat_mul_inv (g : Cent r m) : o2_pBmat r m g * o2_pBmat r m g⁻¹ = 1 := by
  rw [← o2_pBmat_mul, mul_inv_cancel, o2_pBmat_one]

private theorem o2_pBmat_inv_mul (g : Cent r m) : o2_pBmat r m g⁻¹ * o2_pBmat r m g = 1 := by
  rw [← o2_pBmat_mul, inv_mul_cancel, o2_pBmat_one]

private def o2_blockA (g : Cent r m) : GL (Fin r) (ZMod 2) :=
  ⟨o2_pAmat r m g, o2_pAmat r m g⁻¹, o2_pAmat_mul_inv r m g, o2_pAmat_inv_mul r m g⟩

private def o2_blockB (g : Cent r m) : GL (Fin m) (ZMod 2) :=
  ⟨o2_pBmat r m g, o2_pBmat r m g⁻¹, o2_pBmat_mul_inv r m g, o2_pBmat_inv_mul r m g⟩

private theorem o2_coe_blockA (g : Cent r m) :
    (o2_blockA r m g : Matrix (Fin r) (Fin r) (ZMod 2)) = o2_pAmat r m g := rfl

private theorem o2_coe_blockB (g : Cent r m) :
    (o2_blockB r m g : Matrix (Fin m) (Fin m) (ZMod 2)) = o2_pBmat r m g := rfl

private theorem o2_blockA_mul (g h : Cent r m) :
    o2_blockA r m (g * h) = o2_blockA r m g * o2_blockA r m h := by
  apply Units.ext
  rw [Units.val_mul, o2_coe_blockA, o2_coe_blockA, o2_coe_blockA, o2_pAmat_mul]

private theorem o2_blockB_mul (g h : Cent r m) :
    o2_blockB r m (g * h) = o2_blockB r m g * o2_blockB r m h := by
  apply Units.ext
  rw [Units.val_mul, o2_coe_blockB, o2_coe_blockB, o2_coe_blockB, o2_pBmat_mul]

private theorem o2_blockA_one : o2_blockA r m (1 : Cent r m) = 1 := by
  apply Units.ext
  rw [o2_coe_blockA, o2_pAmat_one]
  rfl

private theorem o2_blockB_one : o2_blockB r m (1 : Cent r m) = 1 := by
  apply Units.ext
  rw [o2_coe_blockB, o2_pBmat_one]
  rfl

def centBlockHom : Cent r m →* (GL (Fin r) (ZMod 2) × GL (Fin m) (ZMod 2)) where
  toFun g := (o2_blockA r m g, o2_blockB r m g)
  map_one' := Prod.ext (o2_blockA_one r m) (o2_blockB_one r m)
  map_mul' := fun g h => Prod.ext (o2_blockA_mul r m g h) (o2_blockB_mul r m g h)

theorem centBlockHom_levi (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)) :
    centBlockHom r m ⟨levi P R, levi_mem_cent r m P R⟩ = (P, R) := by
  apply Prod.ext
  · change o2_blockA r m ⟨levi P R, levi_mem_cent r m P R⟩ = P
    apply Units.ext
    rw [o2_coe_blockA]
    ext i j
    simp [o2_pAmat, o2_toMat, coe_levi, blk]
  · change o2_blockB r m ⟨levi P R, levi_mem_cent r m P R⟩ = R
    apply Units.ext
    rw [o2_coe_blockB]
    ext i j
    simp [o2_pBmat, o2_toMat, coe_levi, blk]

theorem centBlockHom_surjective : Function.Surjective (centBlockHom r m) := by
  rintro ⟨P, R⟩
  exact ⟨⟨levi P R, levi_mem_cent r m P R⟩, centBlockHom_levi r m P R⟩

theorem centBlockHom_eq_one_iff (g : Cent r m) :
    centBlockHom r m g = 1 ↔ ((g.1 : GL (BlkIdx r m) (ZMod 2)) ∈ uSub r m) := by
  constructor
  · intro h
    have hA : o2_blockA r m g = 1 := congrArg Prod.fst h
    have hB : o2_blockB r m g = 1 := congrArg Prod.snd h
    obtain ⟨Pg, Rg, ag, bg, cg, hg⟩ := o2_cent_decomp r m g
    have hPmat : (Pg : Matrix (Fin r) (Fin r) (ZMod 2)) = 1 := by
      rw [← o2_pAmat_eq_of_decomp r m hg, ← o2_coe_blockA]
      exact congrArg (fun x : GL (Fin r) (ZMod 2) => (x : Matrix (Fin r) (Fin r) (ZMod 2))) hA
    have hRmat : (Rg : Matrix (Fin m) (Fin m) (ZMod 2)) = 1 := by
      rw [← o2_pBmat_eq_of_decomp r m hg, ← o2_coe_blockB]
      exact congrArg (fun x : GL (Fin m) (ZMod 2) => (x : Matrix (Fin m) (Fin m) (ZMod 2))) hB
    have hPg : Pg = 1 := Units.ext hPmat
    have hRg : Rg = 1 := Units.ext hRmat
    refine ⟨ag, bg, cg, ?_⟩
    apply Units.ext
    change o2_toMat r m g = (uGL ag bg cg : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2))
    simp [hg, hPmat, hRmat, coe_uGL, uMat]
  · rintro ⟨a, b, c, hg⟩
    have hmat : o2_toMat r m g = uMat a b c := by
      rw [o2_toMat, hg, coe_uGL]
    have hAmat : o2_pAmat r m g = 1 := by
      ext i j
      change o2_toMat r m g (.inl i) (.inl j) = (1 : Matrix (Fin r) (Fin r) (ZMod 2)) i j
      rw [hmat]
      simp [uMat, blk, Matrix.one_apply]
    have hBmat : o2_pBmat r m g = 1 := by
      ext i j
      change o2_toMat r m g (.inr (.inl i)) (.inr (.inl j)) =
        (1 : Matrix (Fin m) (Fin m) (ZMod 2)) i j
      rw [hmat]
      simp [uMat, blk, Matrix.one_apply]
    have hA : o2_blockA r m g = 1 := by
      apply Units.ext
      rw [o2_coe_blockA, hAmat]
      rfl
    have hB : o2_blockB r m g = 1 := by
      apply Units.ext
      rw [o2_coe_blockB, hBmat]
      rfl
    rw [show centBlockHom r m g = (o2_blockA r m g, o2_blockB r m g) from rfl, hA, hB]
    rfl

theorem le_uSub_of_isPGroup_of_normal (D : Subgroup (GL (BlkIdx r m) (ZMod 2)))
    (hDC : D ≤ Cent r m) (hDn : ∀ g ∈ Cent r m, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hD : IsPGroup 2 D) : D ≤ uSub r m := by
  let Dc : Subgroup (Cent r m) := D.subgroupOf (Cent r m)
  have hDcNormal : Dc.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).mpr
      (Subgroup.le_normalizer_iff.mpr hDn)
  have hDcP : IsPGroup 2 Dc := hD.comap_subtype
  have hS : (Dc.map (centBlockHom r m)).Normal :=
    hDcNormal.map (centBlockHom r m) (centBlockHom_surjective r m)
  have hS1normal : ((Dc.map (centBlockHom r m)).map
      (MonoidHom.fst (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))).Normal :=
    hS.map (MonoidHom.fst (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))
      (fun a => ⟨(a, 1), rfl⟩)
  have hS2normal : ((Dc.map (centBlockHom r m)).map
      (MonoidHom.snd (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))).Normal :=
    hS.map (MonoidHom.snd (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))
      (fun a => ⟨(1, a), rfl⟩)
  have hS1P : IsPGroup 2 ((Dc.map (centBlockHom r m)).map
      (MonoidHom.fst (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))) :=
    (hDcP.map (centBlockHom r m)).map
      (MonoidHom.fst (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))
  have hS2P : IsPGroup 2 ((Dc.map (centBlockHom r m)).map
      (MonoidHom.snd (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))) :=
    (hDcP.map (centBlockHom r m)).map
      (MonoidHom.snd (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))
  have hbot1 : ((Dc.map (centBlockHom r m)).map
      (MonoidHom.fst (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))) = ⊥ :=
    @eq_bot_of_isPGroup_of_normal r _ hS1normal hS1P
  have hbot2 : ((Dc.map (centBlockHom r m)).map
      (MonoidHom.snd (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2)))) = ⊥ :=
    @eq_bot_of_isPGroup_of_normal m _ hS2normal hS2P
  intro d hd
  let g : Cent r m := ⟨d, hDC hd⟩
  have hgDc : g ∈ Dc := hd
  have hx : centBlockHom r m g ∈ Dc.map (centBlockHom r m) :=
    Subgroup.mem_map_of_mem (centBlockHom r m) hgDc
  have h1 : (centBlockHom r m g).1 = 1 := by
    have hfst := Subgroup.mem_map_of_mem
      (MonoidHom.fst (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2))) hx
    rw [hbot1] at hfst
    exact Subgroup.mem_bot.mp hfst
  have h2 : (centBlockHom r m g).2 = 1 := by
    have hsnd := Subgroup.mem_map_of_mem
      (MonoidHom.snd (GL (Fin r) (ZMod 2)) (GL (Fin m) (ZMod 2))) hx
    rw [hbot2] at hsnd
    exact Subgroup.mem_bot.mp hsnd
  have hker : centBlockHom r m g = 1 := Prod.ext h1 h2
  have hmem := (centBlockHom_eq_one_iff r m g).mp hker
  simpa [g] using hmem

end CFSG.StandardType.FF81.RootFusionLin

end
