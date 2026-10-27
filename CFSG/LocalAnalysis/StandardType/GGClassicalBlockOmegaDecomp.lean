module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDict
public import CFSG.LocalAnalysis.StandardType.GGOuterInvFieldTags
public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI
public import CFSG.RankThree.GF2n.Smith81.Orth28Omega
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaPlusFour
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Commutator
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagBlocks
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Torus
public import CFSG.LargeExtraspecial.DWFldOrth
public import CFSG.HardMathSupport.Dickson.Bal207.Glue
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix
open Polynomial

private def ggJSo1_orth {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) : Subgroup (GL ι K) where
  carrier := {A | ∀ v, Φ ((A : Matrix ι ι K).mulVec v) = Φ v}
  mul_mem' {a b} ha hb v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' v := by
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' {a} ha v := by
    have h1 : Φ (((a : GL ι K) : Matrix ι ι K).mulVec
        (((a⁻¹ : GL ι K) : Matrix ι ι K).mulVec v)) = Φ v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    exact (ha (((a⁻¹ : GL ι K) : Matrix ι ι K).mulVec v)).symm.trans h1

private lemma ggJSo1_statedOmega_eq_commutator {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K)) :
    StatedOmega ⇑Φ = ⁅ggJSo1_orth Φ, ggJSo1_orth Φ⁆ := by
  have h : Subgroup.closure {A : GL ι K | ∀ v, Φ ((A : Matrix ι ι K).mulVec v) = Φ v} =
      ggJSo1_orth Φ := Subgroup.closure_eq (ggJSo1_orth Φ)
  unfold StatedOmega
  rw [h]

private lemma ggJSo1_pair_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ x ∈ Units.val '' S, ∀ y ∈ Units.val '' S, x * y = y * x := by
  intro x hx y hy
  rcases hx with ⟨s, hs, rfl⟩
  rcases hy with ⟨s', hs', rfl⟩
  simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F))
    (hS s hs s' hs')

private lemma ggJSo1_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      a * b = b * a := by
  intro a ha b hb
  exact Algebra.adjoin_induction₂ (R := F) (A := Matrix ι ι F) (s := Units.val '' S)
    (p := fun a b _ _ => a * b = b * a)
    (fun x y hx hy => ggJSo1_pair_comm S hS x hx y hy)
    (fun r₁ r₂ => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, mul_comm])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun x y z hx hy hz hxz hyz => by rw [add_mul, mul_add, hxz, hyz])
    (fun x y z hx hy hz hxy hxz => by rw [mul_add, add_mul, hxy, hxz])
    (fun x y z hx hy hz hxz hyz => by
      rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc])
    (fun x y z hx hy hz hxy hxz => by
      rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc])
    (x := a) (y := b) ha hb

private lemma ggJSo1_adjoin_commute_S {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (a : Matrix ι ι F) (ha : a ∈ Algebra.adjoin F (Units.val '' S))
    (s : GL ι F) (hs : s ∈ S) :
    a * (s : Matrix ι ι F) = (s : Matrix ι ι F) * a :=
  ggJSo1_adjoin_comm S hS a ha (s : Matrix ι ι F)
    (Algebra.subset_adjoin ⟨s, hs, rfl⟩)

private lemma ggJSo1_mem_adjoin_commute {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι]
    [Field F] (j : U →* GL ι F) (S : Set (GL ι F))
    (x : U) (hx : x ∈ (Subgroup.centralizer S).comap j) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (j x : Matrix ι ι F) * a = a * (j x : Matrix ι ι F) := by
  have hgen : Units.val '' S ⊆ Subalgebra.centralizer F {(j x : Matrix ι ι F)} := by
    intro y hy
    change y ∈ Subalgebra.centralizer F {(j x : Matrix ι ι F)}
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rcases hy with ⟨t, ht, rfl⟩
    have hmem := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx)) t ht
    have hm : (t : Matrix ι ι F) * (j x : Matrix ι ι F) =
        (j x : Matrix ι ι F) * (t : Matrix ι ι F) := by
      simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hmem
    exact hm.symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F {(j x : Matrix ι ι F)} :=
    Algebra.adjoin_le hgen
  intro a ha
  exact (Subalgebra.mem_centralizer_iff F).mp (hA ha) (j x) (Set.mem_singleton _)

private lemma ggJSo1_inv_comm {R : Type} [Ring R] {x xi e : R} (hx : x * xi = 1)
    (hxi : xi * x = 1) (hc : x * e = e * x) : xi * e = e * xi := by
  calc xi * e = xi * e * (x * xi) := by rw [hx, mul_one]
    _ = xi * (e * x) * xi := by noncomm_ring
    _ = xi * (x * e) * xi := by rw [hc]
    _ = xi * x * e * xi := by noncomm_ring
    _ = e * xi := by rw [hxi]; noncomm_ring

private lemma ggJSo1_blk_val_mul_inv {R : Type} [Ring R] (x xi e : R) (hx : x * xi = 1)
    (hid : e * e = e) (hci : xi * e = e * xi) :
    (x * e + (1 - e)) * (xi * e + (1 - e)) = 1 := by
  have hxe : x * (xi * e) = e := by rw [← mul_assoc, hx, one_mul]
  have hexi : e * (xi * e) = xi * e := by
    calc e * (xi * e) = (e * xi) * e := by rw [mul_assoc]
      _ = (xi * e) * e := by rw [← hci]
      _ = xi * (e * e) := by rw [mul_assoc]
      _ = xi * e := by rw [hid]
  have hxe' : (x * e) * (xi * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private lemma ggJSo1_blk_inv_mul {R : Type} [Ring R] (x xi e : R) (hxi : xi * x = 1)
    (hid : e * e = e) (hc : x * e = e * x) :
    (xi * e + (1 - e)) * (x * e + (1 - e)) = 1 := by
  have hxe : xi * (x * e) = e := by rw [← mul_assoc, hxi, one_mul]
  have hexi : e * (x * e) = x * e := by
    calc e * (x * e) = (e * x) * e := by rw [mul_assoc]
      _ = (x * e) * e := by rw [← hc]
      _ = x * (e * e) := by rw [mul_assoc]
      _ = x * e := by rw [hid]
  have hxe' : (xi * e) * (x * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private noncomputable def ggJSo1_blkAux {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) : GL ι F :=
  Units.mk ((x : Matrix ι ι F) * e + (1 - e))
    (((x⁻¹ : GL ι F) : Matrix ι ι F) * e + (1 - e))
    (ggJSo1_blk_val_mul_inv (x : Matrix ι ι F) ((x⁻¹ : GL ι F) : Matrix ι ι F) e
      (Units.mul_inv x) hid.eq
      (ggJSo1_inv_comm (Units.mul_inv x) (Units.inv_mul x) hcomm))
    (ggJSo1_blk_inv_mul (x : Matrix ι ι F) ((x⁻¹ : GL ι F) : Matrix ι ι F) e
      (Units.inv_mul x) hid.eq hcomm)

private noncomputable def ggJSo1_blk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) : GL ι F := by
  classical
  exact if h : ∃ u : GL ι F, (u : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e)
    then Classical.choose h else 1

private lemma ggJSo1_blk_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    (ggJSo1_blk x e : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e) := by
  have h : ∃ u : GL ι F, (u : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e) :=
    ⟨ggJSo1_blkAux x e hid hcomm, rfl⟩
  rw [ggJSo1_blk, dif_pos h]
  exact Classical.choose_spec h

private lemma ggJSo1_blk_mem_centralizer {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι]
    [Field F] (j : U →* GL ι F) (S : Set (GL ι F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (x : U)
    (hx : x ∈ (Subgroup.centralizer S).comap j) (e : Matrix ι ι F)
    (heA : e ∈ Algebra.adjoin F (Units.val '' S)) (hid : IsIdempotentElem e)
    (hxe : (j x : Matrix ι ι F) * e = e * (j x : Matrix ι ι F)) :
    ggJSo1_blk (j x) e ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ggJSo1_blk_val (j x) e hid hxe]
  have hxs : (s : Matrix ι ι F) * (j x : Matrix ι ι F) =
      (j x : Matrix ι ι F) * (s : Matrix ι ι F) := by
    have hmem := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx)) s hs
    simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hmem
  have hes : e * (s : Matrix ι ι F) = (s : Matrix ι ι F) * e :=
    ggJSo1_adjoin_commute_S S hS e heA s hs
  have h1 : (s : Matrix ι ι F) * ((j x : Matrix ι ι F) * e) =
      (j x : Matrix ι ι F) * ((s : Matrix ι ι F) * e) := by
    rw [← mul_assoc, hxs, mul_assoc]
  noncomm_ring [hxs, hes, h1]

private lemma ggJSo1_blk_mem_glFixing {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hxe : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    ggJSo1_blk x e ∈ glFixing (1 - e) := by
  change ((ggJSo1_blk x e : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e
  rw [ggJSo1_blk_val x e hid hxe]
  have h1 : e * (e * (x : Matrix ι ι F)) = e * (x : Matrix ι ι F) := by
    rw [← mul_assoc, hid.eq]
  noncomm_ring [hid.eq, hxe, h1]

private lemma ggJSo1_blk_mul_mat {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x y : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hx : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F))
    (hy : (y : Matrix ι ι F) * e = e * (y : Matrix ι ι F)) :
    (x * e + (1 - e)) * (y * e + (1 - e)) = (x * y) * e + (1 - e) := by
  have h1 : e * (1 - e) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hid.eq, sub_self]
  have h2 : (1 - e) * e = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hid.eq, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hid.eq]
    abel
  have h4 : (x * e) * (y * e) = (x * y) * e := by
    calc (x * e) * (y * e) = x * (e * (y * e)) := by rw [Matrix.mul_assoc]
      _ = x * ((e * y) * e) := by rw [Matrix.mul_assoc]
      _ = x * ((y * e) * e) := by rw [← hy]
      _ = x * (y * (e * e)) := by rw [Matrix.mul_assoc]
      _ = x * (y * e) := by rw [hid.eq]
      _ = (x * y) * e := by rw [Matrix.mul_assoc]
  calc (x * e + (1 - e)) * (y * e + (1 - e))
      = (x * e) * (y * e) + (x * e) * (1 - e) +
          ((1 - e) * (y * e) + (1 - e) * (1 - e)) := by
        noncomm_ring
    _ = (x * e) * (y * e) + 0 + (0 + (1 - e)) := by
        rw [show (x * e) * (1 - e) = 0 by
              rw [Matrix.mul_assoc, h1, Matrix.mul_zero],
            show (1 - e) * (y * e) = 0 by
              rw [hy, ← Matrix.mul_assoc, h2, Matrix.zero_mul],
            h3]
    _ = (x * y) * e + (1 - e) := by rw [h4]; abel

private lemma ggJSo1_blk_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x y : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hx : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F))
    (hy : (y : Matrix ι ι F) * e = e * (y : Matrix ι ι F)) :
    ggJSo1_blk (x * y) e = ggJSo1_blk x e * ggJSo1_blk y e := by
  apply Units.ext
  have hxy : ((x * y : GL ι F) : Matrix ι ι F) * e =
      e * ((x * y : GL ι F) : Matrix ι ι F) := by
    rw [Units.val_mul, Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]
  rw [Units.val_mul, ggJSo1_blk_val (x * y) e hid hxy,
    ggJSo1_blk_val x e hid hx, ggJSo1_blk_val y e hid hy]
  exact (ggJSo1_blk_mul_mat x y e hid hx hy).symm

private lemma ggJSo1_blk_inv_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hx : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    (((ggJSo1_blk x e)⁻¹ : GL ι F) : Matrix ι ι F) =
      (((x⁻¹ : GL ι F) : Matrix ι ι F) * e + (1 - e)) := by
  have hcomm : ((x⁻¹ : GL ι F) : Matrix ι ι F) * e =
      e * ((x⁻¹ : GL ι F) : Matrix ι ι F) :=
    ggJSo1_inv_comm (Units.mul_inv x) (Units.inv_mul x) hx
  have hprod : ggJSo1_blk x e * ggJSo1_blk x⁻¹ e = 1 := by
    rw [← ggJSo1_blk_mul x x⁻¹ e hid hx hcomm, mul_inv_cancel]
    apply Units.ext
    rw [ggJSo1_blk_val 1 e hid (by rw [Units.val_one, one_mul, mul_one]),
      Units.val_one, one_mul, add_sub_cancel]
  rw [inv_eq_of_mul_eq_one_right hprod]
  exact ggJSo1_blk_val x⁻¹ e hid hcomm

private lemma ggJSo1_blk_conj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x c : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hxe : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F))
    (hce : (c : Matrix ι ι F) * e = e * (c : Matrix ι ι F))
    (hcfix : (c : Matrix ι ι F) * (1 - e) = 1 - e) :
    ((ggJSo1_blk x e : GL ι F) : Matrix ι ι F) * (c : Matrix ι ι F) *
        (((ggJSo1_blk x e)⁻¹ : GL ι F) : Matrix ι ι F) =
      (x : Matrix ι ι F) * (c : Matrix ι ι F) * ((x⁻¹ : GL ι F) : Matrix ι ι F) := by
  rw [ggJSo1_blk_val x e hid hxe, ggJSo1_blk_inv_val x e hid hxe]
  have hxi : ((x⁻¹ : GL ι F) : Matrix ι ι F) * e =
      e * ((x⁻¹ : GL ι F) : Matrix ι ι F) :=
    ggJSo1_inv_comm (Units.mul_inv x) (Units.inv_mul x) hxe
  have hcfix' : (1 - e) * (c : Matrix ι ι F) = 1 - e := by
    calc (1 - e) * (c : Matrix ι ι F)
        = (c : Matrix ι ι F) - e * (c : Matrix ι ι F) := by
          rw [Matrix.sub_mul, Matrix.one_mul]
      _ = (c : Matrix ι ι F) - (c : Matrix ι ι F) * e := by rw [hce]
      _ = (c : Matrix ι ι F) * (1 - e) := by
          simpa only [Matrix.mul_one] using
            (Matrix.mul_sub (c : Matrix ι ι F) 1 e).symm
      _ = 1 - e := hcfix
  have hx1 : (x : Matrix ι ι F) * (1 - e) = (1 - e) * (x : Matrix ι ι F) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hxe]
  have hxi1 : ((x⁻¹ : GL ι F) : Matrix ι ι F) * (1 - e) =
      (1 - e) * ((x⁻¹ : GL ι F) : Matrix ι ι F) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hxi]
  have hprod : (x * e + (1 - e)) * (x⁻¹ * e + (1 - e)) = 1 := by
    have h := Units.mul_inv (ggJSo1_blk x e)
    rw [ggJSo1_blk_val x e hid hxe, ggJSo1_blk_inv_val x e hid hxe] at h
    exact h
  have haux : ((x : Matrix ι ι F) * (c : Matrix ι ι F) *
      ((x⁻¹ : GL ι F) : Matrix ι ι F)) * (1 - e) = 1 - e := by
    calc ((x : Matrix ι ι F) * (c : Matrix ι ι F) *
          ((x⁻¹ : GL ι F) : Matrix ι ι F)) * (1 - e)
        = (x : Matrix ι ι F) * (c : Matrix ι ι F) *
            (((x⁻¹ : GL ι F) : Matrix ι ι F) * (1 - e)) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix ι ι F) * (c : Matrix ι ι F) *
            ((1 - e) * ((x⁻¹ : GL ι F) : Matrix ι ι F)) := by rw [hxi1]
      _ = (x : Matrix ι ι F) * ((c : Matrix ι ι F) * (1 - e)) *
            ((x⁻¹ : GL ι F) : Matrix ι ι F) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix ι ι F) * (1 - e) * ((x⁻¹ : GL ι F) : Matrix ι ι F) := by
            rw [hcfix]
      _ = ((1 - e) * (x : Matrix ι ι F)) * ((x⁻¹ : GL ι F) : Matrix ι ι F) := by
            rw [hx1]
      _ = 1 - e := by
            rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hxc : ((x : Matrix ι ι F) * (c : Matrix ι ι F) *
      ((x⁻¹ : GL ι F) : Matrix ι ι F)) * (x * e) =
      (x : Matrix ι ι F) * (c : Matrix ι ι F) * e := by
    calc ((x : Matrix ι ι F) * (c : Matrix ι ι F) *
          ((x⁻¹ : GL ι F) : Matrix ι ι F)) * (x * e)
        = (x : Matrix ι ι F) * (c : Matrix ι ι F) *
            (((x⁻¹ : GL ι F) : Matrix ι ι F) * (x * e)) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix ι ι F) * (c : Matrix ι ι F) *
            ((((x⁻¹ : GL ι F) : Matrix ι ι F) * x) * e) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix ι ι F) * (c : Matrix ι ι F) * (1 * e) := by rw [Units.inv_mul]
      _ = (x : Matrix ι ι F) * (c : Matrix ι ι F) * e := by rw [Matrix.one_mul]
  have hright : ((x : Matrix ι ι F) * (c : Matrix ι ι F) *
      ((x⁻¹ : GL ι F) : Matrix ι ι F)) * ((x : Matrix ι ι F) * e + (1 - e)) =
      (x : Matrix ι ι F) * (c : Matrix ι ι F) * e + (1 - e) := by
    rw [Matrix.mul_add, hxc, haux]
  have hkey : (x * e + (1 - e)) * (c : Matrix ι ι F) =
      ((x : Matrix ι ι F) * (c : Matrix ι ι F) *
        ((x⁻¹ : GL ι F) : Matrix ι ι F)) * ((x : Matrix ι ι F) * e + (1 - e)) := by
    calc (x * e + (1 - e)) * (c : Matrix ι ι F)
        = (x * e) * (c : Matrix ι ι F) + (1 - e) * (c : Matrix ι ι F) := by
          rw [Matrix.add_mul]
      _ = (x : Matrix ι ι F) * (e * (c : Matrix ι ι F)) + (1 - e) := by
          rw [Matrix.mul_assoc, hcfix']
      _ = (x : Matrix ι ι F) * ((c : Matrix ι ι F) * e) + (1 - e) := by
          rw [← hce]
      _ = (x : Matrix ι ι F) * (c : Matrix ι ι F) * e + (1 - e) := by
          rw [Matrix.mul_assoc]
      _ = ((x : Matrix ι ι F) * (c : Matrix ι ι F) *
            ((x⁻¹ : GL ι F) : Matrix ι ι F)) * ((x : Matrix ι ι F) * e + (1 - e)) := by
          rw [← hright]
  calc (((x : Matrix ι ι F) * e + (1 - e)) * (c : Matrix ι ι F) *
        (((x⁻¹ : GL ι F) : Matrix ι ι F) * e + (1 - e)))
      = (((x : Matrix ι ι F) * (c : Matrix ι ι F) *
            ((x⁻¹ : GL ι F) : Matrix ι ι F)) *
          ((x : Matrix ι ι F) * e + (1 - e))) *
        (((x⁻¹ : GL ι F) : Matrix ι ι F) * e + (1 - e)) := by rw [hkey]
    _ = ((x : Matrix ι ι F) * (c : Matrix ι ι F) *
          ((x⁻¹ : GL ι F) : Matrix ι ι F)) *
          (((x : Matrix ι ι F) * e + (1 - e)) *
            (((x⁻¹ : GL ι F) : Matrix ι ι F) * e + (1 - e))) := by
          rw [Matrix.mul_assoc]
    _ = ((x : Matrix ι ι F) * (c : Matrix ι ι F) *
          ((x⁻¹ : GL ι F) : Matrix ι ι F)) * 1 := by rw [hprod]
    _ = (x : Matrix ι ι F) * (c : Matrix ι ι F) * ((x⁻¹ : GL ι F) : Matrix ι ι F) := by
          rw [Matrix.mul_one]

private lemma ggJSo1_blk_commute_matrices {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (P : Finset (Matrix ι ι F))
    (hPsum : ∑ p ∈ P, p = 1)
    (horth : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0)
    (hpA : ∀ p ∈ P, p ∈ A)
    {M N ε ε' : Matrix ι ι F} (hε : ε ∈ P) (hε' : ε' ∈ P) (hne : ε ≠ ε')
    (hMA : ∀ a ∈ A, M * a = a * M) (hNA : ∀ a ∈ A, N * a = a * N)
    (hMfix : M * (1 - ε) = 1 - ε) (hNfix : N * (1 - ε') = 1 - ε') :
    M * N = N * M := by
  have hMNp : ∀ p ∈ P, M * N * p = N * M * p := by
    intro p hp
    by_cases hpε : p = ε
    · rw [hpε] at *
      clear hpε
      have hNε : N * ε = ε := by
        have h1 : (1 - ε') * ε = ε := by
          rw [Matrix.sub_mul, Matrix.one_mul, horth ε' hε' ε hε hne.symm, sub_zero]
        calc N * ε = N * ((1 - ε') * ε) := by rw [h1]
          _ = (N * (1 - ε')) * ε := by rw [Matrix.mul_assoc]
          _ = (1 - ε') * ε := by rw [hNfix]
          _ = ε := h1
      calc M * N * ε = M * (N * ε) := by rw [Matrix.mul_assoc]
        _ = M * ε := by rw [hNε]
        _ = ε * M := hMA ε (hpA ε hε)
        _ = (N * ε) * M := by rw [hNε]
        _ = N * (ε * M) := by rw [Matrix.mul_assoc]
        _ = N * (M * ε) := by rw [hMA ε (hpA ε hε)]
        _ = N * M * ε := by rw [Matrix.mul_assoc]
    · by_cases hpε' : p = ε'
      · rw [hpε'] at *
        clear hpε'
        have h1e : (1 - ε) * ε' = ε' := by
          rw [Matrix.sub_mul, Matrix.one_mul, horth ε hε ε' hε' hne, sub_zero]
        have hMε' : M * ε' = ε' := by
          calc M * ε' = M * ((1 - ε) * ε') := by rw [h1e]
            _ = (M * (1 - ε)) * ε' := by rw [Matrix.mul_assoc]
            _ = (1 - ε) * ε' := by rw [hMfix]
            _ = ε' := h1e
        have h2 : (1 - ε) * (N * ε') = N * ε' := by
          rw [hNA ε' (hpA ε' hε'), ← Matrix.mul_assoc, h1e]
        have hMNε' : M * (N * ε') = N * ε' := by
          rw [← h2, ← Matrix.mul_assoc, hMfix, h2]
        calc M * N * ε' = M * (N * ε') := by rw [Matrix.mul_assoc]
          _ = N * ε' := hMNε'
          _ = N * (M * ε') := by rw [hMε']
          _ = N * M * ε' := by rw [Matrix.mul_assoc]
      · have hMp : M * p = p := by
          have h1 : (1 - ε) * p = p := by
            rw [Matrix.sub_mul, Matrix.one_mul, horth ε hε p hp (fun h => hpε h.symm), sub_zero]
          calc M * p = M * ((1 - ε) * p) := by rw [h1]
            _ = (M * (1 - ε)) * p := by rw [Matrix.mul_assoc]
            _ = (1 - ε) * p := by rw [hMfix]
            _ = p := h1
        have hNp : N * p = p := by
          have h1 : (1 - ε') * p = p := by
            rw [Matrix.sub_mul, Matrix.one_mul, horth ε' hε' p hp (fun h => hpε' h.symm), sub_zero]
          calc N * p = N * ((1 - ε') * p) := by rw [h1]
            _ = (N * (1 - ε')) * p := by rw [Matrix.mul_assoc]
            _ = (1 - ε') * p := by rw [hNfix]
            _ = p := h1
        calc M * N * p = M * (N * p) := by rw [Matrix.mul_assoc]
          _ = M * p := by rw [hNp]
          _ = p := hMp
          _ = N * p := by rw [hNp]
          _ = N * (M * p) := by rw [hMp]
          _ = N * M * p := by rw [Matrix.mul_assoc]
  have hsum : M * N * (∑ p ∈ P, p) = N * M * (∑ p ∈ P, p) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hMNp p hp)
  rwa [hPsum, Matrix.mul_one, Matrix.mul_one] at hsum

private theorem ggJSo1_exists_ne_zero_ne_one_of_card_ne_two
    {K : Type} [Field K] [Fintype K] (hK : Nat.card K ≠ 2) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  haveI : Nontrivial K := ⟨0, 1, zero_ne_one⟩
  have h1 : 1 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have h2 : 2 < Nat.card K := by omega
  have hcard : ({0, 1} : Finset K).card = 2 := by
    rw [Finset.card_pair_eq_two_iff]
    exact zero_ne_one
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [hcard, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact h2
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, ?_, ?_⟩
  · intro h
    exact hc (by simp [h])
  · intro h
    exact hc (by simp [h])

private theorem ggJSo1_omegaGroup_le_commutator
    {ι K : Type} [Fintype ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) (h5 : 5 ≤ Fintype.card ι) :
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ, TauCeti.QuadraticMap.orthogonalGroup Φ⁆ := by
  have hdim : Module.finrank K (ι → K) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card K
  have h4' : 4 ≤ Module.finrank K (ι → K) := by rw [hdim]; exact h4
  have h5' : 5 ≤ Module.finrank K (ι → K) := by rw [hdim]; exact h5
  refine (CFSG.RankThree.GF2n.Smith81.omegaGroup_le_elementaryGroup_of_four_le
    (V := ι → K) hΦ h4').trans ?_
  by_cases hK2 : Nat.card K = 2
  · haveI : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K :=
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.of_natCard_eq_two hK2
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.elementaryGroup_le_commutator
      (V := ι → K) hΦ (Or.inl h5')
  · obtain ⟨c, hc0, hc1⟩ := ggJSo1_exists_ne_zero_ne_one_of_card_ne_two (K := K) hK2
    exact CFSG.RankThree.GF2n.Stroth80.Classify.elementaryGroup_le_commutator
      (V := ι → K) hΦ hc0 hc1

private theorem ggJSo1_omegaGroup_eq_commutator
    {ι K : Type} [Fintype ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) (h5 : 5 ≤ Fintype.card ι) :
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ, TauCeti.QuadraticMap.orthogonalGroup Φ⁆ :=
  le_antisymm (ggJSo1_omegaGroup_le_commutator Φ hΦ h4 h5)
    (CFSG.LargeExtraspecial.DW.commutator_le_omegaGroup hΦ)

private theorem ggJSo1_mem_statedOmega_iff_omegaGroup
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) (h5 : 5 ≤ Fintype.card ι) (w : GL ι K) :
    w ∈ CFSG.Open.StatedOmega ⇑Φ ↔
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K w ∈
        CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl,
    ggJSo1_omegaGroup_eq_commutator Φ hΦ h4 h5, Subgroup.mem_comap]
  rfl

private lemma ggJSo1_statedOmega_le_orth {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) : StatedOmega ⇑Φ ≤ ggJSo1_orth Φ := by
  rw [ggJSo1_statedOmega_eq_commutator]
  exact Subgroup.commutator_le.mpr (fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact (ggJSo1_orth Φ).mul_mem
      ((ggJSo1_orth Φ).mul_mem ((ggJSo1_orth Φ).mul_mem h₁ h₂)
        ((ggJSo1_orth Φ).inv_mem h₁))
      ((ggJSo1_orth Φ).inv_mem h₂))

private lemma ggJSo1_const_on_fixedSpace {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) (e : Matrix ι ι K)
    (he : e ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) :
    ∃ c : K, ∀ v : ι → K, (b : Matrix ι ι K) *ᵥ v = v → e *ᵥ v = c • v := by
  classical
  refine Algebra.adjoin_induction
    (p := fun e _ => ∃ c : K, ∀ v : ι → K,
      (b : Matrix ι ι K) *ᵥ v = v → e *ᵥ v = c • v) ?_ ?_ ?_ ?_ he
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨1, fun v hv => by rw [hv, one_smul]⟩
  · intro r
    refine ⟨r, fun v _ => ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  · intro x y _ _ hx hy
    obtain ⟨c₁, h₁⟩ := hx
    obtain ⟨c₂, h₂⟩ := hy
    refine ⟨c₁ + c₂, fun v hv => ?_⟩
    rw [Matrix.add_mulVec, h₁ v hv, h₂ v hv, add_smul]
  · intro x y _ _ hx hy
    obtain ⟨c₁, h₁⟩ := hx
    obtain ⟨c₂, h₂⟩ := hy
    refine ⟨c₁ * c₂, fun v hv => ?_⟩
    rw [← Matrix.mulVec_mulVec, h₂ v hv, Matrix.mulVec_smul, h₁ v hv, smul_smul,
      mul_comm c₂ c₁]

private lemma ggJSo1_eps_fixed_scalar {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) (ε : Matrix ι ι K)
    (he : ε ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
    (hid : IsIdempotentElem ε) :
    ∃ c : K, (c = 0 ∨ c = 1) ∧ ∀ v : ι → K,
      (b : Matrix ι ι K) *ᵥ v = v → ε *ᵥ v = c • v := by
  classical
  by_cases hW : ∃ v : ι → K, (b : Matrix ι ι K) *ᵥ v = v ∧ v ≠ 0
  · obtain ⟨v, hv, hvne⟩ := hW
    obtain ⟨c, hc⟩ := ggJSo1_const_on_fixedSpace b ε he
    have hc2 : c * c = c := by
      have h1 : ε *ᵥ (ε *ᵥ v) = ε *ᵥ v := by rw [Matrix.mulVec_mulVec, hid.eq]
      rw [hc v hv, Matrix.mulVec_smul, hc v hv, smul_smul] at h1
      have h2 : (c * c - c) • v = 0 := by rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hvne
    have hc01 : c = 0 ∨ c = 1 := by
      have h3 : c * (c - 1) = 0 := by linear_combination hc2
      rcases mul_eq_zero.mp h3 with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    exact ⟨c, hc01, hc⟩
  · push Not at hW
    refine ⟨0, Or.inl rfl, fun v hv => ?_⟩
    rw [hW v hv]
    simp

private lemma ggJSo1_oddOrderIsometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Φ (orderOf b)
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
    exact ggJSo1_statedOmega_le_orth Φ hb v
  · rw [← map_pow, pow_orderOf_eq_one, map_one]
  · intro h
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h)
  · exact hΦ.1

private lemma ggJSo1_blk_mem_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (u : ↥(StatedOmega ⇑Φ))
    (hu : u ∈ (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype)
    (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε) :
    ggJSo1_blk (u : GL ι K) ε ∈ StatedOmega ⇑Φ := by
  classical
  let x := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b
  let u₀ : (ι → K) ≃ₗ[K] (ι → K) :=
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K (u : GL ι K)
  let wM : GL ι K := ggJSo1_blk (u : GL ι K) ε
  let W₀ : (ι → K) ≃ₗ[K] (ι → K) :=
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K wM
  have h4 : 4 ≤ Fintype.card ι := by omega
  have h5 : 5 ≤ Fintype.card ι := by omega
  have hS : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have huA : (u : GL ι K) ∈ Subgroup.centralizer ({b} : Set (GL ι K)) :=
    Subgroup.mem_comap.mp hu
  have huAcomm : ∀ a ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))),
      ((u : GL ι K) : Matrix ι ι K) * a = a * ((u : GL ι K) : Matrix ι ι K) :=
    ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) u hu
  have hid : IsIdempotentElem ε := hε.2.1
  have hadj : formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) ε = ε := hε.2.2.2.1
  have hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det :=
    ggOmegaBlk_G_isUnit_det Φ hΦ
  have huε : ((u : GL ι K) : Matrix ι ι K) * ε = ε * ((u : GL ι K) : Matrix ι ι K) := huAcomm ε hε.1
  have huorth : (u : GL ι K) ∈ ggJSo1_orth Φ := ggJSo1_statedOmega_le_orth Φ u.2
  have hAiso : ∀ v, Φ (((u : GL ι K) : Matrix ι ι K) *ᵥ v) = Φ v := huorth
  have hwiso : ∀ v, Φ (wM *ᵥ v) = Φ v := by
    intro v
    rw [show (wM : Matrix ι ι K) = ((u : GL ι K) : Matrix ι ι K) * ε + (1 - ε) from
      ggJSo1_blk_val (u : GL ι K) ε hid huε]
    exact ggOmegaBlk_blk_isometry Φ hG hid hadj huε hAiso v
  have hWo : W₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
    exact hwiso v
  have hUo : u₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
    exact hAiso v
  have hwcent : wM ∈ Subgroup.centralizer ({b} : Set (GL ι K)) :=
    ggJSo1_blk_mem_centralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) hS u hu ε
      hε.1 hid huε
  have hWcomm : W₀ * x = x * W₀ := by
    have h := (Subgroup.mem_centralizer_iff.mp hwcent) b (Set.mem_singleton b)
    have h' : wM * b = b * wM := h.symm
    change CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K wM *
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b *
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K wM
    rw [← map_mul, ← map_mul, h']
  have hUcomm : u₀ * x = x * u₀ := by
    have h := (Subgroup.mem_centralizer_iff.mp huA) b (Set.mem_singleton b)
    have h' : (u : GL ι K) * b = b * (u : GL ι K) := h.symm
    change CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K (u : GL ι K) *
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b *
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K (u : GL ι K)
    rw [← map_mul, ← map_mul, h']
  let Wc : ↥(CFSG.RankThree.PartOne.KCOrthogonal.isometryCentralizer Φ x) :=
    ⟨W₀, Subgroup.mem_inf.mpr ⟨hWo,
      Subgroup.mem_centralizer_singleton_iff.mpr hWcomm⟩⟩
  let Uc : ↥(CFSG.RankThree.PartOne.KCOrthogonal.isometryCentralizer Φ x) :=
    ⟨u₀, Subgroup.mem_inf.mpr ⟨hUo,
      Subgroup.mem_centralizer_singleton_iff.mpr hUcomm⟩⟩
  have hx : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Φ (orderOf b) x :=
    ggJSo1_oddOrderIsometry Φ hΦ b hb hodd
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have hhom := hx.dicksonCentralizer_eq_dicksonFixed hodd hΦ hRep
  have huom : u₀ ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Φ hΦ :=
    (ggJSo1_mem_statedOmega_iff_omegaGroup Φ hΦ h4 h5 (u : GL ι K)).mp u.2
  have hdickU : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Φ hΦ ⟨u₀, hUo⟩ = 1 := by
    have hker : (⟨u₀, hUo⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Φ)) ∈
        (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Φ hΦ).ker := by
      rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker Φ hΦ]
      exact Subgroup.mem_subgroupOf.mpr huom
    exact MonoidHom.mem_ker.mp hker
  have hDfU : CFSG.RankThree.PartOne.KCOrthogonal.dicksonFixed hx Uc = 1 := by
    rw [← DFunLike.congr_fun hhom Uc]
    change CFSG.RankThree.OrthogonalInvolutions.dicksonHom Φ hΦ ⟨u₀, hUo⟩ = 1
    exact hdickU
  obtain ⟨c, hc01, hc⟩ := ggJSo1_eps_fixed_scalar b ε hε.1 hid
  have hDfW : CFSG.RankThree.PartOne.KCOrthogonal.dicksonFixed hx Wc = 1 := by
    rcases hc01 with hc0 | hc1
    · have hres : CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ x Wc = 1 := by
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        rw [CFSG.RankThree.PartOne.KCOrthogonal.coe_isometryRestrictFixed,
          LinearEquiv.coe_one, id_eq]
        rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
        have hbw : (b : Matrix ι ι K) *ᵥ (w : ι → K) = (w : ι → K) := by
          have hw := (CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace).mp w.2
          rwa [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply] at hw
        have hcw : ε *ᵥ (w : ι → K) = c • (w : ι → K) := hc (w : ι → K) hbw
        rw [show (wM : Matrix ι ι K) = ((u : GL ι K) : Matrix ι ι K) * ε + (1 - ε) from
          ggJSo1_blk_val (u : GL ι K) ε hid huε]
        rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hcw, hc0, zero_smul,
          Matrix.sub_mulVec, Matrix.one_mulVec, hcw, hc0, zero_smul, sub_zero,
          Matrix.mulVec_zero, zero_add]
      have hcod : ((CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ x).codRestrict _
          (fun g => CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed_mem_orthogonalGroup
            g)) Wc = 1 := by
        apply Subtype.ext
        change CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ x Wc = 1
        exact hres
      simp only [CFSG.RankThree.PartOne.KCOrthogonal.dicksonFixed, MonoidHom.comp_apply]
      rw [hcod, map_one]
    · have hres : CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ x Wc =
          CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ x Uc := by
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        rw [CFSG.RankThree.PartOne.KCOrthogonal.coe_isometryRestrictFixed,
          CFSG.RankThree.PartOne.KCOrthogonal.coe_isometryRestrictFixed,
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
        have hbw : (b : Matrix ι ι K) *ᵥ (w : ι → K) = (w : ι → K) := by
          have hw := (CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace).mp w.2
          rwa [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply] at hw
        have hcw : ε *ᵥ (w : ι → K) = c • (w : ι → K) := hc (w : ι → K) hbw
        rw [show (wM : Matrix ι ι K) = ((u : GL ι K) : Matrix ι ι K) * ε + (1 - ε) from
          ggJSo1_blk_val (u : GL ι K) ε hid huε]
        rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hcw, hc1, Matrix.mulVec_smul,
          one_smul, Matrix.sub_mulVec, Matrix.one_mulVec, hcw, hc1, one_smul, sub_self,
          add_zero]
      have hcod : ((CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ x).codRestrict _
          (fun g => CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed_mem_orthogonalGroup
            g)) Wc =
          ((CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ x).codRestrict _
          (fun g => CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed_mem_orthogonalGroup
            g)) Uc := by
        apply Subtype.ext
        change CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ x Wc =
          CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ x Uc
        exact hres
      have hDf_eq : CFSG.RankThree.PartOne.KCOrthogonal.dicksonFixed hx Wc =
          CFSG.RankThree.PartOne.KCOrthogonal.dicksonFixed hx Uc := by
        simp only [CFSG.RankThree.PartOne.KCOrthogonal.dicksonFixed, MonoidHom.comp_apply]
        rw [hcod]
      rw [hDf_eq, hDfU]
  have hdickW : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Φ hΦ ⟨W₀, hWo⟩ = 1 := by
    change CFSG.RankThree.PartOne.KCOrthogonal.dicksonCentralizer Φ x hΦ Wc = 1
    rw [DFunLike.congr_fun hhom Wc]
    exact hDfW
  change wM ∈ StatedOmega ⇑Φ
  rw [ggJSo1_mem_statedOmega_iff_omegaGroup Φ hΦ h4 h5 wM]
  have hmem : (⟨W₀, hWo⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Φ)) ∈
      (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Φ hΦ).ker :=
    MonoidHom.mem_ker.mpr hdickW
  rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker Φ hΦ] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

private lemma ggJSo1_blk_mem_glBlockCentralizer {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (u : (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype) :
    (⟨ggJSo1_blk ((u : StatedOmega ⇑Φ) : GL ι K) ε,
        ggJSo1_blk_mem_statedOmega Φ hΦ h8 b hb hodd u u.2 ε hε⟩ :
      StatedOmega ⇑Φ) ∈
      glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε := by
  have hS : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have huε : (((u : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * ε =
      ε * (((u : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) :=
    ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K))
      (u : StatedOmega ⇑Φ) u.2 ε hε.1
  show (⟨ggJSo1_blk ((u : StatedOmega ⇑Φ) : GL ι K) ε,
      ggJSo1_blk_mem_statedOmega Φ hΦ h8 b hb hodd u u.2 ε hε⟩ :
      StatedOmega ⇑Φ) ∈
    (Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ glFixing (1 - ε)).comap
      (StatedOmega ⇑Φ).subtype
  rw [Subgroup.mem_comap]
  exact Subgroup.mem_inf.mpr ⟨
    ggJSo1_blk_mem_centralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) hS
      (u : StatedOmega ⇑Φ) u.2 ε hε.1 hε.2.1 huε,
    ggJSo1_blk_mem_glFixing ((u : StatedOmega ⇑Φ) : GL ι K) ε hε.2.1 huε⟩

noncomputable def omegaBlockHom {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε) :
    (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype →*
      glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε :=
  MonoidHom.mk'
    (fun u =>
      ⟨⟨ggJSo1_blk ((u : StatedOmega ⇑Φ) : GL ι K) ε,
          ggJSo1_blk_mem_statedOmega Φ hΦ h8 b hb hodd u u.2 ε hε⟩,
        ggJSo1_blk_mem_glBlockCentralizer Φ hΦ h8 b hb hodd ε hε u⟩)
    (by
      intro u v
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      have huε : (((u : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * ε =
          ε * (((u : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) :=
        ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K))
          (u : StatedOmega ⇑Φ) u.2 ε hε.1
      have hvε : (((v : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * ε =
          ε * (((v : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) :=
        ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K))
          (v : StatedOmega ⇑Φ) v.2 ε hε.1
      exact congrArg (fun w : GL ι K => (w : Matrix ι ι K))
        (ggJSo1_blk_mul (((u : StatedOmega ⇑Φ) : GL ι K))
          (((v : StatedOmega ⇑Φ) : GL ι K)) ε hε.2.1 huε hvε))

lemma omegaBlockHom_val {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (u : (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype) :
    ((((omegaBlockHom Φ hΦ h8 b hb hodd ε hε u :
        glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) :
        StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) =
      (((((u : (Subgroup.centralizer ({b} : Set (GL ι K))).comap
          (StatedOmega ⇑Φ).subtype) : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K)) *
        ε + (1 - ε) := by
  change (ggJSo1_blk ((u : StatedOmega ⇑Φ) : GL ι K) ε : Matrix ι ι K) =
    (((u : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * ε + (1 - ε)
  exact ggJSo1_blk_val ((u : StatedOmega ⇑Φ) : GL ι K) ε hε.2.1
    (ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K))
      (u : StatedOmega ⇑Φ) u.2 ε hε.1)

lemma omegaBlockHom_conj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (g : (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype)
    (c : glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) :
    ((omegaBlockHom Φ hΦ h8 b hb hodd ε hε g :
        glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) :
        StatedOmega ⇑Φ) * (c : StatedOmega ⇑Φ) *
        (((omegaBlockHom Φ hΦ h8 b hb hodd ε hε g :
          glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) :
          StatedOmega ⇑Φ)⁻¹) =
      (g : StatedOmega ⇑Φ) * (c : StatedOmega ⇑Φ) * (g : StatedOmega ⇑Φ)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  have hgε : (((g : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * ε =
      ε * (((g : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) :=
    ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K))
      (g : StatedOmega ⇑Φ) g.2 ε hε.1
  have hc_inf : ((c : StatedOmega ⇑Φ) : GL ι K) ∈
      Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ glFixing (1 - ε) :=
    Subgroup.mem_inf.mp (Subgroup.mem_comap.mp c.2)
  have hcε : (((c : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * ε =
      ε * (((c : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) :=
    ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K))
      (c : StatedOmega ⇑Φ) (Subgroup.mem_comap.mpr hc_inf.1) ε hε.1
  have hcfix : (((c : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * (1 - ε) = 1 - ε :=
    hc_inf.2
  change ((ggJSo1_blk (((g : StatedOmega ⇑Φ) : GL ι K)) ε : GL ι K) : Matrix ι ι K) *
      (((c : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) *
      (((ggJSo1_blk (((g : StatedOmega ⇑Φ) : GL ι K)) ε)⁻¹ : GL ι K) : Matrix ι ι K) =
    ((((g : StatedOmega ⇑Φ) : GL ι K)) : Matrix ι ι K) *
      (((c : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) *
      (((((g : StatedOmega ⇑Φ) : GL ι K))⁻¹ : GL ι K) : Matrix ι ι K)
  exact ggJSo1_blk_conj (((g : StatedOmega ⇑Φ) : GL ι K))
    (((c : StatedOmega ⇑Φ) : GL ι K)) ε hε.2.1 hgε hcε hcfix

private lemma ggJSo1_exists_prod {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (G : Matrix ι ι F → Subgroup U)
    (P : Finset (Matrix ι ι F))
    (horth : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0)
    (hfix : ∀ p ∈ P, ∀ x ∈ G p, (j x : Matrix ι ι F) * (1 - p) = 1 - p)
    (hcomm : ∀ p ∈ P, ∀ x ∈ G p, (j x : Matrix ι ι F) * p = p * (j x : Matrix ι ι F))
    (g : ∀ ε : {p // p ∈ P}, G (ε : Matrix ι ι F)) :
    ∃ w : U, w ∈ (⨆ ε : {p // p ∈ P}, G (ε : Matrix ι ι F)) ∧
      ∀ ε : {p // p ∈ P},
        (j w : Matrix ι ι F) * (ε : Matrix ι ι F) =
        (j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F) := by
  classical
  have key : ∀ sT : Finset {p // p ∈ P},
      ∃ w ∈ (⨆ ε ∈ sT, G (ε : Matrix ι ι F)),
        (∀ ε ∈ sT, (j w : Matrix ι ι F) * (ε : Matrix ι ι F) =
          (j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F)) ∧
        (∀ ε : {p // p ∈ P}, ε ∉ sT →
          (j w : Matrix ι ι F) * (ε : Matrix ι ι F) = (ε : Matrix ι ι F)) := by
    intro sT
    induction sT using Finset.induction_on with
    | empty =>
        refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
        · intro ε hε; simp at hε
        · intro ε _; show (j 1 : Matrix ι ι F) * (ε : Matrix ι ι F) = (ε : Matrix ι ι F)
          rw [map_one, Units.val_one, Matrix.one_mul]
    | insert a sT ha ih =>
        obtain ⟨w, hw_mem, hw_in, hw_out⟩ := ih
        have hga_fix : (j (g a) : Matrix ι ι F) * (1 - (a : Matrix ι ι F)) =
            1 - (a : Matrix ι ι F) := hfix a a.2 (g a) (g a).2
        have hga_fix_ne : ∀ ε : Matrix ι ι F, ε ∈ P → ε ≠ (a : Matrix ι ι F) →
            (j (g a) : Matrix ι ι F) * ε = ε := by
          intro ε hεP hne
          have h1 : (1 - (a : Matrix ι ι F)) * ε = ε := by
            rw [Matrix.sub_mul, Matrix.one_mul,
              horth a a.2 ε hεP (fun h => hne h.symm), sub_zero]
          calc (j (g a) : Matrix ι ι F) * ε
              = (j (g a) : Matrix ι ι F) * ((1 - (a : Matrix ι ι F)) * ε) := by rw [h1]
            _ = ((j (g a) : Matrix ι ι F) * (1 - (a : Matrix ι ι F))) * ε := by
                rw [Matrix.mul_assoc]
            _ = (1 - (a : Matrix ι ι F)) * ε := by rw [hga_fix]
            _ = ε := h1
        have hle_a : G (a : Matrix ι ι F) ≤ ⨆ p ∈ insert a sT, G (p : Matrix ι ι F) := by
          apply le_iSup_of_le (f := fun p => ⨆ (_ : p ∈ insert a sT), G (p : Matrix ι ι F)) a
          apply le_iSup_of_le (f := fun _ : a ∈ insert a sT =>
            G (a : Matrix ι ι F)) (Finset.mem_insert_self a sT)
          exact le_rfl
        have hle_T : (⨆ p ∈ sT, G (p : Matrix ι ι F)) ≤
            ⨆ p ∈ insert a sT, G (p : Matrix ι ι F) := by
          apply iSup_le; intro p; apply iSup_le; intro hp
          apply le_iSup_of_le (f := fun q =>
            ⨆ (_ : q ∈ insert a sT), G (q : Matrix ι ι F)) p
          apply le_iSup_of_le (f := fun _ : p ∈ insert a sT => G (p : Matrix ι ι F))
            (Finset.mem_insert_of_mem hp)
          exact le_rfl
        refine ⟨(g a) * w, ?_, ?_, ?_⟩
        · exact (⨆ p ∈ insert a sT, G (p : Matrix ι ι F)).mul_mem (hle_a (g a).2) (hle_T hw_mem)
        · intro ε hε
          rw [Finset.mem_insert] at hε
          rcases hε with hεa | hε
          · rw [hεa]
            have hw_a : (j w : Matrix ι ι F) * (a : Matrix ι ι F) = (a : Matrix ι ι F) :=
              hw_out a ha
            rw [map_mul, Units.val_mul, Matrix.mul_assoc, hw_a]
          · have hw_e := hw_in ε hε
            have hcomm_e : (j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F) =
                (ε : Matrix ι ι F) * (j (g ε) : Matrix ι ι F) := hcomm ε ε.2 (g ε) (g ε).2
            have hga_e : (j (g a) : Matrix ι ι F) * (ε : Matrix ι ι F) = (ε : Matrix ι ι F) :=
              hga_fix_ne (ε : Matrix ι ι F) ε.2 (fun hmat => ha (by
                have hsub : ε = a := Subtype.ext hmat
                exact hsub ▸ hε))
            calc (j ((g a) * w) : Matrix ι ι F) * (ε : Matrix ι ι F)
                = (j (g a) : Matrix ι ι F) *
                    ((j w : Matrix ι ι F) * (ε : Matrix ι ι F)) := by
                  rw [map_mul, Units.val_mul, Matrix.mul_assoc]
              _ = (j (g a) : Matrix ι ι F) *
                    ((j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F)) := by rw [hw_e]
              _ = (j (g a) : Matrix ι ι F) *
                    ((ε : Matrix ι ι F) * (j (g ε) : Matrix ι ι F)) := by rw [hcomm_e]
              _ = ((j (g a) : Matrix ι ι F) * (ε : Matrix ι ι F)) *
                    (j (g ε) : Matrix ι ι F) := by rw [Matrix.mul_assoc]
              _ = (ε : Matrix ι ι F) * (j (g ε) : Matrix ι ι F) := by rw [hga_e]
              _ = (j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F) := hcomm_e.symm
        · intro ε hε
          have hne : (ε : Matrix ι ι F) ≠ (a : Matrix ι ι F) := fun hmat =>
            hε ((Subtype.ext hmat).symm ▸ Finset.mem_insert_self a sT)
          have hw_e := hw_out ε (fun hmem => hε (Finset.mem_insert_of_mem hmem))
          rw [map_mul, Units.val_mul, Matrix.mul_assoc, hw_e, hga_fix_ne (ε : Matrix ι ι F) ε.2 hne]
  obtain ⟨w, hw_mem, hw_in, _⟩ := key Finset.univ
  exact ⟨w, by simpa using hw_mem, fun ε => hw_in ε (Finset.mem_univ ε)⟩

private lemma ggJSo1_eq_of_blocks {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (hj : Function.Injective j)
    (P : Finset (Matrix ι ι F)) (hPsum : ∑ p ∈ P, p = 1)
    {x y : U}
    (h : ∀ ε : {p // p ∈ P}, (j x : Matrix ι ι F) * (ε : Matrix ι ι F) =
        (j y : Matrix ι ι F) * (ε : Matrix ι ι F)) :
    x = y := by
  apply hj
  apply Units.ext
  have hsum1 : (∑ ε : {p : Matrix ι ι F // p ∈ P}, (ε : Matrix ι ι F)) = 1 := by
    rw [Finset.sum_coe_sort P (fun i : Matrix ι ι F => i), hPsum]
  calc (j x : Matrix ι ι F)
      = (j x : Matrix ι ι F) * 1 := (Matrix.mul_one _).symm
    _ = (j x : Matrix ι ι F) * (∑ ε : {p : Matrix ι ι F // p ∈ P}, (ε : Matrix ι ι F)) := by
        rw [hsum1]
    _ = ∑ ε : {p : Matrix ι ι F // p ∈ P}, (j x : Matrix ι ι F) * (ε : Matrix ι ι F) := by
        rw [Finset.mul_sum]
    _ = ∑ ε : {p : Matrix ι ι F // p ∈ P}, (j y : Matrix ι ι F) * (ε : Matrix ι ι F) :=
        Finset.sum_congr rfl (fun ε _ => h ε)
    _ = (j y : Matrix ι ι F) * (∑ ε : {p : Matrix ι ι F // p ∈ P}, (ε : Matrix ι ι F)) := by
        rw [Finset.mul_sum]
    _ = (j y : Matrix ι ι F) * 1 := by rw [hsum1]
    _ = (j y : Matrix ι ι F) := Matrix.mul_one _

private lemma ggJSo1_eq_of_blk {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (hj : Function.Injective j)
    {G : Matrix ι ι F → Subgroup U} {ε : Matrix ι ι F} {x y : G ε}
    (hfixx : (j x : Matrix ι ι F) * (1 - ε) = 1 - ε)
    (hfixy : (j y : Matrix ι ι F) * (1 - ε) = 1 - ε)
    (h : (j x : Matrix ι ι F) * ε = (j y : Matrix ι ι F) * ε) :
    x = y := by
  apply Subtype.ext
  apply hj
  apply Units.ext
  calc (j x : Matrix ι ι F)
      = (j x : Matrix ι ι F) * ε + (j x : Matrix ι ι F) * (1 - ε) := by
        rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
    _ = (j x : Matrix ι ι F) * ε + (1 - ε) := by rw [hfixx]
    _ = (j y : Matrix ι ι F) * ε + (1 - ε) := by rw [h]
    _ = (j y : Matrix ι ι F) * ε + (j y : Matrix ι ι F) * (1 - ε) := by rw [hfixy]
    _ = (j y : Matrix ι ι F) := by rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]

private lemma ggJSo1_card_eq_prod {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (hj : Function.Injective j) (G : Matrix ι ι F → Subgroup U)
    (P : Finset (Matrix ι ι F)) (hPsum : ∑ p ∈ P, p = 1)
    (horth : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0)
    (hfix : ∀ p ∈ P, ∀ x ∈ G p, (j x : Matrix ι ι F) * (1 - p) = 1 - p)
    (hcomm : ∀ p ∈ P, ∀ x ∈ G p, (j x : Matrix ι ι F) * p = p * (j x : Matrix ι ι F))
    (C : Subgroup U) (hGleC : ∀ p, G p ≤ C)
    (toBlock : ↥C → ∀ ε : {p // p ∈ P}, G (ε : Matrix ι ι F))
    (htoBlock : ∀ u : ↥C, ∀ ε : {p // p ∈ P},
      (j (toBlock u ε) : Matrix ι ι F) * (ε : Matrix ι ι F) =
      (j (u : U) : Matrix ι ι F) * (ε : Matrix ι ι F)) :
    Nat.card ↥C = ∏ p ∈ P, Nat.card ↥(G p) := by
  classical
  let Ψ : (∀ ε : {p // p ∈ P}, G (ε : Matrix ι ι F)) → ↥C := fun g =>
    ⟨Classical.choose (ggJSo1_exists_prod j G P horth hfix hcomm g),
      (iSup_le (fun ε : {p // p ∈ P} => hGleC (ε : Matrix ι ι F)))
        (Classical.choose_spec (ggJSo1_exists_prod j G P horth hfix hcomm g)).1⟩
  have hsurj : Function.Surjective Ψ := by
    intro u
    refine ⟨toBlock u, ?_⟩
    apply Subtype.ext
    apply ggJSo1_eq_of_blocks j hj P hPsum
    intro ε
    rw [(Classical.choose_spec
      (ggJSo1_exists_prod j G P horth hfix hcomm (toBlock u))).2 ε]
    exact htoBlock u ε
  have hinj : Function.Injective Ψ := by
    intro g h hgh
    funext ε
    apply ggJSo1_eq_of_blk j hj
      (hfix (ε : Matrix ι ι F) ε.2 (g ε) (g ε).2)
      (hfix (ε : Matrix ι ι F) ε.2 (h ε) (h ε).2)
    have hb : (j ((Ψ g : ↥C) : U) : Matrix ι ι F) * (ε : Matrix ι ι F) =
        (j ((Ψ h : ↥C) : U) : Matrix ι ι F) * (ε : Matrix ι ι F) := by rw [hgh]
    rw [(Classical.choose_spec (ggJSo1_exists_prod j G P horth hfix hcomm g)).2 ε,
      (Classical.choose_spec (ggJSo1_exists_prod j G P horth hfix hcomm h)).2 ε] at hb
    exact hb
  calc Nat.card ↥C = Nat.card (∀ ε : {p // p ∈ P}, G (ε : Matrix ι ι F)) :=
        (Nat.card_congr (Equiv.ofBijective Ψ ⟨hinj, hsurj⟩)).symm
    _ = ∏ ε : {p // p ∈ P}, Nat.card ↥(G (ε : Matrix ι ι F)) := Nat.card_pi
    _ = ∏ p ∈ P, Nat.card ↥(G p) :=
        Finset.prod_coe_sort P (fun p : Matrix ι ι F => Nat.card ↥(G p))

theorem centralizer_block_decomp_Omega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    ∃ P : Finset (Matrix ι ι K),
      (∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
        (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε) ∧
      (∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0) ∧ ∑ ε ∈ P, ε = 1 ∧
      (∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' →
        ∀ x ∈ glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε,
        ∀ y ∈ glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε', Commute x y) ∧
      (⨆ ε ∈ P, glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) =
        (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype ∧
      Nat.card ↥((Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype) =
        ∏ ε ∈ P, Nat.card ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) := by
  classical
  let G : Matrix ι ι K := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  let star : Matrix ι ι K → Matrix ι ι K := formAdj (RingHom.id K) G
  let GG : Matrix ι ι K → Subgroup ↥(StatedOmega ⇑Φ) :=
    fun ε => glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε
  let C : Subgroup ↥(StatedOmega ⇑Φ) :=
    (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype
  have hGdet : IsUnit G.det := by simpa [G] using ggOmegaBlk_G_isUnit_det Φ hΦ
  have hS : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hAcomm : ∀ a ∈ A, ∀ b' ∈ A, a * b' = b' * a :=
    ggJSo1_adjoin_comm ({b} : Set (GL ι K)) hS
  have hone : star 1 = 1 := by
    simpa [star] using Geo.formAdj_one (RingHom.id K) hGdet
  have hadd : ∀ a ∈ A, ∀ b' ∈ A, star (a + b') = star a + star b' := by
    intro a _ b' _; exact Geo.formAdj_add (RingHom.id K) G a b'
  obtain ⟨P, hPprim, hPorth, hPsum⟩ :=
    Block.exists_finset_isPrimStarIdemIn_sum_eq star A hAcomm hadd
      (Subalgebra.one_mem A) IsIdempotentElem.one hone
  have hpA : ∀ p ∈ P, p ∈ A := fun p hp => (hPprim p hp).1.1
  have hpid : ∀ p ∈ P, IsIdempotentElem p := fun p hp => (hPprim p hp).1.2.1
  have hpstar : ∀ p ∈ P, star p = p := fun p hp => (hPprim p hp).1.2.2.2.1
  have hεprim : ∀ ε : Matrix ι ι K, ε ∈ P →
      IsPrimAdjIdemIn (RingHom.id K) G A ε :=
    fun ε hε => (Block.isPrimStarIdemIn_formAdj_iff (RingHom.id K) G A ε).mp
      (hPprim ε hε).1
  let toBlock : ↥C → (∀ ε : {p : Matrix ι ι K // p ∈ P}, GG (ε : Matrix ι ι K)) :=
    fun u ε =>
      omegaBlockHom Φ hΦ h8 b hb hodd (ε : Matrix ι ι K)
        (hεprim (ε : Matrix ι ι K) ε.2) u
  have htoBlock : ∀ (u : ↥C) (ε : {p : Matrix ι ι K // p ∈ P}),
      (((StatedOmega ⇑Φ).subtype (toBlock u ε)) : Matrix ι ι K) *
        (ε : Matrix ι ι K) =
      (((StatedOmega ⇑Φ).subtype (u : ↥(StatedOmega ⇑Φ))) : Matrix ι ι K) *
        (ε : Matrix ι ι K) := by
    intro u ε
    rw [show toBlock u ε = omegaBlockHom Φ hΦ h8 b hb hodd (ε : Matrix ι ι K)
        (hεprim (ε : Matrix ι ι K) ε.2) u from rfl]
    change ((((omegaBlockHom Φ hΦ h8 b hb hodd (ε : Matrix ι ι K)
        (hεprim (ε : Matrix ι ι K) ε.2) u :
        glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) :
        StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * (ε : Matrix ι ι K) =
      ((((u : C) : StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * (ε : Matrix ι ι K)
    rw [omegaBlockHom_val Φ hΦ h8 b hb hodd (ε : Matrix ι ι K)
      (hεprim (ε : Matrix ι ι K) ε.2) u]
    noncomm_ring [(hpid (ε : Matrix ι ι K) ε.2).eq]
  have hGleC : ∀ ε : Matrix ι ι K, GG ε ≤ C := fun ε => Subgroup.comap_mono inf_le_left
  refine ⟨P, ?_, ?_, hPsum, ?_, ?_, ?_⟩
  · intro ε hε
    exact (Block.isPrimStarIdemIn_formAdj_iff (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) A ε).mp
      (by simpa [star, G] using (hPprim ε hε).1)
  · intro ε hε ε' hε' hne
    exact hPorth ε hε ε' hε' hne
  · intro ε hε ε' hε' hne x hx y hy
    have hx_inf : (x : GL ι K) ∈
        Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ glFixing (1 - ε) :=
      Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)
    have hy_inf : (y : GL ι K) ∈
        Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ glFixing (1 - ε') :=
      Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hy)
    have hMA : ∀ a ∈ A, (x : GL ι K) * a = a * (x : GL ι K) :=
      ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K))
        x (Subgroup.mem_comap.mpr hx_inf.1)
    have hNA : ∀ a ∈ A, (y : GL ι K) * a = a * (y : GL ι K) :=
      ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K))
        y (Subgroup.mem_comap.mpr hy_inf.1)
    have key : ((x : GL ι K) : Matrix ι ι K) * ((y : GL ι K) : Matrix ι ι K) =
        ((y : GL ι K) : Matrix ι ι K) * ((x : GL ι K) : Matrix ι ι K) :=
      ggJSo1_blk_commute_matrices A P hPsum hPorth hpA hε hε' hne hMA hNA
        hx_inf.2 hy_inf.2
    change x * y = y * x
    apply Subtype.ext
    apply Units.ext
    exact key
  · show (⨆ ε ∈ P, GG ε) = C
    apply le_antisymm
    · apply iSup_le; intro ε; apply iSup_le; intro hε; intro x hx
      exact Subgroup.mem_comap.mpr (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1
    · intro u hu
      obtain ⟨w, hw_mem, hw_prop⟩ :=
        ggJSo1_exists_prod (StatedOmega ⇑Φ).subtype GG P hPorth
          (fun p hp x hx => (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2)
          (fun p hp x hx => ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype
            ({b} : Set (GL ι K)) x
            (Subgroup.mem_comap.mpr (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1)
            p (hpA p hp))
          (toBlock ⟨u, hu⟩)
      have hw_mem' : w ∈ (⨆ ε ∈ P, GG ε) := by
        simpa only [iSup_subtype] using hw_mem
      have hw_eq : w = u :=
        ggJSo1_eq_of_blocks (StatedOmega ⇑Φ).subtype (Subgroup.subtype_injective _) P hPsum
          (fun ε => by rw [hw_prop ε, htoBlock ⟨u, hu⟩ ε])
      rw [← hw_eq]; exact hw_mem'
  · show Nat.card ↥C = ∏ p ∈ P, Nat.card ↥(GG p)
    exact ggJSo1_card_eq_prod (StatedOmega ⇑Φ).subtype (Subgroup.subtype_injective _) GG P hPsum
      hPorth
      (fun p hp x hx => (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2)
      (fun p hp x hx => ggJSo1_mem_adjoin_commute (StatedOmega ⇑Φ).subtype
        ({b} : Set (GL ι K)) x
        (Subgroup.mem_comap.mpr (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1)
        p (hpA p hp))
      C hGleC toBlock htoBlock

theorem omegaStatedOmega_map_mem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (σ : K ≃+* K)
    (hΦσ : ∀ v : ι → K, Φ (fun i => σ (v i)) = σ (Φ v))
    {g : GL ι K} (hg : g ∈ StatedOmega ⇑Φ) :
    Matrix.GeneralLinearGroup.map σ.toRingHom g ∈ StatedOmega ⇑Φ := by
  let f : GL ι K →* GL ι K := Matrix.GeneralLinearGroup.map σ.toRingHom
  have hmul : ∀ (y : GL ι K) (v : ι → K),
      (((f y : GL ι K) : Matrix ι ι K) *ᵥ v) =
        (fun i => σ (((y : Matrix ι ι K) *ᵥ fun j => σ.symm (v j)) i)) := by
    intro y v
    ext i
    rw [show (((f y : GL ι K) : Matrix ι ι K)) = (((y : GL ι K) : Matrix ι ι K)).map ⇑σ from
      Matrix.GeneralLinearGroup.val_map_apply σ.toRingHom y]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
      σ.apply_symm_apply]
  have hgen : ∀ y : GL ι K, (∀ v, Φ (((y : Matrix ι ι K) *ᵥ v)) = Φ v) →
      ∀ v, Φ (((f y : GL ι K) : Matrix ι ι K) *ᵥ v) = Φ v := by
    intro y hy v
    rw [hmul]
    calc Φ (fun i => σ (((y : Matrix ι ι K) *ᵥ fun j => σ.symm (v j)) i))
        = σ (Φ (((y : Matrix ι ι K) *ᵥ fun j => σ.symm (v j)))) := hΦσ _
      _ = σ (Φ (fun j => σ.symm (v j))) := by rw [hy]
      _ = Φ v := by
          have h := hΦσ (fun j => σ.symm (v j))
          simpa using h.symm
  have hIle : (CFSG.MatrixModel.isometryCore ⇑Φ).map f ≤
      CFSG.MatrixModel.isometryCore ⇑Φ := by
    rw [CFSG.MatrixModel.isometryCore, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.subset_closure (hgen y hy)
  have hmain : f g ∈ ⁅CFSG.MatrixModel.isometryCore ⇑Φ,
      CFSG.MatrixModel.isometryCore ⇑Φ⁆ := by
    have h1 : f g ∈ (⁅CFSG.MatrixModel.isometryCore ⇑Φ,
        CFSG.MatrixModel.isometryCore ⇑Φ⁆).map f := Subgroup.mem_map_of_mem f hg
    have h2 : (⁅CFSG.MatrixModel.isometryCore ⇑Φ,
        CFSG.MatrixModel.isometryCore ⇑Φ⁆).map f =
        ⁅(CFSG.MatrixModel.isometryCore ⇑Φ).map f,
          (CFSG.MatrixModel.isometryCore ⇑Φ).map f⁆ := Subgroup.map_commutator _ _ f
    have h3 : ⁅(CFSG.MatrixModel.isometryCore ⇑Φ).map f,
        (CFSG.MatrixModel.isometryCore ⇑Φ).map f⁆ ≤
        ⁅CFSG.MatrixModel.isometryCore ⇑Φ, CFSG.MatrixModel.isometryCore ⇑Φ⁆ :=
      Subgroup.commutator_mono hIle hIle
    exact h3 (h2 ▸ h1)
  exact hmain

@[expose] noncomputable def omegaStatedOmegaMap {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (σ : K ≃+* K)
    (hΦσ : ∀ v : ι → K, Φ (fun i => σ (v i)) = σ (Φ v)) :
    StatedOmega ⇑Φ →* StatedOmega ⇑Φ :=
  MonoidHom.codRestrict
    ((Matrix.GeneralLinearGroup.map σ.toRingHom).comp (StatedOmega ⇑Φ).subtype)
    (StatedOmega ⇑Φ)
    (fun x => omegaStatedOmega_map_mem Φ σ hΦσ x.2)

@[simp] lemma omegaStatedOmegaMap_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (σ : K ≃+* K)
    (hΦσ : ∀ v : ι → K, Φ (fun i => σ (v i)) = σ (Φ v))
    (x : StatedOmega ⇑Φ) :
    ((omegaStatedOmegaMap Φ σ hΦσ x : StatedOmega ⇑Φ) : GL ι K) =
      Matrix.GeneralLinearGroup.map σ.toRingHom (x : GL ι K) := rfl

@[expose] noncomputable def omegaCentralizerMap {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (σ : K ≃+* K)
    (hΦσ : ∀ v : ι → K, Φ (fun i => σ (v i)) = σ (Φ v)) (b : GL ι K) :
    (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype →*
      (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.map σ.toRingHom b} : Set (GL ι K))).comap
        (StatedOmega ⇑Φ).subtype :=
  MonoidHom.codRestrict
    ((omegaStatedOmegaMap Φ σ hΦσ).comp
      (Subgroup.subtype
        ((Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype)))
    ((Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.map σ.toRingHom b} : Set (GL ι K))).comap
      (StatedOmega ⇑Φ).subtype)
    (fun x => by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      change (((omegaStatedOmegaMap Φ σ hΦσ x : StatedOmega ⇑Φ) : GL ι K)) *
          Matrix.GeneralLinearGroup.map σ.toRingHom b =
        Matrix.GeneralLinearGroup.map σ.toRingHom b *
          (((omegaStatedOmegaMap Φ σ hΦσ x : StatedOmega ⇑Φ) : GL ι K))
      rw [omegaStatedOmegaMap_apply, ← map_mul, ← map_mul]
      exact congrArg (Matrix.GeneralLinearGroup.map σ.toRingHom)
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp x.2)))

@[simp] lemma omegaCentralizerMap_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (σ : K ≃+* K)
    (hΦσ : ∀ v : ι → K, Φ (fun i => σ (v i)) = σ (Φ v)) (b : GL ι K)
    (x : (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype) :
    (((omegaCentralizerMap Φ σ hΦσ b x :
        (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map σ.toRingHom b} : Set (GL ι K))).comap
          (StatedOmega ⇑Φ).subtype) : StatedOmega ⇑Φ) : GL ι K) =
      Matrix.GeneralLinearGroup.map σ.toRingHom ((x : StatedOmega ⇑Φ) : GL ι K) := rfl

@[expose] noncomputable def omegaBlockMap {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (σ : K ≃+* K)
    (hΦσ : ∀ v : ι → K, Φ (fun i => σ (v i)) = σ (Φ v))
    (b : GL ι K) (ε : Matrix ι ι K) :
    glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε →*
      glBlockCentralizer (StatedOmega ⇑Φ).subtype
        ({Matrix.GeneralLinearGroup.map σ.toRingHom b} : Set (GL ι K)) (ε.map σ) :=
  MonoidHom.codRestrict
    ((omegaStatedOmegaMap Φ σ hΦσ).comp
      (Subgroup.subtype
        (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)))
    (glBlockCentralizer (StatedOmega ⇑Φ).subtype
      ({Matrix.GeneralLinearGroup.map σ.toRingHom b} : Set (GL ι K)) (ε.map σ))
    (fun x => by
      rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
      constructor
      · rw [Subgroup.mem_centralizer_singleton_iff]
        change (((omegaStatedOmegaMap Φ σ hΦσ x : StatedOmega ⇑Φ) : GL ι K)) *
            Matrix.GeneralLinearGroup.map σ.toRingHom b =
          Matrix.GeneralLinearGroup.map σ.toRingHom b *
            (((omegaStatedOmegaMap Φ σ hΦσ x : StatedOmega ⇑Φ) : GL ι K))
        rw [omegaStatedOmegaMap_apply, ← map_mul, ← map_mul]
        exact congrArg (Matrix.GeneralLinearGroup.map σ.toRingHom)
          (Subgroup.mem_centralizer_singleton_iff.mp
            (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp x.2)).1)
      · change ((((omegaStatedOmegaMap Φ σ hΦσ x : StatedOmega ⇑Φ) : GL ι K) :
            Matrix ι ι K) * (1 - ε.map σ) = 1 - ε.map σ)
        rw [omegaStatedOmegaMap_apply, Matrix.GeneralLinearGroup.val_map_apply]
        have hx := (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp x.2)).2
        have h := congrArg (fun M : Matrix ι ι K => M.map ⇑σ) hx
        simpa [Matrix.map_mul, Matrix.map_sub (⇑σ) (fun a b => map_sub σ a b),
          Matrix.map_one (⇑σ) (map_zero σ) (map_one σ)] using h)

@[simp] lemma omegaBlockMap_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (σ : K ≃+* K)
    (hΦσ : ∀ v : ι → K, Φ (fun i => σ (v i)) = σ (Φ v))
    (b : GL ι K) (ε : Matrix ι ι K)
    (x : glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) :
    (((omegaBlockMap Φ σ hΦσ b ε x :
        glBlockCentralizer (StatedOmega ⇑Φ).subtype
          ({Matrix.GeneralLinearGroup.map σ.toRingHom b} : Set (GL ι K)) (ε.map σ)) :
        StatedOmega ⇑Φ) : GL ι K) =
      Matrix.GeneralLinearGroup.map σ.toRingHom ((x : StatedOmega ⇑Φ) : GL ι K) := rfl

abbrev omegaCentralizerSubgroup {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (b : GL ι K) : Subgroup (StatedOmega ⇑Φ) :=
  (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype

abbrev omegaBlockSubgroup {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (b : GL ι K) (ε : Matrix ι ι K) :
    Subgroup (StatedOmega ⇑Φ) :=
  glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε

@[expose] noncomputable def omegaSemilinConjGL {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (S : (ι → K) ≃+ (ι → K)) (σ : K ≃+* K)
    (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v) :
    GL ι K →* GL ι K :=
  (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.toMonoidHom.comp
    ((CFSG.RankThree.PartOne.KCOrthogonal.semilinConj S σ hS).comp
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom)

theorem omegaSemilinConjGL_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (S : (ι → K) ≃+ (ι → K)) (σ : K ≃+* K)
    (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v) (g : GL ι K) (v : ι → K) :
    ((omegaSemilinConjGL S σ hS g : GL ι K) : Matrix ι ι K) *ᵥ v =
      S (((g : GL ι K) : Matrix ι ι K) *ᵥ S.symm v) := by
  simp only [omegaSemilinConjGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, MulEquiv.apply_symm_apply,
    CFSG.RankThree.PartOne.KCOrthogonal.semilinConj_apply,
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]

theorem omegaSemilinConjGL_mem_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K)) (S : (ι → K) ≃+ (ι → K)) (σ : K ≃+* K)
    (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v) (μ : K)
    (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v))
    {g : GL ι K} (hg : g ∈ StatedOmega ⇑Φ) :
    omegaSemilinConjGL S σ hS g ∈ StatedOmega ⇑Φ := by
  have hg' : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K g ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ, TauCeti.QuadraticMap.orthogonalGroup Φ⁆ := by
    have hg'' := hg
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl] at hg''
    exact Subgroup.mem_comap.mp hg''
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl,
    Subgroup.mem_comap]
  change (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K)
    (omegaSemilinConjGL S σ hS g) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ, TauCeti.QuadraticMap.orthogonalGroup Φ⁆
  rw [show (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K)
      (omegaSemilinConjGL S σ hS g) =
      CFSG.RankThree.PartOne.KCOrthogonal.semilinConj S σ hS
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K g) by
    simp [omegaSemilinConjGL]]
  exact CFSG.RankThree.PartOne.KCOrthogonal.semilinConj_mem_orthDerived S σ hS μ hSΦ hg'

theorem omegaSemilinConjGL_commute_of_commute {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (S : (ι → K) ≃+ (ι → K)) (σ : K ≃+* K)
    (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v) (b g : GL ι K)
    (hSb : ∀ v : ι → K, S (((b : GL ι K) : Matrix ι ι K) *ᵥ v) =
      ((b : GL ι K) : Matrix ι ι K) *ᵥ S v)
    (hg : g * b = b * g) :
    omegaSemilinConjGL S σ hS g * b = b * omegaSemilinConjGL S σ hS g := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    omegaSemilinConjGL_apply]
  have hb : S.symm (((b : GL ι K) : Matrix ι ι K) *ᵥ Pi.single i 1) =
      ((b : GL ι K) : Matrix ι ι K) *ᵥ S.symm (Pi.single i 1) := by
    apply S.injective
    rw [S.apply_symm_apply, hSb, S.apply_symm_apply]
  have hm : ((g : GL ι K) : Matrix ι ι K) * ((b : GL ι K) : Matrix ι ι K) =
      ((b : GL ι K) : Matrix ι ι K) * ((g : GL ι K) : Matrix ι ι K) := by
    simpa using congrArg (fun e : GL ι K => (e : Matrix ι ι K)) hg
  have hgv : ((g : GL ι K) : Matrix ι ι K) *ᵥ
        (((b : GL ι K) : Matrix ι ι K) *ᵥ S.symm (Pi.single i 1)) =
      ((b : GL ι K) : Matrix ι ι K) *ᵥ
        (((g : GL ι K) : Matrix ι ι K) *ᵥ S.symm (Pi.single i 1)) := by
    calc
      ((g : GL ι K) : Matrix ι ι K) *ᵥ
          (((b : GL ι K) : Matrix ι ι K) *ᵥ S.symm (Pi.single i 1)) =
        (((g : GL ι K) : Matrix ι ι K) * ((b : GL ι K) : Matrix ι ι K)) *ᵥ
          S.symm (Pi.single i 1) := Matrix.mulVec_mulVec (S.symm (Pi.single i 1))
            ((g : GL ι K) : Matrix ι ι K) ((b : GL ι K) : Matrix ι ι K)
      _ = (((b : GL ι K) : Matrix ι ι K) * ((g : GL ι K) : Matrix ι ι K)) *ᵥ
          S.symm (Pi.single i 1) := by rw [hm]
      _ = ((b : GL ι K) : Matrix ι ι K) *ᵥ
          (((g : GL ι K) : Matrix ι ι K) *ᵥ S.symm (Pi.single i 1)) :=
        (Matrix.mulVec_mulVec (S.symm (Pi.single i 1))
          ((b : GL ι K) : Matrix ι ι K) ((g : GL ι K) : Matrix ι ι K)).symm
  rw [hb, hgv]
  rw [omegaSemilinConjGL_apply]
  exact hSb (((g : GL ι K) : Matrix ι ι K) *ᵥ S.symm (Pi.single i 1))

theorem omegaSemilin_one_sub {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (S : (ι → K) ≃+ (ι → K)) (ε : Matrix ι ι K)
    (hSε : ∀ v : ι → K, S (ε *ᵥ v) = ε *ᵥ S v) (v : ι → K) :
    S ((1 - ε) *ᵥ v) = (1 - ε) *ᵥ S v := by
  have hone : (1 : Matrix ι ι K) *ᵥ v = v := Matrix.one_mulVec v
  have hone' : (1 : Matrix ι ι K) *ᵥ S v = S v := Matrix.one_mulVec (S v)
  rw [Matrix.sub_mulVec, hone, map_sub S, hSε, Matrix.sub_mulVec, hone']

theorem omegaSemilin_symm_one_sub {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (S : (ι → K) ≃+ (ι → K)) (ε : Matrix ι ι K)
    (hSε : ∀ v : ι → K, S (ε *ᵥ v) = ε *ᵥ S v) (v : ι → K) :
    S.symm ((1 - ε) *ᵥ v) = (1 - ε) *ᵥ S.symm v := by
  apply S.injective
  rw [S.apply_symm_apply, omegaSemilin_one_sub S ε hSε, S.apply_symm_apply]

theorem omegaSemilinConjGL_fixes_one_sub {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (S : (ι → K) ≃+ (ι → K)) (σ : K ≃+* K)
    (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v) (ε : Matrix ι ι K)
    (hSε : ∀ v : ι → K, S (ε *ᵥ v) = ε *ᵥ S v) {g : GL ι K}
    (hg : ((g : GL ι K) : Matrix ι ι K) * (1 - ε) = 1 - ε) :
    ((omegaSemilinConjGL S σ hS g : GL ι K) : Matrix ι ι K) * (1 - ε) = 1 - ε := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, omegaSemilinConjGL_apply,
    omegaSemilin_symm_one_sub S ε hSε, Matrix.mulVec_mulVec, hg,
    omegaSemilin_one_sub S ε hSε, S.apply_symm_apply]

@[expose] noncomputable def omegaSemilinStatedOmegaMap {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Φ : QuadraticForm K (ι → K)) (S : (ι → K) ≃+ (ι → K))
    (σ : K ≃+* K) (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v)
    (μ : K) (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v)) :
    StatedOmega ⇑Φ →* StatedOmega ⇑Φ :=
  MonoidHom.codRestrict
    ((omegaSemilinConjGL S σ hS).comp (StatedOmega ⇑Φ).subtype)
    (StatedOmega ⇑Φ)
    (fun x => omegaSemilinConjGL_mem_statedOmega Φ S σ hS μ hSΦ x.2)

@[simp] theorem omegaSemilinStatedOmegaMap_apply {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Φ : QuadraticForm K (ι → K)) (S : (ι → K) ≃+ (ι → K))
    (σ : K ≃+* K) (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v)
    (μ : K) (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v))
    (x : StatedOmega ⇑Φ) :
    ((omegaSemilinStatedOmegaMap Φ S σ hS μ hSΦ x : StatedOmega ⇑Φ) : GL ι K) =
      omegaSemilinConjGL S σ hS (x : GL ι K) := rfl

theorem omegaSemilinConjGL_injective {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (S : (ι → K) ≃+ (ι → K)) (σ : K ≃+* K)
    (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v) :
    Function.Injective (omegaSemilinConjGL S σ hS) := by
  intro g h hgh
  apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective
  exact CFSG.RankThree.PartOne.KCOrthogonal.semilinConj_injective S σ hS
    (by simpa [omegaSemilinConjGL] using
      congrArg (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) hgh)

theorem omegaSemilinStatedOmegaMap_injective {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K)) (S : (ι → K) ≃+ (ι → K)) (σ : K ≃+* K)
    (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v) (μ : K)
    (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v)) :
    Function.Injective (omegaSemilinStatedOmegaMap Φ S σ hS μ hSΦ) := by
  intro x y hxy
  apply Subtype.ext
  apply omegaSemilinConjGL_injective S σ hS
  simpa [omegaSemilinStatedOmegaMap_apply] using
    congrArg (fun z : StatedOmega ⇑Φ => ((z : StatedOmega ⇑Φ) : GL ι K)) hxy

@[expose] noncomputable def omegaSemilinStatedOmegaAut {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] [Fintype K] (Φ : QuadraticForm K (ι → K))
    (S : (ι → K) ≃+ (ι → K)) (σ : K ≃+* K)
    (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v) (μ : K)
    (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v)) :
    MulAut (StatedOmega ⇑Φ) :=
  MulEquiv.ofBijective (omegaSemilinStatedOmegaMap Φ S σ hS μ hSΦ)
    ⟨omegaSemilinStatedOmegaMap_injective Φ S σ hS μ hSΦ,
      by
        haveI : Finite (Matrix ι ι K) := Finite.of_fintype _
        haveI : Finite (GL ι K) :=
          Finite.of_injective (fun g : GL ι K => (g : Matrix ι ι K))
            (fun g h hgh => Units.ext hgh)
        haveI : Finite ↥(StatedOmega ⇑Φ) :=
          Finite.of_injective (fun x : StatedOmega ⇑Φ => (x : GL ι K))
            Subtype.coe_injective
        exact Finite.surjective_of_injective
          (omegaSemilinStatedOmegaMap_injective Φ S σ hS μ hSΦ)⟩

@[simp] theorem omegaSemilinStatedOmegaAut_apply {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] (Φ : QuadraticForm K (ι → K)) (S : (ι → K) ≃+ (ι → K))
    (σ : K ≃+* K) (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v)
    (μ : K) (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v)) (g : StatedOmega ⇑Φ) :
    ((omegaSemilinStatedOmegaAut Φ S σ hS μ hSΦ g : StatedOmega ⇑Φ) : GL ι K) =
      omegaSemilinConjGL S σ hS (g : GL ι K) := rfl

@[expose] noncomputable def omegaSemilinCentralizerMap {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Φ : QuadraticForm K (ι → K)) (S : (ι → K) ≃+ (ι → K))
    (σ : K ≃+* K) (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v)
    (μ : K) (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v)) (b : GL ι K)
    (hSb : ∀ v : ι → K, S (((b : GL ι K) : Matrix ι ι K) *ᵥ v) =
      ((b : GL ι K) : Matrix ι ι K) *ᵥ S v) :
    omegaCentralizerSubgroup Φ b →* omegaCentralizerSubgroup Φ b :=
  MonoidHom.codRestrict
    ((omegaSemilinStatedOmegaMap Φ S σ hS μ hSΦ).comp
      (Subgroup.subtype (omegaCentralizerSubgroup Φ b)))
    (omegaCentralizerSubgroup Φ b)
    (fun x => by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype,
        omegaSemilinStatedOmegaMap_apply]
      exact omegaSemilinConjGL_commute_of_commute S σ hS b
        (((x : omegaCentralizerSubgroup Φ b) : StatedOmega ⇑Φ) : GL ι K) hSb
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp x.2)))

@[simp] theorem omegaSemilinCentralizerMap_apply {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Φ : QuadraticForm K (ι → K)) (S : (ι → K) ≃+ (ι → K))
    (σ : K ≃+* K) (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v)
    (μ : K) (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v)) (b : GL ι K)
    (hSb : ∀ v : ι → K, S (((b : GL ι K) : Matrix ι ι K) *ᵥ v) =
      ((b : GL ι K) : Matrix ι ι K) *ᵥ S v) (x : omegaCentralizerSubgroup Φ b) :
    (((omegaSemilinCentralizerMap Φ S σ hS μ hSΦ b hSb x : omegaCentralizerSubgroup Φ b) :
        StatedOmega ⇑Φ) : GL ι K) =
      omegaSemilinConjGL S σ hS (((x : omegaCentralizerSubgroup Φ b) : StatedOmega ⇑Φ) : GL ι K) := rfl

@[expose] noncomputable def omegaSemilinBlockMap {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Φ : QuadraticForm K (ι → K)) (S : (ι → K) ≃+ (ι → K))
    (σ : K ≃+* K) (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v)
    (μ : K) (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v)) (b : GL ι K) (ε : Matrix ι ι K)
    (hSb : ∀ v : ι → K, S (((b : GL ι K) : Matrix ι ι K) *ᵥ v) =
      ((b : GL ι K) : Matrix ι ι K) *ᵥ S v)
    (hSε : ∀ v : ι → K, S (ε *ᵥ v) = ε *ᵥ S v) :
    omegaBlockSubgroup Φ b ε →* omegaBlockSubgroup Φ b ε :=
  MonoidHom.codRestrict
    ((omegaSemilinStatedOmegaMap Φ S σ hS μ hSΦ).comp
      (Subgroup.subtype (omegaBlockSubgroup Φ b ε)))
    (omegaBlockSubgroup Φ b ε)
    (fun x => by
      change (((omegaSemilinStatedOmegaMap Φ S σ hS μ hSΦ
          ((x : omegaBlockSubgroup Φ b ε) : StatedOmega ⇑Φ) : StatedOmega ⇑Φ) : GL ι K)) ∈
        (Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ glFixing (1 - ε))
      rw [Subgroup.mem_inf]
      constructor
      · rw [Subgroup.mem_centralizer_singleton_iff]
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype,
          omegaSemilinStatedOmegaMap_apply]
        exact omegaSemilinConjGL_commute_of_commute S σ hS b
          (((x : omegaBlockSubgroup Φ b ε) : StatedOmega ⇑Φ) : GL ι K) hSb
          (Subgroup.mem_centralizer_singleton_iff.mp
            (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp x.2)).1)
      · change ((((omegaSemilinStatedOmegaMap Φ S σ hS μ hSΦ x :
            StatedOmega ⇑Φ) : GL ι K) : Matrix ι ι K) * (1 - ε) = 1 - ε)
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype,
          omegaSemilinStatedOmegaMap_apply]
        exact omegaSemilinConjGL_fixes_one_sub S σ hS ε hSε
          (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp x.2)).2)

@[simp] theorem omegaSemilinBlockMap_apply {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Φ : QuadraticForm K (ι → K)) (S : (ι → K) ≃+ (ι → K))
    (σ : K ≃+* K) (hS : ∀ (c : K) (v : ι → K), S (c • v) = σ c • S v)
    (μ : K) (hSΦ : ∀ v : ι → K, Φ (S v) = μ * σ (Φ v)) (b : GL ι K) (ε : Matrix ι ι K)
    (hSb : ∀ v : ι → K, S (((b : GL ι K) : Matrix ι ι K) *ᵥ v) =
      ((b : GL ι K) : Matrix ι ι K) *ᵥ S v)
    (hSε : ∀ v : ι → K, S (ε *ᵥ v) = ε *ᵥ S v) (x : omegaBlockSubgroup Φ b ε) :
    (((omegaSemilinBlockMap Φ S σ hS μ hSΦ b ε hSb hSε x : omegaBlockSubgroup Φ b ε) :
        StatedOmega ⇑Φ) : GL ι K) =
      omegaSemilinConjGL S σ hS (((x : omegaBlockSubgroup Φ b ε) : StatedOmega ⇑Φ) : GL ι K) := by
  simp [omegaSemilinBlockMap, omegaSemilinStatedOmegaMap_apply]

theorem omegaSemilin_isometry_mul_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (b : GL ι K)
    (hb : ∀ v : ι → K, Φ (((b : GL ι K) : Matrix ι ι K) *ᵥ v) = Φ v) :
    ((b : GL ι K) : Matrix ι ι K).transpose *
        LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * ((b : GL ι K) : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
  have hpol : ∀ x y : ι → K,
      QuadraticMap.polar Φ (((b : GL ι K) : Matrix ι ι K) *ᵥ x)
        (((b : GL ι K) : Matrix ι ι K) *ᵥ y) =
      QuadraticMap.polar Φ x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hb (x + y), hb x, hb y]
  apply (LinearEquiv.injective Matrix.toBilin')
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, ← ggOmegaBlk_polar_eq_dot Φ
      (((b : GL ι K) : Matrix ι ι K) *ᵥ x) (((b : GL ι K) : Matrix ι ι K) *ᵥ y),
    ← ggOmegaBlk_polar_eq_dot Φ x y]
  exact hpol x y

theorem omegaSemilin_isPrimIdemIn_formAdj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id K)) = G) (b : GL ι K)
    (hSU : Matrix.transpose (((b : GL ι K) : Matrix ι ι K).map (RingHom.id K)) *
        G * ((b : GL ι K) : Matrix ι ι K) = G)
    {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e) :
    IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
      (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G e) := by
  classical
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  have hcomm_b : ∀ a ∈ A, Commute a (((b : GL ι K) : Matrix ι ι K)) := by
    intro a ha
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute
      (s := Units.val '' ({b} : Set (GL ι K))) (a := ((b : GL ι K) : Matrix ι ι K))
      (b := a) ha (by
        intro x hx
        obtain ⟨s, hs, rfl⟩ := hx
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Commute.refl _)).symm
  have hAcomm : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := by
    intro a ha c hc
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute
      (s := Units.val '' ({b} : Set (GL ι K))) hc (by
        intro x hx
        obtain ⟨s, hs, rfl⟩ := hx
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hcomm_b a ha)).eq
  have hSU' : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose (((s : GL ι K) : Matrix ι ι K).map (RingHom.id K)) *
        G * ((s : GL ι K) : Matrix ι ι K) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa using hSU
  have hstarA : ∀ {a : Matrix ι ι K}, a ∈ A →
      CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G a ∈ A := by
    intro a ha
    exact CFSG.StandardType.ClassicalPosition.Geo.formAdj_mem_adjoin
      (RingHom.id K) hG (S := ({b} : Set (GL ι K))) hSU' ha
  have heA : e ∈ A := he.1
  have heidem : IsIdempotentElem e := he.2.1
  have hene : e ≠ 0 := he.2.2.1
  have hemin : ∀ x ∈ A, IsIdempotentElem x → x * e = x → x = 0 ∨ x = e := he.2.2.2
  have hstar_e_idem : IsIdempotentElem
      (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G e) := by
    show CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G e *
        CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G e =
      CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G e
    rw [← CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG e e,
      heidem.eq]
  have hstar_e_ne : CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G e ≠ 0 := by
    intro h0
    have he0 : e = 0 := by
      calc e = CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G
            (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G e) :=
              (CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj
                (RingHom.id K) (fun x => rfl) hG hGh e).symm
        _ = CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G 0 := by rw [h0]
        _ = 0 := by simp [CFSG.StandardType.ClassicalPosition.formAdj]
    exact hene he0
  refine ⟨hstarA heA, hstar_e_idem, hstar_e_ne, ?_⟩
  intro x hxA hxidem hxe
  have hx'A : CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x ∈ A :=
    hstarA hxA
  have hx'idem : IsIdempotentElem
      (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x) := by
    show CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x *
        CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x =
      CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x
    rw [← CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG x x,
      hxidem.eq]
  have hx'e : CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x * e =
      CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x := by
    have h := congrArg (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G) hxe
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG x
        (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G e),
      CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj
        (RingHom.id K) (fun x => rfl) hG hGh e] at h
    rw [hAcomm e heA (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x)
      hx'A] at h
    exact h
  rcases hemin (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x)
    hx'A hx'idem hx'e with h0 | heq
  · left
    calc x = CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G
          (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x) :=
            (CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj
              (RingHom.id K) (fun x => rfl) hG hGh x).symm
      _ = CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G 0 := by rw [h0]
      _ = 0 := by simp [CFSG.StandardType.ClassicalPosition.formAdj]
  · right
    calc x = CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G
          (CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G x) :=
            (CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj
              (RingHom.id K) (fun x => rfl) hG hGh x).symm
      _ = CFSG.StandardType.ClassicalPosition.formAdj (RingHom.id K) G e := by rw [heq]

theorem exists_isPrimAdjIdemIn_isComponentOf_glBlockCentralizer {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (J : Subgroup (StatedOmega ⇑Φ))
    (hJ : CFSG.Assembly.IsComponentOf J (omegaCentralizerSubgroup Φ b)) :
    ∃ ε : Matrix ι ι K,
      IsPrimAdjIdemIn (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
        (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε ∧
      CFSG.Assembly.IsComponentOf J (omegaBlockSubgroup Φ b ε) := by
  obtain ⟨P, hP, horth, hsum, hc, hsup, hcard⟩ :=
    centralizer_block_decomp_Omega Φ hΦ h8 b hb hodd
  have hJ' : CFSG.Assembly.IsComponentOf J (⨆ ε ∈ P, omegaBlockSubgroup Φ b ε) := by
    rwa [hsup]
  obtain ⟨ε, hεP, hJε⟩ :=
    exists_isComponentOf_block P (fun ε => omegaBlockSubgroup Φ b ε) hc hJ'
  exact ⟨ε, hP ε hεP, hJε⟩

end CFSG.StandardType.ClassicalBlocks
