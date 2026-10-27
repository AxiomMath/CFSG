module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableData

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem pairVec_add (x : X3) (u v : Fin Tag.E6.rank → ℤ) :
    pairVec x (u + v) = pairVec x u + pairVec x v := by
  simp [pairVec, mul_add, Finset.sum_add_distrib]

theorem pairVec_zsmul (x : X3) (n : ℤ) (v : Fin Tag.E6.rank → ℤ) :
    pairVec x (n • v) = (n : ZMod 3) * pairVec x v := by
  simp [pairVec, Finset.mul_sum, mul_left_comm]

theorem pairVec_single (x : X3) (i : Fin Tag.E6.rank) :
    pairVec x (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = x i := by
  simp [pairVec, Pi.single_apply]

noncomputable def pairHom (x : X3) : (Fin Tag.E6.rank → ℤ) →+ ZMod 3 where
  toFun := pairVec x
  map_zero' := by simp [pairVec]
  map_add' := pairVec_add x

theorem pairVec_sum {ι : Type*} (x : X3) (s : Finset ι) (f : ι → Fin Tag.E6.rank → ℤ) :
    pairVec x (∑ i ∈ s, f i) = ∑ i ∈ s, pairVec x (f i) :=
  map_sum (pairHom x) f s

theorem pi_eq_sum (v : Fin Tag.E6.rank → ℤ) :
    v = ∑ i, v i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

@[expose] noncomputable def smulX (w : WeylGroup Tag.E6) (x : X3) : X3 :=
  fun i => pairVec x (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))

theorem pairVec_smulX (w : WeylGroup Tag.E6) (x : X3) (v : Fin Tag.E6.rank → ℤ) :
    pairVec (smulX w x) v = pairVec x (w⁻¹ • v) := by
  conv_rhs => rw [pi_eq_sum v]
  rw [Finset.smul_sum, pairVec_sum]
  have hL : pairVec (smulX w x) v =
      ∑ i, pairVec x (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) * (v i : ZMod 3) := rfl
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, pairVec_zsmul, mul_comm]

theorem pairVec_eq_of_forall {x y : X3} (h : ∀ v, pairVec x v = pairVec y v) : x = y := by
  funext i
  have := h (Pi.single i 1)
  rwa [pairVec_single, pairVec_single] at this

noncomputable instance : MulAction (WeylGroup Tag.E6) X3 where
  smul := smulX
  one_smul x := by
    apply pairVec_eq_of_forall
    intro v
    change pairVec (smulX 1 x) v = pairVec x v
    rw [pairVec_smulX, inv_one, one_smul]
  mul_smul w₁ w₂ x := by
    apply pairVec_eq_of_forall
    intro v
    change pairVec (smulX (w₁ * w₂) x) v = pairVec (smulX w₁ (smulX w₂ x)) v
    rw [pairVec_smulX, pairVec_smulX, pairVec_smulX, mul_inv_rev, mul_smul]

theorem pairVec_smul (w : WeylGroup Tag.E6) (x : X3) (v : Fin Tag.E6.rank → ℤ) :
    pairVec (w • x) v = pairVec x (w⁻¹ • v) :=
  pairVec_smulX w x v

theorem pairVec_smul_self (w : WeylGroup Tag.E6) (x : X3) (v : Fin Tag.E6.rank → ℤ) :
    pairVec (w • x) (w • v) = pairVec x v := by
  rw [pairVec_smul, inv_smul_smul]

theorem pairVec_reflect (x : X3) (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ℤ) :
    pairVec x (reflect Tag.E6 i v) = pairVec (dualRefl i x) v := by
  have h1 : pairVec x (reflect Tag.E6 i v) =
      pairVec x v - ((∑ j, Tag.E6.cartan i j * v j : ℤ) : ZMod 3) * x i := by
    have := map_sub (pairHom x) v
      ((∑ j, Tag.E6.cartan i j * v j) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
    change pairVec x (v - _) = pairVec x v - pairVec x _ at this
    rw [pairVec_zsmul, pairVec_single] at this
    exact this
  have h2 : pairVec (dualRefl i x) v = pairVec x v -
      x i * ∑ c, ((Tag.E6.cartan i c : ℤ) : ZMod 3) * (v c : ZMod 3) := by
    simp only [pairVec, dualRefl, sub_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_sub_distrib (fun c => x c * (v c : ZMod 3))
      (fun c => x i * (((Tag.E6.cartan i c : ℤ) : ZMod 3) * (v c : ZMod 3)))
  rw [h1, h2]
  push_cast
  ring

theorem simple_smul_X3 (i : Fin Tag.E6.rank) (x : X3) : simple Tag.E6 i • x = dualRefl i x := by
  apply pairVec_eq_of_forall
  intro v
  rw [pairVec_smul, CoxeterSystem.inv_simple, simple_smul, pairVec_reflect]

@[expose] noncomputable def stabVec (x : X3) : Subgroup (WeylGroup Tag.E6) :=
  MulAction.stabilizer (WeylGroup Tag.E6) x

@[expose] def kerReflVec (x : X3) : Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure {r | ∃ (w : WeylGroup Tag.E6) (i : Fin Tag.E6.rank),
    w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ kerRoots x ∧ r = w * simple Tag.E6 i * w⁻¹}

@[expose] noncomputable def TableVec (x : X3) : Prop :=
  kerReflVec x = stabVec x ∨ (((kerRoots x).ncard = 18 ∨ (kerRoots x).ncard = 24) ∧
    ((kerReflVec x).subgroupOf (stabVec x)).index = 3)


theorem pairVec_sub (x : X3) (u v : Fin Tag.E6.rank → ℤ) :
    pairVec x (u - v) = pairVec x u - pairVec x v := by
  have h := pairVec_add x (u - v) v
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem conj_simple_smul (w : WeylGroup Tag.E6) (i : Fin Tag.E6.rank)
    (v : Fin Tag.E6.rank → ℤ) :
    (w * simple Tag.E6 i * w⁻¹) • v = v - (∑ j, Tag.E6.cartan i j * (w⁻¹ • v) j) •
      (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
  have hu : reflect Tag.E6 i (w⁻¹ • v) =
      (w⁻¹ • v) - (∑ j, Tag.E6.cartan i j * (w⁻¹ • v) j) • Pi.single i 1 := rfl
  rw [mul_smul, mul_smul, simple_smul, hu, smul_sub, smul_inv_smul, smul_comm]

theorem kerReflVec_le_stabVec_of_forall {x y : X3} (hy : ∀ α ∈ kerRoots x, pairVec y α = 0) :
    kerReflVec x ≤ stabVec y := by
  rw [kerReflVec]
  refine (Subgroup.closure_le (stabVec y)).2 ?_
  rintro r ⟨w, i, hmem, rfl⟩
  rw [SetLike.mem_coe, stabVec]
  show (w * simple Tag.E6 i * w⁻¹) • y = y
  apply pairVec_eq_of_forall
  intro v
  have hinv : (w * simple Tag.E6 i * w⁻¹)⁻¹ = w * simple Tag.E6 i * w⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, CoxeterSystem.inv_simple, mul_assoc]
  rw [pairVec_smul, hinv, conj_simple_smul, pairVec_sub, pairVec_zsmul, hy _ hmem, mul_zero]
  ring

theorem kerReflVec_le_stabVec (x : X3) : kerReflVec x ≤ stabVec x :=
  kerReflVec_le_stabVec_of_forall fun _ hα => hα.2

end CFSG.StandardType.NTPlane

end
