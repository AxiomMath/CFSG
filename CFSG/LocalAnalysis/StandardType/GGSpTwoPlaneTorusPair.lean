module

public import CFSG.LocalAnalysis.StandardType.GGSpTwoPlaneTorus
import CFSG.ClassicalGroups.Alternating.TransvectionGenerationTwo

public section

namespace CFSG.StandardType

namespace TwoThree

open Matrix CFSG.LieType.SteinbergBR.EvenSp

variable {K : Type} [Field K] {r : ℕ}

private noncomputable def planeBlockIncl (k : Fin r) :
    (Fin 2 → K) →ₗ[K] (Fin r ⊕ Fin r → K) where
  toFun u i := if i = Sum.inl k then u 0 else if i = Sum.inr k then u 1 else 0
  map_add' u v := by
    funext i
    by_cases h1 : i = Sum.inl k <;> by_cases h2 : i = Sum.inr k <;> simp [h1, h2]
  map_smul' c u := by
    funext i
    by_cases h1 : i = Sum.inl k <;> by_cases h2 : i = Sum.inr k <;> simp [h1, h2]

private theorem planeBlockIncl_apply_inl (k : Fin r) (u : Fin 2 → K) :
    planeBlockIncl k u (Sum.inl k) = u 0 := by
  simp [planeBlockIncl]

private theorem planeBlockIncl_apply_inr (k : Fin r) (u : Fin 2 → K) :
    planeBlockIncl k u (Sum.inr k) = u 1 := by
  simp [planeBlockIncl]

private theorem planeBlockIncl_apply_inl_of_ne {j k : Fin r} (h : j ≠ k) (u : Fin 2 → K) :
    planeBlockIncl k u (Sum.inl j) = 0 := by
  simp [planeBlockIncl, h]

private theorem planeBlockIncl_apply_inr_of_ne {j k : Fin r} (h : j ≠ k) (u : Fin 2 → K) :
    planeBlockIncl k u (Sum.inr j) = 0 := by
  simp [planeBlockIncl, h]

private theorem planeBlockIncl_injective (k : Fin r) :
    Function.Injective (planeBlockIncl (K := K) (r := r) k) := by
  intro u v h
  have h0 : u 0 = v 0 := by
    simpa [planeBlockIncl_apply_inl] using congrFun h (Sum.inl k)
  have h1 : u 1 = v 1 := by
    simpa [planeBlockIncl_apply_inr] using congrFun h (Sum.inr k)
  funext t
  fin_cases t
  · exact h0
  · exact h1

private noncomputable def planeBlockSub (k : Fin r) : Submodule K (Fin r ⊕ Fin r → K) :=
  LinearMap.range (planeBlockIncl k)

private theorem planeBlockIncl_mem (k : Fin r) (u : Fin 2 → K) :
    planeBlockIncl k u ∈ planeBlockSub k :=
  ⟨u, rfl⟩

private noncomputable def planeBlockProj (k : Fin r) : Module.End K (Fin r ⊕ Fin r → K) :=
  (planeBlockIncl k).comp (LinearMap.pi fun t : Fin 2 =>
    LinearMap.proj (if t = 0 then Sum.inl k else Sum.inr k))

private theorem planeBlockProj_apply (k : Fin r) (v : Fin r ⊕ Fin r → K) :
    planeBlockProj k v =
      planeBlockIncl k fun t : Fin 2 => v (if t = 0 then Sum.inl k else Sum.inr k) := by
  rfl

private theorem planeBlockProj_mem (k : Fin r) (v : Fin r ⊕ Fin r → K) :
    planeBlockProj k v ∈ planeBlockSub k :=
  planeBlockIncl_mem k _

private theorem planeBlockProj_sum :
    (∑ k : Fin r, planeBlockProj (K := K) k) = 1 := by
  refine LinearMap.ext fun v => funext fun i => ?_
  have hsum : (∑ k : Fin r, planeBlockProj (K := K) k) v =
      ∑ k : Fin r, planeBlockProj k v := by
    simpa only using (LinearMap.sum_apply (t := Finset.univ)
      (f := fun k => planeBlockProj (K := K) k) v)
  rw [hsum, Finset.sum_apply, Module.End.one_apply]
  rcases i with j | j
  · rw [Finset.sum_eq_single j]
    · rw [planeBlockProj_apply]
      simp [planeBlockIncl]
    · intro b _ hbj
      rw [planeBlockProj_apply]
      rw [planeBlockIncl_apply_inl_of_ne (Ne.symm hbj)]
    · intro hj
      simp at hj
  · rw [Finset.sum_eq_single j]
    · rw [planeBlockProj_apply]
      have h0 : (0 : Fin 2) ≠ 1 := by decide
      simp [planeBlockIncl]
    · intro b _ hbj
      rw [planeBlockProj_apply]
      rw [planeBlockIncl_apply_inr_of_ne (Ne.symm hbj)]
    · intro hj
      simp at hj


private noncomputable def spAct (g : CFSG.Open.StatedSp r K) :
    Module.End K (Fin r ⊕ Fin r → K) :=
  Matrix.toLin' ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)

private theorem spAct_apply (g : CFSG.Open.StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spAct g v = ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v :=
  Matrix.toLin'_apply _ _

private theorem spAct_mul (a b : CFSG.Open.StatedSp r K) :
    spAct (a * b) = spAct a * spAct b := by
  refine LinearMap.ext fun v => ?_
  rw [spAct_apply, Module.End.mul_apply, spAct_apply, spAct_apply, Subgroup.coe_mul,
    Units.val_mul, Matrix.mulVec_mulVec]

private theorem planeMat_mulVec_inl (h : Fin r → Matrix (Fin 2) (Fin 2) K)
    (v : Fin r ⊕ Fin r → K) (j : Fin r) :
    (planeMat h *ᵥ v) (Sum.inl j) = h j 0 0 * v (Sum.inl j) + h j 0 1 * v (Sum.inr j) := by
  simp [planeMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.diagonal]

private theorem planeMat_mulVec_inr (h : Fin r → Matrix (Fin 2) (Fin 2) K)
    (v : Fin r ⊕ Fin r → K) (j : Fin r) :
    (planeMat h *ᵥ v) (Sum.inr j) = h j 1 0 * v (Sum.inl j) + h j 1 1 * v (Sum.inr j) := by
  simp [planeMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.diagonal]

private def sumCongrPerm (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin r ⊕ Fin r) :=
  Equiv.sumCongr σ σ

private theorem planePermGL_val (σ : Equiv.Perm (Fin r)) :
    ((planePermGL (K := K) σ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Equiv.Perm.permMatrix K (sumCongrPerm σ).symm :=
  rfl

private theorem planeMat_submatrix_sumCongr (σ : Equiv.Perm (Fin r))
    (g : Fin r → Matrix (Fin 2) (Fin 2) K) :
    (planeMat g).submatrix (sumCongrPerm σ).symm (sumCongrPerm σ).symm =
      planeMat (g ∘ σ.symm) := by
  have hsymm : (sumCongrPerm σ).symm = Equiv.sumCongr σ.symm σ.symm := by
    rw [sumCongrPerm, Equiv.Perm.sumCongr_symm]
  rw [hsymm]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [planeMat, Matrix.submatrix_apply, Matrix.diagonal_apply, Equiv.sumCongr_apply,
      ]

private noncomputable def planeInvGL (k : Fin r) : GL (Fin r ⊕ Fin r) K :=
  planeHom (Pi.mulSingle k (swapGL (K := K)))

private theorem planeInvGL_val (k : Fin r) :
    ((planeInvGL (K := K) k : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      planeMat (fun j => ((Pi.mulSingle k (swapGL (K := K)) : Fin r → GL (Fin 2) K) j :
        Matrix (Fin 2) (Fin 2) K)) :=
  planeHom_val (K := K) (n := r) (Pi.mulSingle k (swapGL (K := K)))

private theorem commute_planeOps (y z : Module.End K (Fin r ⊕ Fin r → K))
    (h : Commute y z) :
    Commute (1 + y + y ^ 2) (1 + z + z ^ 2) ∧
      Commute (1 + y + y ^ 2) (z + z ^ 2) ∧
      Commute (y + y ^ 2) (1 + z + z ^ 2) ∧
      Commute (y + y ^ 2) (z + z ^ 2) := by
  have hyB : Commute y (1 + z + z ^ 2) := by
    have h' : Commute y (1 + (z + z ^ 2)) :=
      (Commute.one_right y).add_right (h.add_right (h.pow_right 2))
    simpa [add_assoc] using h'
  have hy2B : Commute (y ^ 2) (1 + z + z ^ 2) := by
    have h' : Commute (y ^ 2) (1 + (z + z ^ 2)) :=
      (Commute.one_right (y ^ 2)).add_right
        ((h.pow_left 2).add_right ((h.pow_left 2).pow_right 2))
    simpa [add_assoc] using h'
  have hAB : Commute (1 + y + y ^ 2) (1 + z + z ^ 2) :=
    ((Commute.one_left _).add_left hyB).add_left hy2B
  have hyC : Commute y (z + z ^ 2) := h.add_right (h.pow_right 2)
  have hy2C : Commute (y ^ 2) (z + z ^ 2) :=
    (h.pow_left 2).add_right ((h.pow_left 2).pow_right 2)
  have hAC : Commute (1 + y + y ^ 2) (z + z ^ 2) :=
    ((Commute.one_left _).add_left hyC).add_left hy2C
  have hDz : Commute (y + y ^ 2) z := h.add_left (h.pow_left 2)
  have hDz2 : Commute (y + y ^ 2) (z ^ 2) :=
    (h.pow_right 2).add_left ((h.pow_left 2).pow_right 2)
  have hDC : Commute (y + y ^ 2) (z + z ^ 2) := hDz.add_right hDz2
  have hDB : Commute (y + y ^ 2) (1 + z + z ^ 2) := by
    have h' : Commute (y + y ^ 2) (1 + (z + z ^ 2)) :=
      (Commute.one_right (y + y ^ 2)).add_right hDC
    simpa [add_assoc] using h'
  exact ⟨hAB, hAC, hDB, hDC⟩

private theorem finset_noncommProd_mapsTo {ι : Type*} (s : Finset ι)
    (W : Submodule K (Fin r ⊕ Fin r → K)) (g : ι → Module.End K (Fin r ⊕ Fin r → K))
    (comm : (s : Set ι).Pairwise (fun a b => Commute (g a) (g b)))
    (hg : ∀ i ∈ s, ∀ w ∈ W, g i w ∈ W) :
    ∀ w ∈ W, (s.noncommProd g comm) w ∈ W := by
  classical
  induction s using Finset.induction_on with
  | empty => intro w hw; exact hw
  | insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem s a g comm ha]
      intro w hw
      rw [Module.End.mul_apply]
      exact hg a (Finset.mem_insert_self _ _) _
        (ih (comm.mono fun x hx => Finset.mem_insert_of_mem hx)
          (fun i hi => hg i (Finset.mem_insert_of_mem hi)) w hw)

private theorem finset_noncommProd_fix {ι : Type*} (s : Finset ι)
    (g : ι → Module.End K (Fin r ⊕ Fin r → K)) (v : Fin r ⊕ Fin r → K)
    (comm : (s : Set ι).Pairwise (fun a b => Commute (g a) (g b)))
    (h : ∀ i ∈ s, g i v = v) : (s.noncommProd g comm) v = v := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem s a g comm ha, Module.End.mul_apply,
        ih (comm.mono fun x hx => Finset.mem_insert_of_mem hx)
          (fun i hi => h i (Finset.mem_insert_of_mem hi)),
        h a (Finset.mem_insert_self _ _)]

private theorem normalizes_mul {T : Subgroup (CFSG.Open.StatedSp r K)}
    {P Q : CFSG.Open.StatedSp r K}
    (hP : ∀ t ∈ T, P * t * P⁻¹ ∈ T) (hQ : ∀ t ∈ T, Q * t * Q⁻¹ ∈ T) :
    ∀ t ∈ T, P * Q * t * (P * Q)⁻¹ ∈ T := by
  intro t ht
  rw [show P * Q * t * (P * Q)⁻¹ = P * (Q * t * Q⁻¹) * P⁻¹ by group]
  exact hP _ (hQ t ht)

private theorem commute_of_conj_eq {P y : CFSG.Open.StatedSp r K}
    (h : P * y * P⁻¹ = y) : P * y = y * P := by
  calc P * y = (P * y * P⁻¹) * P := by group
    _ = y * P := by rw [h]

private theorem planeMat_mulVec_planeBlockIncl (h : Fin r → Matrix (Fin 2) (Fin 2) K)
    (k : Fin r) (u : Fin 2 → K) :
    planeMat h *ᵥ planeBlockIncl k u = planeBlockIncl k (h k *ᵥ u) := by
  ext i
  rcases i with j | j
  · rw [planeMat_mulVec_inl]
    by_cases hjk : j = k
    · subst hjk
      rw [planeBlockIncl_apply_inl, planeBlockIncl_apply_inr, planeBlockIncl_apply_inl]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · rw [planeBlockIncl_apply_inl_of_ne hjk, planeBlockIncl_apply_inr_of_ne hjk,
        planeBlockIncl_apply_inl_of_ne hjk]
      simp
  · rw [planeMat_mulVec_inr]
    by_cases hjk : j = k
    · subst hjk
      rw [planeBlockIncl_apply_inl, planeBlockIncl_apply_inr, planeBlockIncl_apply_inr]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · rw [planeBlockIncl_apply_inl_of_ne hjk, planeBlockIncl_apply_inr_of_ne hjk,
        planeBlockIncl_apply_inr_of_ne hjk]
      simp

private theorem permMatrix_conj {n R : Type*} [Fintype n] [DecidableEq n] [Field R]
    (σ : Equiv.Perm n) (A : Matrix n n R) :
    Equiv.Perm.permMatrix R σ * A * Equiv.Perm.permMatrix R (σ⁻¹) = A.submatrix σ σ := by
  change σ.toPEquiv.toMatrix * A * (σ⁻¹).toPEquiv.toMatrix = A.submatrix σ σ
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rfl

private theorem permMatrix_inv {n R : Type*} [Fintype n] [DecidableEq n] [Field R]
    (σ : Equiv.Perm n) :
    Equiv.Perm.permMatrix R (σ⁻¹) = (Equiv.Perm.permMatrix R σ)⁻¹ := by
  have h : Equiv.Perm.permMatrix R σ * Equiv.Perm.permMatrix R (σ⁻¹) = 1 := by
    rw [← Matrix.permMatrix_mul (σ := σ⁻¹) (τ := σ), inv_mul_cancel]
    simp
  exact (Matrix.inv_eq_right_inv h).symm

private theorem planePermGL_conj_planeInvGL (σ : Equiv.Perm (Fin r)) (k : Fin r) :
    planePermGL (K := K) σ * planeInvGL (K := K) k * (planePermGL (K := K) σ)⁻¹ =
      planeInvGL (K := K) (σ k) := by
  apply Units.ext
  change ((planePermGL (K := K) σ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((planeInvGL (K := K) k : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (((planePermGL (K := K) σ)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
    ((planeInvGL (K := K) (σ k) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  have hInv : (((planePermGL (K := K) σ)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Equiv.Perm.permMatrix K (sumCongrPerm σ) := by
    rw [← map_inv, planePermGL_val]
    rw [show sumCongrPerm σ⁻¹ = (sumCongrPerm σ).symm by
      rw [sumCongrPerm, sumCongrPerm, Equiv.Perm.sumCongr_symm]
      simp [Equiv.Perm.inv_def]]
    rw [Equiv.symm_symm]
  rw [planePermGL_val, planeInvGL_val, planeInvGL_val, hInv]
  have hconj := permMatrix_conj (sumCongrPerm σ).symm
    (planeMat fun j => ((Pi.mulSingle k (swapGL (K := K)) : Fin r → GL (Fin 2) K) j :
      Matrix (Fin 2) (Fin 2) K))
  have hτinv : ((sumCongrPerm σ).symm)⁻¹ = sumCongrPerm σ := by
    rw [Equiv.Perm.inv_def, Equiv.symm_symm]
  rw [hτinv] at hconj
  rw [hconj, planeMat_submatrix_sumCongr]
  have hg : (fun j => ((Pi.mulSingle k (swapGL (K := K)) : Fin r → GL (Fin 2) K) j :
      Matrix (Fin 2) (Fin 2) K)) ∘ σ.symm =
      (fun j => ((Pi.mulSingle (σ k) (swapGL (K := K)) : Fin r → GL (Fin 2) K) j :
        Matrix (Fin 2) (Fin 2) K)) := by
    funext j
    rw [Function.comp_apply]
    by_cases h : j = σ k
    · subst h
      simp [Pi.mulSingle_eq_same]
    · have h' : σ.symm j ≠ k := by
        intro hh
        apply h
        have hc := congrArg σ hh
        simpa using hc
      simp [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h']
  rw [hg]

private theorem noncommProd_eq_planeBlockProj (k : Fin r)
    (Q : Fin r → Module.End K (Fin r ⊕ Fin r → K))
    (comm : ((Finset.univ.erase k : Finset (Fin r)) : Set (Fin r)).Pairwise
      (fun a b => Commute (Q a) (Q b)))
    (hfix : ∀ l ∈ Finset.univ.erase k, ∀ u, Q l (planeBlockIncl k u) = planeBlockIncl k u)
    (hkill : ∀ l ∈ Finset.univ.erase k, ∀ u, Q l (planeBlockIncl l u) = 0) :
    (Finset.univ.erase k).noncommProd Q comm = planeBlockProj (K := K) k := by
  refine LinearMap.ext fun v => ?_
  have hsum : (∑ j : Fin r, planeBlockProj j v) = v := by
    have h := congrArg (fun f : Module.End K (Fin r ⊕ Fin r → K) => f v)
      (planeBlockProj_sum (K := K) (r := r))
    simpa only [LinearMap.sum_apply, Module.End.one_apply, Finset.sum_apply] using h
  conv_lhs => rw [← hsum]
  rw [map_sum]
  rw [Finset.sum_eq_single k]
  · rw [planeBlockProj_apply]
    set u : Fin 2 → K := fun t => v (if t = 0 then Sum.inl k else Sum.inr k)
    exact finset_noncommProd_fix _ Q _ comm (fun l hl => hfix l hl u)
  · intro j _ hjk
    rw [planeBlockProj_apply]
    have hj : j ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩
    rw [← Finset.noncommProd_erase_mul (Finset.univ.erase k) hj Q comm]
    rw [Module.End.mul_apply, hkill j hj, LinearMap.map_zero]
  · intro hk; simp at hk

section

variable [CharP K 2]

private theorem spAct_commute_spPlaneTorus (f g : Fin r → Multiplicative (ZMod 3)) :
    Commute (spAct (spPlaneTorus (K := K) (r := r) f))
      (spAct (spPlaneTorus (K := K) (r := r) g)) := by
  show spAct (spPlaneTorus (K := K) (r := r) f) *
      spAct (spPlaneTorus (K := K) (r := r) g) =
    spAct (spPlaneTorus (K := K) (r := r) g) *
      spAct (spPlaneTorus (K := K) (r := r) f)
  rw [← spAct_mul, ← spAct_mul, ← map_mul, ← map_mul, mul_comm]

private theorem spPlaneTorus_apply (f : Fin r → Multiplicative (ZMod 3)) :
    ((spPlaneTorus (K := K) (r := r) f : CFSG.Open.StatedSp r K) :
        GL (Fin r ⊕ Fin r) K) = planeHom (fun j => tPow (f j)) :=
  rfl

private theorem spPlaneTorus_planeBlockIncl (f : Fin r → Multiplicative (ZMod 3))
    (k : Fin r) (u : Fin 2 → K) :
    spAct (spPlaneTorus f) (planeBlockIncl k u) =
      planeBlockIncl k (((tPow (f k) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u) := by
  rw [spAct_apply, spPlaneTorus_apply, planeHom_val]
  exact planeMat_mulVec_planeBlockIncl _ _ _

private noncomputable def planeBlockE (a : Multiplicative (ZMod 3)) : Matrix (Fin 2) (Fin 2) K :=
  (1 : Matrix (Fin 2) (Fin 2) K) + ((tPow a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) +
    ((tPow a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2

private noncomputable def planeBlockF (a : Multiplicative (ZMod 3)) : Matrix (Fin 2) (Fin 2) K :=
  ((tPow a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) +
    ((tPow a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2

private noncomputable def planeEOp (f : Fin r → Multiplicative (ZMod 3)) :
    Module.End K (Fin r ⊕ Fin r → K) :=
  1 + spAct (spPlaneTorus f) + (spAct (spPlaneTorus f)) ^ 2

private noncomputable def planeFOp (f : Fin r → Multiplicative (ZMod 3)) :
    Module.End K (Fin r ⊕ Fin r → K) :=
  spAct (spPlaneTorus f) + (spAct (spPlaneTorus f)) ^ 2

private theorem planeEOp_planeBlockIncl (f : Fin r → Multiplicative (ZMod 3))
    (k : Fin r) (u : Fin 2 → K) :
    planeEOp f (planeBlockIncl k u) =
      planeBlockIncl k (planeBlockE (f k) *ᵥ u) := by
  simp only [planeEOp, planeBlockE, LinearMap.add_apply, pow_two,
    Module.End.mul_apply, Module.End.one_apply, spPlaneTorus_planeBlockIncl, map_add,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]

private theorem planeFOp_planeBlockIncl (f : Fin r → Multiplicative (ZMod 3))
    (k : Fin r) (u : Fin 2 → K) :
    planeFOp f (planeBlockIncl k u) =
      planeBlockIncl k (planeBlockF (f k) *ᵥ u) := by
  simp only [planeFOp, planeBlockF, LinearMap.add_apply, pow_two,
    Module.End.mul_apply, spPlaneTorus_planeBlockIncl, map_add, Matrix.add_mulVec,
    Matrix.mulVec_mulVec]

private theorem tGL_matrix_sq :
    (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) ^ 2 = !![1, 1; 1, 0] := by
  change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) ^ 2 = !![1, 1; 1, 0]
  rw [pow_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem tGL_matrix_pow_three :
    (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
  have h := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K))
    (tGL_pow_three (K := K))
  simpa using h

private theorem tGL_matrix_add_sq_add_one :
    (1 : Matrix (Fin 2) (Fin 2) K) +
      (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) +
      (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) ^ 2 = 0 := by
  rw [tGL_matrix_sq]
  change (1 : Matrix (Fin 2) (Fin 2) K) + !![0, 1; 1, 1] + !![1, 1; 1, 0] = 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem mul_zmod_three_cases (a : Multiplicative (ZMod 3)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 ∨ a = Multiplicative.ofAdd 2 := by
  fin_cases a <;> decide

private theorem tPow_ofAdd_two :
    tPow (K := K) (Multiplicative.ofAdd 2) = tGL ^ 2 := by
  rw [tPow, TableBSymp.zmodPowHom_apply, toAdd_ofAdd,
    show ZMod.val (2 : ZMod 3) = 2 from rfl]

private theorem planeBlockE_one : planeBlockE (K := K) 1 = 1 := by
  simp [planeBlockE, CharTwo.add_self_eq_zero]

private theorem planeBlockE_ofAdd_one :
    planeBlockE (K := K) (Multiplicative.ofAdd 1) = 0 := by
  simpa [planeBlockE, tPow_ofAdd_one] using tGL_matrix_add_sq_add_one (K := K)

private theorem planeBlockE_ofAdd_two :
    planeBlockE (K := K) (Multiplicative.ofAdd 2) = 0 := by
  rw [planeBlockE, tPow_ofAdd_two, Units.val_pow_eq_pow_val]
  have h4 : (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) ^ 4 =
      (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, tGL_matrix_pow_three, one_mul]
  have h22 : ((((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) ^ 2) ^ 2 =
      (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) ^ 4 := by
    simpa using (pow_mul (((tGL (K := K) : GL (Fin 2) K)) :
      Matrix (Fin 2) (Fin 2) K) 2 2).symm
  rw [h22, h4]
  simpa [add_comm, add_left_comm, add_assoc] using tGL_matrix_add_sq_add_one (K := K)

private theorem planeBlockE_eq (a : Multiplicative (ZMod 3)) :
    planeBlockE (K := K) a = if a = 1 then 1 else 0 := by
  rcases mul_zmod_three_cases a with rfl | rfl | rfl
  · rw [planeBlockE_one]; simp
  · rw [planeBlockE_ofAdd_one, if_neg (by decide)]
  · rw [planeBlockE_ofAdd_two, if_neg (by decide)]

private theorem planeBlockF_one : planeBlockF (K := K) 1 = 0 := by
  simp [planeBlockF, CharTwo.add_self_eq_zero]

private theorem planeBlockF_ofAdd_one :
    planeBlockF (K := K) (Multiplicative.ofAdd 1) = 1 := by
  rw [planeBlockF, tPow_ofAdd_one, tGL_matrix_sq]
  change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) + !![1, 1; 1, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem planeBlockF_ofAdd_two :
    planeBlockF (K := K) (Multiplicative.ofAdd 2) = 1 := by
  rw [planeBlockF, tPow_ofAdd_two, Units.val_pow_eq_pow_val]
  have h4 : (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) ^ 4 =
      (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, tGL_matrix_pow_three, one_mul]
  have h22 : ((((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) ^ 2) ^ 2 =
      (((tGL (K := K) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) ^ 4 := by
    simpa using (pow_mul (((tGL (K := K) : GL (Fin 2) K)) :
      Matrix (Fin 2) (Fin 2) K) 2 2).symm
  rw [h22, h4, tGL_matrix_sq]
  change (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) + !![0, 1; 1, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem planeBlockF_eq (a : Multiplicative (ZMod 3)) :
    planeBlockF (K := K) a = if a = 1 then 0 else 1 := by
  rcases mul_zmod_three_cases a with rfl | rfl | rfl
  · rw [planeBlockF_one]; simp
  · rw [planeBlockF_ofAdd_one, if_neg (by decide)]
  · rw [planeBlockF_ofAdd_two, if_neg (by decide)]

private theorem planeEOp_fix_of_eq_one {f : Fin r → Multiplicative (ZMod 3)} {k : Fin r}
    (h : f k = 1) (u : Fin 2 → K) :
    planeEOp f (planeBlockIncl k u) = planeBlockIncl k u := by
  rw [planeEOp_planeBlockIncl, planeBlockE_eq, if_pos h, Matrix.one_mulVec]

private theorem planeEOp_kill_of_ne_one {f : Fin r → Multiplicative (ZMod 3)} {k : Fin r}
    (h : f k ≠ 1) (u : Fin 2 → K) :
    planeEOp f (planeBlockIncl k u) = 0 := by
  rw [planeEOp_planeBlockIncl, planeBlockE_eq, if_neg h, Matrix.zero_mulVec, map_zero]

private theorem planeFOp_fix_of_ne_one {f : Fin r → Multiplicative (ZMod 3)} {k : Fin r}
    (h : f k ≠ 1) (u : Fin 2 → K) :
    planeFOp f (planeBlockIncl k u) = planeBlockIncl k u := by
  rw [planeFOp_planeBlockIncl, planeBlockF_eq, if_neg h, Matrix.one_mulVec]

private theorem planeFOp_kill_of_eq_one {f : Fin r → Multiplicative (ZMod 3)} {k : Fin r}
    (h : f k = 1) (u : Fin 2 → K) :
    planeFOp f (planeBlockIncl k u) = 0 := by
  rw [planeFOp_planeBlockIncl, planeBlockF_eq, if_pos h, Matrix.zero_mulVec, map_zero]

private theorem eq_or_inv_of_ne_one {a b : Multiplicative (ZMod 3)}
    (ha : a ≠ 1) (hb : b ≠ 1) : b = a ∨ b = a⁻¹ := by
  rcases mul_zmod_three_cases a with rfl | rfl | rfl
  · exact absurd rfl ha
  · rcases mul_zmod_three_cases b with rfl | rfl | rfl
    · exact absurd rfl hb
    · left; rfl
    · right; decide
  · rcases mul_zmod_three_cases b with rfl | rfl | rfl
    · exact absurd rfl hb
    · right; decide
    · left; rfl

private theorem mul_self_ne_one_of_ne_one {a : Multiplicative (ZMod 3)} (ha : a ≠ 1) :
    a * a ≠ 1 := by
  rcases mul_zmod_three_cases a with rfl | rfl | rfl
  · exact absurd rfl ha
  · decide
  · decide

private theorem inv_ne_one_of_ne_one {a : Multiplicative (ZMod 3)} (ha : a ≠ 1) :
    a⁻¹ ≠ 1 := by
  intro h
  exact ha (inv_eq_one.mp h)

private theorem mul_mul_inv_exactly_one {a c : Multiplicative (ZMod 3)}
    (ha : a ≠ 1) (hc : c ≠ 1) :
    (a * c = 1 ∧ a * c⁻¹ ≠ 1) ∨ (a * c ≠ 1 ∧ a * c⁻¹ = 1) := by
  rcases eq_or_inv_of_ne_one ha hc with h | h
  · rw [h]
    exact Or.inr ⟨mul_self_ne_one_of_ne_one ha, mul_inv_cancel a⟩
  · rw [h]
    refine Or.inl ⟨mul_inv_cancel a, ?_⟩
    rw [show (a⁻¹)⁻¹ = a from inv_inv a]
    exact mul_self_ne_one_of_ne_one ha

private theorem mul_inv_mul_exactly_one {a c : Multiplicative (ZMod 3)}
    (ha : a ≠ 1) (hc : c ≠ 1) :
    (a * c = 1 ∧ a⁻¹ * c ≠ 1) ∨ (a * c ≠ 1 ∧ a⁻¹ * c = 1) := by
  rcases eq_or_inv_of_ne_one ha hc with h | h
  · rw [h]
    exact Or.inr ⟨mul_self_ne_one_of_ne_one ha, inv_mul_cancel a⟩
  · rw [h]
    refine Or.inl ⟨mul_inv_cancel a, ?_⟩
    have hsq := mul_self_ne_one_of_ne_one ha
    have hinv : (a * a)⁻¹ ≠ 1 := by
      intro h
      exact hsq (inv_eq_one.mp h)
    rw [show a⁻¹ * a⁻¹ = (a * a)⁻¹ from (_root_.mul_inv_rev a a).symm]
    exact hinv

private theorem planeEOp_mapsTo (f : Fin r → Multiplicative (ZMod 3))
    (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : ∀ w ∈ W, spAct (spPlaneTorus (K := K) (r := r) f) w ∈ W) :
    ∀ w ∈ W, planeEOp f w ∈ W := by
  intro w hw
  have hy : spAct (spPlaneTorus (K := K) (r := r) f) w ∈ W := hW w hw
  have hy2 : spAct (spPlaneTorus (K := K) (r := r) f)
      (spAct (spPlaneTorus (K := K) (r := r) f) w) ∈ W := hW _ hy
  simp only [planeEOp, LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply]
  exact W.add_mem (W.add_mem hw hy) hy2

private theorem planeFOp_mapsTo (f : Fin r → Multiplicative (ZMod 3))
    (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : ∀ w ∈ W, spAct (spPlaneTorus (K := K) (r := r) f) w ∈ W) :
    ∀ w ∈ W, planeFOp f w ∈ W := by
  intro w hw
  have hy : spAct (spPlaneTorus (K := K) (r := r) f) w ∈ W := hW w hw
  have hy2 : spAct (spPlaneTorus (K := K) (r := r) f)
      (spAct (spPlaneTorus (K := K) (r := r) f) w) ∈ W := hW _ hy
  simp only [planeFOp, LinearMap.add_apply, pow_two, Module.End.mul_apply]
  exact W.add_mem hy hy2

private theorem planeQ_commute (f g : Fin r → Multiplicative (ZMod 3)) (k : Fin r) :
    Commute (if f k = 1 then planeEOp (K := K) (r := r) f else planeFOp (K := K) (r := r) f)
      (if g k = 1 then planeEOp (K := K) (r := r) g else planeFOp (K := K) (r := r) g) := by
  have h := commute_planeOps (spAct (spPlaneTorus (K := K) (r := r) f))
    (spAct (spPlaneTorus (K := K) (r := r) g)) (spAct_commute_spPlaneTorus f g)
  by_cases hf : f k = 1 <;> by_cases hg : g k = 1 <;> simp [hf, hg]
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

private theorem eq_coord_of_no_exactly_one (Y' : Subgroup (Fin r → Multiplicative (ZMod 3)))
    {k l : Fin r}
    (hk1 : ∀ f ∈ Y', f k = 1 → f l = 1)
    (hl1 : ∀ f ∈ Y', f l = 1 → f k = 1)
    (hno' : ∀ f ∈ Y', ¬ ((f k = 1 ∧ f l ≠ 1) ∨ (f k ≠ 1 ∧ f l = 1)))
    {f0 : Fin r → Multiplicative (ZMod 3)} (hf0 : f0 ∈ Y')
    (h0k : f0 k ≠ 1) (hb : f0 l = f0 k) :
    ∀ f ∈ Y', f k = f l := by
  intro f hf
  by_cases hfk : f k = 1
  · rw [hfk, hk1 f hf hfk]
  · have hfl : f l ≠ 1 := fun h => hfk (hl1 f hf h)
    have hsame : f l = f k := by
      by_contra hne
      have hinv : f l = (f k)⁻¹ := (eq_or_inv_of_ne_one hfk hfl).resolve_left hne
      have hmem : f0 * f ∈ Y' := Y'.mul_mem hf0 hf
      have hcoordk : (f0 * f) k = f0 k * f k := rfl
      have hcoordl : (f0 * f) l = f0 l * f l := rfl
      have hprod := mul_mul_inv_exactly_one h0k hfk
      rw [← hcoordk, ← hb, ← hinv, ← hcoordl] at hprod
      exact hno' (f0 * f) hmem hprod
    exact hsame.symm

private theorem inv_coord_of_no_exactly_one (Y' : Subgroup (Fin r → Multiplicative (ZMod 3)))
    {k l : Fin r}
    (hk1 : ∀ f ∈ Y', f k = 1 → f l = 1)
    (hl1 : ∀ f ∈ Y', f l = 1 → f k = 1)
    (hno' : ∀ f ∈ Y', ¬ ((f k = 1 ∧ f l ≠ 1) ∨ (f k ≠ 1 ∧ f l = 1)))
    {f0 : Fin r → Multiplicative (ZMod 3)} (hf0 : f0 ∈ Y')
    (h0k : f0 k ≠ 1) (hb : f0 l = (f0 k)⁻¹) :
    ∀ f ∈ Y', f k = (f l)⁻¹ := by
  intro f hf
  by_cases hfk : f k = 1
  · rw [hfk, hk1 f hf hfk]
    rfl
  · have hfl : f l ≠ 1 := fun h => hfk (hl1 f hf h)
    have hinv : f l = (f k)⁻¹ := by
      by_contra hne
      have hsame : f l = f k := (eq_or_inv_of_ne_one hfk hfl).resolve_right hne
      have hmem : f0 * f ∈ Y' := Y'.mul_mem hf0 hf
      have hcoordk : (f0 * f) k = f0 k * f k := rfl
      have hcoordl : (f0 * f) l = f0 l * f l := rfl
      have hprod := mul_inv_mul_exactly_one h0k hfk
      rw [← hcoordk, ← hb, ← hsame, ← hcoordl] at hprod
      exact hno' (f0 * f) hmem hprod
    rw [hinv]
    exact (inv_inv (f k)).symm

private theorem eq_or_inv_pair_of_no_exactly_one
    (Y' : Subgroup (Fin r → Multiplicative (ZMod 3))) {k l : Fin r}
    (hk_ne : ∃ f ∈ Y', f k ≠ 1)
    (hno' : ∀ f ∈ Y', ¬ ((f k = 1 ∧ f l ≠ 1) ∨ (f k ≠ 1 ∧ f l = 1))) :
    (∀ f ∈ Y', f k = f l) ∨ (∀ f ∈ Y', f k = (f l)⁻¹) := by
  have hk1 : ∀ f ∈ Y', f k = 1 → f l = 1 := by
    intro f hf h
    by_contra hl
    exact hno' f hf (Or.inl ⟨h, hl⟩)
  have hl1 : ∀ f ∈ Y', f l = 1 → f k = 1 := by
    intro f hf h
    by_contra hk
    exact hno' f hf (Or.inr ⟨hk, h⟩)
  obtain ⟨f0, hf0, h0k⟩ := hk_ne
  have h0l : f0 l ≠ 1 := fun h => h0k (hl1 f0 hf0 h)
  rcases eq_or_inv_of_ne_one h0k h0l with hb | hb
  · exact Or.inl (eq_coord_of_no_exactly_one Y' hk1 hl1 hno' hf0 h0k hb)
  · exact Or.inr (inv_coord_of_no_exactly_one Y' hk1 hl1 hno' hf0 h0k hb)

private theorem exists_exactly_one_one (Y' : Subgroup (Fin r → Multiplicative (ZMod 3)))
    (hnota : ¬ ∃ k, ∀ f ∈ Y', f k = 1)
    (hnotb : ¬ ∃ k l, k ≠ l ∧ ∀ f ∈ Y', f k = f l)
    (hnotc : ¬ ∃ k l, k ≠ l ∧ ∀ f ∈ Y', f k = (f l)⁻¹)
    {k l : Fin r} (hkl : k ≠ l) :
    ∃ f ∈ Y', (f k = 1 ∧ f l ≠ 1) ∨ (f k ≠ 1 ∧ f l = 1) := by
  classical
  by_contra hno
  have hno' : ∀ f ∈ Y', ¬ ((f k = 1 ∧ f l ≠ 1) ∨ (f k ≠ 1 ∧ f l = 1)) := by
    intro f hf h
    exact hno ⟨f, hf, h⟩
  have hk_ne : ∃ f ∈ Y', f k ≠ 1 := by
    by_contra h
    apply hnota
    refine ⟨k, fun f hf => ?_⟩
    by_contra h'
    exact h ⟨f, hf, h'⟩
  rcases eq_or_inv_pair_of_no_exactly_one Y' hk_ne hno' with h | h
  · exact hnotb ⟨k, l, hkl, h⟩
  · exact hnotc ⟨k, l, hkl, h⟩

private noncomputable def planeQFamily (k : Fin r)
    (fOf : Fin r → Fin r → Multiplicative (ZMod 3)) :
    Fin r → Module.End K (Fin r ⊕ Fin r → K) := fun l =>
  if fOf l k = 1 then planeEOp (K := K) (r := r) (fOf l)
  else planeFOp (K := K) (r := r) (fOf l)

private theorem planeQFamily_comm (k : Fin r)
    (fOf : Fin r → Fin r → Multiplicative (ZMod 3)) :
    ((Finset.univ.erase k : Finset (Fin r)) : Set (Fin r)).Pairwise
      (fun a b => Commute (planeQFamily (K := K) (r := r) k fOf a)
        (planeQFamily (K := K) (r := r) k fOf b)) := by
  intro a _ b _ _
  exact planeQ_commute (fOf a) (fOf b) k

private theorem planeQFamily_mapsTo {k : Fin r}
    (Y' : Subgroup (Fin r → Multiplicative (ZMod 3)))
    {fOf : Fin r → Fin r → Multiplicative (ZMod 3)}
    (hfOf : ∀ l (_hl : l ≠ k), fOf l ∈ Y' ∧
      ((fOf l k = 1 ∧ fOf l l ≠ 1) ∨ (fOf l k ≠ 1 ∧ fOf l l = 1)))
    (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : ∀ f ∈ Y', ∀ w ∈ W, spAct (spPlaneTorus (K := K) (r := r) f) w ∈ W) :
    ∀ l ∈ Finset.univ.erase k, ∀ w ∈ W, planeQFamily (K := K) (r := r) k fOf l w ∈ W := by
  intro l hl w hw
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  have hmem : fOf l ∈ Y' := (hfOf l hlk).1
  dsimp [planeQFamily]
  by_cases hfk : fOf l k = 1
  · rw [if_pos hfk]
    exact planeEOp_mapsTo (fOf l) W (hW (fOf l) hmem) w hw
  · rw [if_neg hfk]
    exact planeFOp_mapsTo (fOf l) W (hW (fOf l) hmem) w hw

private theorem planeQFamily_fix (k : Fin r)
    (fOf : Fin r → Fin r → Multiplicative (ZMod 3)) :
    ∀ l ∈ Finset.univ.erase k, ∀ u,
      planeQFamily (K := K) (r := r) k fOf l (planeBlockIncl k u) = planeBlockIncl k u := by
  intro l hl u
  dsimp [planeQFamily]
  by_cases hfk : fOf l k = 1
  · rw [if_pos hfk]; exact planeEOp_fix_of_eq_one hfk u
  · rw [if_neg hfk]; exact planeFOp_fix_of_ne_one hfk u

private theorem planeQFamily_kill {k : Fin r}
    (Y' : Subgroup (Fin r → Multiplicative (ZMod 3)))
    {fOf : Fin r → Fin r → Multiplicative (ZMod 3)}
    (hfOf : ∀ l (_hl : l ≠ k), fOf l ∈ Y' ∧
      ((fOf l k = 1 ∧ fOf l l ≠ 1) ∨ (fOf l k ≠ 1 ∧ fOf l l = 1))) :
    ∀ l ∈ Finset.univ.erase k, ∀ u,
      planeQFamily (K := K) (r := r) k fOf l (planeBlockIncl l u) = 0 := by
  intro l hl u
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  have hspec := (hfOf l hlk).2
  dsimp [planeQFamily]
  by_cases hfk : fOf l k = 1
  · rw [if_pos hfk]
    have hll : fOf l l ≠ 1 := by
      rcases hspec with h | h
      · exact h.2
      · exact absurd hfk h.1
    exact planeEOp_kill_of_ne_one hll u
  · rw [if_neg hfk]
    have hll : fOf l l = 1 := by
      rcases hspec with h | h
      · exact absurd h.1 hfk
      · exact h.2
    exact planeFOp_kill_of_eq_one hll u

private theorem planeBlockProj_mapsTo_of_not_cases
    (Y' : Subgroup (Fin r → Multiplicative (ZMod 3)))
    (hnota : ¬ ∃ k, ∀ f ∈ Y', f k = 1)
    (hnotb : ¬ ∃ k l, k ≠ l ∧ ∀ f ∈ Y', f k = f l)
    (hnotc : ¬ ∃ k l, k ≠ l ∧ ∀ f ∈ Y', f k = (f l)⁻¹)
    (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : ∀ f ∈ Y', ∀ w ∈ W, spAct (spPlaneTorus (K := K) (r := r) f) w ∈ W)
    (k : Fin r) :
    ∀ w ∈ W, planeBlockProj (K := K) k w ∈ W := by
  classical
  let fOf : (l : Fin r) → Fin r → Multiplicative (ZMod 3) := fun l =>
    if h : l = k then fun _ => 1
    else Classical.choose (exists_exactly_one_one Y' hnota hnotb hnotc (Ne.symm h))
  have hfOf : ∀ l (hl : l ≠ k), fOf l ∈ Y' ∧
      ((fOf l k = 1 ∧ fOf l l ≠ 1) ∨ (fOf l k ≠ 1 ∧ fOf l l = 1)) := by
    intro l hl
    dsimp [fOf]
    rw [dif_neg hl]
    exact Classical.choose_spec (exists_exactly_one_one Y' hnota hnotb hnotc (Ne.symm hl))
  let Q := planeQFamily (K := K) (r := r) k fOf
  have hcomm := planeQFamily_comm (K := K) (r := r) k fOf
  have hQmaps := planeQFamily_mapsTo Y' hfOf W hW
  have hQfix := planeQFamily_fix (K := K) (r := r) k fOf
  have hQkill := planeQFamily_kill (K := K) (r := r) Y' hfOf
  have hprod := noncommProd_eq_planeBlockProj k Q hcomm hQfix hQkill
  have hRmaps : ∀ w ∈ W, (Finset.univ.erase k).noncommProd Q hcomm w ∈ W :=
    finset_noncommProd_mapsTo _ W Q hcomm hQmaps
  intro w hw
  rw [← hprod]
  exact hRmaps w hw

private def planeJ : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

private theorem form_planeBlockIncl (k : Fin r) (u w : Fin 2 → K) :
    planeBlockIncl k u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ planeBlockIncl k w) =
      u ⬝ᵥ (planeJ (K := K) *ᵥ w) := by
  simp [planeBlockIncl, planeJ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks, Fin.sum_univ_two, CharTwo.neg_eq]

private theorem quadForm_pos [Finite K] (hK : Nat.card K = 2) (u : Fin 2 → K) (hu : u ≠ 0) :
    u 0 * u 0 + u 0 * u 1 + u 1 * u 1 = 1 := by
  have h0 := CFSG.ClassicalGroups.Alternating.eq_zero_or_eq_one_of_card_eq_two hK (u 0)
  have h1 := CFSG.ClassicalGroups.Alternating.eq_zero_or_eq_one_of_card_eq_two hK (u 1)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0, h1, CharTwo.add_self_eq_zero]
  exfalso
  apply hu
  funext i
  fin_cases i <;> simp [h0, h1]

private theorem planeJ_tPow_mulVec (a : Multiplicative (ZMod 3)) (ha : a ≠ 1)
    (u : Fin 2 → K) :
    u ⬝ᵥ (planeJ (K := K) *ᵥ
      (((tPow (K := K) a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u)) =
      u 0 * u 0 + u 0 * u 1 + u 1 * u 1 := by
  rcases mul_zmod_three_cases a with rfl | rfl | rfl
  · exact absurd rfl ha
  · rw [tPow_ofAdd_one]
    change u ⬝ᵥ ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) *ᵥ
      ((!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) *ᵥ u)) =
      u 0 * u 0 + u 0 * u 1 + u 1 * u 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · rw [tPow_ofAdd_two, Units.val_pow_eq_pow_val]
    change u ⬝ᵥ ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (((!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) ^ 2) *ᵥ u)) =
      u 0 * u 0 + u 0 * u 1 + u 1 * u 1
    rw [show (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      !![1, 1; 1, 0] from tGL_matrix_sq]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

private theorem eq_bot_of_not_cases (hfin : Finite K) (hK : Nat.card K = 2)
    (Y' : Subgroup (Fin r → Multiplicative (ZMod 3)))
    (hnota : ¬ ∃ k, ∀ f ∈ Y', f k = 1)
    {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hWiso : ∀ u ∈ W, ∀ v ∈ W, u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) = 0)
    (hWY : ∀ f ∈ Y', ∀ w ∈ W, spAct (spPlaneTorus (K := K) (r := r) f) w ∈ W)
    (hproj : ∀ k, ∀ w ∈ W, planeBlockProj (K := K) k w ∈ W) :
    W = ⊥ := by
  refine (Submodule.eq_bot_iff W).mpr fun w hw => ?_
  by_contra hw0
  have hsum : (∑ k : Fin r, planeBlockProj (K := K) k w) = w := by
    have h := congrArg (fun f : Module.End K (Fin r ⊕ Fin r → K) => f w)
      (planeBlockProj_sum (K := K) (r := r))
    simpa only [LinearMap.sum_apply, Module.End.one_apply, Finset.sum_apply] using h
  have hex : ∃ k, planeBlockProj (K := K) k w ≠ 0 := by
    by_contra h
    apply hw0
    rw [← hsum]
    exact Finset.sum_eq_zero fun k _ => by
      by_contra hk
      exact h ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hex
  have hfk_exists : ∃ f ∈ Y', f k ≠ 1 := by
    by_contra h
    apply hnota
    refine ⟨k, fun f hf => ?_⟩
    by_contra h'
    exact h ⟨f, hf, h'⟩
  obtain ⟨f, hf, hfk⟩ := hfk_exists
  obtain ⟨u, hu_eq⟩ := planeBlockProj_mem (K := K) k w
  have hvW : planeBlockIncl k u ∈ W := by rw [hu_eq]; exact hproj k w hw
  have hk_u : planeBlockIncl k u ≠ 0 := by rw [hu_eq]; exact hk
  have hu : u ≠ 0 := fun hu0 => hk_u (by rw [hu0, map_zero])
  have hyvW : spAct (spPlaneTorus (K := K) (r := r) f) (planeBlockIncl k u) ∈ W :=
    hWY f hf _ hvW
  have hform := hWiso (planeBlockIncl k u) hvW
    (spAct (spPlaneTorus (K := K) (r := r) f) (planeBlockIncl k u)) hyvW
  rw [spPlaneTorus_planeBlockIncl, form_planeBlockIncl] at hform
  rw [planeJ_tPow_mulVec (f k) hfk u, @quadForm_pos K _ _ hfin hK u hu] at hform
  exact one_ne_zero hform

private theorem planeInv_normalizes (k : Fin r) :
    ∀ t ∈ (spPlaneTorus (K := K) (r := r)).range,
      planeInv (K := K) k * t * (planeInv (K := K) k)⁻¹ ∈
        (spPlaneTorus (K := K) (r := r)).range := by
  rintro t ⟨f, rfl⟩
  rw [planeInv_conj_spPlaneTorus]
  exact ⟨_, rfl⟩

private theorem planePerm_normalizes (σ : Equiv.Perm (Fin r)) :
    ∀ t ∈ (spPlaneTorus (K := K) (r := r)).range,
      planePerm (K := K) σ * t * (planePerm (K := K) σ)⁻¹ ∈
        (spPlaneTorus (K := K) (r := r)).range := by
  rintro t ⟨f, rfl⟩
  rw [planePerm_conj_spPlaneTorus]
  exact ⟨_, rfl⟩

private theorem exists_involution_case_coord
    {Y : Subgroup (CFSG.Open.StatedSp r K)}
    (hY : Y ≤ (spPlaneTorus (K := K) (r := r)).range) {k : Fin r}
    (ha : ∀ f : Fin r → Multiplicative (ZMod 3),
      spPlaneTorus (K := K) (r := r) f ∈ Y → f k = 1) :
    ∃ P : CFSG.Open.StatedSp r K, P * P = 1 ∧
      (∀ t ∈ (spPlaneTorus (K := K) (r := r)).range,
        P * t * P⁻¹ ∈ (spPlaneTorus (K := K) (r := r)).range) ∧
      (∀ y ∈ Y, P * y = y * P) ∧
      ∃ t ∈ (spPlaneTorus (K := K) (r := r)).range, P * t ≠ t * P := by
  classical
  refine ⟨planeInv k, planeInv_mul_self k, planeInv_normalizes k, ?_, ?_⟩
  · intro y hy
    obtain ⟨f, hf⟩ := hY hy
    have hfk : f k = 1 := ha f (hf ▸ hy)
    have hconj : planeInv (K := K) k * y * (planeInv (K := K) k)⁻¹ = y := by
      rw [← hf, planeInv_conj_spPlaneTorus]
      congr 1
      funext j
      by_cases hjk : j = k
      · subst hjk
        rw [Function.update_self, hfk]
        exact inv_one
      · simp [Function.update_of_ne hjk]
    exact commute_of_conj_eq hconj
  · let g : Fin r → Multiplicative (ZMod 3) := Pi.mulSingle k (Multiplicative.ofAdd 1)
    refine ⟨spPlaneTorus g, ⟨g, rfl⟩, ?_⟩
    intro hcomm
    have hconj : planeInv (K := K) k * spPlaneTorus g * (planeInv (K := K) k)⁻¹ =
        spPlaneTorus g := by
      calc planeInv (K := K) k * spPlaneTorus g * (planeInv (K := K) k)⁻¹
          = (spPlaneTorus g * planeInv (K := K) k) * (planeInv (K := K) k)⁻¹ := by
            rw [hcomm]
        _ = spPlaneTorus g := by group
    rw [planeInv_conj_spPlaneTorus] at hconj
    have hg_eq := spPlaneTorus_injective hconj
    have hk := congrFun hg_eq k
    simp [g, Function.update_self] at hk
    exact (by decide : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 3))⁻¹ ≠
      Multiplicative.ofAdd 1) hk

private theorem planePerm_swap_mul_self {k l : Fin r} :
    planePerm (K := K) (Equiv.swap k l) * planePerm (K := K) (Equiv.swap k l) = 1 := by
  have hswap : Equiv.swap k l * Equiv.swap k l = 1 := by
    ext x
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_self, Equiv.Perm.one_apply]
  rw [← map_mul, hswap, map_one]

private theorem planePerm_swap_not_centralizes {k l : Fin r} (hkl : k ≠ l) :
    ∃ t ∈ (spPlaneTorus (K := K) (r := r)).range,
      planePerm (K := K) (Equiv.swap k l) * t ≠ t * planePerm (K := K) (Equiv.swap k l) := by
  classical
  let σ : Equiv.Perm (Fin r) := Equiv.swap k l
  let g : Fin r → Multiplicative (ZMod 3) := Pi.mulSingle k (Multiplicative.ofAdd 1)
  have hg : g ∘ σ.symm ≠ g := by
    intro h
    have hk := congrFun h l
    rw [Function.comp_apply] at hk
    dsimp [σ] at hk
    rw [Equiv.swap_apply_right] at hk
    dsimp [g] at hk
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hkl)] at hk
    exact (by decide : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 3)) ≠ 1) hk
  refine ⟨spPlaneTorus g, ⟨g, rfl⟩, ?_⟩
  intro hcomm
  have hconj : planePerm (K := K) σ * spPlaneTorus g * (planePerm (K := K) σ)⁻¹ =
      spPlaneTorus g := by
    calc planePerm (K := K) σ * spPlaneTorus g * (planePerm (K := K) σ)⁻¹
        = (spPlaneTorus g * planePerm (K := K) σ) * (planePerm (K := K) σ)⁻¹ := by
          rw [hcomm]
      _ = spPlaneTorus g := by group
  rw [planePerm_conj_spPlaneTorus] at hconj
  exact hg (spPlaneTorus_injective hconj)

private theorem exists_involution_case_equal
    {Y : Subgroup (CFSG.Open.StatedSp r K)}
    (hY : Y ≤ (spPlaneTorus (K := K) (r := r)).range) {k l : Fin r} (hkl : k ≠ l)
    (hb : ∀ f : Fin r → Multiplicative (ZMod 3),
      spPlaneTorus (K := K) (r := r) f ∈ Y → f k = f l) :
    ∃ P : CFSG.Open.StatedSp r K, P * P = 1 ∧
      (∀ t ∈ (spPlaneTorus (K := K) (r := r)).range,
        P * t * P⁻¹ ∈ (spPlaneTorus (K := K) (r := r)).range) ∧
      (∀ y ∈ Y, P * y = y * P) ∧
      ∃ t ∈ (spPlaneTorus (K := K) (r := r)).range, P * t ≠ t * P := by
  classical
  let σ : Equiv.Perm (Fin r) := Equiv.swap k l
  refine ⟨planePerm σ, planePerm_swap_mul_self, planePerm_normalizes σ, ?_, ?_⟩
  · intro y hy
    obtain ⟨f, hf⟩ := hY hy
    have hfk : f k = f l := hb f (hf ▸ hy)
    have hconj : planePerm (K := K) σ * y * (planePerm (K := K) σ)⁻¹ = y := by
      rw [← hf, planePerm_conj_spPlaneTorus]
      congr 1
      funext j
      rw [Function.comp_apply]
      dsimp [σ]
      by_cases hjk : j = k
      · subst hjk
        rw [Equiv.swap_apply_left]
        exact hfk.symm
      · by_cases hjl : j = l
        · subst hjl
          rw [Equiv.swap_apply_right]
          exact hfk
        · rw [Equiv.swap_apply_of_ne_of_ne hjk hjl]
    exact commute_of_conj_eq hconj
  · exact planePerm_swap_not_centralizes hkl

private theorem planePerm_conj_planeInv (σ : Equiv.Perm (Fin r)) (k : Fin r) :
    planePerm (K := K) σ * planeInv (K := K) k * (planePerm (K := K) σ)⁻¹ =
      planeInv (K := K) (σ k) := by
  apply Subtype.ext
  change (planePermGL (K := K) σ * planeInvGL (K := K) k *
    (planePermGL (K := K) σ)⁻¹ : GL (Fin r ⊕ Fin r) K) = planeInvGL (K := K) (σ k)
  exact planePermGL_conj_planeInvGL σ k

private theorem planeInvSwap_mul_self {k l : Fin r} :
    (planePerm (K := K) (Equiv.swap k l) * planeInv (K := K) k * planeInv (K := K) l) *
      (planePerm (K := K) (Equiv.swap k l) * planeInv (K := K) k * planeInv (K := K) l) = 1 := by
  set S := planePerm (K := K) (Equiv.swap k l)
  set A := planeInv (K := K) k
  set B := planeInv (K := K) l
  have hSAS : S * A * S⁻¹ = B := by
    simpa [S, A, B, Equiv.swap_apply_left] using planePerm_conj_planeInv (Equiv.swap k l) k
  have hSBS : S * B * S⁻¹ = A := by
    simpa [S, A, B, Equiv.swap_apply_right] using planePerm_conj_planeInv (Equiv.swap k l) l
  have hSA : S * A = B * S := by
    calc S * A = (S * A * S⁻¹) * S := by group
      _ = B * S := by rw [hSAS]
  have hSB : S * B = A * S := by
    calc S * B = (S * B * S⁻¹) * S := by group
      _ = A * S := by rw [hSBS]
  have hSS : S * S = 1 := planePerm_swap_mul_self
  have hAA : A * A = 1 := planeInv_mul_self k
  have hBB : B * B = 1 := planeInv_mul_self l
  calc (S * A * B) * (S * A * B) = S * A * (B * S) * A * B := by group
    _ = S * A * (S * A) * A * B := by rw [hSA]
    _ = S * (A * S) * A * A * B := by group
    _ = S * (S * B) * A * A * B := by rw [hSB]
    _ = (S * S) * (B * (A * A) * B) := by group
    _ = B * (A * A) * B := by rw [hSS, one_mul]
    _ = B * B := by rw [hAA, mul_one]
    _ = 1 := hBB

private theorem update_inv_swap_eq {f : Fin r → Multiplicative (ZMod 3)} {k l : Fin r}
    (hkl : k ≠ l) (hf : f k = (f l)⁻¹) :
    (Function.update (Function.update f l (f l)⁻¹) k
      ((Function.update f l (f l)⁻¹) k)⁻¹) ∘ (Equiv.swap k l).symm = f := by
  funext j
  rw [Function.comp_apply, Equiv.symm_swap]
  by_cases hjk : j = k
  · subst hjk
    rw [Equiv.swap_apply_left]
    simp [Function.update_of_ne (Ne.symm hkl), hf]
  · by_cases hjl : j = l
    · subst hjl
      rw [Equiv.swap_apply_right]
      simp [Function.update_of_ne (Ne.symm hjk), hf]
      exact inv_inv (f j)
    · rw [Equiv.swap_apply_of_ne_of_ne hjk hjl]
      simp [Function.update_of_ne hjk, Function.update_of_ne hjl]

private theorem planeInvSwap_centralizes {k l : Fin r} (hkl : k ≠ l)
    {f : Fin r → Multiplicative (ZMod 3)} (hf : f k = (f l)⁻¹) :
    (planePerm (K := K) (Equiv.swap k l) * planeInv (K := K) k * planeInv (K := K) l) *
        spPlaneTorus (K := K) (r := r) f *
        (planePerm (K := K) (Equiv.swap k l) * planeInv (K := K) k * planeInv (K := K) l)⁻¹ =
      spPlaneTorus (K := K) (r := r) f := by
  set S := planePerm (K := K) (Equiv.swap k l)
  set A := planeInv (K := K) k
  set B := planeInv (K := K) l
  let f1 : Fin r → Multiplicative (ZMod 3) := Function.update f l (f l)⁻¹
  let f2 : Fin r → Multiplicative (ZMod 3) := Function.update f1 k (f1 k)⁻¹
  have hB : B * spPlaneTorus (K := K) (r := r) f * B⁻¹ = spPlaneTorus (K := K) (r := r) f1 := by
    simpa [B, f1] using planeInv_conj_spPlaneTorus l f
  have hA : A * spPlaneTorus (K := K) (r := r) f1 * A⁻¹ =
      spPlaneTorus (K := K) (r := r) f2 := by
    simpa [A, f2] using planeInv_conj_spPlaneTorus k f1
  have hS : S * spPlaneTorus (K := K) (r := r) f2 * S⁻¹ =
      spPlaneTorus (K := K) (r := r) (f2 ∘ (Equiv.swap k l).symm) := by
    simpa [S] using planePerm_conj_spPlaneTorus (Equiv.swap k l) f2
  calc (S * A * B) * spPlaneTorus (K := K) (r := r) f * (S * A * B)⁻¹
      = S * (A * (B * spPlaneTorus (K := K) (r := r) f * B⁻¹) * A⁻¹) * S⁻¹ := by group
    _ = S * (A * spPlaneTorus (K := K) (r := r) f1 * A⁻¹) * S⁻¹ := by rw [hB]
    _ = S * spPlaneTorus (K := K) (r := r) f2 * S⁻¹ := by rw [hA]
    _ = spPlaneTorus (K := K) (r := r) (f2 ∘ (Equiv.swap k l).symm) := hS
    _ = spPlaneTorus (K := K) (r := r) f := by
      congr 1
      simpa [f1, f2] using update_inv_swap_eq hkl hf

private theorem planeInvSwap_not_centralizes {k l : Fin r} (hkl : k ≠ l) :
    ∃ t ∈ (spPlaneTorus (K := K) (r := r)).range,
      (planePerm (K := K) (Equiv.swap k l) * planeInv (K := K) k * planeInv (K := K) l) * t ≠
        t * (planePerm (K := K) (Equiv.swap k l) * planeInv (K := K) k * planeInv (K := K) l) := by
  classical
  set S := planePerm (K := K) (Equiv.swap k l)
  set A := planeInv (K := K) k
  set B := planeInv (K := K) l
  let g : Fin r → Multiplicative (ZMod 3) := Pi.mulSingle k (Multiplicative.ofAdd 1)
  let f1 : Fin r → Multiplicative (ZMod 3) := Function.update g l (g l)⁻¹
  let f2 : Fin r → Multiplicative (ZMod 3) := Function.update f1 k (f1 k)⁻¹
  have hB : B * spPlaneTorus (K := K) (r := r) g * B⁻¹ = spPlaneTorus (K := K) (r := r) f1 := by
    simpa [B, f1] using planeInv_conj_spPlaneTorus l g
  have hA : A * spPlaneTorus (K := K) (r := r) f1 * A⁻¹ =
      spPlaneTorus (K := K) (r := r) f2 := by
    simpa [A, f2] using planeInv_conj_spPlaneTorus k f1
  have hS : S * spPlaneTorus (K := K) (r := r) f2 * S⁻¹ =
      spPlaneTorus (K := K) (r := r) (f2 ∘ (Equiv.swap k l).symm) := by
    simpa [S] using planePerm_conj_spPlaneTorus (Equiv.swap k l) f2
  refine ⟨spPlaneTorus (K := K) (r := r) g, ⟨g, rfl⟩, ?_⟩
  intro hcomm
  have hstep : (S * A * B) * spPlaneTorus (K := K) (r := r) g * (S * A * B)⁻¹ =
      spPlaneTorus (K := K) (r := r) (f2 ∘ (Equiv.swap k l).symm) := by
    calc (S * A * B) * spPlaneTorus (K := K) (r := r) g * (S * A * B)⁻¹
        = S * (A * (B * spPlaneTorus (K := K) (r := r) g * B⁻¹) * A⁻¹) * S⁻¹ := by group
      _ = S * (A * spPlaneTorus (K := K) (r := r) f1 * A⁻¹) * S⁻¹ := by rw [hB]
      _ = S * spPlaneTorus (K := K) (r := r) f2 * S⁻¹ := by rw [hA]
      _ = spPlaneTorus (K := K) (r := r) (f2 ∘ (Equiv.swap k l).symm) := hS
  have hconj : (S * A * B) * spPlaneTorus (K := K) (r := r) g * (S * A * B)⁻¹ =
      spPlaneTorus (K := K) (r := r) g := by
    calc (S * A * B) * spPlaneTorus (K := K) (r := r) g * (S * A * B)⁻¹
        = (spPlaneTorus (K := K) (r := r) g * (S * A * B)) * (S * A * B)⁻¹ := by rw [hcomm]
      _ = spPlaneTorus (K := K) (r := r) g := by group
  have hfun : f2 ∘ (Equiv.swap k l).symm = g :=
    spPlaneTorus_injective (hstep.symm.trans hconj)
  have hk := congrFun hfun k
  rw [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left] at hk
  dsimp [f2, f1, g] at hk
  rw [Function.update_of_ne (Ne.symm hkl), Function.update_self,
    Pi.mulSingle_eq_of_ne (Ne.symm hkl), Pi.mulSingle_eq_same] at hk
  exact (by decide : (1 : Multiplicative (ZMod 3)) ≠ Multiplicative.ofAdd 1)
    (inv_one.symm.trans hk)

private theorem exists_involution_case_inverse
    {Y : Subgroup (CFSG.Open.StatedSp r K)}
    (hY : Y ≤ (spPlaneTorus (K := K) (r := r)).range) {k l : Fin r} (hkl : k ≠ l)
    (hc : ∀ f : Fin r → Multiplicative (ZMod 3),
      spPlaneTorus (K := K) (r := r) f ∈ Y → f k = (f l)⁻¹) :
    ∃ P : CFSG.Open.StatedSp r K, P * P = 1 ∧
      (∀ t ∈ (spPlaneTorus (K := K) (r := r)).range,
        P * t * P⁻¹ ∈ (spPlaneTorus (K := K) (r := r)).range) ∧
      (∀ y ∈ Y, P * y = y * P) ∧
      ∃ t ∈ (spPlaneTorus (K := K) (r := r)).range, P * t ≠ t * P := by
  refine ⟨planePerm (Equiv.swap k l) * planeInv k * planeInv l,
    planeInvSwap_mul_self (K := K), ?_, ?_,
    planeInvSwap_not_centralizes (K := K) (r := r) hkl⟩
  · exact normalizes_mul (normalizes_mul (planePerm_normalizes (Equiv.swap k l))
      (planeInv_normalizes k)) (planeInv_normalizes l)
  · intro y hy
    obtain ⟨f, hf⟩ := hY hy
    have hconj := planeInvSwap_centralizes (K := K) (r := r) hkl (hc f (hf ▸ hy))
    rw [hf] at hconj
    exact commute_of_conj_eq hconj

theorem exists_involution_of_isotropic (hK : Nat.card K = 2)
    {Y : Subgroup (CFSG.Open.StatedSp r K)} (hY : Y ≤ (spPlaneTorus (K := K) (r := r)).range)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hW : W ≠ ⊥)
    (hWiso : ∀ u ∈ W, ∀ v ∈ W,
      u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) = 0)
    (hWY : ∀ y ∈ Y, ∀ w ∈ W,
      ((y : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w ∈ W) :
    ∃ P : CFSG.Open.StatedSp r K, P * P = 1 ∧
      (∀ t ∈ (spPlaneTorus (K := K) (r := r)).range,
        P * t * P⁻¹ ∈ (spPlaneTorus (K := K) (r := r)).range) ∧
      (∀ y ∈ Y, P * y = y * P) ∧
      ∃ t ∈ (spPlaneTorus (K := K) (r := r)).range, P * t ≠ t * P := by
  classical
  let Y' : Subgroup (Fin r → Multiplicative (ZMod 3)) :=
    Y.comap (spPlaneTorus (K := K) (r := r))
  have hmem : ∀ f : Fin r → Multiplicative (ZMod 3), f ∈ Y' ↔ spPlaneTorus f ∈ Y :=
    fun f => Subgroup.mem_comap
  by_cases ha : ∃ k, ∀ f ∈ Y', f k = 1
  · obtain ⟨k, hk⟩ := ha
    exact exists_involution_case_coord hY fun f hf => hk f ((hmem f).mpr hf)
  by_cases hb : ∃ k l, k ≠ l ∧ ∀ f ∈ Y', f k = f l
  · obtain ⟨k, l, hkl, hklf⟩ := hb
    exact exists_involution_case_equal hY hkl fun f hf => hklf f ((hmem f).mpr hf)
  by_cases hc : ∃ k l, k ≠ l ∧ ∀ f ∈ Y', f k = (f l)⁻¹
  · obtain ⟨k, l, hkl, hklf⟩ := hc
    exact exists_involution_case_inverse hY hkl fun f hf => hklf f ((hmem f).mpr hf)
  · have hWY' : ∀ f ∈ Y', ∀ w ∈ W,
        spAct (spPlaneTorus (K := K) (r := r) f) w ∈ W := by
      intro f hf w hw
      rw [spAct_apply]
      exact hWY (spPlaneTorus f) ((hmem f).mp hf) w hw
    have hproj : ∀ k, ∀ w ∈ W, planeBlockProj (K := K) k w ∈ W :=
      fun k => planeBlockProj_mapsTo_of_not_cases Y' ha hb hc W hWY' k
    have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    exact absurd (eq_bot_of_not_cases hfin hK Y' ha hWiso hWY' hproj) hW

end

end TwoThree

end CFSG.StandardType
