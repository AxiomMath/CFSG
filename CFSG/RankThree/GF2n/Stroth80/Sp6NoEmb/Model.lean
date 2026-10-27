module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalLevi
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
open CFSG.QuasithinUnique.Setup.SL2Modules (uElt lElt dElt)
open scoped MatrixGroups

variable {K : Type} [Field K]

abbrev mat (g : StatedSp 3 K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  ((g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)

theorem mat_mul (g h : StatedSp 3 K) : mat (g * h) = mat g * mat h := rfl

theorem mat_injective : Function.Injective (mat (K := K)) := fun _ _ e => Subtype.ext (Units.ext e)

@[expose] noncomputable def slotSL (l : Fin 3) : SL(2, K) →* StatedSp 3 K :=
  block.comp (MonoidHom.mulSingle (fun _ : Fin 3 => SL(2, K)) l)

theorem slotSL_apply (l : Fin 3) (g : SL(2, K)) : slotSL l g = block (Pi.mulSingle l g) := rfl

@[expose] noncomputable def dSlot (l : Fin 3) (c : Kˣ) : StatedSp 3 K := slotSL l (dElt c)

theorem slotSL_commute {l m : Fin 3} (hlm : l ≠ m) (g h : SL(2, K)) :
    Commute (slotSL l g) (slotSL m h) := by
  rw [slotSL_apply, slotSL_apply, Commute, SemiconjBy, ← map_mul, ← map_mul]
  congr 1
  funext i
  by_cases hil : i = l
  · subst hil
    simp [Pi.mulSingle_apply, hlm]
  · by_cases him : i = m
    · subst him
      simp [Pi.mulSingle_apply, hil]
    · simp [Pi.mulSingle_apply, hil, him]

@[expose] noncomputable def levi : GL (Fin 3) K →* StatedSp 3 K where
  toFun A := leviSp (A : Matrix (Fin 3) (Fin 3) K) ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_leviSp]
    simp [fromBlocks_one]
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    change fromBlocks ((A * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0
        (((A * B)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
      fromBlocks (A : Matrix (Fin 3) (Fin 3) K) 0 0 ((A⁻¹ : GL (Fin 3) K) : Matrix _ _ K)ᵀ *
        fromBlocks (B : Matrix (Fin 3) (Fin 3) K) 0 0 ((B⁻¹ : GL (Fin 3) K) : Matrix _ _ K)ᵀ
    rw [fromBlocks_multiply, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.transpose_mul]
    simp

theorem coe_levi (A : GL (Fin 3) K) :
    (((levi A : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      fromBlocks (A : Matrix (Fin 3) (Fin 3) K) 0 0 ((A⁻¹ : GL (Fin 3) K) : Matrix _ _ K)ᵀ :=
  rfl

@[expose] noncomputable def zeta (c : Kˣ) : StatedSp 3 K := levi (Units.map (algebraMap K (Matrix (Fin 3) (Fin 3) K)).toMonoidHom c)

theorem zeta_commute (c : Kˣ) (A : GL (Fin 3) K) : Commute (zeta c) (levi A) := by
  rw [zeta, Commute, SemiconjBy, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  simp [Units.val_mul, Algebra.algebraMap_eq_smul_one]

@[expose] noncomputable def diagGL (τ : Fin 3 → Kˣ) : GL (Fin 3) K :=
  ⟨diagonal fun i => (τ i : K), diagonal fun i => ((τ i)⁻¹ : Kˣ),
    by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩

theorem coe_diagGL (τ : Fin 3 → Kˣ) :
    ((diagGL τ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal fun i => (τ i : K) := rfl

theorem coe_diagGL_inv (τ : Fin 3 → Kˣ) :
    (((diagGL τ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun i => (((τ i)⁻¹ : Kˣ) : K) := rfl

theorem dElt_one : dElt (1 : Kˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dElt]

theorem levi_diagGL (τ : Fin 3 → Kˣ) : levi (diagGL τ) = block fun i => dElt (τ i) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_levi, coe_block, coe_diagGL, coe_diagGL_inv]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;>
    simp [blockMatrix, dElt, hij, diagonal_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂]

theorem dSlot_eq_levi (l : Fin 3) (c : Kˣ) : dSlot l c = levi (diagGL (Pi.mulSingle l c)) := by
  rw [levi_diagGL, dSlot, slotSL_apply]
  congr 1
  funext i
  by_cases hil : i = l
  · subst hil
    simp
  · rw [Pi.mulSingle_apply, Pi.mulSingle_apply, if_neg hil, if_neg hil]
    exact dElt_one.symm

theorem zeta_eq_levi_diagGL (c : Kˣ) : zeta c = levi (diagGL fun _ => c) := by
  rw [zeta]
  congr 1

theorem zeta_eq_mul (c : Kˣ) : zeta c = dSlot 0 c * dSlot 1 c * dSlot 2 c := by
  rw [zeta_eq_levi_diagGL, dSlot_eq_levi, dSlot_eq_levi, dSlot_eq_levi, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, coe_diagGL,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [Pi.mulSingle_apply]

theorem levi_diagGL_commute (τ σ : Fin 3 → Kˣ) : Commute (levi (diagGL τ)) (levi (diagGL σ)) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_diagGL, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

@[expose] noncomputable def rootE {i j : Fin 3} (hij : i ≠ j) (c : K) : StatedSp 3 K :=
  levi (TauCeti.transvectionUnit hij c)

@[expose] def permGL (σ : Equiv.Perm (Fin 3)) : GL (Fin 3) K :=
  ⟨σ.permMatrix K, (σ⁻¹).permMatrix K,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

@[expose] noncomputable def wSwap (i j : Fin 3) : StatedSp 3 K := levi (permGL (Equiv.swap i j))

theorem coe_permGL (σ : Equiv.Perm (Fin 3)) :
    ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = σ.permMatrix K := rfl

theorem coe_permGL_inv (σ : Equiv.Perm (Fin 3)) :
    (((permGL σ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (σ⁻¹).permMatrix K := rfl

theorem permMatrix_mul_diagonal_mul (σ : Equiv.Perm (Fin 3)) (d : Fin 3 → K) :
    σ.permMatrix K * diagonal d * (σ⁻¹).permMatrix K = diagonal (d ∘ σ) := by
  rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  change ((diagonal d).submatrix σ id).submatrix id σ⁻¹.symm = _
  rw [Matrix.submatrix_submatrix]
  have : (σ⁻¹.symm : Fin 3 → Fin 3) = σ := by
    funext x
    rfl
  rw [show ((id : Fin 3 → Fin 3) ∘ σ⁻¹.symm) = σ from this, Function.comp_id]
  exact Matrix.submatrix_diagonal_equiv d σ

theorem levi_permGL_conj_block (σ : Equiv.Perm (Fin 3)) (g : Fin 3 → SL(2, K)) :
    levi (permGL σ) * block g * (levi (permGL σ))⁻¹ = block (g ∘ σ) := by
  apply mat_injective
  rw [mat_mul, mat_mul, ← map_inv]
  simp only [mat, coe_levi, coe_block, inv_inv, coe_permGL, coe_permGL_inv,
    Matrix.transpose_permMatrix]
  unfold blockMatrix
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, inv_inv]
  rw [permMatrix_mul_diagonal_mul, permMatrix_mul_diagonal_mul, permMatrix_mul_diagonal_mul,
    permMatrix_mul_diagonal_mul]
  rfl

theorem wSwap_conj_slotSL (i j : Fin 3) (h : SL(2, K)) :
    wSwap i j * slotSL i h * (wSwap i j)⁻¹ = slotSL j h := by
  rw [wSwap, slotSL_apply, levi_permGL_conj_block, slotSL_apply]
  congr 1
  funext x
  simp only [Function.comp_apply, Pi.mulSingle_apply]
  by_cases hx : x = j
  · subst hx
    simp
  · rw [if_neg hx, if_neg]
    intro h'
    apply hx
    have := congrArg (Equiv.swap i j) h'
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this

theorem coe_mulSingle_apply (l i : Fin 3) (g : SL(2, K)) :
    (((Pi.mulSingle l g : Fin 3 → SL(2, K)) i : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      if i = l then (g : Matrix (Fin 2) (Fin 2) K) else 1 := by
  by_cases h : i = l
  · subst h; simp
  · simp [Pi.mulSingle_apply, h]

theorem mat_slotSL (l : Fin 3) (g : SL(2, K)) :
    mat (slotSL l g) = blockMatrix fun i => if i = l then (g : Matrix (Fin 2) (Fin 2) K) else 1 := by
  rw [mat, slotSL_apply, coe_block]
  congr 1
  funext i
  exact coe_mulSingle_apply l i g

theorem mat_slotSL_uElt (c : K) :
    mat (slotSL 0 (uElt c)) = Matrix.transvection (Sum.inl 0 : Fin 3 ⊕ Fin 3) (Sum.inr 0) c := by
  rw [mat_slotSL]
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, blockMatrix, uElt, Matrix.single_apply, Matrix.one_apply]

theorem mat_slotSL_lElt (c : K) :
    mat (slotSL 0 (lElt c)) = Matrix.transvection (Sum.inr 0 : Fin 3 ⊕ Fin 3) (Sum.inl 0) c := by
  rw [mat_slotSL]
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, blockMatrix, lElt, Matrix.single_apply, Matrix.one_apply]

theorem mat_rootE {i j : Fin 3} (hij : i ≠ j) (c : K) :
    mat (rootE hij c) = Matrix.transvection (Sum.inl i : Fin 3 ⊕ Fin 3) (Sum.inl j) c *
      Matrix.transvection (Sum.inr j : Fin 3 ⊕ Fin 3) (Sum.inr i) (-c) := by
  rw [mat, rootE, coe_levi, TauCeti.transvectionUnit_inv, TauCeti.coe_transvectionUnit,
    TauCeti.coe_transvectionUnit]
  simp only [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul]
  have hz : Matrix.single (Sum.inl i : Fin 3 ⊕ Fin 3) (Sum.inl j) c *
      Matrix.single (Sum.inr j) (Sum.inr i) (-c) = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact Sum.inl_ne_inr
  rw [hz, add_zero]
  ext (a | a) (b | b) <;>
    simp [Matrix.single_apply, Matrix.one_apply, Matrix.add_apply, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂] <;> grind

open TauCeti.GLSymplecticFin in
theorem closure_slot_rootE_eq_top :
    Subgroup.closure (Set.range (slotSL (K := K) 0) ∪
      {g | ∃ (i j : Fin 3) (hij : i ≠ j) (c : K), g = rootE hij c}) = ⊤ := by
  set H := Subgroup.closure (Set.range (slotSL (K := K) 0) ∪
      {g | ∃ (i j : Fin 3) (hij : i ≠ j) (c : K), g = rootE hij c}) with hH
  set e := CFSG.StandardType.GGOppRadSpU.finEquiv (n := 3) (K := K)
  have hcomap : H.comap e.toMonoidHom = ⊤ := by
    apply eq_top_of_root_subgroups
    apply RootSubgroupIndex.hom_apply_mem_of_difference_of_long _ 0
    · intro i j hij c
      show e (differenceShortRootUnit hij c) ∈ H
      have h1 : e (differenceShortRootUnit hij c) = rootE hij c := by
        apply mat_injective
        rw [mat_rootE, mat, CFSG.StandardType.GGOppRadSpU.coe_finEquiv_difference, Units.val_mul,
          TauCeti.coe_transvectionUnit, TauCeti.coe_transvectionUnit]
      rw [h1]
      exact Subgroup.subset_closure (Or.inr ⟨i, j, hij, c, rfl⟩)
    · intro c
      show e (positiveLongRootTransvectionUnit 0 c) ∈ H
      have h1 : e (positiveLongRootTransvectionUnit 0 c) = slotSL 0 (uElt c) := by
        apply mat_injective
        rw [mat_slotSL_uElt, mat, CFSG.StandardType.GGOppRadSpU.coe_finEquiv_positiveLong,
          TauCeti.coe_transvectionUnit]
      rw [h1]
      exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · intro c
      show e (negativeLongRootTransvectionUnit 0 c) ∈ H
      have h1 : e (negativeLongRootTransvectionUnit 0 c) = slotSL 0 (lElt c) := by
        apply mat_injective
        rw [mat_slotSL_lElt, mat, CFSG.StandardType.GGOppRadSpU.coe_finEquiv_negativeLong,
          TauCeti.coe_transvectionUnit]
      rw [h1]
      exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  refine eq_top_iff.mpr fun g _ => ?_
  have hg : e.symm g ∈ H.comap e.toMonoidHom := hcomap ▸ Subgroup.mem_top _
  simpa using hg

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
