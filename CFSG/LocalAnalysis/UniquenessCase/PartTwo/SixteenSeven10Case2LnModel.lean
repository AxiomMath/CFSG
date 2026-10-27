module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenDefs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open scoped TensorProduct

private def s16c1610_a1 : ↥(CFSG.Quasithin.permCore 3) :=
  ⟨![1, 1, 0], by
    show ∑ i, (![1, 1, 0] : Fin 3 → ZMod 2) i = 0
    decide⟩

private def s16c1610_a2 : ↥(CFSG.Quasithin.permCore 3) :=
  ⟨![0, 1, 1], by
    show ∑ i, (![0, 1, 1] : Fin 3 → ZMod 2) i = 0
    decide⟩

private def s16c1610_sigma0 : Equiv.Perm (Fin 3) := finRotate 3

private lemma s16c1610_zmod2_sum_zero (p0 p1 p2 : ZMod 2) (h : p0 + p1 + p2 = 0) :
    p2 = p0 + p1 := by
  revert p0 p1 p2
  decide

private lemma s16c1610_zmod2_add_add_cancel (p q : ZMod 2) : p + (p + q) = q := by
  revert p q
  decide

private lemma s16c1610_a1a2_span :
    ⊤ ≤ Submodule.span (ZMod 2) (Set.range ![s16c1610_a1, s16c1610_a2]) := by
  intro x _
  have hx : x = (x : Fin 3 → ZMod 2) 0 • s16c1610_a1 +
      ((x : Fin 3 → ZMod 2) 0 + (x : Fin 3 → ZMod 2) 1) • s16c1610_a2 := by
    apply Subtype.ext
    funext j
    have hsum : ∑ i, (x : Fin 3 → ZMod 2) i = 0 := x.2
    rw [Fin.sum_univ_three] at hsum
    have h2 := s16c1610_zmod2_sum_zero _ _ _ hsum
    fin_cases j <;> simp [s16c1610_a1, s16c1610_a2, h2, s16c1610_zmod2_add_add_cancel]
  rw [hx]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private noncomputable def s16c1610_basis :
    Module.Basis (Fin 2) (ZMod 2) ↥(CFSG.Quasithin.permCore 3) :=
  Module.Basis.mk (v := ![s16c1610_a1, s16c1610_a2])
    (by
      rw [Fintype.linearIndependent_iffₛ]
      intro f g hfg i
      fin_cases i
      · have h0 := congrFun (congrArg Subtype.val hfg) 0
        simpa [Fin.sum_univ_two, s16c1610_a1, s16c1610_a2] using h0
      · have h0 := congrFun (congrArg Subtype.val hfg) 0
        have h1 := congrFun (congrArg Subtype.val hfg) 1
        simp [Fin.sum_univ_two, s16c1610_a1, s16c1610_a2] at h0 h1
        rw [h0] at h1
        exact add_left_cancel h1)
    s16c1610_a1a2_span

private lemma s16c1610_basis_zero : s16c1610_basis 0 = s16c1610_a1 := by
  simp [s16c1610_basis, Module.Basis.mk_apply]

private lemma s16c1610_basis_one : s16c1610_basis 1 = s16c1610_a2 := by
  simp [s16c1610_basis, Module.Basis.mk_apply]

private lemma s16c1610_permAct_sigma0_a1 :
    CFSG.Quasithin.permAct s16c1610_sigma0 (s16c1610_a1 : Fin 3 → ZMod 2) =
      (s16c1610_a2 : Fin 3 → ZMod 2) := by
  funext i
  fin_cases i <;> decide

private lemma s16c1610_permAct_sigma0_a2 :
    CFSG.Quasithin.permAct s16c1610_sigma0 (s16c1610_a2 : Fin 3 → ZMod 2) =
      (s16c1610_a1 : Fin 3 → ZMod 2) + (s16c1610_a2 : Fin 3 → ZMod 2) := by
  funext i
  fin_cases i <;> decide

private lemma s16c1610_sigma0_pow_three : s16c1610_sigma0 ^ 3 = 1 := by
  decide

private lemma s16c1610_sigma0_ne_one : s16c1610_sigma0 ≠ 1 := by
  decide

private lemma s16c1610_basisFun_linearCombination {m : ℕ} (w : Fin m → ZMod 2) :
    Fintype.linearCombination (ZMod 2) (Pi.basisFun (ZMod 2) (Fin m)) w = w := by
  rw [Fintype.linearCombination_apply]
  conv_rhs => rw [← Module.Basis.sum_repr (Pi.basisFun (ZMod 2) (Fin m)) w]
  simp

private lemma s16c1610_tensor_decomp {m : ℕ}
    (t : ↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) :
    ∃ c₁ c₂ : Fin m → ZMod 2,
      t = s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂ := by
  let b := s16c1610_basis
  let std := Pi.basisFun (ZMod 2) (Fin m)
  let bt := b.tensorProduct std
  refine ⟨fun j => bt.repr t (0, j), fun j => bt.repr t (1, j), ?_⟩
  have hb0 : b 0 = s16c1610_a1 := by rw [show b = s16c1610_basis from rfl, s16c1610_basis_zero]
  have hb1 : b 1 = s16c1610_a2 := by rw [show b = s16c1610_basis from rfl, s16c1610_basis_one]
  have h0 : (∑ j : Fin m, bt.repr t (0, j) • bt (0, j)) =
      s16c1610_a1 ⊗ₜ[ZMod 2] (fun j => bt.repr t (0, j)) := by
    dsimp only [bt, std]
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Module.Basis.tensorProduct_apply, ← TensorProduct.tmul_smul])]
    rw [← TensorProduct.tmul_sum, ← Fintype.linearCombination_apply,
      s16c1610_basisFun_linearCombination, hb0]
  have h1 : (∑ j : Fin m, bt.repr t (1, j) • bt (1, j)) =
      s16c1610_a2 ⊗ₜ[ZMod 2] (fun j => bt.repr t (1, j)) := by
    dsimp only [bt, std]
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Module.Basis.tensorProduct_apply, ← TensorProduct.tmul_smul])]
    rw [← TensorProduct.tmul_sum, ← Fintype.linearCombination_apply,
      s16c1610_basisFun_linearCombination, hb1]
  conv_lhs => rw [← Module.Basis.sum_repr bt t]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, h0, h1]

private lemma s16c1610_zmod2_add_self (p : ZMod 2) : p + p = 0 := by
  revert p
  decide

private lemma s16c1610_add_self_vec {m : ℕ} (x : Fin m → ZMod 2) : x + x = 0 := by
  funext c
  exact s16c1610_zmod2_add_self (x c)

private lemma s16c1610_add_add_comm_cancel {m : ℕ} (x y : Fin m → ZMod 2) :
    y + (x + y) = x := by
  funext c
  show y c + (x c + y c) = x c
  rw [add_comm (x c) (y c), s16c1610_zmod2_add_add_cancel]

private noncomputable def s16c1610_leEquivGL (m : ℕ) :
    ((Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) ≃*
      Matrix.GeneralLinearGroup (Fin m) (ZMod 2) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin m → ZMod 2)).symm.trans
    (Matrix.GeneralLinearGroup.toLin (n := Fin m) (R := ZMod 2)).symm

private lemma s16c1610_leEquivGL_mulVec {m : ℕ}
    (e : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) (v : Fin m → ZMod 2) :
    ((s16c1610_leEquivGL m e : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec v) = e v := by
  have h1 : (Matrix.GeneralLinearGroup.toLin (n := Fin m) (R := ZMod 2)
      (s16c1610_leEquivGL m e) : (Fin m → ZMod 2) → (Fin m → ZMod 2)) = e := by
    rw [s16c1610_leEquivGL, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have h2 := Matrix.GeneralLinearGroup.toLin_apply (A := s16c1610_leEquivGL m e) v
  rw [h1, Matrix.mulVecLin_apply] at h2
  exact h2.symm

private noncomputable def s16c1610_blockALM {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) (i j : I) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  b.constr (ZMod 2) fun k => if k = i then b j else if k = j then b i + b j else b k

private lemma s16c1610_blockALM_apply {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) (i j : I) (k : I) :
    s16c1610_blockALM b i j (b k) =
      (if k = i then b j else if k = j then b i + b j else b k) := by
  simp only [s16c1610_blockALM, Module.Basis.constr_basis]

private lemma s16c1610_blockALM_cube {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) (i j : I) (hij : i ≠ j) :
    (s16c1610_blockALM b i j).comp ((s16c1610_blockALM b i j).comp
      (s16c1610_blockALM b i j)) = LinearMap.id := by
  classical
  have hAi : s16c1610_blockALM b i j (b i) = b j := by
    rw [s16c1610_blockALM_apply]
    simp
  have hAj : s16c1610_blockALM b i j (b j) = b i + b j := by
    rw [s16c1610_blockALM_apply]
    simp [hij, Ne.symm hij]
  have hAk : ∀ k, k ≠ i → k ≠ j → s16c1610_blockALM b i j (b k) = b k := by
    intro k h1 h2
    rw [s16c1610_blockALM_apply]
    simp [h1, h2]
  apply Module.Basis.ext b
  intro k
  change s16c1610_blockALM b i j (s16c1610_blockALM b i j
    (s16c1610_blockALM b i j (b k))) = b k
  by_cases h₁ : k = i
  · subst h₁
    rw [hAi, hAj, map_add, hAi, hAj, s16c1610_add_add_comm_cancel]
  · by_cases h₂ : k = j
    · subst h₂
      rw [hAj, map_add, hAi, hAj, map_add, hAj, map_add, hAi, hAj,
        s16c1610_add_add_comm_cancel]
    · rw [hAk k h₁ h₂, hAk k h₁ h₂, hAk k h₁ h₂]

private noncomputable def s16c1610_blockA {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) (i j : I) (hij : i ≠ j) :
    (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2) :=
  LinearEquiv.ofLinearMap (s16c1610_blockALM b i j)
    ((s16c1610_blockALM b i j).comp (s16c1610_blockALM b i j))
    (s16c1610_blockALM_cube b i j hij)
    (by rw [LinearMap.comp_assoc]; exact s16c1610_blockALM_cube b i j hij)

private lemma s16c1610_blockA_coe {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) :
    (s16c1610_blockA b i j hij : (Fin m → ZMod 2) → (Fin m → ZMod 2)) =
      s16c1610_blockALM b i j :=
  rfl

private lemma s16c1610_blockA_apply_other {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) {k : I}
    (h₁ : k ≠ i) (h₂ : k ≠ j) :
    (s16c1610_blockA b i j hij : (Fin m → ZMod 2) → (Fin m → ZMod 2)) (b k) = b k := by
  rw [s16c1610_blockA_coe, s16c1610_blockALM_apply]
  simp [h₁, h₂]

private lemma s16c1610_blockA_apply_i {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) :
    (s16c1610_blockA b i j hij : (Fin m → ZMod 2) → (Fin m → ZMod 2)) (b i) = b j := by
  rw [s16c1610_blockA_coe, s16c1610_blockALM_apply]
  simp

private lemma s16c1610_blockA_apply_j {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) :
    (s16c1610_blockA b i j hij : (Fin m → ZMod 2) → (Fin m → ZMod 2)) (b j) = b i + b j := by
  rw [s16c1610_blockA_coe, s16c1610_blockALM_apply]
  simp [hij, Ne.symm hij]

private lemma s16c1610_blockA_cube {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) :
    s16c1610_blockA b i j hij ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  change s16c1610_blockALM b i j (s16c1610_blockALM b i j
    (s16c1610_blockALM b i j x)) = x
  have h := congrFun (congrArg DFunLike.coe (s16c1610_blockALM_cube b i j hij)) x
  simpa using h

private lemma s16c1610_blockA_ne_one {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) :
    s16c1610_blockA b i j hij ≠ 1 := by
  intro h
  have h1 : (s16c1610_blockA b i j hij : (Fin m → ZMod 2) → (Fin m → ZMod 2)) (b i) =
      b i := by rw [h]; rfl
  rw [s16c1610_blockA_apply_i] at h1
  exact (b.linearIndependent.injective.ne hij) h1.symm

private noncomputable def s16c1610_glBlockA {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) (i j : I) (hij : i ≠ j) :
    Matrix.GeneralLinearGroup (Fin m) (ZMod 2) :=
  s16c1610_leEquivGL m (s16c1610_blockA b i j hij)

private lemma s16c1610_glBlockA_mulVec_i {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) :
    ((s16c1610_glBlockA b i j hij : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (b i)) = b j := by
  rw [s16c1610_glBlockA, s16c1610_leEquivGL_mulVec, s16c1610_blockA_apply_i]

private lemma s16c1610_glBlockA_mulVec_j {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) :
    ((s16c1610_glBlockA b i j hij : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (b j)) =
      b i + b j := by
  rw [s16c1610_glBlockA, s16c1610_leEquivGL_mulVec, s16c1610_blockA_apply_j]

private lemma s16c1610_glBlockA_pow_three {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) :
    s16c1610_glBlockA b i j hij ^ 3 = 1 := by
  rw [s16c1610_glBlockA, ← map_pow, s16c1610_blockA_cube, map_one]

private lemma s16c1610_glBlockA_ne_one {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) :
    s16c1610_glBlockA b i j hij ≠ 1 := by
  intro h
  rw [s16c1610_glBlockA] at h
  have h' : s16c1610_blockA b i j hij = 1 :=
    (s16c1610_leEquivGL m).injective (h.trans (map_one _).symm)
  exact s16c1610_blockA_ne_one b hij h'

private lemma s16c1610_zmod2_eq_of_add_eq_zero (p q : ZMod 2) (h : p + q = 0) : p = q := by
  revert p q
  decide

private lemma s16c1610_eq_of_add_eq_zero {m : ℕ} {x y : Fin m → ZMod 2} (h : x + y = 0) :
    x = y := by
  funext c
  exact s16c1610_zmod2_eq_of_add_eq_zero (x c) (y c) (congrFun h c)

private lemma s16c1610_glBlockA_mulVec_other {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j : I} (hij : i ≠ j) {k : I}
    (h₁ : k ≠ i) (h₂ : k ≠ j) :
    ((s16c1610_glBlockA b i j hij : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (b k)) = b k := by
  rw [s16c1610_glBlockA, s16c1610_leEquivGL_mulVec, s16c1610_blockA_apply_other b hij h₁ h₂]

private lemma s16c1610_tensor_add_self {m : ℕ}
    (x : ↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) : x + x = 0 := by
  rw [← one_smul (ZMod 2) x, ← add_smul, show (1 + 1 : ZMod 2) = 0 by decide, zero_smul]

private lemma s16c1610_ofAdd_add {α : Type*} [Add α] (x y : α) :
    Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl

private lemma s16c1610_tensor_fix_rank2 {m : ℕ} (c₁ c₂ : Fin m → ZMod 2) :
    s16c1610_a2 ⊗ₜ[ZMod 2] (c₁ + c₂) +
        (s16c1610_a1 + s16c1610_a2) ⊗ₜ[ZMod 2] c₁ =
      s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂ := by
  calc s16c1610_a2 ⊗ₜ[ZMod 2] (c₁ + c₂) + (s16c1610_a1 + s16c1610_a2) ⊗ₜ[ZMod 2] c₁
      = s16c1610_a2 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂ +
          (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₁) := by
        rw [TensorProduct.tmul_add, TensorProduct.add_tmul]
    _ = (s16c1610_a2 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₁) +
          (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂) := by abel
    _ = 0 + (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂) := by
        rw [s16c1610_tensor_add_self]
    _ = s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂ := by rw [zero_add]

private lemma s16c1610_fix_pure {W : Type} [CommGroup W] {G : Subgroup (MulAut W)} {m : ℕ}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin m) (ZMod 2))}
    {ψ : W ≃* Multiplicative (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2))}
    (hcompat : ∀ (γ : ↥G) (a a' : ↥(CFSG.Quasithin.permCore 3)) (c c' : Fin m → ZMod 2),
      (a' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      c' = ((φ γ).2 : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c →
        ψ ((γ : MulAut W) (ψ.symm (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c)))) =
          Multiplicative.ofAdd (a' ⊗ₜ[ZMod 2] c'))
    {a : ↥(CFSG.Quasithin.permCore 3)} {c : Fin m → ZMod 2}
    {g : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)}
    (hg : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c = c) {w : W}
    (hw : ψ w = Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c)) :
    (φ.symm (1, g) : MulAut W) w = w := by
  have hφ : φ (φ.symm (1, g)) = (1, g) := MulEquiv.apply_symm_apply φ _
  have h := hcompat (φ.symm (1, g)) a a c c
    (by rw [hφ]; rfl) (by rw [hφ]; exact hg.symm)
  rw [← hw] at h
  simp only [MulEquiv.symm_apply_apply] at h
  exact ψ.injective h

private lemma s16c1610_fix_rank2 {W : Type} [CommGroup W] {G : Subgroup (MulAut W)} {m : ℕ}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin m) (ZMod 2))}
    {ψ : W ≃* Multiplicative (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2))}
    (hcompat : ∀ (γ : ↥G) (a a' : ↥(CFSG.Quasithin.permCore 3)) (c c' : Fin m → ZMod 2),
      (a' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      c' = ((φ γ).2 : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c →
        ψ ((γ : MulAut W) (ψ.symm (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c)))) =
          Multiplicative.ofAdd (a' ⊗ₜ[ZMod 2] c'))
    {c₁ c₂ : Fin m → ZMod 2} {g : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)}
    (hg₁ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁ = c₁ + c₂)
    (hg₂ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂ = c₁) {w : W}
    (hw : ψ w = Multiplicative.ofAdd
      (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂)) :
    (φ.symm (s16c1610_sigma0, g) : MulAut W) w = w := by
  have hφ : φ (φ.symm (s16c1610_sigma0, g)) = (s16c1610_sigma0, g) :=
    MulEquiv.apply_symm_apply φ _
  have h₁ := hcompat (φ.symm (s16c1610_sigma0, g)) s16c1610_a1 s16c1610_a2 c₁
    ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁)
    (by rw [hφ]; exact s16c1610_permAct_sigma0_a1.symm)
    (by rw [hφ])
  have h₂ := hcompat (φ.symm (s16c1610_sigma0, g)) s16c1610_a2
    (s16c1610_a1 + s16c1610_a2) c₂ ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)
    (by rw [hφ]; exact s16c1610_permAct_sigma0_a2.symm)
    (by rw [hφ])
  have hmain : ψ ((φ.symm (s16c1610_sigma0, g) : MulAut W)
      (ψ.symm (Multiplicative.ofAdd
        (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂)))) =
      Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂) := by
    calc ψ ((φ.symm (s16c1610_sigma0, g) : MulAut W)
          (ψ.symm (Multiplicative.ofAdd
            (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂))))
        = ψ ((φ.symm (s16c1610_sigma0, g) : MulAut W)
            (ψ.symm (Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁)) *
              ψ.symm (Multiplicative.ofAdd (s16c1610_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [s16c1610_ofAdd_add, map_mul]
      _ = ψ ((φ.symm (s16c1610_sigma0, g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁))) *
            (φ.symm (s16c1610_sigma0, g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16c1610_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [map_mul]
      _ = ψ ((φ.symm (s16c1610_sigma0, g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁)))) *
            ψ ((φ.symm (s16c1610_sigma0, g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16c1610_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [map_mul]
      _ = Multiplicative.ofAdd
            (s16c1610_a2 ⊗ₜ[ZMod 2] ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁)) *
            Multiplicative.ofAdd
              ((s16c1610_a1 + s16c1610_a2) ⊗ₜ[ZMod 2]
                ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)) := by
          rw [h₁, h₂]
      _ = Multiplicative.ofAdd
            (s16c1610_a2 ⊗ₜ[ZMod 2] ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁) +
              (s16c1610_a1 + s16c1610_a2) ⊗ₜ[ZMod 2]
                ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)) := by
          rw [s16c1610_ofAdd_add]
      _ = Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ +
            s16c1610_a2 ⊗ₜ[ZMod 2] c₂) := by
          rw [hg₁, hg₂, s16c1610_tensor_fix_rank2]
  have hmain' : ψ ((φ.symm (s16c1610_sigma0, g) : MulAut W) w) = ψ w := by
    have hw' : w = ψ.symm (Multiplicative.ofAdd
        (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂)) := by
      rw [← hw, MulEquiv.symm_apply_apply]
    rw [hw', hmain, MulEquiv.apply_symm_apply]
  exact ψ.injective hmain'

private lemma s16c1610_exists_coord_ne_zero {m : ℕ} {v : Fin m → ZMod 2} (hv : v ≠ 0) :
    ∃ j : Fin m, v j ≠ 0 := by
  by_contra h
  exact hv (funext (fun j => by
    by_contra hj
    exact h ⟨j, hj⟩))

private noncomputable def s16c1610_proj {m : ℕ} (j : Fin m) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj j

private lemma s16c1610_proj_apply {m : ℕ} (j : Fin m) (v : Fin m → ZMod 2) :
    s16c1610_proj j v = v j := rfl

private noncomputable def s16c1610_pairMap {m : ℕ} (c₁ c₂ : Fin m → ZMod 2)
    (f₁ f₂ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun v := v + (f₂ v) • c₁ + ((f₁ + f₂) v) • c₂
  map_add' v w := by
    simp only [map_add, add_smul]
    module
  map_smul' a v := by
    simp only [map_smul, RingHom.id_apply, smul_add, smul_smul]
    module

private lemma s16c1610_exists_rank2Equiv {m : ℕ} {c₁ c₂ : Fin m → ZMod 2}
    (h : LinearIndependent (ZMod 2) ![c₁, c₂]) :
    ∃ e : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2),
      e c₁ = c₁ + c₂ ∧ e c₂ = c₁ ∧ e ^ 3 = 1 := by
  classical
  have hc₁ : c₁ ≠ 0 := h.ne_zero 0
  obtain ⟨j₁, hj₁⟩ := s16c1610_exists_coord_ne_zero hc₁
  let f₁' : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 := (c₁ j₁)⁻¹ • LinearMap.proj j₁
  have hf₁'c₁ : f₁' c₁ = 1 := by
    simp only [f₁', LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hj₁
  let lam : ZMod 2 := f₁' c₂
  let c₂' : Fin m → ZMod 2 := c₂ + lam • c₁
  have hc₂' : c₂' ≠ 0 := by
    intro h0
    have h0' : c₂ + lam • c₁ = 0 := h0
    have hc₂ : c₂ = lam • c₁ := by
      funext i
      exact s16c1610_zmod2_eq_of_add_eq_zero (c₂ i) ((lam • c₁) i)
        (by simpa only [Pi.add_apply, Pi.zero_apply] using congrFun h0' i)
    have hrel : lam • c₁ + c₂ = 0 := by
      rw [hc₂]
      exact s16c1610_add_self_vec (lam • c₁)
    have hf := (Fintype.linearIndependent_iffₛ (R := ZMod 2)).mp h
    have hsum : ∑ i : Fin 2, (![lam, 1] : Fin 2 → ZMod 2) i • ![c₁, c₂] i =
        ∑ i : Fin 2, (![0, 0] : Fin 2 → ZMod 2) i • ![c₁, c₂] i := by
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simpa using hrel
    have h1 := hf ![lam, 1] ![0, 0] hsum 1
    simp at h1
  obtain ⟨j₂, hj₂⟩ := s16c1610_exists_coord_ne_zero hc₂'
  let f₂' : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 := (c₂' j₂)⁻¹ • LinearMap.proj j₂
  have hf₂'c₂' : f₂' c₂' = 1 := by
    simp only [f₂', LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hj₂
  have hf₂'c₂ : f₂' c₂ + (f₂' c₁) * lam = 1 := by
    have h1 : f₂' c₂ + (f₂' c₁) * lam = f₂' c₂' := by
      change f₂' c₂ + (f₂' c₁) * lam = f₂' (c₂ + lam • c₁)
      rw [map_add, map_smul, smul_eq_mul]
      ring_nf <;> reduce_mod_char
    rw [h1, hf₂'c₂']
  let f₂ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 := f₂' + (f₂' c₁) • f₁'
  let f₁ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 := f₁' + lam • f₂
  have hf₂c₁ : f₂ c₁ = 0 := by
    simp only [f₂, LinearMap.add_apply, LinearMap.smul_apply, hf₁'c₁, smul_eq_mul, mul_one]
    ring_nf <;> reduce_mod_char
  have hf₂c₂ : f₂ c₂ = 1 := by
    simp only [f₂, LinearMap.add_apply, LinearMap.smul_apply]
    exact hf₂'c₂
  have hf₁c₁ : f₁ c₁ = 1 := by
    simp only [f₁, LinearMap.add_apply, LinearMap.smul_apply, hf₂c₁, smul_eq_mul, mul_zero,
      add_zero, hf₁'c₁]
  have hf₁c₂ : f₁ c₂ = 0 := by
    simp only [f₁, LinearMap.add_apply, LinearMap.smul_apply, hf₂c₂, smul_eq_mul, mul_one]
    change f₁' c₂ + lam = 0
    rw [show f₁' c₂ = lam from rfl]
    ring_nf <;> reduce_mod_char
  let g : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) := s16c1610_pairMap c₁ c₂ f₁ f₂
  have hgc₁ : g c₁ = c₁ + c₂ := by
    change c₁ + (f₂ c₁) • c₁ + ((f₁ + f₂) c₁) • c₂ = c₁ + c₂
    have h1 : (f₁ + f₂) c₁ = 1 := by rw [LinearMap.add_apply, hf₁c₁, hf₂c₁, add_zero]
    rw [hf₂c₁, h1, zero_smul, one_smul, add_zero]
  have hgc₂ : g c₂ = c₁ := by
    change c₂ + (f₂ c₂) • c₁ + ((f₁ + f₂) c₂) • c₂ = c₁
    have h1 : (f₁ + f₂) c₂ = 1 := by rw [LinearMap.add_apply, hf₁c₂, hf₂c₂, zero_add]
    rw [hf₂c₂, h1, one_smul, one_smul]
    rw [add_assoc, add_comm c₁ c₂, ← add_assoc, s16c1610_add_self_vec, zero_add]
  have hgA : ∀ v, f₁ (g v) = f₁ v + f₂ v := by
    intro v
    change f₁ (v + (f₂ v) • c₁ + ((f₁ + f₂) v) • c₂) = f₁ v + f₂ v
    simp only [map_add, map_smul, LinearMap.add_apply, hf₁c₁, hf₁c₂, smul_eq_mul]
    ring_nf <;> reduce_mod_char
  have hgB : ∀ v, f₂ (g v) = f₁ v := by
    intro v
    change f₂ (v + (f₂ v) • c₁ + ((f₁ + f₂) v) • c₂) = f₁ v
    simp only [map_add, map_smul, LinearMap.add_apply, hf₂c₁, hf₂c₂, smul_eq_mul]
    ring_nf <;> reduce_mod_char
  have hg3 : g.comp (g.comp g) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    change g (g (g v)) = v
    have hA : f₂ (g (g v)) = f₁ v + f₂ v := by rw [hgB (g v), hgA v]
    have hB : (f₁ + f₂) (g (g v)) = f₁ v := by
      rw [LinearMap.add_apply, hgA (g v), hgB (g v), hgA v, hgB v]
      ring_nf <;> reduce_mod_char
    have hC : g (g v) = g v + (f₁ v) • c₁ + (f₂ v) • c₂ := by
      have e1 : f₂ (g v) = f₁ v := hgB v
      have e2 : (f₁ + f₂) (g v) = f₂ v := by
        rw [LinearMap.add_apply, hgA v, hgB v]
        ring_nf <;> reduce_mod_char
      change g v + (f₂ (g v)) • c₁ + ((f₁ + f₂) (g v)) • c₂ = _
      rw [e1, e2]
    change g (g v) + (f₂ (g (g v))) • c₁ + ((f₁ + f₂) (g (g v))) • c₂ = v
    rw [hA, hB, hC]
    change (v + (f₂ v) • c₁ + ((f₁ + f₂) v) • c₂) + (f₁ v) • c₁ + (f₂ v) • c₂ +
      (f₁ v + f₂ v) • c₁ + (f₁ v) • c₂ = v
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply]
    ring_nf <;> reduce_mod_char
  refine ⟨LinearEquiv.ofLinearMap g (g.comp g) hg3 (by rw [LinearMap.comp_assoc]; exact hg3),
    ?_, ?_, ?_⟩
  · rw [LinearEquiv.coe_ofLinearMap]; exact hgc₁
  · rw [LinearEquiv.coe_ofLinearMap]; exact hgc₂
  · apply LinearEquiv.ext
    intro v
    change (g.comp (g.comp g)) v = v
    rw [hg3]
    rfl

private noncomputable def s16c1610_blockMap {m : ℕ} (u w : Fin m → ZMod 2)
    (α β : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun v := v + (α v) • u + (β v) • w
  map_add' v w' := by
    simp only [map_add, add_smul]
    module
  map_smul' a v := by
    simp only [map_smul, RingHom.id_apply, smul_add, smul_smul]
    module

private lemma s16c1610_exists_pureEquiv {m : ℕ} (hm : 3 ≤ m) {c : Fin m → ZMod 2}
    (hc : c ≠ 0) :
    ∃ e : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2),
      e c = c ∧ e ^ 3 = 1 ∧ e ≠ 1 := by
  classical
  obtain ⟨j₁, hj₁⟩ := s16c1610_exists_coord_ne_zero hc
  have hcard : 1 < Fintype.card (Fin m) := by rw [Fintype.card_fin]; omega
  obtain ⟨j₂, hj₂⟩ := Fintype.exists_ne_of_one_lt_card hcard j₁
  have hcardα : 1 < Fintype.card {j : Fin m // j ≠ j₁} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    omega
  obtain ⟨⟨j₃, hj₃₁⟩, hj₃₂⟩ := Fintype.exists_ne_of_one_lt_card hcardα ⟨j₂, hj₂⟩
  have hj₃₂' : j₃ ≠ j₂ := fun h => hj₃₂ (Subtype.ext h)
  let u : Fin m → ZMod 2 := fun i => if i = j₂ then 1 else 0
  let w : Fin m → ZMod 2 := fun i => if i = j₃ then 1 else 0
  let α : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    s16c1610_proj j₂ + s16c1610_proj j₃ + ((c j₂ + c j₃) * (c j₁)⁻¹) • s16c1610_proj j₁
  let β : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    s16c1610_proj j₂ + ((c j₂) * (c j₁)⁻¹) • s16c1610_proj j₁
  have hαc : α c = 0 := by
    simp only [α, LinearMap.add_apply, LinearMap.smul_apply, s16c1610_proj_apply]
    change c j₂ + c j₃ + ((c j₂ + c j₃) * (c j₁)⁻¹) * c j₁ = 0
    rw [mul_assoc, inv_mul_cancel₀ hj₁, mul_one]
    ring_nf <;> reduce_mod_char
  have hβc : β c = 0 := by
    simp only [β, LinearMap.add_apply, LinearMap.smul_apply, s16c1610_proj_apply]
    change c j₂ + (c j₂ * (c j₁)⁻¹) * c j₁ = 0
    rw [mul_assoc, inv_mul_cancel₀ hj₁, mul_one]
    ring_nf <;> reduce_mod_char
  have hαu : α u = 1 := by
    change u j₂ + u j₃ + ((c j₂ + c j₃) * (c j₁)⁻¹) • u j₁ = 1
    simp [u, hj₂, hj₃₂', Ne.symm hj₃₂', Ne.symm hj₂]
  have hαw : α w = 1 := by
    change w j₂ + w j₃ + ((c j₂ + c j₃) * (c j₁)⁻¹) • w j₁ = 1
    simp [w, hj₃₂', hj₃₁, Ne.symm hj₃₂', Ne.symm hj₃₁]
  have hβu : β u = 1 := by
    change u j₂ + ((c j₂) * (c j₁)⁻¹) • u j₁ = 1
    simp [u, hj₂, Ne.symm hj₂]
  have hβw : β w = 0 := by
    change w j₂ + ((c j₂) * (c j₁)⁻¹) • w j₁ = 0
    simp [w, hj₃₂', hj₃₁, Ne.symm hj₃₂', Ne.symm hj₃₁]
  let g : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) := s16c1610_blockMap u w α β
  have hgc : g c = c := by
    change c + (α c) • u + (β c) • w = c
    rw [hαc, hβc, zero_smul, zero_smul, add_zero, add_zero]
  have hgu : g u = w := by
    change u + (α u) • u + (β u) • w = w
    rw [hαu, hβu, one_smul, one_smul, s16c1610_add_self_vec u, zero_add]
  have hgw : g w = u + w := by
    change w + (α w) • u + (β w) • w = u + w
    rw [hαw, hβw, one_smul, zero_smul, add_zero, add_comm]
  have hgA : ∀ v, α (g v) = β v := by
    intro v
    change α (v + (α v) • u + (β v) • w) = β v
    simp only [map_add, map_smul, hαu, hαw, smul_eq_mul, mul_one, mul_zero, add_zero]
    ring_nf <;> reduce_mod_char
  have hgB : ∀ v, β (g v) = α v + β v := by
    intro v
    change β (v + (α v) • u + (β v) • w) = α v + β v
    simp only [map_add, map_smul, hβu, hβw, smul_eq_mul, mul_one, mul_zero, add_zero]
    ring_nf <;> reduce_mod_char
  have hg3 : g.comp (g.comp g) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    change g (g (g v)) = v
    have hA : α (g (g v)) = α v + β v := by rw [hgA (g v), hgB v]
    have hB : β (g (g v)) = α v := by
      rw [hgB (g v), hgA v, hgB v]
      ring_nf <;> reduce_mod_char
    have hC : g (g v) = g v + (β v) • u + (α v + β v) • w := by
      change g v + (α (g v)) • u + (β (g v)) • w = _
      rw [hgA v, hgB v]
    change g (g v) + (α (g (g v))) • u + (β (g (g v))) • w = v
    rw [hA, hB, hC]
    change (g v + (β v) • u + (α v + β v) • w) + (α v + β v) • u + (α v) • w = v
    change (v + (α v) • u + (β v) • w + (β v) • u + (α v + β v) • w) +
      (α v + β v) • u + (α v) • w = v
    funext i
    simp only [Pi.add_apply, Pi.smul_apply]
    ring_nf <;> reduce_mod_char
  let e : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2) :=
    LinearEquiv.ofLinearMap g (g.comp g) hg3 (by rw [LinearMap.comp_assoc]; exact hg3)
  refine ⟨e, hgc, ?_, ?_⟩
  · apply LinearEquiv.ext
    intro v
    change (g.comp (g.comp g)) v = v
    rw [hg3]
    rfl
  · intro h
    have h1 : g u = u := by
      have h2 := congrArg (fun f : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2) =>
        f u) h
      have h3 : e u = g u := rfl
      rw [h3] at h2
      simpa using h2
    rw [hgu] at h1
    have h2 := congrFun h1 j₂
    simp [u, w, hj₃₂', Ne.symm hj₃₂'] at h2

private lemma s16c1610_zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem s16c1610_tensor_exists_order_three_fix {W : Type} [CommGroup W]
    {G : Subgroup (MulAut W)} {m : ℕ} (hm : 3 ≤ m) (h : IsTensorS3L2 W G m) {w : W}
    (hw : w ≠ 1) : ∃ y ∈ G, orderOf y = 3 ∧ (y : MulAut W) w = w := by
  obtain ⟨φ, ψ, hcompat⟩ := h
  let t := Multiplicative.toAdd (ψ w)
  have hwt : ψ w = Multiplicative.ofAdd t := rfl
  have ht : t ≠ 0 := by
    intro h0
    exact hw (ψ.injective (by simp [hwt, h0]))
  obtain ⟨c₁, c₂, hdecomp⟩ := s16c1610_tensor_decomp t
  by_cases hind : LinearIndependent (ZMod 2) ![c₁, c₂]
  · obtain ⟨e, he₁, he₂, he3⟩ := s16c1610_exists_rank2Equiv hind
    let g := s16c1610_leEquivGL m e
    have hg₁ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁ = c₁ + c₂ := by
      rw [s16c1610_leEquivGL_mulVec, he₁]
    have hg₂ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂ = c₁ := by
      rw [s16c1610_leEquivGL_mulVec, he₂]
    have hwt' : ψ w = Multiplicative.ofAdd
        (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂) := by
      rw [hwt, hdecomp]
    have hq3 : (s16c1610_sigma0, g) ^ 3 = 1 := by
      show (s16c1610_sigma0 ^ 3, g ^ 3) = 1
      rw [s16c1610_sigma0_pow_three, ← map_pow, he3, map_one]
      rfl
    have hqne : (s16c1610_sigma0, g) ≠ 1 := by
      intro hh
      exact s16c1610_sigma0_ne_one (congrArg Prod.fst hh)
    refine ⟨(φ.symm (s16c1610_sigma0, g) : MulAut W),
      (φ.symm (s16c1610_sigma0, g)).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq φ.symm]
      exact orderOf_eq_prime_iff.mpr ⟨hq3, hqne⟩
    · exact s16c1610_fix_rank2 hcompat hg₁ hg₂ hwt'
  · have hdep : c₁ = 0 ∨ c₂ = 0 ∨ c₁ = c₂ := by
      by_contra hcon
      push Not at hcon
      refine hind ((Fintype.linearIndependent_iffₛ (R := ZMod 2) (v := ![c₁, c₂])).mpr
        (fun f g hfg => ?_))
      have hd : (f 0 - g 0) • c₁ + (f 1 - g 1) • c₂ = 0 := by
        have h1 : f 0 • c₁ + f 1 • c₂ = g 0 • c₁ + g 1 • c₂ := by
          simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons] using hfg
        have h2 : (f 0 - g 0) • c₁ + (f 1 - g 1) • c₂ =
            (f 0 • c₁ + f 1 • c₂) - (g 0 • c₁ + g 1 • c₂) := by
          module
        rw [h2, h1, sub_self]
      rcases s16c1610_zmod2_eq_zero_or_one (f 0 - g 0) with h0 | h0 <;>
        rcases s16c1610_zmod2_eq_zero_or_one (f 1 - g 1) with h1 | h1
      · intro i
        fin_cases i
        · exact sub_eq_zero.mp h0
        · exact sub_eq_zero.mp h1
      · rw [h0, h1, zero_smul, one_smul, zero_add] at hd
        exact (hcon.2.1 hd).elim
      · rw [h0, h1, one_smul, zero_smul, add_zero] at hd
        exact (hcon.1 hd).elim
      · rw [h0, h1, one_smul, one_smul] at hd
        exact (hcon.2.2 (s16c1610_eq_of_add_eq_zero hd)).elim
    obtain ⟨a, c, hc, hdecomp'⟩ : ∃ (a : ↥(CFSG.Quasithin.permCore 3)) (c : Fin m → ZMod 2),
        c ≠ 0 ∧ t = a ⊗ₜ[ZMod 2] c := by
      rcases hdep with h₁ | h₁ | h₁
      · refine ⟨s16c1610_a2, c₂, ?_, ?_⟩
        · intro hc₂
          exact ht (by simp [hdecomp, h₁, hc₂])
        · simp [hdecomp, h₁]
      · refine ⟨s16c1610_a1, c₁, ?_, ?_⟩
        · intro hc₁
          exact ht (by simp [hdecomp, h₁, hc₁])
        · simp [hdecomp, h₁]
      · refine ⟨s16c1610_a1 + s16c1610_a2, c₁, ?_, ?_⟩
        · intro hc₁
          have hc₂ : c₂ = 0 := by rw [← h₁, hc₁]
          exact ht (by simp [hdecomp, h₁, hc₁, hc₂])
        · rw [hdecomp, h₁, ← TensorProduct.add_tmul]
    obtain ⟨e, hec, he3, hene⟩ := s16c1610_exists_pureEquiv hm hc
    let g := s16c1610_leEquivGL m e
    have hg : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c = c := by
      rw [s16c1610_leEquivGL_mulVec, hec]
    have hwt' : ψ w = Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c) := by
      rw [hwt, hdecomp']
    have hq3 : ((1 : Equiv.Perm (Fin 3)), g) ^ 3 = 1 := by
      show (((1 : Equiv.Perm (Fin 3)) ^ 3, g ^ 3)) = 1
      rw [one_pow, ← map_pow, he3, map_one]
      rfl
    have hqne : ((1 : Equiv.Perm (Fin 3)), g) ≠ 1 := by
      intro hh
      have hg1 : g = 1 := congrArg Prod.snd hh
      exact hene ((s16c1610_leEquivGL m).injective
        (hg1.trans (map_one (s16c1610_leEquivGL m)).symm))
    refine ⟨(φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W),
      (φ.symm ((1 : Equiv.Perm (Fin 3)), g)).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq φ.symm]
      exact orderOf_eq_prime_iff.mpr ⟨hq3, hqne⟩
    · exact s16c1610_fix_pure hcompat hg hwt'

private theorem s16c1610_exists_basis {K : Type*} [Field K] [Fintype K]
    {m k : ℕ} (v : Fin k → (Fin m → K)) (hv : LinearIndependent K v) :
    ∃ b : Module.Basis (Fin m) K (Fin m → K), ∃ i : Fin k → Fin m,
      Function.Injective i ∧ ∀ j, b (i j) = v j := by
  classical
  let s : Set (Fin m → K) := Set.range v
  have hs : LinearIndepOn K id s := hv.linearIndepOn_id
  let b₀ := Module.Basis.extend hs
  have hcard₀ : Fintype.card (hs.extend (Set.subset_univ s)) = m := by
    rw [← Module.finrank_eq_card_basis b₀, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  let e : (hs.extend (Set.subset_univ s)) ≃ Fin m := Fintype.equivFinOfCardEq hcard₀
  let b := b₀.reindex e
  have hb : ∀ x, b (e x) = (x : Fin m → K) := by
    intro x
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    exact Module.Basis.extend_apply_self hs x
  refine ⟨b, fun j => e ⟨v j, hs.subset_extend _ (Set.mem_range_self j)⟩, ?_, ?_⟩
  · intro j j' hjj
    have h2 : (⟨v j, hs.subset_extend _ (Set.mem_range_self j)⟩ :
        hs.extend (Set.subset_univ s)) =
        ⟨v j', hs.subset_extend _ (Set.mem_range_self j')⟩ := e.injective hjj
    exact hv.injective (Subtype.ext_iff.mp h2)
  · intro j
    exact hb _

private lemma s16c1610_four_ne (i0 : Fin 5) :
    ∃ j₁ j₂ j₃ j₄ : Fin 5, j₁ ≠ i0 ∧ j₂ ≠ i0 ∧ j₃ ≠ i0 ∧ j₄ ≠ i0 ∧
      j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₁ ≠ j₄ ∧ j₂ ≠ j₃ ∧ j₂ ≠ j₄ ∧ j₃ ≠ j₄ := by
  decide +revert

private lemma s16c1610_two_ne {i0 i1 : Fin 5} (h : i0 ≠ i1) :
    ∃ j k : Fin 5, j ≠ i0 ∧ j ≠ i1 ∧ k ≠ i0 ∧ k ≠ i1 ∧ j ≠ k := by
  decide +revert

private lemma s16c1610_permAct_one (n : ℕ) (a : Fin n → ZMod 2) :
    CFSG.Quasithin.permAct (1 : Equiv.Perm (Fin n)) a = a := by
  funext i
  simp [CFSG.Quasithin.permAct]

private lemma s16c1610_glBlockA_commute {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) (Fin m → ZMod 2)) {i j k l : I}
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    s16c1610_glBlockA b i j hij * s16c1610_glBlockA b k l hkl =
      s16c1610_glBlockA b k l hkl * s16c1610_glBlockA b i j hij := by
  have hAB : s16c1610_blockA b i j hij * s16c1610_blockA b k l hkl =
      s16c1610_blockA b k l hkl * s16c1610_blockA b i j hij := by
    have hlin : (s16c1610_blockA b i j hij :
          (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)).comp
        (s16c1610_blockA b k l hkl :
          (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) =
        (s16c1610_blockA b k l hkl :
          (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)).comp
        (s16c1610_blockA b i j hij :
          (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) := by
      apply Module.Basis.ext b
      intro x
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change (s16c1610_blockA b i j hij : (Fin m → ZMod 2) → (Fin m → ZMod 2))
          ((s16c1610_blockA b k l hkl : (Fin m → ZMod 2) → (Fin m → ZMod 2)) (b x)) =
        (s16c1610_blockA b k l hkl : (Fin m → ZMod 2) → (Fin m → ZMod 2))
          ((s16c1610_blockA b i j hij : (Fin m → ZMod 2) → (Fin m → ZMod 2)) (b x))
      rcases eq_or_ne x i with rfl | hxi
      · conv_lhs => rw [s16c1610_blockA_apply_other b hkl hik hil,
          s16c1610_blockA_apply_i b hij]
        conv_rhs => rw [s16c1610_blockA_apply_i b hij,
          s16c1610_blockA_apply_other b hkl hjk hjl]
      · rcases eq_or_ne x j with rfl | hxj
        · conv_lhs => rw [s16c1610_blockA_apply_other b hkl hjk hjl,
            s16c1610_blockA_apply_j b hij]
          conv_rhs => rw [s16c1610_blockA_apply_j b hij, map_add,
            s16c1610_blockA_apply_other b hkl hik hil,
            s16c1610_blockA_apply_other b hkl hjk hjl]
        · rcases eq_or_ne x k with rfl | hxk
          · conv_lhs => rw [s16c1610_blockA_apply_i b hkl,
              s16c1610_blockA_apply_other b hij hil.symm hjl.symm]
            conv_rhs => rw [s16c1610_blockA_apply_other b hij hik.symm hjk.symm,
              s16c1610_blockA_apply_i b hkl]
          · rcases eq_or_ne x l with rfl | hxl
            · conv_lhs => rw [s16c1610_blockA_apply_j b hkl, map_add,
                s16c1610_blockA_apply_other b hij hik.symm hjk.symm,
                s16c1610_blockA_apply_other b hij hil.symm hjl.symm]
              conv_rhs => rw [s16c1610_blockA_apply_other b hij hil.symm hjl.symm,
                s16c1610_blockA_apply_j b hkl]
            · conv_lhs => rw [s16c1610_blockA_apply_other b hkl hxk hxl,
                s16c1610_blockA_apply_other b hij hxi hxj]
              conv_rhs => rw [s16c1610_blockA_apply_other b hij hxi hxj,
                s16c1610_blockA_apply_other b hkl hxk hxl]
    apply LinearEquiv.ext
    intro v
    have h := DFunLike.congr_fun hlin v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact h
  calc s16c1610_glBlockA b i j hij * s16c1610_glBlockA b k l hkl
      = s16c1610_leEquivGL m (s16c1610_blockA b i j hij) *
          s16c1610_leEquivGL m (s16c1610_blockA b k l hkl) := rfl
    _ = s16c1610_leEquivGL m (s16c1610_blockA b i j hij *
          s16c1610_blockA b k l hkl) := (map_mul _ _ _).symm
    _ = s16c1610_leEquivGL m (s16c1610_blockA b k l hkl *
          s16c1610_blockA b i j hij) := by rw [hAB]
    _ = s16c1610_leEquivGL m (s16c1610_blockA b k l hkl) *
          s16c1610_leEquivGL m (s16c1610_blockA b i j hij) := map_mul _ _ _
    _ = s16c1610_glBlockA b k l hkl * s16c1610_glBlockA b i j hij := rfl

private lemma s16c1610_zpowers_le_normalizer_of_commute {H : Type*} [Group H] {a b : H}
    (h : a * b = b * a) :
    Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a) := by
  rw [Subgroup.zpowers_le]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : (a ^ n) * b = b * (a ^ n) := (show Commute a b from h).zpow_left n
    rw [← hn, ← hc, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers a n
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute (a ^ n) b := (show Commute a b from h).zpow_left n
    have hx' : b⁻¹ * a ^ n * b = a ^ n := by
      have h1 : b⁻¹ * a ^ n = a ^ n * b⁻¹ := hc.inv_right.eq.symm
      rw [h1]
      group
    have hxy : x = b⁻¹ * (b * x * b⁻¹) * b := by group
    rw [hxy, ← hn, hx']
    exact Subgroup.zpow_mem_zpowers a n

private lemma s16c1610_disjoint_zpowers_of_prime {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    {a b : H} (ha : a ^ p = 1) (ha1 : a ≠ 1) (hain : a ∉ Subgroup.zpowers b) :
    Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b) := by
  rw [Subgroup.disjoint_def]
  intro x hxa hxb
  by_contra hx1
  haveI : Fact p.Prime := ⟨hp⟩
  have hoa : orderOf a = p := orderOf_eq_prime ha ha1
  have hdvd : orderOf x ∣ p := by
    rw [← hoa]
    exact orderOf_dvd_of_mem_zpowers hxa
  have hox : orderOf x = p := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  haveI : Finite (Subgroup.zpowers a) :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, ha⟩).finite_zpowers
  have heq : Subgroup.zpowers x = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxa)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hox])
  have hax : a ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers a
  exact hain (Subgroup.zpowers_le.2 hxb hax)

private lemma s16c1610_closure_pair_elemAbelian_nine {H : Type*} [Group H] {q₁ q₂ : H}
    (h₁ : q₁ ^ 3 = 1) (h₂ : q₂ ^ 3 = 1) (hne : q₁ ≠ 1) (hne₂ : q₂ ≠ 1)
    (hcomm : q₁ * q₂ = q₂ * q₁) (hdisj : Disjoint (Subgroup.zpowers q₁) (Subgroup.zpowers q₂)) :
    IsElemAbelian 3 (Subgroup.closure ({q₁, q₂} : Set H)) ∧
      Nat.card (Subgroup.closure ({q₁, q₂} : Set H)) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcomm' : ∀ x ∈ ({q₁, q₂} : Set H), ∀ y ∈ ({q₁, q₂} : Set H), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hcomm
    · exact hcomm.symm
    · rfl
  have hpw : ∀ x ∈ ({q₁, q₂} : Set H), x ^ 3 = 1 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h₁
    · exact h₂
  refine ⟨IsElemAbelian.closure_of_commute hcomm' hpw, ?_⟩
  have hclosure : Subgroup.closure ({q₁, q₂} : Set H) =
      Subgroup.zpowers q₁ ⊔ Subgroup.zpowers q₂ := by
    rw [show ({q₁, q₂} : Set H) = {q₁} ∪ {q₂} from by ext x; simp [or_comm],
      Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  rw [hclosure,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (s16c1610_zpowers_le_normalizer_of_commute hcomm) hdisj,
    Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime h₁ hne, orderOf_eq_prime h₂ hne₂]

private lemma s16c1610_fix_two_pure {W : Type} [CommGroup W] {G : Subgroup (MulAut W)} {m : ℕ}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin m) (ZMod 2))}
    {ψ : W ≃* Multiplicative (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2))}
    (hcompat : ∀ (γ : ↥G) (a a' : ↥(CFSG.Quasithin.permCore 3)) (c c' : Fin m → ZMod 2),
      (a' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      c' = ((φ γ).2 : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c →
        ψ ((γ : MulAut W) (ψ.symm (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c)))) =
          Multiplicative.ofAdd (a' ⊗ₜ[ZMod 2] c'))
    {c₁ c₂ : Fin m → ZMod 2} {g : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)}
    (hg₁ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁ = c₁)
    (hg₂ : (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂ = c₂) {w : W}
    (hw : ψ w = Multiplicative.ofAdd
      (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂)) :
    (φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W) w = w := by
  have hφ : φ (φ.symm ((1 : Equiv.Perm (Fin 3)), g)) = ((1 : Equiv.Perm (Fin 3)), g) :=
    MulEquiv.apply_symm_apply φ _
  have h₁ := hcompat (φ.symm ((1 : Equiv.Perm (Fin 3)), g)) s16c1610_a1 s16c1610_a1 c₁
    ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁)
    (by rw [hφ]; exact s16c1610_permAct_one 3 (s16c1610_a1 : Fin 3 → ZMod 2))
    (by rw [hφ])
  have h₂ := hcompat (φ.symm ((1 : Equiv.Perm (Fin 3)), g)) s16c1610_a2 s16c1610_a2 c₂
    ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)
    (by rw [hφ]; exact s16c1610_permAct_one 3 (s16c1610_a2 : Fin 3 → ZMod 2))
    (by rw [hφ])
  have hmain : ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
      (ψ.symm (Multiplicative.ofAdd
        (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂)))) =
      Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂) := by
    calc ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
          (ψ.symm (Multiplicative.ofAdd
            (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂))))
        = ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
            (ψ.symm (Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁)) *
              ψ.symm (Multiplicative.ofAdd (s16c1610_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [s16c1610_ofAdd_add, map_mul]
      _ = ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁))) *
            (φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16c1610_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [map_mul]
      _ = ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁)))) *
            ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W)
              (ψ.symm (Multiplicative.ofAdd (s16c1610_a2 ⊗ₜ[ZMod 2] c₂)))) := by
          rw [map_mul]
      _ = Multiplicative.ofAdd
            (s16c1610_a1 ⊗ₜ[ZMod 2] ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁)) *
            Multiplicative.ofAdd
              (s16c1610_a2 ⊗ₜ[ZMod 2]
                ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)) := by
          rw [h₁, h₂]
      _ = Multiplicative.ofAdd
            (s16c1610_a1 ⊗ₜ[ZMod 2] ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₁) +
              s16c1610_a2 ⊗ₜ[ZMod 2]
                ((g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c₂)) := by
          rw [s16c1610_ofAdd_add]
      _ = Multiplicative.ofAdd (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ +
            s16c1610_a2 ⊗ₜ[ZMod 2] c₂) := by
          rw [hg₁, hg₂]
  have hmain' : ψ ((φ.symm ((1 : Equiv.Perm (Fin 3)), g) : MulAut W) w) = ψ w := by
    have hw' : w = ψ.symm (Multiplicative.ofAdd
        (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂)) := by
      rw [← hw, MulEquiv.symm_apply_apply]
    rw [hw', hmain, MulEquiv.apply_symm_apply]
  exact ψ.injective hmain'

private lemma s16c1610_fix_closure {W : Type} [CommGroup W] {G : Subgroup (MulAut W)}
    {q₁ q₂ : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))} {w : W}
    (h₁ : (φ.symm q₁ : MulAut W) w = w) (h₂ : (φ.symm q₂ : MulAut W) w = w) :
    ∀ q ∈ Subgroup.closure ({q₁, q₂} : Set _), (φ.symm q : MulAut W) w = w := by
  intro q hq
  have hstab : Subgroup.closure ({φ.symm q₁, φ.symm q₂} : Set ↥G) ≤
      (MulAction.stabilizer (MulAut W) w).comap G.subtype := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact MulAction.mem_stabilizer_iff.mpr h₁
    · exact MulAction.mem_stabilizer_iff.mpr h₂
  have hmem : φ.symm q ∈ Subgroup.closure ({φ.symm q₁, φ.symm q₂} : Set ↥G) := by
    have h : φ.symm q ∈ (Subgroup.closure ({q₁, q₂} : Set _)).map φ.symm.toMonoidHom :=
      ⟨q, hq, rfl⟩
    rwa [MonoidHom.map_closure, Set.image_pair] at h
  exact MulAction.mem_stabilizer_iff.mp (hstab hmem)

private lemma s16c1610_transport_e9 {W : Type} [CommGroup W] {G : Subgroup (MulAut W)}
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))}
    {E₀ : Subgroup (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))} {w : W}
    (hE : IsElemAbelian 3 E₀) (hcard : Nat.card E₀ = 9)
    (hfix : ∀ q ∈ E₀, (φ.symm q : MulAut W) w = w) :
    ∃ E : Subgroup (MulAut W), E ≤ G ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ e ∈ E, (e : MulAut W) w = w := by
  refine ⟨E₀.map (G.subtype.comp φ.symm.toMonoidHom), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (φ.symm q).2
  · exact hE.map (G.subtype.comp φ.symm.toMonoidHom)
  · rw [Subgroup.card_map_of_injective (f := G.subtype.comp φ.symm.toMonoidHom)
      ((Subgroup.subtype_injective G).comp φ.symm.injective)]
    exact hcard
  · rintro _ ⟨q, hq, rfl⟩
    exact hfix q hq

theorem s16c1610_tensor_exists_elemAbelian_nine_fix {W : Type} [CommGroup W]
    {G : Subgroup (MulAut W)} (h : IsTensorS3L2 W G 5) {w : W} (hw : w ≠ 1) :
    ∃ E : Subgroup (MulAut W), E ≤ G ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ e ∈ E, (e : MulAut W) w = w := by
  obtain ⟨φ, ψ, hcompat⟩ := h
  let t := Multiplicative.toAdd (ψ w)
  have hwt : ψ w = Multiplicative.ofAdd t := rfl
  have ht : t ≠ 0 := by
    intro h0
    exact hw (ψ.injective (by simp [hwt, h0]))
  obtain ⟨c₁, c₂, hdecomp⟩ := s16c1610_tensor_decomp t
  by_cases hind : LinearIndependent (ZMod 2) ![c₁, c₂]
  · have hind' : LinearIndependent (ZMod 2)
        (fun j : Fin 2 => (![c₂, c₁] : Fin 2 → (Fin 5 → ZMod 2)) j) := by
      have h := hind.comp (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1).injective
      have h2 : ((![c₁, c₂] : Fin 2 → (Fin 5 → ZMod 2)) ∘ (Equiv.swap (0 : Fin 2) 1)) =
          (fun j : Fin 2 => (![c₂, c₁] : Fin 2 → (Fin 5 → ZMod 2)) j) := by
        funext j
        fin_cases j <;> rfl
      rwa [h2] at h
    obtain ⟨b, i, hi_inj, hbi⟩ := s16c1610_exists_basis
      (fun j : Fin 2 => (![c₂, c₁] : Fin 2 → (Fin 5 → ZMod 2)) j) hind'
    have hbi0 : b (i 0) = c₂ := hbi 0
    have hbi1 : b (i 1) = c₁ := hbi 1
    have h01 : i 0 ≠ i 1 := hi_inj.ne (by decide : (0 : Fin 2) ≠ 1)
    obtain ⟨p, q, hp0, hp1, hq0, hq1, hpq⟩ := s16c1610_two_ne h01
    let g := s16c1610_glBlockA b (i 0) (i 1) h01
    let k := s16c1610_glBlockA b p q hpq
    have hgc₂ : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).mulVec c₂ = c₁ := by
      rw [← hbi0, ← hbi1]
      exact s16c1610_glBlockA_mulVec_i b h01
    have hgc₁ : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).mulVec c₁ = c₁ + c₂ := by
      rw [← hbi1, ← hbi0, s16c1610_glBlockA_mulVec_j b h01, add_comm]
    have hkc₁ : (k : Matrix (Fin 5) (Fin 5) (ZMod 2)).mulVec c₁ = c₁ := by
      rw [← hbi1]
      exact s16c1610_glBlockA_mulVec_other b hpq hp1.symm hq1.symm
    have hkc₂ : (k : Matrix (Fin 5) (Fin 5) (ZMod 2)).mulVec c₂ = c₂ := by
      rw [← hbi0]
      exact s16c1610_glBlockA_mulVec_other b hpq hp0.symm hq0.symm
    have hg3 : g ^ 3 = 1 := s16c1610_glBlockA_pow_three b h01
    have hk3 : k ^ 3 = 1 := s16c1610_glBlockA_pow_three b hpq
    have hgne : g ≠ 1 := s16c1610_glBlockA_ne_one b h01
    have hkne : k ≠ 1 := s16c1610_glBlockA_ne_one b hpq
    have hcomm_gk : g * k = k * g :=
      s16c1610_glBlockA_commute b h01 hpq hp0.symm hq0.symm hp1.symm hq1.symm
    have hwt' : ψ w = Multiplicative.ofAdd
        (s16c1610_a1 ⊗ₜ[ZMod 2] c₁ + s16c1610_a2 ⊗ₜ[ZMod 2] c₂) := by
      rw [hwt, hdecomp]
    let q₁ : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 5) (ZMod 2) :=
      (s16c1610_sigma0, g)
    let q₂ : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 5) (ZMod 2) := (1, k)
    have hq₁3 : q₁ ^ 3 = 1 := by
      show (s16c1610_sigma0 ^ 3, g ^ 3) = 1
      rw [s16c1610_sigma0_pow_three, hg3]
      rfl
    have hq₂3 : q₂ ^ 3 = 1 := by
      show ((1 : Equiv.Perm (Fin 3)) ^ 3, k ^ 3) = 1
      rw [one_pow, hk3]
      rfl
    have hq₁ne : q₁ ≠ 1 := by
      intro hh
      exact s16c1610_sigma0_ne_one (congrArg Prod.fst hh)
    have hq₂ne : q₂ ≠ 1 := by
      intro hh
      exact hkne (congrArg Prod.snd hh)
    have hcomm : q₁ * q₂ = q₂ * q₁ := by
      show ((s16c1610_sigma0 * 1, g * k) : Equiv.Perm (Fin 3) ×
          Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) =
        (1 * s16c1610_sigma0, k * g)
      rw [mul_one, one_mul, hcomm_gk]
    have hq₁_notin : q₁ ∉ Subgroup.zpowers q₂ := by
      intro hmem
      have hmap : (Prod.fst q₁) ∈ (Subgroup.zpowers q₂).map
          (MonoidHom.fst (Equiv.Perm (Fin 3))
            (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))) := ⟨q₁, hmem, rfl⟩
      rw [MonoidHom.map_zpowers] at hmap
      change q₁.1 ∈ Subgroup.zpowers (1 : Equiv.Perm (Fin 3)) at hmap
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmap
      exact s16c1610_sigma0_ne_one hmap
    have hdisj := s16c1610_disjoint_zpowers_of_prime (by norm_num) hq₁3 hq₁ne hq₁_notin
    have hE := s16c1610_closure_pair_elemAbelian_nine hq₁3 hq₂3 hq₁ne hq₂ne hcomm hdisj
    have hfix₁ : (φ.symm q₁ : MulAut W) w = w :=
      s16c1610_fix_rank2 hcompat hgc₁ hgc₂ hwt'
    have hfix₂ : (φ.symm q₂ : MulAut W) w = w :=
      s16c1610_fix_two_pure hcompat hkc₁ hkc₂ hwt'
    exact s16c1610_transport_e9 hE.1 hE.2 (s16c1610_fix_closure hfix₁ hfix₂)
  · have hdep : c₁ = 0 ∨ c₂ = 0 ∨ c₁ = c₂ := by
      by_contra hcon
      push Not at hcon
      refine hind ((Fintype.linearIndependent_iffₛ (R := ZMod 2) (v := ![c₁, c₂])).mpr
        (fun f g hfg => ?_))
      have hd : (f 0 - g 0) • c₁ + (f 1 - g 1) • c₂ = 0 := by
        have h1 : f 0 • c₁ + f 1 • c₂ = g 0 • c₁ + g 1 • c₂ := by
          simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons] using hfg
        have h2 : (f 0 - g 0) • c₁ + (f 1 - g 1) • c₂ =
            (f 0 • c₁ + f 1 • c₂) - (g 0 • c₁ + g 1 • c₂) := by
          module
        rw [h2, h1, sub_self]
      rcases s16c1610_zmod2_eq_zero_or_one (f 0 - g 0) with h0 | h0 <;>
        rcases s16c1610_zmod2_eq_zero_or_one (f 1 - g 1) with h1 | h1
      · intro i
        fin_cases i
        · exact sub_eq_zero.mp h0
        · exact sub_eq_zero.mp h1
      · rw [h0, h1, zero_smul, one_smul, zero_add] at hd
        exact (hcon.2.1 hd).elim
      · rw [h0, h1, one_smul, zero_smul, add_zero] at hd
        exact (hcon.1 hd).elim
      · rw [h0, h1, one_smul, one_smul] at hd
        exact (hcon.2.2 (s16c1610_eq_of_add_eq_zero hd)).elim
    obtain ⟨a, c, hc, hdecomp'⟩ : ∃ (a : ↥(CFSG.Quasithin.permCore 3)) (c : Fin 5 → ZMod 2),
        c ≠ 0 ∧ t = a ⊗ₜ[ZMod 2] c := by
      rcases hdep with h₁ | h₁ | h₁
      · refine ⟨s16c1610_a2, c₂, ?_, ?_⟩
        · intro hc₂
          exact ht (by simp [hdecomp, h₁, hc₂])
        · simp [hdecomp, h₁]
      · refine ⟨s16c1610_a1, c₁, ?_, ?_⟩
        · intro hc₁
          exact ht (by simp [hdecomp, h₁, hc₁])
        · simp [hdecomp, h₁]
      · refine ⟨s16c1610_a1 + s16c1610_a2, c₁, ?_, ?_⟩
        · intro hc₁
          have hc₂ : c₂ = 0 := by rw [← h₁, hc₁]
          exact ht (by simp [hdecomp, h₁, hc₁, hc₂])
        · rw [hdecomp, h₁, ← TensorProduct.add_tmul]
    have hwt' : ψ w = Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c) := by rw [hwt, hdecomp']
    have hli_c : LinearIndependent (ZMod 2) (fun _ : Fin 1 => c) := by
      rw [Fintype.linearIndependent_iffₛ]
      intro f g hfg j
      fin_cases j
      rw [Fin.sum_univ_one, Fin.sum_univ_one] at hfg
      obtain ⟨j', hj'⟩ := s16c1610_exists_coord_ne_zero hc
      have hcoord : f 0 * c j' = g 0 * c j' := by
        have := congrFun hfg j'
        simpa [Pi.smul_apply] using this
      exact mul_right_cancel₀ hj' hcoord
    obtain ⟨b, i, hi_inj, hbi⟩ := s16c1610_exists_basis (fun _ : Fin 1 => c) hli_c
    have hbi0 : b (i 0) = c := hbi 0
    obtain ⟨j₁, j₂, j₃, j₄, hj₁, hj₂, hj₃, hj₄, hj₁₂, hj₁₃, hj₁₄, hj₂₃, hj₂₄, hj₃₄⟩ :=
      s16c1610_four_ne (i 0)
    let g₁ := s16c1610_glBlockA b j₁ j₂ hj₁₂
    let g₂ := s16c1610_glBlockA b j₃ j₄ hj₃₄
    have hg₁c : (g₁ : Matrix (Fin 5) (Fin 5) (ZMod 2)).mulVec c = c := by
      rw [← hbi0]
      exact s16c1610_glBlockA_mulVec_other b hj₁₂ hj₁.symm hj₂.symm
    have hg₂c : (g₂ : Matrix (Fin 5) (Fin 5) (ZMod 2)).mulVec c = c := by
      rw [← hbi0]
      exact s16c1610_glBlockA_mulVec_other b hj₃₄ hj₃.symm hj₄.symm
    have hg₁3 : g₁ ^ 3 = 1 := s16c1610_glBlockA_pow_three b hj₁₂
    have hg₂3 : g₂ ^ 3 = 1 := s16c1610_glBlockA_pow_three b hj₃₄
    have hg₁ne : g₁ ≠ 1 := s16c1610_glBlockA_ne_one b hj₁₂
    have hg₂ne : g₂ ≠ 1 := s16c1610_glBlockA_ne_one b hj₃₄
    have hcomm_g : g₁ * g₂ = g₂ * g₁ :=
      s16c1610_glBlockA_commute b hj₁₂ hj₃₄ hj₁₃ hj₁₄ hj₂₃ hj₂₄
    have hnotin_g : g₁ ∉ Subgroup.zpowers g₂ := by
      intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hg₂fix : g₂ • b j₁ = b j₁ := by
        rw [show g₂ • b j₁ =
          (g₂ : Matrix (Fin 5) (Fin 5) (ZMod 2)).mulVec (b j₁) from rfl]
        exact s16c1610_glBlockA_mulVec_other b hj₃₄ hj₁₃ hj₁₄
      have hpow : (g₂ ^ n) • b j₁ = b j₁ :=
        smul_eq_self_of_mem_zpowers (Subgroup.zpow_mem_zpowers g₂ n) hg₂fix
      have hg₁fix : g₁ • b j₁ = b j₁ := by rw [← hn]; exact hpow
      have hg₁j : g₁ • b j₁ = b j₂ := by
        rw [show g₁ • b j₁ =
          (g₁ : Matrix (Fin 5) (Fin 5) (ZMod 2)).mulVec (b j₁) from rfl]
        exact s16c1610_glBlockA_mulVec_i b hj₁₂
      rw [hg₁j] at hg₁fix
      exact (b.linearIndependent.injective.ne hj₁₂) hg₁fix.symm
    let q₁ : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 5) (ZMod 2) := (1, g₁)
    let q₂ : Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin 5) (ZMod 2) := (1, g₂)
    have hq₁3 : q₁ ^ 3 = 1 := by
      show ((1 : Equiv.Perm (Fin 3)) ^ 3, g₁ ^ 3) = 1
      rw [one_pow, hg₁3]
      rfl
    have hq₂3 : q₂ ^ 3 = 1 := by
      show ((1 : Equiv.Perm (Fin 3)) ^ 3, g₂ ^ 3) = 1
      rw [one_pow, hg₂3]
      rfl
    have hq₁ne : q₁ ≠ 1 := by
      intro hh
      exact hg₁ne (congrArg Prod.snd hh)
    have hq₂ne : q₂ ≠ 1 := by
      intro hh
      exact hg₂ne (congrArg Prod.snd hh)
    have hcomm : q₁ * q₂ = q₂ * q₁ := by
      show ((1 * 1, g₁ * g₂) : Equiv.Perm (Fin 3) ×
          Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) = (1 * 1, g₂ * g₁)
      rw [hcomm_g]
    have hq₁_notin : q₁ ∉ Subgroup.zpowers q₂ := by
      intro hmem
      have hmap : (Prod.snd q₁) ∈ (Subgroup.zpowers q₂).map
          (MonoidHom.snd (Equiv.Perm (Fin 3))
            (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))) := ⟨q₁, hmem, rfl⟩
      rw [MonoidHom.map_zpowers] at hmap
      exact hnotin_g (by simpa using hmap)
    have hdisj := s16c1610_disjoint_zpowers_of_prime (by norm_num) hq₁3 hq₁ne hq₁_notin
    have hE := s16c1610_closure_pair_elemAbelian_nine hq₁3 hq₂3 hq₁ne hq₂ne hcomm hdisj
    have hfix₁ : (φ.symm q₁ : MulAut W) w = w :=
      s16c1610_fix_pure hcompat hg₁c hwt'
    have hfix₂ : (φ.symm q₂ : MulAut W) w = w :=
      s16c1610_fix_pure hcompat hg₂c hwt'
    exact s16c1610_transport_e9 hE.1 hE.2 (s16c1610_fix_closure hfix₁ hfix₂)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
