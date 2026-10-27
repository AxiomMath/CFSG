module

public import CFSG.Monster.Generated.Centralizer
import CFSG.Monster.Visible.ShortGen
import Mathlib.LinearAlgebra.Lagrange

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Parity Matrix Module

@[expose] noncomputable def shortEig (a : symMat) (c : ShortIdx) : ℚ :=
  qf c (a : Matrix (Fin 24) (Fin 24) ℚ) / 8

theorem shortEig_injective_iff (a : symMat) :
    Function.Injective (shortEig a) ↔ ∀ c d : ShortIdx,
      qf c (a : Matrix (Fin 24) (Fin 24) ℚ) = qf d (a : Matrix (Fin 24) (Fin 24) ℚ) → c = d := by
  refine forall_congr' fun c => forall_congr' fun d => ?_
  rw [shortEig, shortEig, div_left_inj' (by norm_num : (8 : ℚ) ≠ 0)]

@[expose] noncomputable def inXₗ : SpaceX →ₗ[ℚ] SpaceB :=
  LinearMap.inr ℚ symMat (SpaceX × SpaceW) ∘ₗ LinearMap.inl ℚ SpaceX SpaceW

theorem inXₗ_apply (x : SpaceX) : inXₗ x = inX x := rfl

@[expose] noncomputable def inAₗ : symMat →ₗ[ℚ] SpaceB := LinearMap.inl ℚ symMat (SpaceX × SpaceW)

theorem inAₗ_apply (A : symMat) : inAₗ A = inA A := rfl

theorem gmul_inA_inX_shortEig (a : symMat) (x : SpaceX) :
    gmul (inA a) (inX x) = inX (fun c => shortEig a c * x c) := by
  rw [Parity.gmul_inA_inX]
  refine congrArg inX (funext fun c => ?_)
  simp only [shortEig]
  ring

theorem pow_gmul_inA_inX (a : symMat) (n : ℕ) (x : SpaceX) :
    ((gmul (inA a) : Module.End ℚ SpaceB) ^ n) (inX x) =
      inX (fun c => shortEig a c ^ n * x c) := by
  induction n generalizing x with
  | zero => simp [inX]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, gmul_inA_inX_shortEig, ih]
    congr 1
    funext c
    ring

theorem aeval_gmul_inA_inX (a : symMat) (p : Polynomial ℚ) (x : SpaceX) :
    Polynomial.aeval (gmul (inA a) : Module.End ℚ SpaceB) p (inX x) =
      inX (fun c => p.eval (shortEig a c) * x c) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, hp, hq]
    refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
    funext c
    simp [add_mul]
  | monomial n r =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, pow_gmul_inA_inX,
      Module.algebraMap_end_apply]
    refine Prod.ext (smul_zero _) (Prod.ext ?_ (smul_zero _))
    funext c
    simp [mul_assoc]

theorem commute_aeval {A : Type*} [Ring A] [Algebra ℚ A] (H L : A) (h : Commute H L)
    (p : Polynomial ℚ) : Commute H (Polynomial.aeval L p) := by
  have h1 : Algebra.adjoin ℚ {L} ≤ Subalgebra.centralizer ℚ {H} := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact h.eq
  have h2 := h1 (Polynomial.aeval_mem_adjoin_singleton ℚ L (p := p))
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact h2 H rfl

theorem fix_inX_single {h : SpaceB ≃ₗ[ℚ] SpaceB} (hh : IsAlgAut h) {a : symMat}
    (hlam : Function.Injective (shortEig a)) {β : SpaceX} (hβ : ∀ c, β c ≠ 0)
    (ha : h (inA a) = inA a) (hb : h (inX β) = inX β) (c : ShortIdx) :
    h (inX (Pi.single c 1)) = inX (Pi.single c 1) := by
  classical
  set L : Module.End ℚ SpaceB := gmul (inA a) with hL
  set p : Polynomial ℚ := Lagrange.basis (Finset.univ : Finset ShortIdx) (shortEig a) c with hp
  have hcomm : Commute (h.toLinearMap : Module.End ℚ SpaceB) L := by
    refine LinearMap.ext fun v => ?_
    change h (gmul (inA a) v) = gmul (inA a) (h v)
    rw [hh, ha]
  have hev : ∀ d, p.eval (shortEig a d) = if d = c then 1 else 0 := by
    intro d
    by_cases hd : d = c
    · subst hd
      rw [ite_eq_left rfl]
      exact Lagrange.eval_basis_self (fun x _ y _ hxy => hlam hxy) (Finset.mem_univ _)
    · rw [ite_eq_right hd]
      exact Lagrange.eval_basis_of_ne (Ne.symm hd) (Finset.mem_univ _)
  have key : Polynomial.aeval L p (inX β) = β c • inX (Pi.single c 1) := by
    rw [aeval_gmul_inA_inX]
    refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
    funext d
    simp only [hev]
    split_ifs with hd <;> simp [hd]
  have h1 : h (Polynomial.aeval L p (inX β)) = Polynomial.aeval L p (inX β) := by
    have := LinearMap.congr_fun
      (commute_aeval (A := Module.End ℚ SpaceB) _ L hcomm p).eq (inX β)
    rw [Module.End.mul_apply, Module.End.mul_apply] at this
    change h (Polynomial.aeval L p (inX β)) = Polynomial.aeval L p (h (inX β)) at this
    rw [this, hb]
  rw [key, map_smul] at h1
  exact smul_right_injective _ (hβ c) h1

theorem fix_inX {h : SpaceB ≃ₗ[ℚ] SpaceB}
    (hsingle : ∀ c : ShortIdx, h (inX (Pi.single c 1)) = inX (Pi.single c 1)) (x : SpaceX) :
    h (inX x) = inX x := by
  have hlin : h.toLinearMap ∘ₗ inXₗ = inXₗ := (Pi.basisFun ℚ ShortIdx).ext fun c => by
    rw [Pi.basisFun_apply]
    exact hsingle c
  exact LinearMap.congr_fun hlin x

theorem gmul_inX_single_self (c : ShortIdx) :
    gmul (inX (Pi.single c 1)) (inX (Pi.single c 1)) = inA ((8 : ℚ)⁻¹ • UmatS c) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun d => ?_) ?_)
  · change gmulA (inX (Pi.single c 1)) (inX (Pi.single c 1)) = (8 : ℚ)⁻¹ • Umat c
    simp [gmulA, Pi.single_apply]
  · change gmulX (inX (Pi.single c 1)) (inX (Pi.single c 1)) d = 0
    simp [gmulX, qf_zero, Pi.single_apply, tau_self_left]
  · change gmulW (inX (Pi.single c 1)) (inX (Pi.single c 1)) = 0
    simp [gmulW, gmulWHalf]

section AxisSpan

open CFSG.Monster.SpinLattice

variable {S : Submodule ℚ symMat} (hS : ∀ r : Q, IsShortCoord (coordOf r) → axisE r ∈ S)
include hS

theorem basisA_offDiag_mem {i j : Fin 24} (hij : i < j) : basisA s(i, j) ∈ S := by
  have e : basisA s(i, j) = axisE (rPlus i j) - axisE (rMinus i j) := by
    apply Subtype.ext
    rw [coe_basisA, ite_eq_right hij.ne, Submodule.coe_sub, coe_axisE_rPlus hij,
      coe_axisE_rMinus hij, projMat_vPlus_sub_vMinus]
  rw [e]
  exact S.sub_mem (hS _ (isShortCoord_rPlus hij)) (hS _ (isShortCoord_rMinus hij))

theorem exists_diagPair_mem {i j : Fin 24} (hij : i ≠ j) :
    ∃ A : symMat, A ∈ S ∧
      (A : Matrix (Fin 24) (Fin 24) ℚ) = Matrix.single i i 1 + Matrix.single j j 1 := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨axisE (rPlus i j) + axisE (rMinus i j),
      S.add_mem (hS _ (isShortCoord_rPlus h)) (hS _ (isShortCoord_rMinus h)), ?_⟩
    rw [Submodule.coe_add, coe_axisE_rPlus h, coe_axisE_rMinus h, projMat_vPlus_add_vMinus]
  · refine ⟨axisE (rPlus j i) + axisE (rMinus j i),
      S.add_mem (hS _ (isShortCoord_rPlus h)) (hS _ (isShortCoord_rMinus h)), ?_⟩
    rw [Submodule.coe_add, coe_axisE_rPlus h, coe_axisE_rMinus h, projMat_vPlus_add_vMinus,
      add_comm]

theorem basisA_diag_mem (i : Fin 24) : basisA s(i, i) ∈ S := by
  have hne : i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 := by revert i; decide
  obtain ⟨A₁, h₁, e₁⟩ := exists_diagPair_mem hS hne.1
  obtain ⟨A₂, h₂, e₂⟩ := exists_diagPair_mem hS hne.2.1
  obtain ⟨A₃, h₃, e₃⟩ := exists_diagPair_mem hS hne.2.2
  have e : basisA s(i, i) = (2 : ℚ)⁻¹ • (A₁ + A₂ - A₃) := by
    apply Subtype.ext
    rw [coe_basisA, ite_eq_left rfl, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_add,
      e₁, e₂, e₃]
    module
  rw [e]
  exact S.smul_mem _ (S.sub_mem (S.add_mem h₁ h₂) h₃)

theorem basisA_mem (z : PairIdx) : basisA z ∈ S := by
  induction z using Sym2.ind with
  | _ i j =>
    rcases lt_trichotomy i j with h | rfl | h
    · exact basisA_offDiag_mem hS h
    · exact basisA_diag_mem hS i
    · rw [Sym2.eq_swap]
      exact basisA_offDiag_mem hS h

theorem eq_top_of_axisE_mem : S = ⊤ :=
  eq_top_iff.2 (basisA.span_eq ▸ Submodule.span_le.2 (by
    rintro _ ⟨z, rfl⟩
    exact basisA_mem hS z))

end AxisSpan

theorem fix_inA {h : SpaceB ≃ₗ[ℚ] SpaceB} (hh : IsAlgAut h)
    (hsingle : ∀ c : ShortIdx, h (inX (Pi.single c 1)) = inX (Pi.single c 1)) (A : symMat) :
    h (inA A) = inA A := by
  let S : Submodule ℚ symMat := LinearMap.eqLocus (h.toLinearMap ∘ₗ inAₗ) inAₗ
  have hU : ∀ c, UmatS c ∈ S := by
    intro c
    have h1 := hh (inX (Pi.single c 1)) (inX (Pi.single c 1))
    rw [hsingle, gmul_inX_single_self] at h1
    have h1' : h (inAₗ ((8 : ℚ)⁻¹ • UmatS c)) = inAₗ ((8 : ℚ)⁻¹ • UmatS c) := h1
    simp only [map_smul] at h1'
    exact smul_right_injective _ (by norm_num : (8 : ℚ)⁻¹ ≠ 0) h1'
  have hS : ∀ r : Q, IsShortCoord (coordOf r) → axisE r ∈ S := by
    intro r hr
    have e : axisE r = (32 : ℚ)⁻¹ • UmatS (shortCls hr) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, coe_UmatS, Umat_eq_axisE hr, smul_smul]
      norm_num
    rw [e]
    exact S.smul_mem _ (hU _)
  have htop : S = ⊤ := eq_top_of_axisE_mem hS
  have hA : A ∈ S := htop ▸ Submodule.mem_top
  exact hA

theorem bform_inA_right (v : SpaceB) (A : symMat) :
    bform v (inA A) =
      trace ((v.1 : Matrix (Fin 24) (Fin 24) ℚ) * (A : Matrix (Fin 24) (Fin 24) ℚ)) := by
  simp [bform_apply]

theorem bform_inX_right (v : SpaceB) (x : SpaceX) : bform v (inX x) = ∑ c, v.2.1 c * x c := by
  simp [bform_apply]

theorem apply_inW_of_fix {h : SpaceB ≃ₗ[ℚ] SpaceB}
    (hiso : ∀ u v, bform (h u) (h v) = bform u v)
    (hA : ∀ A : symMat, h (inA A) = inA A) (hX : ∀ x : SpaceX, h (inX x) = inX x)
    (N : SpaceW) : h (inW N) = inW (resW h N) := by
  set v := h (inW N) with hv
  have hAo : ∀ A : symMat, bform v (inA A) = 0 := fun A =>
    calc bform v (inA A) = bform (h (inW N)) (h (inA A)) := by rw [hA A]
      _ = bform (inW N) (inA A) := hiso _ _
      _ = 0 := by simp [bform_apply]
  have hXo : ∀ x : SpaceX, bform v (inX x) = 0 := fun x =>
    calc bform v (inX x) = bform (h (inW N)) (h (inX x)) := by rw [hX x]
      _ = bform (inW N) (inX x) := hiso _ _
      _ = 0 := by simp [bform_apply]
  have h1 : v.1 = 0 := by
    have h0 : bform (inA v.1) (inA v.1) = 0 := by
      rw [bform_inA_right, ← bform_inA_right v, hAo]
    by_contra hne
    have hne' : inA v.1 ≠ 0 := fun h' => hne (congrArg Prod.fst h')
    exact (bform_self_pos hne').ne' h0
  have h2 : v.2.1 = 0 := by
    have h0 : bform (inX v.2.1) (inX v.2.1) = 0 := by
      rw [bform_inX_right, ← bform_inX_right v, hXo]
    by_contra hne
    have hne' : inX v.2.1 ≠ 0 := fun h' => hne (congrArg (fun w : SpaceB => w.2.1) h')
    exact (bform_self_pos hne').ne' h0
  exact Prod.ext h1 (Prod.ext h2 rfl)

theorem commute_Q_of_commute_Rmat {M : Matrix SpinIdx SpinIdx ℚ}
    (hM : ∀ c : ShortIdx, Rmat c * M = M * Rmat c) (g : Q) :
    ((g : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * M =
      M * ((g : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) := by
  have hg : g ∈ Subgroup.closure {r : Q | IsShortCoord (coordOf r)} := by
    rw [Visible.closure_isShortCoord_eq_top]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rw [coe_Q_eq_sgn_smul_Rmat hx, Matrix.smul_mul, Matrix.mul_smul, hM]
  | one => rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  | mul x y _ _ hx hy =>
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx,
      Matrix.mul_assoc]
  | inv x _ hx =>
    have h1 : ((x⁻¹ : Q) : GL SpinIdx ℚ).val * (x : GL SpinIdx ℚ).val = 1 := by
      rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (x : GL SpinIdx ℚ).val * ((x⁻¹ : Q) : GL SpinIdx ℚ).val = 1 := by
      rw [Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((x⁻¹ : Q) : GL SpinIdx ℚ).val * M
        = ((x⁻¹ : Q) : GL SpinIdx ℚ).val * M * ((x : GL SpinIdx ℚ).val *
            ((x⁻¹ : Q) : GL SpinIdx ℚ).val) := by rw [h2, Matrix.mul_one]
      _ = ((x⁻¹ : Q) : GL SpinIdx ℚ).val * (M * (x : GL SpinIdx ℚ).val) *
            ((x⁻¹ : Q) : GL SpinIdx ℚ).val := by simp only [Matrix.mul_assoc]
      _ = ((x⁻¹ : Q) : GL SpinIdx ℚ).val * ((x : GL SpinIdx ℚ).val * M) *
            ((x⁻¹ : Q) : GL SpinIdx ℚ).val := by rw [hx]
      _ = (((x⁻¹ : Q) : GL SpinIdx ℚ).val * (x : GL SpinIdx ℚ).val) * M *
            ((x⁻¹ : Q) : GL SpinIdx ℚ).val := by simp only [Matrix.mul_assoc]
      _ = M * ((x⁻¹ : Q) : GL SpinIdx ℚ).val := by rw [h1, Matrix.one_mul]

theorem exists_scalar_of_commute_Rmat {M : Matrix SpinIdx SpinIdx ℚ}
    (hM : ∀ c : ShortIdx, Rmat c * M = M * Rmat c) : ∃ c : ℚ, M = Matrix.scalar SpinIdx c :=
  exists_scalar_of_commute_Q fun g hg => commute_Q_of_commute_Rmat hM ⟨g, hg⟩

section SpinMatrix

variable (R : Module.End ℚ SpaceW)
  (hR : ∀ B : Matrix (Fin 24) (Fin 24) ℚ, Bᵀ = B → ∀ N : SpaceW, R (N * B) = R N * B)
include hR

theorem commute_mul_single (N : SpaceW) (i j : Fin 24) :
    R (N * single i j (1 : ℚ)) = R N * single i j (1 : ℚ) := by
  by_cases hij : i = j
  · subst hij
    exact hR _ (transpose_single i i 1) N
  · have e : single i j (1 : ℚ) =
        single i i (1 : ℚ) * (single i j (1 : ℚ) + single j i (1 : ℚ)) := by
      simp [Matrix.mul_add, hij]
    have hF : (single i j (1 : ℚ) + single j i (1 : ℚ))ᵀ =
        single i j (1 : ℚ) + single j i (1 : ℚ) := by
      rw [transpose_add, transpose_single, transpose_single, add_comm]
    rw [e, ← Matrix.mul_assoc N, hR _ hF (N * single i i (1 : ℚ)),
      hR _ (transpose_single i i (1 : ℚ)) N, Matrix.mul_assoc _ (single i i (1 : ℚ))]

omit hR in
@[expose] noncomputable def spinOf : Matrix SpinIdx SpinIdx ℚ :=
  Matrix.of fun b a => R (single a 0 1) b 0

theorem eq_spinOf_mul (N : SpaceW) : R N = spinOf R * N := by
  have hlin : R = lr (spinOf R) 1 := by
    refine (Matrix.stdBasis ℚ SpinIdx (Fin 24)).ext fun k => ?_
    obtain ⟨a, j⟩ := k
    rw [lr_apply, Matrix.stdBasis_eq_single, Matrix.mul_one]
    have h1 : R (single a j (1 : ℚ)) = R (single a 0 (1 : ℚ)) * single (0 : Fin 24) j (1 : ℚ) := by
      have := commute_mul_single R hR (single a 0 1) 0 j
      rwa [single_mul_single_same, one_mul] at this
    rw [h1]
    ext b k
    by_cases hk : k = j
    · subst hk
      rw [mul_single_apply_same, mul_single_apply_same, mul_one, mul_one, spinOf, of_apply]
    · rw [mul_single_apply_of_ne _ _ _ _ _ hk, mul_single_apply_of_ne _ _ _ _ _ hk]
  have := LinearMap.congr_fun hlin N
  rwa [lr_apply, Matrix.mul_one] at this

theorem spinOf_commute_Rmat
    (hK : ∀ (c : ShortIdx) (N : SpaceW), R (Rmat c * N * Kc c) = Rmat c * R N * Kc c)
    (c : ShortIdx) : Rmat c * spinOf R = spinOf R * Rmat c := by
  have hN : ∀ N : SpaceW, spinOf R * Rmat c * N = Rmat c * spinOf R * N := by
    intro N
    have h := hK c N
    rw [eq_spinOf_mul R hR, eq_spinOf_mul R hR] at h
    have h2 : spinOf R * Rmat c * N * Kc c = Rmat c * spinOf R * N * Kc c := by
      simp only [Matrix.mul_assoc] at h ⊢
      exact h
    have h3 := congrArg (· * (1 - (28 : ℚ)⁻¹ • Umat c)) h2
    simp only [Matrix.mul_assoc, Kc_mul_Kinv, Matrix.mul_one] at h3
    simp only [Matrix.mul_assoc]
    exact h3
  ext a b
  have := congrFun (congrFun (hN (single b 0 1)) a) 0
  rw [mul_single_apply_same, mul_single_apply_same, mul_one, mul_one] at this
  exact this.symm

theorem exists_eq_smul_of_intertwines
    (hK : ∀ (c : ShortIdx) (N : SpaceW), R (Rmat c * N * Kc c) = Rmat c * R N * Kc c) :
    ∃ c : ℚ, ∀ N : SpaceW, R N = c • N := by
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_Rmat (spinOf_commute_Rmat R hR hK)
  refine ⟨c, fun N => ?_⟩
  rw [eq_spinOf_mul R hR, hc, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

end SpinMatrix

theorem resW_mul_sym_of_fix {h : SpaceB ≃ₗ[ℚ] SpaceB} (hh : IsAlgAut h)
    (hA : ∀ A : symMat, h (inA A) = inA A) (hW : ∀ N : SpaceW, h (inW N) = inW (resW h N))
    (B : Matrix (Fin 24) (Fin 24) ℚ) (hB : Bᵀ = B) (N : SpaceW) :
    resW h (N * B) = resW h N * B := by
  obtain ⟨A, hAB⟩ : ∃ A : symMat, MA (A : Matrix (Fin 24) (Fin 24) ℚ) = B :=
    ⟨⟨B - (trace B / 32) • (1 : Matrix (Fin 24) (Fin 24) ℚ), by
      rw [mem_symMat, transpose_sub, transpose_smul, transpose_one, hB]⟩, MA_surj B⟩
  rw [← hAB]
  have h1 := hh (inA A) (inW N)
  rw [gmul_inA_inW, hA A, hW, hW, gmul_inA_inW] at h1
  exact congrArg (fun w : SpaceB => w.2.2) h1

theorem resW_Rmat_mul_Kc {h : SpaceB ≃ₗ[ℚ] SpaceB} (hh : IsAlgAut h)
    (hX : ∀ x : SpaceX, h (inX x) = inX x) (hW : ∀ N : SpaceW, h (inW N) = inW (resW h N))
    (c : ShortIdx) (N : SpaceW) :
    resW h (Rmat c * N * Kc c) = Rmat c * resW h N * Kc c := by
  have e1 : ∀ N : SpaceW, gmul (inX (Pi.single c 1)) (inW N) =
      inW ((8 : ℚ)⁻¹ • (Rmat c * N * Kc c)) := by
    intro N
    rw [gmul_inW_eq rfl]
    refine congrArg inW ?_
    have := Lw_inX_smul_single 1 c N
    rw [one_smul] at this
    rw [this]
    norm_num
  have h1 := hh (inX (Pi.single c 1)) (inW N)
  rw [e1, hX, hW, hW, e1] at h1
  have h2 := congrArg (fun w : SpaceB => w.2.2) h1
  change resW h ((8 : ℚ)⁻¹ • (Rmat c * N * Kc c)) = (8 : ℚ)⁻¹ • (Rmat c * resW h N * Kc c) at h2
  rw [map_smul] at h2
  exact smul_right_injective _ (by norm_num : (8 : ℚ)⁻¹ ≠ 0) h2

theorem eq_one_of_fixes_A_X_W {a : symMat} {β : SpaceX} {N₀ : SpaceW}
    (hlam : Function.Injective (shortEig a)) (hβ : ∀ c, β c ≠ 0) (hN₀ : N₀ ≠ 0)
    {h : SpaceB ≃ₗ[ℚ] SpaceB} (hh : h ∈ AutO) (ha : h (inA a) = inA a)
    (hb : h (inX β) = inX β) (hw : h (inW N₀) = inW N₀) : h = 1 := by
  obtain ⟨hmul, hiso⟩ := mem_AutO.1 hh
  have hsingle := fix_inX_single hmul hlam hβ ha hb
  have hX := fix_inX hsingle
  have hA := fix_inA hmul hsingle
  have hW := apply_inW_of_fix hiso hA hX
  have hR := resW_mul_sym_of_fix hmul hA hW
  obtain ⟨c, hc⟩ := exists_eq_smul_of_intertwines (resW h) hR (resW_Rmat_mul_Kc hmul hX hW)
  have hc1 : c = 1 := by
    have h1 : resW h N₀ = N₀ := by rw [resW_apply, hw]
    rw [hc] at h1
    by_contra hne
    apply hN₀
    have h2 : (c - 1) • N₀ = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
  have hWfix : ∀ N, h (inW N) = inW N := fun N => by rw [hW, hc, hc1, one_smul]
  refine LinearEquiv.ext fun v => ?_
  have hv : v = inA v.1 + inX v.2.1 + inW v.2.2 :=
    Prod.ext (by simp) (Prod.ext (by simp) (by simp))
  calc h v = h (inA v.1 + inX v.2.1 + inW v.2.2) := congrArg h hv
    _ = inA v.1 + inX v.2.1 + inW v.2.2 := by rw [map_add, map_add, hA, hX, hWfix]
    _ = v := hv.symm
    _ = (1 : SpaceB ≃ₗ[ℚ] SpaceB) v := rfl

theorem sum_smul_basisB_eq_inX (β : SpaceX) :
    ∑ c : ShortIdx, β c • basisB (Sum.inr (Sum.inl c)) = inX β := by
  have h1 : ∀ c, basisB (Sum.inr (Sum.inl c)) = inXₗ (Pi.single c 1) := fun c =>
    basisB_inr_inl c
  have h2 : ∑ c : ShortIdx, β c • (Pi.single c 1 : SpaceX) = β := by
    ext d
    simp [Pi.single_apply]
  simp only [h1, ← map_smul, ← map_sum, h2]
  rfl

theorem basisB_inr_inl_eq_Xlift (c : ShortIdx) :
    basisB (Sum.inr (Sum.inl c)) = inX (Xlift (rep c.1)) := by
  rw [basisB_inr_inl, Xlift_rep_eq]

theorem exists_equiv_of_isometry (f : SpaceB →ₗ[ℚ] SpaceB)
    (hiso : ∀ u v, bform (f u) (f v) = bform u v) : ∃ g : SpaceB ≃ₗ[ℚ] SpaceB, ∀ u, g u = f u := by
  have hinj : Function.Injective f := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun u hu => ?_)
    by_contra hne
    have h1 := bform_self_pos hne
    rw [← hiso, hu] at h1
    simp at h1
  exact ⟨LinearEquiv.ofInjectiveEndo f hinj, fun u => rfl⟩

theorem eq_one_of_fixes_three_vectors {a₀ : symMat} {β : SpaceX} {N₀ : SpaceW}
    (hlam : Function.Injective (shortEig a₀)) (hβ : ∀ c, β c ≠ 0) (hN₀ : N₀ ≠ 0)
    {a b w : SpaceB} (ha : a = inA a₀) (hb : b = ∑ c, β c • basisB (Sum.inr (Sum.inl c)))
    (hw : w = inW N₀) {h : SpaceB ≃ₗ[ℚ] SpaceB} (hh : h ∈ AutO) (hha : h a = a) (hhb : h b = b)
    (hhw : h w = w) : h = 1 := by
  rw [sum_smul_basisB_eq_inX] at hb
  subst ha hb hw
  exact eq_one_of_fixes_A_X_W hlam hβ hN₀ hh hha hhb hhw

theorem eq_of_apply_eq_three_vectors {a₀ : symMat} {β : SpaceX} {N₀ : SpaceW}
    (hlam : Function.Injective (shortEig a₀)) (hβ : ∀ c, β c ≠ 0) (hN₀ : N₀ ≠ 0)
    {a b w : SpaceB} (ha : a = inA a₀) (hb : b = ∑ c, β c • basisB (Sum.inr (Sum.inl c)))
    (hw : w = inW N₀) {g h : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) (hh : h ∈ AutO)
    (hga : g a = h a) (hgb : g b = h b) (hgw : g w = h w) : g = h := by
  have hq : g⁻¹ * h = 1 := by
    refine eq_one_of_fixes_three_vectors hlam hβ hN₀ ha hb hw (AutO.mul_mem (AutO.inv_mem hg) hh)
      ?_ ?_ ?_
    · change g.symm (h a) = a
      rw [← hga]
      exact g.symm_apply_apply a
    · change g.symm (h b) = b
      rw [← hgb]
      exact g.symm_apply_apply b
    · change g.symm (h w) = w
      rw [← hgw]
      exact g.symm_apply_apply w
  exact inv_mul_eq_one.1 hq

theorem rational_three_vector_separation {a₀ : symMat} {β : SpaceX} {N₀ : SpaceW}
    (hlam : Function.Injective (shortEig a₀)) (hβ : ∀ c, β c ≠ 0) (hN₀ : N₀ ≠ 0)
    {a b w : SpaceB} (ha : a = inA a₀) (hb : b = ∑ c, β c • basisB (Sum.inr (Sum.inl c)))
    (hw : w = inW N₀) :
    (∀ f : SpaceB →ₗ[ℚ] SpaceB, (∀ u v, bform (f u) (f v) = bform u v) →
      (∀ u v, f (gmul u v) = gmul (f u) (f v)) → f a = a → f b = b → f w = w →
      f = LinearMap.id) ∧
    (∀ h : SpaceB ≃ₗ[ℚ] SpaceB, h ∈ AutO → h a = a → h b = b → h w = w → h = 1) ∧
    (∀ g h : SpaceB ≃ₗ[ℚ] SpaceB, g ∈ AutO → h ∈ AutO → g a = h a → g b = h b → g w = h w →
      g = h) := by
  refine ⟨fun f hiso hmul hfa hfb hfw => ?_, fun h hh hha hhb hhw =>
    eq_one_of_fixes_three_vectors hlam hβ hN₀ ha hb hw hh hha hhb hhw,
    fun g h hg hh hga hgb hgw =>
      eq_of_apply_eq_three_vectors hlam hβ hN₀ ha hb hw hg hh hga hgb hgw⟩
  obtain ⟨g, hg⟩ := exists_equiv_of_isometry f hiso
  have hgmem : g ∈ AutO := mem_AutO.2 ⟨fun u v => by rw [hg, hg, hg, hmul],
    fun u v => by rw [hg, hg, hiso]⟩
  have h1 : g = 1 := eq_one_of_fixes_three_vectors hlam hβ hN₀ ha hb hw hgmem
    (by rw [hg, hfa]) (by rw [hg, hfb]) (by rw [hg, hfw])
  refine LinearMap.ext fun u => ?_
  rw [← hg, h1]
  rfl

theorem three_vector_separation_Gmat {a₀ : symMat} {β : SpaceX} {N₀ : SpaceW}
    (hlam : Function.Injective (shortEig a₀)) (hβ : ∀ c, β c ≠ 0) (hN₀ : N₀ ≠ 0)
    {a b w : SpaceB} (ha : a = inA a₀) (hb : b = ∑ c, β c • basisB (Sum.inr (Sum.inl c)))
    (hw : w = inW N₀) :
    (∀ h ∈ Generated.Gmat, h a = a → h b = b → h w = w → h = 1) ∧
    (∀ g ∈ Generated.Gmat, ∀ h ∈ Generated.Gmat, g a = h a → g b = h b → g w = h w → g = h) :=
  ⟨fun _ hh hha hhb hhw => eq_one_of_fixes_three_vectors hlam hβ hN₀ ha hb hw
      (Generated.Gmat_le_AutO hh) hha hhb hhw,
    fun _ hg _ hh hga hgb hgw => eq_of_apply_eq_three_vectors hlam hβ hN₀ ha hb hw
      (Generated.Gmat_le_AutO hg) (Generated.Gmat_le_AutO hh) hga hgb hgw⟩

end CFSG.Monster.Griess
