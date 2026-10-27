module

public import CFSG.OddTranspositions.PartThree.FiveReflection
import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
import CFSG.LocalAnalysis.ComponentInitial.LinearOrthogonalBasis

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix Module

section Transport

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [CommRing F]

theorem conj_mem_fischerTransvections_iff {b b' : LinearMap.BilinForm F (ι → F)} (g₀ : GL ι F)
    (hiso : ∀ x y, b' ((g₀ : Matrix ι ι F) *ᵥ x) ((g₀ : Matrix ι ι F) *ᵥ y) = b x y)
    (g : GL ι F) :
    g₀ * g * g₀⁻¹ ∈ CFSG.Open.fischerTransvections (fun x y => -2 * b' x y)
        (fun v => b' v v = 1) ↔
      g ∈ CFSG.Open.fischerTransvections (fun x y => -2 * b x y) (fun v => b v v = 1) := by
  set P : Matrix ι ι F := (g₀ : Matrix ι ι F) with hP
  set Q : Matrix ι ι F := ((g₀⁻¹ : GL ι F) : Matrix ι ι F) with hQ
  have hl : ∀ x, Q *ᵥ (P *ᵥ x) = x := fun x => by
    rw [hP, hQ, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hr : ∀ x, P *ᵥ (Q *ᵥ x) = x := fun x => by
    rw [hP, hQ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hconj : ∀ x, ((g₀ * g * g₀⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ x =
      P *ᵥ ((g : Matrix ι ι F) *ᵥ (Q *ᵥ x)) := fun x => by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨v', hv', hg⟩
    refine ⟨Q *ᵥ v', ?_, fun x => ?_⟩
    · show b (Q *ᵥ v') (Q *ᵥ v') = 1
      rw [← hiso, hr]
      exact hv'
    · have h1 := hg (P *ᵥ x)
      rw [hconj, hl] at h1
      have h2 := congrArg (fun z => Q *ᵥ z) h1
      simp only [hl, Matrix.mulVec_add, Matrix.mulVec_smul] at h2
      have key : b' (P *ᵥ x) v' = b x (Q *ᵥ v') := by
        have := hiso x (Q *ᵥ v')
        rwa [hr] at this
      rw [h2]
      show x + (-2 * b' (P *ᵥ x) v') • (Q *ᵥ v') = x + (-2 * b x (Q *ᵥ v')) • (Q *ᵥ v')
      rw [key]
  · rintro ⟨v, hv, hg⟩
    refine ⟨P *ᵥ v, ?_, fun x => ?_⟩
    · show b' (P *ᵥ v) (P *ᵥ v) = 1
      rw [hiso]
      exact hv
    · rw [hconj, hg (Q *ᵥ x)]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hr]
      have key : b' x (P *ᵥ v) = b (Q *ᵥ x) v := by
        have := hiso (Q *ᵥ x) v
        rwa [hr] at this
      show x + (-2 * b (Q *ᵥ x) v) • (P *ᵥ v) = x + (-2 * b' x (P *ᵥ v)) • (P *ᵥ v)
      rw [key]

theorem mem_closure_conj_iff {T T' : Set (GL ι F)} (g₀ : GL ι F)
    (hT : ∀ g, g ∈ T ↔ g₀ * g * g₀⁻¹ ∈ T') (g : GL ι F) :
    g ∈ Subgroup.closure T ↔ g₀ * g * g₀⁻¹ ∈ Subgroup.closure T' := by
  have himg : (MulAut.conj g₀).toMonoidHom '' T = T' := by
    ext g'
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hT g).1 hg
    · intro hg'
      refine ⟨g₀⁻¹ * g' * g₀, (hT _).2 (by simpa [mul_assoc] using hg'), ?_⟩
      simp [mul_assoc]
  rw [← himg, ← MonoidHom.map_closure]
  exact (Subgroup.mem_map_iff_mem (MulAut.conj g₀).injective).symm

theorem fischerCentralQuotientModel_of_conj {G : Type*} [Group G] {D : Set G}
    {H H' : Subgroup (GL ι F)} {T T' : Set (GL ι F)} (g₀ : GL ι F)
    (hH : ∀ g, g ∈ H ↔ g₀ * g * g₀⁻¹ ∈ H') (hT : ∀ g, g ∈ T ↔ g₀ * g * g₀⁻¹ ∈ T')
    (h : CFSG.Open.fischerCentralQuotientModel D H T) :
    CFSG.Open.fischerCentralQuotientModel D H' T' := by
  obtain ⟨φ, hφ⟩ := h
  let e : H ≃* H' :=
    { toFun := fun h => ⟨g₀ * h * g₀⁻¹, (hH h).1 h.2⟩
      invFun := fun h => ⟨g₀⁻¹ * h * g₀, (hH _).2 (by simp [mul_assoc])⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  let ψ : H ⧸ Subgroup.center H ≃* H' ⧸ Subgroup.center H' :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  refine ⟨φ.trans ψ, fun g => ?_⟩
  rw [hφ g]
  constructor
  · rintro ⟨h, hhT, hφg⟩
    exact ⟨e h, (hT _).1 hhT, by rw [MulEquiv.trans_apply, hφg]; rfl⟩
  · rintro ⟨h', hh'T, hφg⟩
    refine ⟨e.symm h', (hT _).2 (by simpa [e, mul_assoc] using hh'T), ?_⟩
    apply ψ.injective
    rw [← MulEquiv.trans_apply, hφg]
    exact (congrArg (QuotientGroup.mk : H' → H' ⧸ Subgroup.center H')
      (e.apply_symm_apply h')).symm

end Transport

section Classification

theorem exists_orthogonal_basis_one_last {k : ℕ}
    {b : LinearMap.BilinForm (ZMod 5) (Fin (k + 1) → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ (e : Basis (Fin (k + 1)) (ZMod 5) (Fin (k + 1) → ZMod 5)) (c : ZMod 5), c ≠ 0 ∧
      (∀ i j, i ≠ j → b (e i) (e j) = 0) ∧ (∀ i, i ≠ Fin.last k → b (e i) (e i) = 1) ∧
      b (e (Fin.last k)) (e (Fin.last k)) = c := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hB : b.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => by rw [hsym]; exact hy x⟩
  have hBs : b.IsSymm := ⟨hsym⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · let e : Basis (Fin 1) (ZMod 5) (Fin 1 → ZMod 5) := Pi.basisFun (ZMod 5) (Fin 1)
    refine ⟨e, b (e (Fin.last 0)) (e (Fin.last 0)), ?_, ?_, ?_, rfl⟩
    · intro h0
      have hz : e (Fin.last 0) = 0 := by
        refine hnd _ fun y => ?_
        have hy : y = y 0 • e (Fin.last 0) := by
          funext i
          fin_cases i
          simp [e]
        rw [hy, map_smul, h0, smul_zero]
      exact e.ne_zero _ hz
    · intro i j hij
      exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
    · intro i hi
      exact absurd (Fin.ext (by have h := i.isLt; show (i : ℕ) = 0; omega)) hi
  · have hodd : Odd (Nat.card (ZMod 5)) := by
      rw [Nat.card_zmod]
      decide
    have hfin : finrank (ZMod 5) (Fin (k + 1) → ZMod 5) = k + 1 := Module.finrank_fin_fun _
    obtain ⟨hex, hbasis⟩ :=
      @CFSG.LocalAnalysis.ComponentInitial.finite_odd_symmetric_equal_value_orthogonal_basis
        (ZMod 5) (ZMod.instField 5) (Fin (k + 1) → ZMod 5) Pi.addCommGroup
        (Pi.Function.module _ _ _)
        (by exact (inferInstance : Module.Finite (ZMod 5) (Fin (k + 1) → ZMod 5)))
        (inferInstance : Finite (ZMod 5)) hodd (k + 1) hfin (by omega) b hB hBs
    obtain ⟨v, hv⟩ := hex 1 one_ne_zero
    obtain ⟨e₀, he₀, -, he₁, hel₀⟩ := hbasis 1 v one_ne_zero hv
    let e : Basis (Fin (k + 1)) (ZMod 5) (Fin (k + 1) → ZMod 5) := e₀
    have he : ∀ i j, i ≠ j → b (e i) (e j) = 0 := fun i j hij => he₀ hij
    have he1 : ∀ i, i ≠ Fin.last k → b (e i) (e i) = 1 := fun i hi =>
      he₁ i (by have := Fin.val_lt_last hi; omega)
    have hel : b (e (Fin.last k)) (e (Fin.last k)) ≠ 0 := hel₀ _ (by simp)
    exact ⟨e, _, hel, he, he1, rfl⟩

theorem exists_sq_mul_eq_neg_fiveCoeff {c : ZMod 5} (hc : c ≠ 0) :
    ∃ (ε : Bool) (a : ZMod 5), a ≠ 0 ∧ a ^ 2 * c = -(if ε then 1 else 2) := by
  revert c
  decide

theorem exists_linearEquiv_fiveForm_of_bilin {k : ℕ}
    {b : LinearMap.BilinForm (ZMod 5) (Fin (k + 1) → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ (ε : Bool) (A : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5)),
      ∀ x y, fiveForm k ε (A x) (A y) = b x y := by
  obtain ⟨e, c, hc, hort, hone, hlast⟩ := exists_orthogonal_basis_one_last hsym hnd
  obtain ⟨ε, a, ha, hac⟩ := exists_sq_mul_eq_neg_fiveCoeff hc
  let u : (ZMod 5)ˣ := Units.mkOfMulEqOne a a⁻¹ (five_mul_inv_cancel ha)
  let w : Fin (k + 1) → (ZMod 5)ˣ := fun i => if i = Fin.last k then u else 1
  let e' := e.unitsSMul w
  have hort' : ∀ i j, i ≠ j → b (e' i) (e' j) = 0 := fun i j hij => by
    simp only [e', Basis.unitsSMul_apply, Units.smul_def, map_smul, LinearMap.smul_apply,
      hort i j hij, smul_zero]
  have hone' : ∀ i, i ≠ Fin.last k → b (e' i) (e' i) = 1 := fun i hi => by
    simp [e', Basis.unitsSMul_apply, w, hi, hone i hi]
  have hlast' : b (e' (Fin.last k)) (e' (Fin.last k)) = -(if ε then 1 else 2) := by
    simp only [e', Basis.unitsSMul_apply, Units.smul_def, w, if_true, map_smul,
      LinearMap.smul_apply, hlast, smul_eq_mul, u, Units.val_mkOfMulEqOne]
    linear_combination hac
  have hexp : ∀ x y, b x y = ∑ i, e'.repr x i * (e'.repr y i * b (e' i) (e' i)) := by
    intro x y
    conv_lhs => rw [← e'.sum_repr x, ← e'.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    calc ∑ j, e'.repr y j * ∑ i, e'.repr x i * b (e' i) (e' j)
        = ∑ j, e'.repr y j * (e'.repr x j * b (e' j) (e' j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single j (fun i _ hij => by rw [hort' i j hij, mul_zero])
            (fun hj => absurd (Finset.mem_univ j) hj)]
      _ = ∑ i, e'.repr x i * (e'.repr y i * b (e' i) (e' i)) :=
          Finset.sum_congr rfl fun i _ => by ring
  refine ⟨ε, e'.equivFun, fun x y => ?_⟩
  have hsum : ∑ i : Fin k, e'.repr x i.castSucc *
      (e'.repr y i.castSucc * b (e' i.castSucc) (e' i.castSucc)) =
      ∑ i : Fin k, e'.repr x i.castSucc * e'.repr y i.castSucc :=
    Finset.sum_congr rfl fun i _ => by rw [hone' i.castSucc (Fin.castSucc_lt_last i).ne, mul_one]
  rw [hexp x y, Fin.sum_univ_castSucc, hsum, hlast']
  simp only [fiveForm, Basis.equivFun_apply]
  ring

end Classification

theorem exists_isFiveReflectionModel_of_fischerModel {X : Type*} [Group X] {E : Set X} {k : ℕ}
    {b : LinearMap.BilinForm (ZMod 5) (Fin (k + 1) → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (h : CFSG.Open.fischerCentralQuotientModel E
      (Subgroup.closure
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) :
    ∃ ε : Bool, IsFiveReflectionModel k ε true E := by
  obtain ⟨ε, A, hA⟩ := exists_linearEquiv_fiveForm_of_bilin hsym hnd
  refine ⟨ε, ?_⟩
  let g₀ : GL (Fin (k + 1)) (ZMod 5) :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv A)
  have hg₀ : ∀ x, (g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = A x := fun x => by
    have h1 := Matrix.GeneralLinearGroup.toLin_apply g₀ x
    simp only [g₀, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hiso : ∀ x y, fiveBilin k ε true ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = b x y := by
    intro x y
    rw [hg₀, hg₀, fiveBilin_apply, hA]
    simp [fiveSignRep]
  have hT := conj_mem_fischerTransvections_iff g₀ hiso
  rw [fischerTransvections_fiveBilin] at hT
  exact fischerCentralQuotientModel_of_conj g₀ (mem_closure_conj_iff g₀ fun g => (hT g).symm)
    (fun g => (hT g).symm) h

end CFSG.OddTranspositions.PartThree

end
