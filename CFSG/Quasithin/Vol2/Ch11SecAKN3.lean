module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.AKN

open Matrix Module
open scoped commutatorElement

variable {K : Type*} [Field K]

theorem pow_three_eq_zero {N : Matrix (Fin 3) (Fin 3) K} (hN : IsNilpotent N) : N ^ 3 = 0 := by
  have h1 : N.charpoly = Polynomial.X ^ 3 := by
    have := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
    rw [Fintype.card_fin] at this
    exact sub_eq_zero.mp this.eq_zero
  have h2 := Matrix.aeval_self_charpoly N
  rwa [h1, Polynomial.aeval_X_pow] at h2

theorem mulVec_pow_comm {A N : Matrix (Fin 3) (Fin 3) K} (h : A * N = N * A) (k : ℕ)
    (v : Fin 3 → K) : A *ᵥ (N ^ k *ᵥ v) = N ^ k *ᵥ (A *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, (Commute.pow_right h k).eq]

theorem mem_span_three {v : Fin 3 → (Fin 3 → K)} (hv : LinearIndependent K v) (x : Fin 3 → K) :
    ∃ a : Fin 3 → K, x = a 0 • v 0 + a 1 • v 1 + a 2 • v 2 := by
  have hb := basisOfLinearIndependentOfCardEqFinrank hv (by simp)
  set b := basisOfLinearIndependentOfCardEqFinrank hv (by simp) with hbdef
  refine ⟨b.repr x, ?_⟩
  have h := b.sum_repr x
  rw [Fin.sum_univ_three] at h
  simp only [hbdef, coe_basisOfLinearIndependentOfCardEqFinrank] at h
  exact h.symm

theorem exists_flag_basis {N : Matrix (Fin 3) (Fin 3) K} (hN0 : N ≠ 0) (hN3 : N ^ 3 = 0) :
    ∃ v : Fin 3 → (Fin 3 → K), LinearIndependent K v ∧
      ∀ A : Matrix (Fin 3) (Fin 3) K, A * N = N * A →
        (∃ a : K, A *ᵥ v 0 = a • v 0) ∧ ∃ a b : K, A *ᵥ v 1 = a • v 1 + b • v 0 := by
  by_cases hN2 : N ^ 2 = 0
  ·
    obtain ⟨w, hw⟩ : ∃ w : Fin 3 → K, N *ᵥ w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hN0 (Matrix.ext_iff_mulVec.mpr fun x => by rw [hall x, zero_mulVec])
    have hNN : ∀ x, N *ᵥ (N *ᵥ x) = 0 := fun x => by
      rw [mulVec_mulVec, ← sq, hN2, zero_mulVec]
    set f := Matrix.toLin' N with hf
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    rw [finrank_fin_fun] at hrk
    have hle : LinearMap.range f ≤ LinearMap.ker f := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply, Matrix.toLin'_apply, hNN]
    have hr1 : finrank K (LinearMap.range f) = 1 := by
      have h1 := Submodule.finrank_mono hle
      have h2 : 1 ≤ finrank K (LinearMap.range f) := by
        rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
        intro h0
        apply hw
        have : N *ᵥ w ∈ LinearMap.range f := ⟨w, by rw [hf, Matrix.toLin'_apply]⟩
        rw [h0] at this
        exact this
      omega
    have hk2 : finrank K (LinearMap.ker f) = 2 := by omega
    have hrange : LinearMap.range f = K ∙ (N *ᵥ w) := by
      symm
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_singleton_le_iff_mem]
        exact ⟨w, by rw [hf, Matrix.toLin'_apply]⟩
      · rw [finrank_span_singleton hw, hr1]
    obtain ⟨u, huk, hu⟩ : ∃ u ∈ LinearMap.ker f, u ∉ K ∙ (N *ᵥ w) := by
      by_contra hall
      push Not at hall
      have hle2 : LinearMap.ker f ≤ K ∙ (N *ᵥ w) := fun u hu => hall u hu
      have := Submodule.finrank_mono hle2
      rw [finrank_span_singleton hw, hk2] at this
      omega
    have huN : N *ᵥ u = 0 := by
      rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply] at huk
      exact huk
    have hli2 : LinearIndependent K ![N *ᵥ w, u] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · rw [ht, zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.mp hst).resolve_right hw, ht⟩
      · exfalso
        apply hu
        have : u = (-(s / t)) • (N *ᵥ w) := by
          have h3 : t • u = -(s • (N *ᵥ w)) := eq_neg_of_add_eq_zero_right hst
          calc u = t⁻¹ • (t • u) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
            _ = (-(s / t)) • (N *ᵥ w) := by
              rw [h3, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hkspan : LinearMap.ker f = Submodule.span K {N *ᵥ w, u} := by
      symm
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]
        intro x hx
        rcases hx with rfl | rfl
        · rw [SetLike.mem_coe, LinearMap.mem_ker, hf, Matrix.toLin'_apply, hNN]
        · exact huk
      · rw [hk2, show ({N *ᵥ w, u} : Set (Fin 3 → K)) = Set.range ![N *ᵥ w, u] by
          rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
            Set.singleton_union]]
        rw [finrank_span_eq_card hli2]
        simp
    refine ⟨![N *ᵥ w, u, w], ?_, fun A hA => ⟨?_, ?_⟩⟩
    ·
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_three] at hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hg
      have hg2 : g 2 = 0 := by
        have := congrArg (N *ᵥ ·) hg
        simp only [mulVec_add, mulVec_smul, hNN, huN, smul_zero, zero_add, mulVec_zero] at this
        exact (smul_eq_zero.mp this).resolve_right hw
      rw [hg2, zero_smul, add_zero] at hg
      have h01 := (LinearIndependent.pair_iff.mp hli2) (g 0) (g 1) hg
      intro i
      fin_cases i
      · exact h01.1
      · exact h01.2
      · exact hg2
    ·
      have hmem : A *ᵥ (N *ᵥ w) ∈ LinearMap.range f := by
        rw [show A *ᵥ (N *ᵥ w) = N *ᵥ (A *ᵥ w) by
          rw [mulVec_mulVec, mulVec_mulVec, hA]]
        exact ⟨A *ᵥ w, by rw [hf, Matrix.toLin'_apply]⟩
      rw [hrange, Submodule.mem_span_singleton] at hmem
      obtain ⟨a, ha⟩ := hmem
      exact ⟨a, by simpa using ha.symm⟩
    ·
      have hmem : A *ᵥ u ∈ LinearMap.ker f := by
        rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply, mulVec_mulVec, ← hA, ← mulVec_mulVec,
          huN, mulVec_zero]
      rw [hkspan, Submodule.mem_span_pair] at hmem
      obtain ⟨a, b, hab⟩ := hmem
      exact ⟨b, a, by simpa [add_comm] using hab.symm⟩
  ·
    obtain ⟨w, hw⟩ : ∃ w : Fin 3 → K, N ^ 2 *ᵥ w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hN2 (Matrix.ext_iff_mulVec.mpr fun x => by rw [hall x, zero_mulVec])
    have h4 : N ^ 4 = 0 := by rw [pow_succ, hN3, zero_mul]
    have hA2 : N ^ 2 *ᵥ (N ^ 2 *ᵥ w) = 0 := by
      rw [mulVec_mulVec, ← pow_add, show (2 + 2 : ℕ) = 4 from rfl, h4, zero_mulVec]
    have hB2 : N ^ 2 *ᵥ (N *ᵥ w) = 0 := by rw [mulVec_mulVec, ← pow_succ, hN3, zero_mulVec]
    have hC1 : N *ᵥ (N ^ 2 *ᵥ w) = 0 := by rw [mulVec_mulVec, ← pow_succ', hN3, zero_mulVec]
    have hD1 : N *ᵥ (N *ᵥ w) = N ^ 2 *ᵥ w := by rw [mulVec_mulVec, ← sq]
    have hli : LinearIndependent K ![N ^ 2 *ᵥ w, N *ᵥ w, w] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_three] at hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hg
      have e2 := congrArg (N ^ 2 *ᵥ ·) hg
      simp only [mulVec_add, mulVec_smul, hA2, hB2, smul_zero, zero_add, mulVec_zero] at e2
      have hg2 : g 2 = 0 := (smul_eq_zero.mp e2).resolve_right hw
      rw [hg2, zero_smul, add_zero] at hg
      have e1 := congrArg (N *ᵥ ·) hg
      simp only [mulVec_add, mulVec_smul, hC1, hD1, smul_zero, zero_add, mulVec_zero] at e1
      have hg1 : g 1 = 0 := (smul_eq_zero.mp e1).resolve_right hw
      rw [hg1, zero_smul, add_zero] at hg
      have hg0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hw
      intro i
      fin_cases i
      · exact hg0
      · exact hg1
      · exact hg2
    refine ⟨![N ^ 2 *ᵥ w, N *ᵥ w, w], hli, fun A hA => ?_⟩
    obtain ⟨a, ha⟩ := mem_span_three hli (A *ᵥ w)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at ha ⊢
    refine ⟨⟨a 2, ?_⟩, ⟨a 2, a 1, ?_⟩⟩
    · rw [mulVec_pow_comm hA 2 w, ha]
      simp only [mulVec_add, mulVec_smul, hA2, hB2, smul_zero, zero_add]
    · rw [show A *ᵥ (N *ᵥ w) = N *ᵥ (A *ᵥ w) by rw [mulVec_mulVec, mulVec_mulVec, hA], ha]
      simp only [mulVec_add, mulVec_smul, hC1, hD1, smul_zero, zero_add]
      rw [add_comm]

noncomputable def conjB (b : Basis (Fin 3) K (Fin 3 → K)) :
    Matrix (Fin 3) (Fin 3) K ≃ₐ[K] Matrix (Fin 3) (Fin 3) K :=
  Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)

theorem conjB_apply (b : Basis (Fin 3) K (Fin 3 → K)) (A : Matrix (Fin 3) (Fin 3) K)
    (i j : Fin 3) : conjB b A i j = b.repr (A *ᵥ b j) i := by
  simp [conjB, LinearMap.toMatrixAlgEquiv_apply, Matrix.toLinAlgEquiv'_apply]

@[expose] def IsUT (M : Matrix (Fin 3) (Fin 3) K) : Prop := M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

theorem IsUT.mul_apply_self {M M' : Matrix (Fin 3) (Fin 3) K} (h : IsUT M) (h' : IsUT M')
    (i : Fin 3) : (M * M') i i = M i i * M' i i := by
  obtain ⟨h10, h20, h21⟩ := h
  obtain ⟨h10', h20', h21'⟩ := h'
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h10', h20', h21']

theorem IsUT.mul {M M' : Matrix (Fin 3) (Fin 3) K} (h : IsUT M) (h' : IsUT M') :
    IsUT (M * M') := by
  obtain ⟨h10, h20, h21⟩ := h
  obtain ⟨h10', h20', h21'⟩ := h'
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h10', h20', h21']

theorem sub_one_pow_three_of_isUT {M : Matrix (Fin 3) (Fin 3) K} (h : IsUT M)
    (hd : ∀ i, M i i = 1) : (M - 1) ^ 3 = 0 := by
  obtain ⟨h10, h20, h21⟩ := h
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, h10, h20, h21, h0, h1,
      h2]

theorem isUT_conjB {N : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → (Fin 3 → K)}
    (hli : LinearIndependent K v)
    (hflag : ∀ A : Matrix (Fin 3) (Fin 3) K, A * N = N * A →
      (∃ a : K, A *ᵥ v 0 = a • v 0) ∧ ∃ a b : K, A *ᵥ v 1 = a • v 1 + b • v 0)
    {A : Matrix (Fin 3) (Fin 3) K} (hA : A * N = N * A) :
    IsUT (conjB (basisOfLinearIndependentOfCardEqFinrank hli (by simp)) A) := by
  obtain ⟨⟨a, ha⟩, ⟨a', b', hb⟩⟩ := hflag A hA
  have hb0 : (basisOfLinearIndependentOfCardEqFinrank hli (by simp)) 0 = v 0 := by simp
  have hb1 : (basisOfLinearIndependentOfCardEqFinrank hli (by simp)) 1 = v 1 := by simp
  refine ⟨?_, ?_, ?_⟩ <;> rw [conjB_apply]
  · rw [hb0, ha, ← hb0, map_smul, Basis.repr_self]
    simp
  · rw [hb0, ha, ← hb0, map_smul, Basis.repr_self]
    simp
  · rw [hb1, hb, ← hb0, ← hb1, map_add, map_smul, map_smul, Basis.repr_self, Basis.repr_self]
    simp

theorem pow_four_eq_one_of_mem_commutator [CharP K 2] {c : GL (Fin 3) K} (hc : c ≠ 1) {k : ℕ}
    (hck : c ^ 2 ^ k = 1) {H : Subgroup (GL (Fin 3) K)} (hH : ∀ h ∈ H, h * c = c * h)
    {x : GL (Fin 3) K} (hx : x ∈ ⁅H, H⁆) : x ^ 4 = 1 := by
  set N : Matrix (Fin 3) (Fin 3) K := (c : Matrix (Fin 3) (Fin 3) K) - 1 with hNdef
  have hN0 : N ≠ 0 := by
    intro h
    apply hc
    ext1
    rw [Units.val_one]
    exact sub_eq_zero.mp h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNnil : IsNilpotent N := ⟨2 ^ k, by
    rw [hNdef, sub_pow_char_pow_of_commute 2 k (Commute.one_right _), one_pow,
      ← Units.val_pow_eq_pow_val, hck, Units.val_one, sub_self]⟩
  obtain ⟨v, hli, hflag⟩ := exists_flag_basis hN0 (pow_three_eq_zero hNnil)
  set b := basisOfLinearIndependentOfCardEqFinrank hli (by simp) with hb
  have hcomm : ∀ g : GL (Fin 3) K, g * c = c * g →
      (g : Matrix (Fin 3) (Fin 3) K) * N = N * g := by
    intro g hg
    have := congrArg Units.val hg
    rw [Units.val_mul, Units.val_mul] at this
    rw [hNdef, mul_sub, sub_mul, mul_one, one_mul, this]
  let S : Subgroup (GL (Fin 3) K) :=
    { carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) * N = N * g ∧
        ∀ i, conjB b (g : Matrix (Fin 3) (Fin 3) K) i i = 1}
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        refine ⟨?_, fun i => ?_⟩
        · rw [Units.val_mul, mul_assoc, hh1, ← mul_assoc, hg1, mul_assoc]
        · rw [Units.val_mul, map_mul, (isUT_conjB hli hflag hg1).mul_apply_self
            (isUT_conjB hli hflag hh1), hg2, hh2, one_mul]
      one_mem' := ⟨by rw [Units.val_one, one_mul, mul_one], fun i => by
        rw [Units.val_one, map_one, Matrix.one_apply_eq]⟩
      inv_mem' := by
        rintro g ⟨hg1, hg2⟩
        have hinv : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N =
            N * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          have h1 : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) = 1 := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
          have h2 : ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) * (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          calc ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) * N
              = ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) * N * ((g : Matrix (Fin 3) (Fin 3) K) *
                ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K)) := by rw [h1, mul_one]
            _ = ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) * (N * (g : Matrix (Fin 3) (Fin 3) K)) *
                ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) := by simp only [mul_assoc]
            _ = ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) * ((g : Matrix (Fin 3) (Fin 3) K) * N) *
                ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) := by rw [hg1]
            _ = (((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) * (g : Matrix (Fin 3) (Fin 3) K)) * N *
                ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) := by simp only [mul_assoc]
            _ = N * ((g⁻¹ : GL (Fin 3) K) : Matrix _ _ K) := by rw [h2, one_mul]
        refine ⟨hinv, fun i => ?_⟩
        have h1 := (isUT_conjB hli hflag hg1).mul_apply_self (isUT_conjB hli hflag hinv) i
        rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
          Matrix.one_apply_eq, hg2, one_mul] at h1
        exact h1.symm }
  have hHS : ⁅H, H⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    have hg1 := hcomm g (hH g hg)
    have hh1 := hcomm h (hH h hh)
    have hgi : (g⁻¹ : GL (Fin 3) K) * c = c * g⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hH g hg, mul_assoc, mul_inv_cancel, mul_one]
    have hhi : (h⁻¹ : GL (Fin 3) K) * c = c * h⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hH h hh, mul_assoc, mul_inv_cancel, mul_one]
    have hgi1 := hcomm _ hgi
    have hhi1 := hcomm _ hhi
    have hprod : ⁅g, h⁆ * c = c * ⁅g, h⁆ := by
      rw [commutatorElement_def]
      calc g * h * g⁻¹ * h⁻¹ * c = g * h * g⁻¹ * (h⁻¹ * c) := by group
        _ = c * (g * h * g⁻¹ * h⁻¹) := by
          rw [hhi, ← mul_assoc, mul_assoc (g * h), hgi, ← mul_assoc, mul_assoc g, hH h hh,
            ← mul_assoc, hH g hg]
          group
    refine ⟨hcomm _ hprod, fun i => ?_⟩
    have hdiag : ∀ (a : GL (Fin 3) K), (a : Matrix (Fin 3) (Fin 3) K) * N = N * a →
        ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N = N * (a⁻¹ : GL (Fin 3) K) →
        conjB b (a : Matrix (Fin 3) (Fin 3) K) i i *
          conjB b ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
      intro a ha hai
      rw [← (isUT_conjB hli hflag ha).mul_apply_self (isUT_conjB hli hflag hai), ← map_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, Matrix.one_apply_eq]
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, map_mul, map_mul,
      map_mul]
    have u1 := isUT_conjB hli hflag hg1
    have u2 := isUT_conjB hli hflag hh1
    have u3 := isUT_conjB hli hflag hgi1
    have u4 := isUT_conjB hli hflag hhi1
    rw [(((u1.mul u2).mul u3)).mul_apply_self u4, ((u1.mul u2)).mul_apply_self u3,
      u1.mul_apply_self u2]
    have d1 := hdiag g hg1 hgi1
    have d2 := hdiag h hh1 hhi1
    linear_combination (conjB b ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i) *
      (conjB b (h : Matrix (Fin 3) (Fin 3) K) i i) * d1 + d2
  obtain ⟨hx1, hx2⟩ := hHS hx
  have hx3 : ((x : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 = 0 := by
    apply (conjB b).injective
    rw [map_pow, map_sub, map_one, map_zero]
    exact sub_one_pow_three_of_isUT (isUT_conjB hli hflag hx1) hx2
  have hx4 : ((x : Matrix (Fin 3) (Fin 3) K) - 1) ^ (2 ^ 2) = 0 := by
    rw [show 2 ^ 2 = 1 + 3 from rfl, pow_add, hx3, mul_zero]
  rw [sub_pow_char_pow_of_commute 2 2 (Commute.one_right _), one_pow, sub_eq_zero] at hx4
  ext1
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact hx4

end CFSG.Quasithin.Vol2.Ch11.SecA.AKN
