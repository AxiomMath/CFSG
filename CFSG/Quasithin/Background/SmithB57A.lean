module

public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

namespace SmithB57

open Matrix CFSG.Timmesfeld

theorem card_modEq_card_fix {X : Type*} [Finite X] {r : ℕ} [Fact r.Prime] (f : X → X)
    (hf : ∀ x, f^[r] x = x) : Nat.card X ≡ Nat.card {x // f x = x} [MOD r] := by
  classical
  have : Fintype X := Fintype.ofFinite X
  let g : Function.End X := f
  have h1 : g ^ r ^ 1 = 1 := by
    rw [pow_one]
    funext x
    exact hf x
  have h := Equiv.Perm.card_fixedPoints_modEq (f := g) h1
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h using 2
  rfl

theorem three_dvd_of_ppd {m r d : ℕ} (hm : 0 < m) (hr : IsPrimitivePrimeDivisor r (3 * m))
    (h : r ∣ 2 ^ (m * d) - 1) : 3 ∣ d := by
  have h1 := (hr.dvd_sub_one_iff (by omega) (m * d)).mp h
  rw [mul_comm m d] at h1
  exact (Nat.mul_dvd_mul_iff_right hm).mp h1

theorem ppd_ne_two {m r : ℕ} (hm : 0 < m) (hr : IsPrimitivePrimeDivisor r (3 * m)) : r ≠ 2 :=
  hr.ne_two (by omega)

theorem ppd_ne_three {m r : ℕ} (hm : 0 < m) (hr : IsPrimitivePrimeDivisor r (3 * m)) :
    r ≠ 3 := by
  rintro rfl
  have h := (hr.dvd_sub_one_iff (by omega) 2).mp (by norm_num)
  have : 3 * m ≤ 2 := Nat.le_of_dvd (by norm_num) h
  omega

theorem eq_of_modEq_pow {m r d e : ℕ} (hm : 0 < m) (hr : IsPrimitivePrimeDivisor r (3 * m))
    (hed : e ≤ d) (h : 2 ^ (m * e) ≡ 2 ^ (m * d) [MOD r]) : 3 ∣ d - e := by
  have hle : 2 ^ (m * e) ≤ 2 ^ (m * d) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h1 : r ∣ 2 ^ (m * d) - 2 ^ (m * e) := (Nat.modEq_iff_dvd' hle).mp h
  have h2 : 2 ^ (m * d) - 2 ^ (m * e) = 2 ^ (m * e) * (2 ^ (m * (d - e)) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, ← Nat.mul_add, Nat.add_sub_cancel' hed]
  rw [h2] at h1
  have hcop : Nat.Coprime r (2 ^ (m * e)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hr.prime Nat.prime_two).mpr (ppd_ne_two hm hr))
  exact three_dvd_of_ppd hm hr (hcop.dvd_of_dvd_mul_left h1)

section Field

variable {F : Type} [Field F]

theorem card_submodule [Fintype F] (W : Submodule F (Fin 3 → F)) :
    Nat.card W = Fintype.card F ^ Module.finrank F W := by
  classical
  have : Fintype W := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := W)]

theorem finrank_le_three (W : Submodule F (Fin 3 → F)) : Module.finrank F W ≤ 3 := by
  have := Submodule.finrank_le W
  rwa [Module.finrank_fin_fun F] at this

@[expose] noncomputable def fixSub (y : Matrix (Fin 3) (Fin 3) F) : Submodule F (Fin 3 → F) :=
  LinearMap.ker (Matrix.toLin' (y - 1))

theorem mem_fixSub {y : Matrix (Fin 3) (Fin 3) F} {v : Fin 3 → F} : v ∈ fixSub y ↔ y *ᵥ v = v := by
  rw [fixSub, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero]

theorem iterate_mulVec (y : Matrix (Fin 3) (Fin 3) F) (n : ℕ) (v : Fin 3 → F) :
    (fun w => y *ᵥ w)^[n] v = (y ^ n) *ᵥ v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, Matrix.mulVec_mulVec, ← pow_succ]

variable [Fintype F] {m r : ℕ}

theorem fixSub_eq_bot (hF : Fintype.card F = 2 ^ m) (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {y : Matrix (Fin 3) (Fin 3) F} (hy : y ^ r = 1)
    (hy1 : y ≠ 1) : fixSub y = ⊥ := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hmod := card_modEq_card_fix (r := r) (fun w : Fin 3 → F => y *ᵥ w)
    (fun v => by rw [iterate_mulVec, hy, Matrix.one_mulVec])
  have hcardX : Nat.card (Fin 3 → F) = 2 ^ (m * 3) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hF, ← pow_mul]
  have hcardW : Nat.card {x : Fin 3 → F // y *ᵥ x = x} = 2 ^ (m * Module.finrank F (fixSub y)) := by
    have e : {x : Fin 3 → F // y *ᵥ x = x} ≃ fixSub y :=
      Equiv.subtypeEquivRight (fun v => mem_fixSub.symm)
    rw [Nat.card_congr e, card_submodule, hF, ← pow_mul]
  rw [hcardX, hcardW] at hmod
  set d := Module.finrank F (fixSub y) with hd
  have hd3 : d ≤ 3 := finrank_le_three _
  have hd3' : d ≠ 3 := by
    intro h3
    apply hy1
    have htop : fixSub y = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
    have : Matrix.toLin' (y - 1) = 0 := by
      rw [fixSub, LinearMap.ker_eq_top] at htop
      exact htop
    have h0 : y - 1 = 0 := Matrix.toLin'.injective (by rw [this, map_zero])
    exact sub_eq_zero.mp h0
  have h3 := eq_of_modEq_pow hm hr hd3 hmod.symm
  have hd0 : d = 0 := by omega
  exact Submodule.finrank_eq_zero.mp hd0

theorem eq_top_of_invariant (hF : Fintype.card F = 2 ^ m) (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {y : Matrix (Fin 3) (Fin 3) F} (hy : y ^ r = 1)
    (hy1 : y ≠ 1) {W : Submodule F (Fin 3 → F)} (hW : ∀ w ∈ W, y *ᵥ w ∈ W) (hW0 : W ≠ ⊥) :
    W = ⊤ := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hfix := fixSub_eq_bot hF hm hr hy hy1
  let f : W → W := fun w => ⟨y *ᵥ (w : Fin 3 → F), hW w w.2⟩
  have hit : ∀ (n : ℕ) (w : W), ((f^[n] w : W) : Fin 3 → F) = (y ^ n) *ᵥ (w : Fin 3 → F) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', pow_succ', ← Matrix.mulVec_mulVec, ← ih]
  have hmod := card_modEq_card_fix (r := r) f (fun w => by
    apply Subtype.ext
    rw [hit, hy, Matrix.one_mulVec])
  have hone : Nat.card {x : W // f x = x} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, Subtype.ext (by simp [f])⟩, ?_⟩
    rintro ⟨w, hw⟩
    have h1 : y *ᵥ (w : Fin 3 → F) = w := congrArg Subtype.val hw
    have h2 : (w : Fin 3 → F) ∈ fixSub y := mem_fixSub.mpr h1
    rw [hfix, Submodule.mem_bot] at h2
    apply Subtype.ext
    exact Subtype.ext h2
  rw [hone, card_submodule, hF, ← pow_mul] at hmod
  set d := Module.finrank F W
  have h3 := eq_of_modEq_pow (e := 0) hm hr (Nat.zero_le d) (by simpa using hmod.symm)
  have hd3 : d ≤ 3 := finrank_le_three _
  have hd0 : d ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hd : d = 3 := by omega
  exact Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hd)

end Field

section Cyclic

variable {F : Type} [Field F] [Fintype F] {m r : ℕ}

theorem linearIndependent_cyclic (hF : Fintype.card F = 2 ^ m) (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {y : Matrix (Fin 3) (Fin 3) F} (hy : y ^ r = 1)
    (hy1 : y ≠ 1) {e : Fin 3 → F} (he : e ≠ 0) :
    LinearIndependent F ![e, y *ᵥ e, y *ᵥ (y *ᵥ e)] := by
  have hne : ∀ W : Submodule F (Fin 3 → F), (∀ w ∈ W, y *ᵥ w ∈ W) → W ≠ ⊥ → W = ⊤ :=
    fun W hW hW0 => eq_top_of_invariant hF hm hr hy hy1 hW hW0
  have h1 : y *ᵥ e ∉ Submodule.span F {e} := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hinv : ∀ w ∈ Submodule.span F {e}, y *ᵥ w ∈ Submodule.span F {e} := by
      intro w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [Matrix.mulVec_smul, ← hc, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
    have hW0 : Submodule.span F {e} ≠ ⊥ := by
      rw [Ne, Submodule.span_singleton_eq_bot]
      exact he
    have htop := hne _ hinv hW0
    have hfr := finrank_span_singleton (K := F) he
    rw [htop, finrank_top, Module.finrank_fin_fun] at hfr
    omega
  have h2 : y *ᵥ (y *ᵥ e) ∉ Submodule.span F {e, y *ᵥ e} := by
    intro hmem
    have hinv : ∀ w ∈ Submodule.span F {e, y *ᵥ e}, y *ᵥ w ∈ Submodule.span F {e, y *ᵥ e} := by
      intro w hw
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ hmem)
      exact Submodule.subset_span (by simp)
    have hW0 : Submodule.span F {e, y *ᵥ e} ≠ ⊥ := by
      intro h
      have : e ∈ Submodule.span F {e, y *ᵥ e} := Submodule.subset_span (by simp)
      rw [h, Submodule.mem_bot] at this
      exact he this
    have htop := hne _ hinv hW0
    have hfr : Module.finrank F (Submodule.span F ({e, y *ᵥ e} : Set (Fin 3 → F))) ≤ 2 := by
      classical
      have := finrank_span_le_card (R := F) ({e, y *ᵥ e} : Set (Fin 3 → F))
      refine this.trans ?_
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_insert_le _ _
    rw [htop, finrank_top, Module.finrank_fin_fun] at hfr
    omega
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have hg2 : g 2 = 0 := by
    by_contra h
    apply h2
    have h' : g 2 • (y *ᵥ (y *ᵥ e)) = -(g 0 • e + g 1 • (y *ᵥ e)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hg
    have : y *ᵥ (y *ᵥ e) = (g 2)⁻¹ • (-(g 0 • e + g 1 • (y *ᵥ e))) := by
      rw [← h', smul_smul, inv_mul_cancel₀ h, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))))
  rw [hg2, zero_smul, add_zero] at hg
  have hg1 : g 1 = 0 := by
    by_contra h
    apply h1
    have h' : g 1 • (y *ᵥ e) = -(g 0 • e) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hg
    have : y *ᵥ e = (g 1)⁻¹ • (-(g 0 • e)) := by
      rw [← h', smul_smul, inv_mul_cancel₀ h, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
  rw [hg1, zero_smul, add_zero] at hg
  have hg0 : g 0 = 0 := by
    rcases smul_eq_zero.mp hg with h | h
    · exact h
    · exact absurd h he
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

end Cyclic

section Conj

variable {F : Type} [Field F] [CharP F 2]

theorem add_self_matrix (A : Matrix (Fin 3) (Fin 3) F) : A + A = 0 := by
  ext i j
  simp [← two_mul, CharTwo.two_eq_zero]

theorem sub_one_mul_self {X : Matrix (Fin 3) (Fin 3) F} (hX : X * X = 1) :
    (X - 1) * (X - 1) = 0 := by
  have h : (X - 1) * (X - 1) = X * X - X - X + 1 := by noncomm_ring
  rw [h, hX]
  have h2 : (1 : Matrix (Fin 3) (Fin 3) F) - X - X + 1 = (1 + 1) - (X + X) := by abel
  rw [h2, add_self_matrix, add_self_matrix, sub_zero]

omit [CharP F 2] in
theorem mulVec_eq_add_of_sub (X : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) :
    X *ᵥ v = v + (X - 1) *ᵥ v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]

theorem exists_conj_transvection {X : Matrix (Fin 3) (Fin 3) F} (hX : X * X = 1) (hX1 : X ≠ 1) :
    ∃ Q : Matrix (Fin 3) (Fin 3) F, Q.det = 1 ∧ X * Q = Q * Matrix.transvection 0 2 1 := by
  set N := X - 1 with hN
  have hNN : N * N = 0 := sub_one_mul_self hX
  have hN0 : N ≠ 0 := fun h => hX1 (sub_eq_zero.mp h)
  obtain ⟨x, hx⟩ : ∃ x, N *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hN0
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [hcon v, Matrix.zero_mulVec]
  set w := N *ᵥ x with hw
  have hNw : N *ᵥ w = 0 := by rw [hw, Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  set Ker := LinearMap.ker (Matrix.toLin' N) with hKer
  have hwK : w ∈ Ker := by rw [hKer, LinearMap.mem_ker, Matrix.toLin'_apply]; exact hNw
  have hrk : Module.finrank F (LinearMap.range (Matrix.toLin' N)) + Module.finrank F Ker = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' N)
    rwa [Module.finrank_fin_fun] at this
  have hRK : LinearMap.range (Matrix.toLin' N) ≤ Ker := by
    rintro _ ⟨v, rfl⟩
    rw [hKer, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      hNN, Matrix.zero_mulVec]
  have h1 := Submodule.finrank_mono hRK
  have hR1 : 1 ≤ Module.finrank F (LinearMap.range (Matrix.toLin' N)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    have : w ∈ LinearMap.range (Matrix.toLin' N) := ⟨x, by rw [Matrix.toLin'_apply]⟩
    rw [h, Submodule.mem_bot] at this
    exact hx this
  have hK2 : 1 < Module.finrank F Ker := by omega
  have hwne : w ≠ 0 := hx
  have hlt : Submodule.span F {w} < Ker := by
    refine Submodule.lt_of_le_of_finrank_lt_finrank ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hwK
    · rw [finrank_span_singleton hwne]; exact hK2
  obtain ⟨u, huK, huw⟩ := IsConcreteLE.exists_of_lt hlt
  have hNu : N *ᵥ u = 0 := by rwa [hKer, LinearMap.mem_ker, Matrix.toLin'_apply] at huK
  have hli : LinearIndependent F ![w, u, x] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have hg2 : g 2 = 0 := by
      have := congrArg (fun v => N *ᵥ v) hg
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNw, hNu, smul_zero, zero_add,
        Matrix.mulVec_zero] at this
      rcases smul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hx
    rw [hg2, zero_smul, add_zero] at hg
    have hg1 : g 1 = 0 := by
      by_contra h
      apply huw
      have h' : g 1 • u = -(g 0 • w) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hg
      have : u = (g 1)⁻¹ • (-(g 0 • w)) := by rw [← h', smul_smul, inv_mul_cancel₀ h, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)))
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h hwne
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  set A : Matrix (Fin 3) (Fin 3) F := Matrix.of ![w, u, x] with hA
  have hAu : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp hli
  have hdet : A.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det A).mp hAu |>.ne_zero
  set d : Fin 3 → F := ![1, (A.det)⁻¹, 1] with hd
  refine ⟨Aᵀ * Matrix.diagonal d, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hd, hdet]
  · have hXw : X *ᵥ w = w := by rw [mulVec_eq_add_of_sub, ← hN, hNw, add_zero]
    have hXu : X *ᵥ u = u := by rw [mulVec_eq_add_of_sub, ← hN, hNu, add_zero]
    have hXx : X *ᵥ x = x + w := by rw [mulVec_eq_add_of_sub, ← hN]
    have hcol : ∀ (k : Fin 3) (c : F), Aᵀ *ᵥ Pi.single k c = c • ![w, u, x] k := by
      intro k c
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Matrix.of_apply,
        Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Pi.smul_apply, smul_eq_mul, mul_comm]
    have hQ : ∀ (k : Fin 3) (c : F), (Aᵀ * Matrix.diagonal d) *ᵥ Pi.single k c =
        (d k * c) • ![w, u, x] k := by
      intro k c
      rw [← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single, hcol]
    have hE : ∀ k : Fin 3, Matrix.transvection (0 : Fin 3) 2 (1 : F) *ᵥ Pi.single k 1 =
        Pi.single k 1 + (if k = 2 then Pi.single 0 1 else 0) := by
      intro k
      rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
      congr 1
      fin_cases k <;> ext i <;> fin_cases i <;> simp [Function.update]
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec _ X, ← Matrix.mulVec_mulVec _ (Aᵀ * Matrix.diagonal d), hE, hQ]
    fin_cases j
    · rw [ite_eq_right (by decide), add_zero, hQ]
      simp [hd, hXw]
    · rw [ite_eq_right (by decide), add_zero, hQ]
      simp [hd, Matrix.mulVec_smul, hXu]
    · rw [ite_eq_left (by decide), Matrix.mulVec_add, hQ, hQ]
      simp [hd, hXx]

end Conj

section Decomp

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {m r : ℕ}

omit [Fintype F] [CharP F 2] in
theorem mulVec_cube (y : Matrix (Fin 3) (Fin 3) F) (e : Fin 3 → F) :
    y *ᵥ (y *ᵥ (y *ᵥ e)) = (y ^ 3) *ᵥ e := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, pow_succ, pow_two, mul_assoc]

omit [Fintype F] [CharP F 2] in
theorem pow_three_ne_one (hm : 0 < m) (hr : IsPrimitivePrimeDivisor r (3 * m))
    {y : Matrix (Fin 3) (Fin 3) F} (hy : y ^ r = 1) (hy1 : y ≠ 1) : y ^ 3 ≠ 1 := by
  intro h3
  have : Fact r.Prime := ⟨hr.prime⟩
  have hord : orderOf y = r := orderOf_eq_prime hy hy1
  have h := orderOf_dvd_of_pow_eq_one h3
  rw [hord] at h
  exact ppd_ne_three hm hr ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_three).mp h)

theorem exists_three_involutions (hF : Fintype.card F = 2 ^ m) (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {y : Matrix (Fin 3) (Fin 3) F} (hy : y ^ r = 1)
    (hy1 : y ≠ 1) (hdet : y.det = 1) :
    ∃ Z₁ Z₂ Z₃ : Matrix (Fin 3) (Fin 3) F, y = Z₁ * Z₂ * Z₃ ∧
      (Z₁ * Z₁ = 1 ∧ Z₁ ≠ 1 ∧ Z₁.det = 1) ∧ (Z₂ * Z₂ = 1 ∧ Z₂ ≠ 1 ∧ Z₂.det = 1) ∧
      (Z₃ * Z₃ = 1 ∧ Z₃ ≠ 1 ∧ Z₃.det = 1) := by
  set e : Fin 3 → F := Pi.single 0 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [he] at this
  have hli := linearIndependent_cyclic hF hm hr hy hy1 he0
  set v : Fin 3 → Fin 3 → F := ![e, y *ᵥ e, y *ᵥ (y *ᵥ e)] with hv
  set A : Matrix (Fin 3) (Fin 3) F := Matrix.of v with hA
  have hAu : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp hli
  set Q : Matrix (Fin 3) (Fin 3) F := Aᵀ with hQ
  have hQdet : IsUnit Q.det := by
    rw [hQ, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det A).mp hAu
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQdet
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQdet
  have hcol : ∀ k : Fin 3, Q *ᵥ Pi.single k 1 = v k := by
    intro k
    ext i
    simp only [hQ, Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Matrix.of_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  set c : Fin 3 → F := Q⁻¹ *ᵥ (y *ᵥ (y *ᵥ (y *ᵥ e))) with hc
  have hQc : Q *ᵥ c = y *ᵥ (y *ᵥ (y *ᵥ e)) := by
    rw [hc, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
  set C : Matrix (Fin 3) (Fin 3) F := !![0, 0, c 0; 1, 0, c 1; 0, 1, c 2] with hC
  have hyQ : y * Q = Q * C := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec _ y, ← Matrix.mulVec_mulVec _ Q, hcol]
    fin_cases j
    · have : C *ᵥ Pi.single 0 1 = Pi.single 1 1 := by
        ext i
        fin_cases i <;> simp [hC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      simp only [Fin.zero_eta]
      rw [this, hcol]
      simp [hv]
    · have : C *ᵥ Pi.single 1 1 = Pi.single 2 1 := by
        ext i
        fin_cases i <;> simp [hC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      simp only [Fin.mk_one]
      rw [this, hcol]
      simp [hv]
    · have : C *ᵥ Pi.single 2 1 = c := by
        ext i
        fin_cases i <;> simp [hC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      simp only [Fin.reduceFinMk]
      rw [this, hQc]
      simp [hv]
  have hCdet : C.det = c 0 := by
    rw [hC, Matrix.det_fin_three]
    simp
  have hc0 : c 0 = 1 := by
    have h1 := congrArg Matrix.det hyQ
    rw [Matrix.det_mul, Matrix.det_mul, hdet, one_mul, hCdet] at h1
    have h2 : Q.det * c 0 = Q.det * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel₀ hQdet.ne_zero h2
  set S02 : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0] with hS02
  set S01 : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, 1] with hS01
  set T : Matrix (Fin 3) (Fin 3) F := !![1, 0, c 1; 0, 1, c 2; 0, 0, 1] with hT
  have hCdec : C = S02 * S01 * T := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hC, hS02, hS01, hT, Matrix.mul_apply, Fin.sum_univ_three, hc0]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hS02sq : S02 * S02 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS02, Matrix.mul_apply, Fin.sum_univ_three]
  have hS01sq : S01 * S01 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS01, Matrix.mul_apply, Fin.sum_univ_three]
  have hTsq : T * T = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hT, Matrix.mul_apply, Fin.sum_univ_three, ← two_mul, h2]
  have hS02ne : S02 ≠ 1 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp [hS02] at this
  have hS01ne : S01 ≠ 1 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp [hS01] at this
  have hTne : T ≠ 1 := by
    intro h
    have h1 : c 1 = 0 := by
      have := congrFun (congrFun h 0) 2
      simpa [hT] using this
    have h2' : c 2 = 0 := by
      have := congrFun (congrFun h 1) 2
      simpa [hT] using this
    have hce : c = Pi.single 0 1 := by
      ext i
      fin_cases i
      · simpa using hc0
      · simpa using h1
      · simpa using h2'
    have hfix : (y ^ 3) *ᵥ e = e := by
      rw [← mulVec_cube, ← hQc, hce, hcol]
      simp [hv]
    have hbot := fixSub_eq_bot hF hm hr (y := y ^ 3)
      (by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]) (pow_three_ne_one hm hr hy hy1)
    have hmem : e ∈ fixSub (y ^ 3) := mem_fixSub.mpr hfix
    rw [hbot, Submodule.mem_bot] at hmem
    exact he0 hmem
  have hdetS02 : S02.det = 1 := by
    rw [hS02, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    have : (-1 : F) = 1 := by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, mul_one, h2]
    simp [this]
  have hdetS01 : S01.det = 1 := by
    rw [hS01, Matrix.det_fin_three]
    have : (-1 : F) = 1 := by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, mul_one, h2]
    simp [this]
  have hdetT : T.det = 1 := by
    rw [hT, Matrix.det_fin_three]
    simp
  have hconj : ∀ W : Matrix (Fin 3) (Fin 3) F, W * W = 1 → W ≠ 1 → W.det = 1 →
      (Q * W * Q⁻¹) * (Q * W * Q⁻¹) = 1 ∧ Q * W * Q⁻¹ ≠ 1 ∧ (Q * W * Q⁻¹).det = 1 := by
    intro W hW hW1 hWd
    refine ⟨?_, ?_, ?_⟩
    · calc (Q * W * Q⁻¹) * (Q * W * Q⁻¹) = Q * W * (Q⁻¹ * Q) * W * Q⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQQ', Matrix.mul_one, Matrix.mul_assoc Q W W, hW, Matrix.mul_one, hQQ]
    · intro h
      apply hW1
      calc W = Q⁻¹ * (Q * W * Q⁻¹) * Q := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul, Matrix.mul_assoc,
              hQQ', Matrix.mul_one]
        _ = 1 := by rw [h, Matrix.mul_one, hQQ']
    · rw [Matrix.det_mul, Matrix.det_mul, hWd, mul_one, Matrix.det_nonsing_inv,
        Ring.mul_inverse_cancel _ hQdet]
  refine ⟨Q * S02 * Q⁻¹, Q * S01 * Q⁻¹, Q * T * Q⁻¹, ?_, hconj S02 hS02sq hS02ne hdetS02,
    hconj S01 hS01sq hS01ne hdetS01, hconj T hTsq hTne hdetT⟩
  calc y = y * Q * Q⁻¹ := by rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
    _ = Q * C * Q⁻¹ := by rw [hyQ]
    _ = Q * S02 * Q⁻¹ * (Q * S01 * Q⁻¹) * (Q * T * Q⁻¹) := by
      rw [hCdec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q⁻¹ Q, hQQ', Matrix.one_mul, ← Matrix.mul_assoc Q⁻¹ Q, hQQ',
        Matrix.one_mul]

end Decomp

section Final

variable {F : Type} [Field F] [Fintype F] {m r : ℕ}

theorem exists_orderOf_eq (hF : Fintype.card F = 2 ^ m) (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) :
    ∃ y : GL (Fin 3) F, orderOf y = r ∧ (y : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  classical
  have : Fact r.Prime := ⟨hr.prime⟩
  have hdvd : r ∣ Nat.card (GL (Fin 3) F) := by
    rw [Matrix.card_GL_field]
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (0 : Fin 3)))
    simp only [Fin.val_zero, pow_zero, hF, ← pow_mul]
    rw [mul_comm]
    exact hr.dvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hdvd
  refine ⟨y, hy, ?_⟩
  set δ : Fˣ := Matrix.GeneralLinearGroup.det y with hδ
  have hδr : δ ^ r = 1 := by
    rw [hδ, ← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have hδ1 : δ = 1 := by
    rcases (Nat.dvd_prime hr.prime).mp (orderOf_dvd_of_pow_eq_one hδr) with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      have h1 : r ∣ Fintype.card Fˣ := h ▸ orderOf_dvd_card
      rw [Fintype.card_units, hF] at h1
      have h2 := (hr.dvd_sub_one_iff (by omega) m).mp h1
      have := Nat.le_of_dvd hm h2
      omega
  have := congrArg Units.val hδ1
  simpa [hδ, Matrix.GeneralLinearGroup.val_det_apply] using this

variable [CharP F 2]

@[expose] noncomputable def E02 : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection (0 : Fin 3) 2 1)
    (by rw [Matrix.det_transvection_of_ne _ _ (by decide)]; exact one_ne_zero)

omit [Fintype F] in
theorem exists_conj_E02 {X : GL (Fin 3) F} (hX : X * X = 1) (hX1 : X ≠ 1) :
    ∃ Q : GL (Fin 3) F, (Q : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ X = Q * E02 * Q⁻¹ := by
  have hXm : (X : Matrix (Fin 3) (Fin 3) F) * X = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, hX, Matrix.GeneralLinearGroup.coe_one]
  have hX1m : (X : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
    intro h
    exact hX1 (Units.ext h)
  obtain ⟨Q, hQd, hQ⟩ := exists_conj_transvection hXm hX1m
  let Q' : GL (Fin 3) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Q (by rw [hQd]; exact one_ne_zero)
  refine ⟨Q', hQd, ?_⟩
  have : X * Q' = Q' * E02 := Units.ext hQ
  rw [← this, mul_inv_cancel_right]

theorem exists_conj_product (hF : Fintype.card F = 2 ^ m) (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {τ : GL (Fin 3) F} (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) :
    ∃ g h : GL (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
      (h : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
      orderOf (τ * (g * τ * g⁻¹) * (h * τ * h⁻¹)) = r := by
  have : Fact r.Prime := ⟨hr.prime⟩
  obtain ⟨y, hy, hyd⟩ := exists_orderOf_eq hF hm hr
  have hyr : (y : Matrix (Fin 3) (Fin 3) F) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hy, pow_orderOf_eq_one, Units.val_one]
  have hy1 : (y : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
    intro h
    have : y = 1 := Units.ext h
    rw [this, orderOf_one] at hy
    exact hr.prime.one_lt.ne' hy.symm
  obtain ⟨Z₁, Z₂, Z₃, hyZ, ⟨h1s, h1n, h1d⟩, ⟨h2s, h2n, h2d⟩, ⟨h3s, h3n, h3d⟩⟩ :=
    exists_three_involutions hF hm hr hyr hy1 hyd
  have hlift : ∀ Z : Matrix (Fin 3) (Fin 3) F, Z * Z = 1 → Z ≠ 1 → Z.det = 1 →
      ∃ k : GL (Fin 3) F, (k : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
        (k * τ * k⁻¹ : GL (Fin 3) F) = (Z : Matrix (Fin 3) (Fin 3) F) := by
    intro Z hZs hZn hZd
    let Zg : GL (Fin 3) F :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Z (by rw [hZd]; exact one_ne_zero)
    have hZg2 : Zg * Zg = 1 := Units.ext hZs
    have hZg1 : Zg ≠ 1 := fun h => hZn (congrArg Units.val h)
    obtain ⟨Q, hQd, hQ⟩ := exists_conj_E02 hZg2 hZg1
    obtain ⟨Qτ, hQτd, hQτ⟩ := exists_conj_E02 hτ2 hτ1
    refine ⟨Q * Qτ⁻¹, ?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hQd, one_mul, Matrix.coe_units_inv,
        Matrix.det_nonsing_inv, hQτd, Ring.inverse_one]
    · have : Q * Qτ⁻¹ * τ * (Q * Qτ⁻¹)⁻¹ = Zg := by
        rw [hQτ, hQ]
        group
      rw [this]
      rfl
  obtain ⟨k₁, hk₁d, hk₁⟩ := hlift Z₁ h1s h1n h1d
  obtain ⟨k₂, hk₂d, hk₂⟩ := hlift Z₂ h2s h2n h2d
  obtain ⟨k₃, hk₃d, hk₃⟩ := hlift Z₃ h3s h3n h3d
  have hyk : y = (k₁ * τ * k₁⁻¹) * (k₂ * τ * k₂⁻¹) * (k₃ * τ * k₃⁻¹) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hk₁, hk₂, hk₃]
    exact hyZ
  have hdet_inv_mul : ∀ a b : GL (Fin 3) F, (a : Matrix (Fin 3) (Fin 3) F).det = 1 →
      (b : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ((a⁻¹ * b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    intro a b ha hb
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hb, mul_one, Matrix.coe_units_inv,
      Matrix.det_nonsing_inv, ha, Ring.inverse_one]
  refine ⟨k₁⁻¹ * k₂, k₁⁻¹ * k₃, hdet_inv_mul _ _ hk₁d hk₂d, hdet_inv_mul _ _ hk₁d hk₃d, ?_⟩
  have hconj : τ * (k₁⁻¹ * k₂ * τ * (k₁⁻¹ * k₂)⁻¹) * (k₁⁻¹ * k₃ * τ * (k₁⁻¹ * k₃)⁻¹) =
      MulAut.conj k₁⁻¹ y := by
    rw [hyk, MulAut.conj_apply]
    group
  rw [hconj, ← hy]
  exact orderOf_injective (MulAut.conj k₁⁻¹).toMonoidHom (MulAut.conj k₁⁻¹).injective y

end Final

section Facts

variable {F : Type} [Field F]

@[expose] noncomputable def tv (i j : Fin 3) (h : i ≠ j) : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j 1)
    (by rw [Matrix.det_transvection_of_ne _ _ h]; exact one_ne_zero)

theorem coe_tv (i j : Fin 3) (h : i ≠ j) :
    ((tv i j h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.transvection i j 1 := rfl

theorem det_tv (i j : Fin 3) (h : i ≠ j) :
    ((tv i j h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  Matrix.det_transvection_of_ne _ _ h 1

theorem E02_eq_tv : (E02 : GL (Fin 3) F) = tv 0 2 (by decide) := rfl

variable [CharP F 2]

theorem tv_mul_self (i j : Fin 3) (h : i ≠ j) : tv i j h * tv i j h = (1 : GL (Fin 3) F) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_tv, Matrix.transvection_mul_transvection_same _ _ h,
    CharTwo.add_self_eq_zero, Matrix.transvection_zero, Matrix.GeneralLinearGroup.coe_one]

theorem tv_comm_square :
    tv 0 1 (by decide) * tv 1 2 (by decide) * tv 0 1 (by decide) * tv 1 2 (by decide) =
      (tv 0 2 (by decide) : GL (Fin 3) F) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_tv]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, ← two_mul, h2]

omit [CharP F 2] in
theorem tv02_comm_tv01 :
    tv 0 2 (by decide) * tv 0 1 (by decide) = (tv 0 1 (by decide) * tv 0 2 (by decide) :
      GL (Fin 3) F) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_tv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply]

omit [CharP F 2] in
theorem tv02_comm_tv12 :
    tv 0 2 (by decide) * tv 1 2 (by decide) = (tv 1 2 (by decide) * tv 0 2 (by decide) :
      GL (Fin 3) F) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_tv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply]

omit [CharP F 2] in
theorem tv02_not_comm_tv21 :
    tv 0 2 (by decide) * tv 2 1 (by decide) ≠ (tv 2 1 (by decide) * tv 0 2 (by decide) :
      GL (Fin 3) F) := by
  intro h
  have h2 : (Matrix.transvection 0 2 1 * Matrix.transvection 2 1 1 : Matrix (Fin 3) (Fin 3) F) =
      Matrix.transvection 2 1 1 * Matrix.transvection 0 2 1 := by
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
    simpa [coe_tv] using this
  have := congrFun (congrFun h2 0) 1
  simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
    Matrix.single_apply] at this

theorem not_central_involution {z : GL (Fin 3) F} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hc : ∀ g : GL (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 → g * z = z * g) : False := by
  obtain ⟨Q, hQd, hQ⟩ := exists_conj_E02 hz2 hz1
  have hzQ := hc Q hQd
  have hE : (E02 : GL (Fin 3) F) = z := by
    have : E02 = Q⁻¹ * z * Q := by rw [hQ]; group
    rw [this, mul_assoc, ← hzQ, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := hc (tv 2 1 (by decide)) (det_tv _ _ _)
  rw [← hE, E02_eq_tv] at h1
  exact tv02_not_comm_tv21 h1.symm

variable [Fintype F] {m r : ℕ}

omit [CharP F 2] in
theorem card_fixSub_le {γ : Matrix (Fin 3) (Fin 3) F} (hγ : γ ≠ 1) :
    Nat.card (fixSub γ) ≤ Fintype.card F ^ 2 := by
  have hne : fixSub γ ≠ ⊤ := by
    intro htop
    apply hγ
    have : Matrix.toLin' (γ - 1) = 0 := by
      rw [fixSub, LinearMap.ker_eq_top] at htop
      exact htop
    have h0 : γ - 1 = 0 := Matrix.toLin'.injective (by rw [this, map_zero])
    exact sub_eq_zero.mp h0
  have hlt := Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at hlt
  rw [card_submodule]
  exact Nat.pow_le_pow_right Fintype.card_pos (by omega)

omit [CharP F 2] in
theorem not_comm_E02 (hF : Fintype.card F = 2 ^ m) (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {y : GL (Fin 3) F} (hy : orderOf y = r) :
    y * E02 ≠ E02 * y := by
  have : Fact r.Prime := ⟨hr.prime⟩
  intro hc
  have hyr : (y : Matrix (Fin 3) (Fin 3) F) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hy, pow_orderOf_eq_one, Units.val_one]
  have hy1 : (y : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
    intro h
    have : y = 1 := Units.ext h
    rw [this, orderOf_one] at hy
    exact hr.prime.one_lt.ne' hy.symm
  have hcm : (y : Matrix (Fin 3) (Fin 3) F) * Matrix.single 0 2 1 =
      Matrix.single 0 2 1 * (y : Matrix (Fin 3) (Fin 3) F) := by
    have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hc
    simp only [Matrix.GeneralLinearGroup.coe_mul, E02_eq_tv, coe_tv, Matrix.transvection] at h1
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h1
    exact add_left_cancel h1
  set e₀ : Fin 3 → F := Pi.single 0 1 with he₀
  have hsingle : ∀ v : Fin 3 → F, Matrix.single 0 2 (1 : F) *ᵥ v = v 2 • e₀ := by
    intro v
    rw [Matrix.single_mulVec]
    ext i
    fin_cases i <;> simp [he₀]
  have hye : (y : Matrix (Fin 3) (Fin 3) F) *ᵥ e₀ ∈ Submodule.span F {e₀} := by
    have he2 : e₀ = Matrix.single 0 2 (1 : F) *ᵥ Pi.single (2 : Fin 3) (1 : F) := by
      rw [hsingle]; simp
    have h3 : (y : Matrix (Fin 3) (Fin 3) F) *ᵥ e₀ =
        ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single (2 : Fin 3) (1 : F)) 2 • e₀ := by
      conv_lhs => rw [he2]
      rw [Matrix.mulVec_mulVec, hcm, ← Matrix.mulVec_mulVec, hsingle]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hinv : ∀ w ∈ Submodule.span F {e₀}, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈
      Submodule.span F {e₀} := by
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ hye
  have he0 : e₀ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [he₀] at this
  have hW0 : Submodule.span F {e₀} ≠ ⊥ := by
    rw [Ne, Submodule.span_singleton_eq_bot]
    exact he0
  have htop := eq_top_of_invariant hF hm hr hyr hy1 hinv hW0
  have hfr := finrank_span_singleton (K := F) he0
  rw [htop, finrank_top, Module.finrank_fin_fun] at hfr
  omega

end Facts

end SmithB57

end CFSG.Quasithin
