module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Unitary
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4RankQ
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial Matrix

section RootMatrix

variable {K : Type} [Field K]

@[expose] def suRootMatrix (σ : K →+* K) (u : K) (j : Fin 2) : Matrix (Fin 4) (Fin 4) K :=
  CFSG.SectionRank.ClassicalOdd.uP σ u (le_refl 4) j j

theorem suRootMatrix_mul {σ : K →+* K} {u : K} (hu : σ u * u = -1) (j : Fin 2) (a b : K) :
    (1 + a • suRootMatrix σ u j) * (1 + b • suRootMatrix σ u j) =
      1 + (a + b) • suRootMatrix σ u j := by
  unfold suRootMatrix
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul_comm,
    CFSG.SectionRank.ClassicalOdd.uP_mul_uP (le_refl 4) hu j j j j, smul_zero, add_zero]
  module

theorem suRootMatrix_hstar_mul {σ : K →+* K} {u : K} (hσ : ∀ x, σ (σ x) = x)
    (hu : σ u * u = -1) (j : Fin 2) {t : K} (ht : σ t = -t) :
    CFSG.SectionRank.ClassicalOdd.hstar σ (1 + t • suRootMatrix σ u j) *
      (1 + t • suRootMatrix σ u j) = 1 := by
  have h1 : CFSG.SectionRank.ClassicalOdd.hstar σ (1 + t • suRootMatrix σ u j) =
      1 + σ t • suRootMatrix σ u j := by
    unfold suRootMatrix
    rw [CFSG.SectionRank.ClassicalOdd.hstar_add, CFSG.SectionRank.ClassicalOdd.hstar_one,
      CFSG.SectionRank.ClassicalOdd.hstar_smul,
      CFSG.SectionRank.ClassicalOdd.hstar_uP (le_refl 4) hσ j j]
  rw [h1, suRootMatrix_mul hu j (σ t) t, ht, neg_add_cancel, zero_smul, add_zero]

theorem suRootMatrix_commute_diagonal {σ : K →+* K} {u : K} {j : Fin 2} {i i' : Fin 4}
    (hj : (j = 0 ∧ i = 0 ∧ i' = 1) ∨ (j = 1 ∧ i = 2 ∧ i' = 3)) {d : Fin 4 → K}
    (hd : d i = d i') (t : K) :
    Matrix.diagonal d * (1 + t • suRootMatrix σ u j) =
      (1 + t • suRootMatrix σ u j) * Matrix.diagonal d := by
  apply commute_diagonal_of_support
  intro a b hab
  rcases hj with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · fin_cases a <;> fin_cases b <;>
      simp_all [suRootMatrix, CFSG.SectionRank.ClassicalOdd.uP,
        CFSG.SectionRank.ClassicalOdd.uε, CFSG.SectionRank.ClassicalOdd.uεbar,
        Matrix.vecMulVec_apply]
  · fin_cases a <;> fin_cases b <;>
      simp_all [suRootMatrix, CFSG.SectionRank.ClassicalOdd.uP,
        CFSG.SectionRank.ClassicalOdd.uε, CFSG.SectionRank.ClassicalOdd.uεbar,
        Matrix.vecMulVec_apply]

theorem suRootMatrix_injective (σ : K →+* K) (u : K) (j : Fin 2) :
    Function.Injective fun t : K => (1 + t • suRootMatrix σ u j : Matrix (Fin 4) (Fin 4) K) := by
  intro t t' h
  let i0 : Fin 4 := ⟨2 * j, by omega⟩
  have h' := congrFun (congrFun h i0) i0
  have hP : (suRootMatrix σ u j) i0 i0 = 1 := by
    fin_cases j <;>
      simp [i0, suRootMatrix, CFSG.SectionRank.ClassicalOdd.uP,
        CFSG.SectionRank.ClassicalOdd.uε, CFSG.SectionRank.ClassicalOdd.uεbar,
        Matrix.vecMulVec_apply]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, hP, mul_one]
    at h'
  exact add_left_cancel h'

end RootMatrix

section RootGroup

variable {K : Type} [Field K]

theorem det_one_add_smul_suRootMatrix {r : ℕ} [Fact r.Prime] [CharP K r] {σ : K →+* K} {u : K}
    (hu : σ u * u = -1) (j : Fin 2) (t : K) :
    (1 + t • suRootMatrix σ u j).det = 1 := by
  have hpow : ∀ n : ℕ, (1 + t • suRootMatrix σ u j) ^ n =
      1 + ((n : K) * t) • suRootMatrix σ u j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, suRootMatrix_mul hu j ((n : K) * t) t]
      rw [show ((n : K) * t + t) = ((n + 1 : ℕ) : K) * t by push_cast; ring]
  have hr : (1 + t • suRootMatrix σ u j) ^ r = 1 := by
    rw [hpow r, CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
  exact CFSG.SectionRank.ClassicalOdd.det_eq_one_of_pow_char (p := r) hr

theorem mem_statedSU_of_eq_one_add_smul_suRootMatrix {r f : ℕ} (h : UnitaryFieldData r f K)
    {u : K} (hu : h.bar u * u = -1) (j : Fin 2) {t : K} (ht : t ∈ h.traceZero)
    {g : GL (Fin 4) K}
    (hg : (g : Matrix (Fin 4) (Fin 4) K) = 1 + t • suRootMatrix h.bar u j) :
    g ∈ StatedSU 4 (r ^ f) K := by
  have h0 : h.trace t = 0 := h.mem_traceZero.mp ht
  have htp : h.bar t = -t := by
    change t + h.bar t = 0 at h0
    linear_combination h0
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [hg]
    haveI : Fact r.Prime := ⟨h.prime⟩
    haveI : CharP K r := h.charP
    exact det_one_add_smul_suRootMatrix hu j t
  · rw [hg]
    have hbar : ((· ^ (r ^ f)) : K → K) = ⇑h.bar := funext fun c => (h.bar_apply c).symm
    rw [hbar]
    exact suRootMatrix_hstar_mul h.bar_bar hu j htp

private theorem exists_statedSU_rootGroup_aux {K : Type} [Field K] {r f : ℕ}
    (h : UnitaryFieldData r f K) {u : K} (hu : h.bar u * u = -1)
    (j₀ : Fin 2) {i i' : Fin 4}
    (hj : (j₀ = 0 ∧ i = 0 ∧ i' = 1) ∨ (j₀ = 1 ∧ i = 2 ∧ i' = 3)) :
    ∃ φ : Multiplicative h.traceZero →* StatedSU 4 (r ^ f) K, Function.Injective φ ∧
      ∀ (a : Multiplicative h.traceZero) (d : Fin 4 → K), d i = d i' →
        Matrix.diagonal d * ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal d := by
  let M : h.traceZero → Matrix (Fin 4) (Fin 4) K :=
    fun t => 1 + (t : K) • suRootMatrix h.bar u j₀
  have hM0 : M 0 = 1 := by simp [M]
  have hMadd : ∀ a b : h.traceZero, M (a + b) = M a * M b := by
    intro a b
    have h1 : ((a + b : h.traceZero) : K) = (a : K) + (b : K) := rfl
    dsimp only [M]
    rw [h1, suRootMatrix_mul hu j₀ (a : K) (b : K)]
  have hMinj : Function.Injective M :=
    (suRootMatrix_injective h.bar u j₀).comp Subtype.val_injective
  let φ₀ : Multiplicative h.traceZero →* GL (Fin 4) K :=
    CFSG.SectionRank.ClassicalOdd.glOfAdd M hM0 hMadd
  have hφ₀inj : Function.Injective φ₀ := CFSG.SectionRank.ClassicalOdd.glOfAdd_injective hMinj
  have hφ₀mem : ∀ a, φ₀ a ∈ StatedSU 4 (r ^ f) K :=
    fun a => mem_statedSU_of_eq_one_add_smul_suRootMatrix h hu j₀ a.toAdd.2 rfl
  refine ⟨φ₀.codRestrict (StatedSU 4 (r ^ f) K) hφ₀mem, ?_, ?_⟩
  · intro a b hab
    apply hφ₀inj
    simpa [MonoidHom.codRestrict_apply] using
      congrArg (fun x : StatedSU 4 (r ^ f) K => (x : GL (Fin 4) K)) hab
  · intro a d hd
    have hc := suRootMatrix_commute_diagonal (σ := h.bar) (u := u) (j := j₀)
      (i := i) (i' := i') hj (d := d) hd (a.toAdd : K)
    simpa [φ₀, M, CFSG.SectionRank.ClassicalOdd.coe_glOfAdd] using hc

theorem exists_statedSU_rootGroup {r f : ℕ} (h : UnitaryFieldData r f K) (hr2 : r ≠ 2)
    {i j : Fin 4} (hij : (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3)) :
    ∃ φ : Multiplicative h.traceZero →* StatedSU 4 (r ^ f) K, Function.Injective φ ∧
      ∀ (a : Multiplicative h.traceZero) (d : Fin 4 → K), d i = d j →
        Matrix.diagonal d * ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal d := by
  haveI : Finite K := h.finite
  haveI : Fact r.Prime := ⟨h.prime⟩
  haveI : CharP K r := h.charP
  have hcard : Nat.card K = (r ^ f) ^ 2 := by
    rw [h.card, ← pow_mul, Nat.mul_comm f 2]
  obtain ⟨u, -, hu, -, -⟩ :=
    CFSG.SectionRank.ClassicalOdd.exists_unitary_elems (p := r) (f := f) hr2 hcard
  have hu' : h.bar u * u = -1 := by
    rw [h.bar_apply]; exact hu
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact exists_statedSU_rootGroup_aux h hu' 0 (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact exists_statedSU_rootGroup_aux h hu' 1 (Or.inr ⟨rfl, rfl, rfl⟩)

end RootGroup

theorem le_pRank_centralizer_stdDiagHomH_su {K : Type} [Field K] [Finite K] {r f : ℕ}
    (h : UnitaryFieldData r f K) (hr2 : r ≠ 2) (ζ : CubeRoot K)
    (hD : D₀ ζ ≤ StatedSU 4 (r ^ f) K) (S : Set (Multiplicative (Fin 4 → ZMod 3)))
    {i j : Fin 4} (hij : (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3))
    (hS : ∀ v ∈ S, Multiplicative.toAdd v i = Multiplicative.toAdd v j) :
    f ≤ CFSG.Open.pRank r (Subgroup.centralizer (stdDiagHomH ζ hD '' S)) := by
  haveI : CharP K r := h.charP
  obtain ⟨φ, hφ, hcommφ⟩ := exists_statedSU_rootGroup h hr2 hij
  apply le_pRank_centralizer_of_diag_commuting (H := StatedSU 4 (r ^ f) K) (p := r) (k := f)
    (A := Multiplicative h.traceZero) h.prime.one_lt (fun a b => mul_comm a b) _ _ φ hφ
    (fun d => d i = d j) _ (stdDiagHomH ζ hD '' S) _
  · intro a
    change Multiplicative.ofAdd (r • a.toAdd) = Multiplicative.ofAdd 0
    congr 1
    apply Subtype.ext
    change r • (a.toAdd : K) = 0
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  · rw [Nat.card_congr Multiplicative.toAdd, h.card_traceZero]
  · intro a d hd
    exact hcommφ a d hd
  · rintro t ⟨v, hv, rfl⟩
    refine ⟨fun k => (ζ.pow (Multiplicative.toAdd v k -
      ∑ l, Multiplicative.toAdd v l) : K), ?_, rfl⟩
    simp only [hS v hv]

private theorem units_val_pow_mul_eq_one {K : Type} [Field K] {q : ℕ} (u : Kˣ)
    (hu : u ^ (q + 1) = 1) : (u : K) ^ q * (u : K) = 1 := by
  have h := congrArg (fun z : Kˣ => (z : K)) hu
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ] at h
  exact h

private theorem units_val_inv_pow_mul_eq_one {K : Type} [Field K] {q : ℕ} (u : Kˣ)
    (hu : u ^ (q + 1) = 1) : (((u⁻¹ : Kˣ) : K)) ^ q * ((u⁻¹ : Kˣ) : K) = 1 := by
  have h : (u : K) ^ (q + 1) = 1 := by
    have := congrArg (fun z : Kˣ => (z : K)) hu
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  rw [Units.val_inv_eq_inv_val, inv_pow, ← mul_inv, ← pow_succ, h, inv_one]

theorem diagUnit_mem_statedSU {K : Type} [Field K] {q : ℕ} (hq : 0 < q) {x y : Kˣ}
    (hx : x ^ (q + 1) = 1) (hy : y ^ (q + 1) = 1) :
    diagUnit (K := K) ![x, x⁻¹, y, y⁻¹] ∈ StatedSU 4 q K := by
  have hxq := units_val_pow_mul_eq_one x hx
  have hxiq := units_val_inv_pow_mul_eq_one x hx
  have hyq := units_val_pow_mul_eq_one y hy
  have hyiq := units_val_inv_pow_mul_eq_one y hy
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [show ((diagUnit (K := K) ![x, x⁻¹, y, y⁻¹] : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal
          (fun i => ((![x, x⁻¹, y, y⁻¹] i : Kˣ) : K)) from rfl,
      Matrix.det_diagonal, ← Units.coe_prod, Fin.prod_univ_four]
    simp
  · rw [show ((diagUnit (K := K) ![x, x⁻¹, y, y⁻¹] : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal
          (fun i => ((![x, x⁻¹, y, y⁻¹] i : Kˣ) : K)) from rfl]
    have hmap : (Matrix.diagonal
          (fun i => ((![x, x⁻¹, y, y⁻¹] i : Kˣ) : K))).map (· ^ q) =
        Matrix.diagonal (fun i => (((![x, x⁻¹, y, y⁻¹] i : Kˣ) : K)) ^ q) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.map_apply, Matrix.diagonal_apply]
      · simp [Matrix.map_apply, Matrix.diagonal_apply, h, zero_pow hq.ne']
    rw [hmap, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simpa using hxq
    · simpa using hxiq
    · simpa using hyq
    · simpa using hyiq

theorem two_le_pRank_centralizer_stdDiagHomH_univ_su {K : Type} [Field K] [Finite K] {q p : ℕ}
    (hq : 0 < q) (hK : Nat.card K = q ^ 2) (hp : p.Prime) (hpq : p ∣ q + 1) (ζ : CubeRoot K)
    (hD : D₀ ζ ≤ StatedSU 4 q K) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer
      (stdDiagHomH ζ hD '' (Set.univ : Set (Multiplicative (Fin 4 → ZMod 3))))) := by
  have hpK : p ∣ Nat.card K - 1 := by
    rw [hK]
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1]
    exact hpq.mul_right (q - 1)
  obtain ⟨a, ha⟩ := exists_units_orderOf_eq_prime hp hpK
  refine two_le_pRank_centralizer_of_diagTorus (H := StatedSU 4 q K) hp ha ?_ _ ?_
  · intro x hx y hy
    have hx1 : x ^ (q + 1) = 1 := by
      have h1 : orderOf x ∣ orderOf a := orderOf_dvd_of_mem_zpowers hx
      rw [ha] at h1
      exact (orderOf_dvd_iff_pow_eq_one).mp (h1.trans hpq)
    have hy1 : y ^ (q + 1) = 1 := by
      have h1 : orderOf y ∣ orderOf a := orderOf_dvd_of_mem_zpowers hy
      rw [ha] at h1
      exact (orderOf_dvd_iff_pow_eq_one).mp (h1.trans hpq)
    exact diagUnit_mem_statedSU hq hx1 hy1
  · rintro t ⟨v, -, rfl⟩
    exact Matrix.isDiag_diagonal _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
