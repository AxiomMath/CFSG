module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix

variable {F : Type*} [Field F]

theorem eq_vecMulVec_of_forall_mulVec {M : Matrix (Fin 3) (Fin 3) F} {v : Fin 3 → F}
    (h : ∀ x : Fin 3 → F, ∃ c : F, M *ᵥ x = c • v) : ∃ φ : Fin 3 → F, M = vecMulVec v φ := by
  choose c hc using fun j : Fin 3 => h (Pi.single j 1)
  refine ⟨c, ?_⟩
  ext i j
  have h1 := congrFun (hc j) i
  rw [mulVec_single_one] at h1
  simp only [col_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [h1, vecMulVec_apply, mul_comm]

theorem exists_ne_zero_dotProduct_eq_zero (φ₁ φ₂ : Fin 3 → F) :
    ∃ x : Fin 3 → F, x ≠ 0 ∧ φ₁ ⬝ᵥ x = 0 ∧ φ₂ ⬝ᵥ x = 0 := by
  let T : (Fin 3 → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := fun x => ![φ₁ ⬝ᵥ x, φ₂ ⬝ᵥ x]
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp [dotProduct_add]
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp [dotProduct_smul] }
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 : Module.finrank F (LinearMap.range T) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range T)
    simpa using this
  have h3 : Module.finrank F (Fin 3 → F) = 3 := by simp
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot, h3] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x, hx0, ?_, ?_⟩
  · have := congrFun (LinearMap.mem_ker.mp hx) 0
    simpa [T] using this
  · have := congrFun (LinearMap.mem_ker.mp hx) 1
    simpa [T] using this

theorem eq_zero_of_smul_one_eq_sub_vecMulVec {a : F} {v₁ φ₁ v₂ φ₂ : Fin 3 → F}
    (h : a • (1 : Matrix (Fin 3) (Fin 3) F) = vecMulVec v₁ φ₁ - vecMulVec v₂ φ₂) : a = 0 := by
  obtain ⟨x, hx0, hx1, hx2⟩ := exists_ne_zero_dotProduct_eq_zero φ₁ φ₂
  have h1 := congrArg (fun M => M *ᵥ x) h
  simp only [smul_mulVec, one_mulVec, sub_mulVec, vecMulVec_mulVec, hx1, hx2,
    MulOpposite.op_zero, zero_smul, sub_zero] at h1
  by_contra ha
  exact hx0 (by simpa [ha] using h1)

theorem eq_of_smul_one_add_vecMulVec_eq {κ κ' : F} {v φ v' φ' : Fin 3 → F}
    (h : κ • (1 : Matrix (Fin 3) (Fin 3) F) + vecMulVec v φ = κ' • 1 + vecMulVec v' φ') :
    κ = κ' ∧ vecMulVec v φ = vecMulVec v' φ' := by
  have h1 : (κ - κ') • (1 : Matrix (Fin 3) (Fin 3) F) = vecMulVec v' φ' - vecMulVec v φ := by
    rw [sub_smul]
    linear_combination (norm := abel) h
  have h2 := eq_zero_of_smul_one_eq_sub_vecMulVec h1
  have h3 : κ = κ' := sub_eq_zero.mp h2
  subst h3
  exact ⟨rfl, by simpa using h⟩

theorem exists_smul_eq_of_vecMulVec_eq {v φ v' φ' : Fin 3 → F} (hφ' : φ' ≠ 0)
    (h : vecMulVec v' φ' = vecMulVec v φ) : ∃ c : F, v' = c • v := by
  obtain ⟨j, hj⟩ : ∃ j, φ' j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ' (funext hcon)
  refine ⟨φ j / φ' j, funext fun i => ?_⟩
  have := congrFun (congrFun h i) j
  rw [vecMulVec_apply, vecMulVec_apply] at this
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hj]
  linear_combination this

theorem exists_eq_vecMulVec_of_sq_eq_zero {N : Matrix (Fin 3) (Fin 3) F} (hN : N * N = 0)
    (hN0 : N ≠ 0) :
    ∃ w ψ : Fin 3 → F, w ≠ 0 ∧ ψ ≠ 0 ∧ ψ ⬝ᵥ w = 0 ∧ N = vecMulVec w ψ := by
  set T := Matrix.mulVecLin N with hT
  have hRK : LinearMap.range T ≤ LinearMap.ker T := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, hT, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_mulVec, hN,
      zero_mulVec]
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 := Submodule.finrank_mono hRK
  have h3 : Module.finrank F (Fin 3 → F) = 3 := by simp
  have hle : Module.finrank F (LinearMap.range T) ≤ 1 := by omega
  obtain ⟨⟨w, hw⟩, hgen⟩ := (finrank_le_one_iff (K := F) (V := LinearMap.range T)).mp hle
  obtain ⟨ψ, hψ⟩ := eq_vecMulVec_of_forall_mulVec (M := N) (v := w) fun x => by
    obtain ⟨c, hc⟩ := hgen ⟨N *ᵥ x, x, rfl⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hN0
    rw [hψ]
    ext i j
    simp
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    apply hN0
    rw [hψ]
    ext i j
    simp
  refine ⟨w, ψ, hw0, hψ0, ?_, hψ⟩
  have h4 : vecMulVec w ψ * vecMulVec w ψ = 0 := by rw [← hψ]; exact hN
  rw [vecMulVec_mul_vecMulVec, vecMulVec_eq_zero] at h4
  rcases h4 with h4 | h4
  · exact absurd h4 hw0
  · by_contra hne
    exact hψ0 (by simpa [hne] using h4)

theorem exists_eigen_of_commute_vecMulVec {g : Matrix (Fin 3) (Fin 3) F} {w ψ : Fin 3 → F}
    (hw : w ≠ 0) (hψ : ψ ≠ 0) (hc : g * vecMulVec w ψ = vecMulVec w ψ * g) :
    ∃ κ : F, g *ᵥ w = κ • w ∧ ψ ᵥ* g = κ • ψ := by
  rw [mul_vecMulVec, vecMulVec_mul] at hc
  obtain ⟨j, hj⟩ : ∃ j, ψ j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hψ (funext hcon)
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (funext hcon)
  set κ := (ψ ᵥ* g) j / ψ j with hκ
  have hgw : g *ᵥ w = κ • w := by
    funext k
    have := congrFun (congrFun hc k) j
    rw [vecMulVec_apply, vecMulVec_apply] at this
    rw [Pi.smul_apply, smul_eq_mul, hκ]
    field_simp
    linear_combination this
  refine ⟨κ, hgw, funext fun l => ?_⟩
  have := congrFun (congrFun hc i) l
  rw [vecMulVec_apply, vecMulVec_apply, hgw, Pi.smul_apply, smul_eq_mul] at this
  rw [Pi.smul_apply, smul_eq_mul]
  have h2 : w i * ((ψ ᵥ* g) l - κ * ψ l) = 0 := by linear_combination -this
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hi
  · linear_combination h3

variable [CharP F 2]

theorem exists_homology_of_commute {g h : Matrix (Fin 3) (Fin 3) F} {c s : F} (hc : c ≠ 0)
    (hg3 : g ^ 3 = c • 1) (hgs : ∀ a : F, g ≠ a • 1) (hgh : g * h = h * g)
    (hh2 : h * h = s ^ 2 • 1) (hhs : h ≠ s • 1) :
    ∃ (κ : F) (v φ : Fin 3 → F), κ ≠ 0 ∧ v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v ≠ 0 ∧
      g = κ • 1 + vecMulVec v φ := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set N := h - s • (1 : Matrix (Fin 3) (Fin 3) F) with hNdef
  have hN : N * N = 0 := by
    have e : N * N = h * h - (2 * s) • h + s ^ 2 • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [hNdef]
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
      module
    rw [e, hh2, h2, zero_mul, zero_smul, sub_zero, ← two_smul F (s ^ 2 • (1 : Matrix (Fin 3)
      (Fin 3) F)), h2, zero_smul]
  have hN0 : N ≠ 0 := fun h0 => hhs (sub_eq_zero.mp h0)
  obtain ⟨w, ψ, hw0, hψ0, hψw, hNw⟩ := exists_eq_vecMulVec_of_sq_eq_zero hN hN0
  have hgN : g * vecMulVec w ψ = vecMulVec w ψ * g := by
    rw [← hNw, hNdef, mul_sub, sub_mul, hgh, mul_smul_comm, mul_one, smul_mul_assoc, one_mul]
  obtain ⟨κ, hgw, hψg⟩ := exists_eigen_of_commute_vecMulVec hw0 hψ0 hgN
  have hg3w : (g ^ 3) *ᵥ w = κ ^ 3 • w := by
    simp only [pow_three', ← mulVec_mulVec, hgw, mulVec_smul, smul_smul]
    congr 1
    ring
  have hκ3 : κ ^ 3 = c := by
    rw [hg3, smul_mulVec, one_mulVec] at hg3w
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw0 (funext hcon)
    have := congrFun hg3w i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_right_cancel₀ hi this).symm
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    exact hc (by rw [← hκ3]; ring)
  set M := g - κ • (1 : Matrix (Fin 3) (Fin 3) F) with hMdef
  have hgM : g = κ • 1 + M := by rw [hMdef]; abel
  have hMw : M *ᵥ w = 0 := by rw [hMdef, sub_mulVec, hgw, smul_mulVec, one_mulVec, sub_self]
  have hψM : ψ ᵥ* M = 0 := by rw [hMdef, vecMul_sub, hψg, vecMul_smul, vecMul_one, sub_self]
  have hM3 : M * (M * M) + κ • (M * M) + κ ^ 2 • M = 0 := by
    have hexp : (κ • (1 : Matrix (Fin 3) (Fin 3) F) + M) ^ 3 =
        κ ^ 3 • 1 + (3 * κ ^ 2) • M + (3 * κ) • (M * M) + M * (M * M) := by
      rw [pow_three]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
        smul_add, mul_assoc]
      module
    have h1 : c • (1 : Matrix (Fin 3) (Fin 3) F) =
        (κ • (1 : Matrix (Fin 3) (Fin 3) F) + M) ^ 3 := by
      rw [← hgM, hg3]
    rw [hexp, ← hκ3] at h1
    have h3' : (3 : F) = 1 := by linear_combination h2
    rw [h3', one_mul, one_mul] at h1
    have h4 : κ ^ 2 • M + κ • (M * M) + M * (M * M) = 0 := by
      have h5 := congrArg (fun A => A - κ ^ 3 • (1 : Matrix (Fin 3) (Fin 3) F)) h1
      simp only [sub_self] at h5
      rw [h5]
      abel
    rw [← h4]
    abel
  have hwR : ∀ y : Fin 3 → F, M *ᵥ y ≠ w := by
    intro y hy
    have h1 := congrArg (fun A => A *ᵥ y) hM3
    simp only [add_mulVec, smul_mulVec, ← mulVec_mulVec, hy, hMw, mulVec_zero, smul_zero,
      zero_add, zero_mulVec] at h1
    have h5 : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ0
    exact hw0 ((smul_eq_zero.mp h1).resolve_left h5)
  set T := Matrix.mulVecLin M with hT
  have hψR : ∀ x : Fin 3 → F, ψ ⬝ᵥ (M *ᵥ x) = 0 := by
    intro x
    rw [dotProduct_mulVec, hψM, zero_dotProduct]
  have hle : Module.finrank F (LinearMap.range T) ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hinf : LinearMap.range T ⊓ Submodule.span F {w} = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hx1, hx2⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx2
      obtain ⟨y, hy⟩ := hx1
      by_cases ha : a = 0
      · rw [ha, zero_smul]
        exact Submodule.zero_mem _
      · exfalso
        apply hwR (a⁻¹ • y)
        rw [hT, Matrix.mulVecLin_apply] at hy
        rw [mulVec_smul, hy, smul_smul, inv_mul_cancel₀ ha, one_smul]
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range T)
      (Submodule.span F {w})
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hw0] at hsup
    have h3 : Module.finrank F (Fin 3 → F) = 3 := by simp
    have htop : LinearMap.range T ⊔ Submodule.span F {w} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_le (LinearMap.range T ⊔ Submodule.span F {w})
      omega
    apply hψ0
    funext i
    have hmem : (Pi.single i 1 : Fin 3 → F) ∈ LinearMap.range T ⊔ Submodule.span F {w} := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have h5 : ψ ⬝ᵥ (Pi.single i 1 : Fin 3 → F) = 0 := by
      rw [← hxy, dotProduct_add, hT, Matrix.mulVecLin_apply, hψR, dotProduct_smul, hψw,
        smul_zero, add_zero]
    rw [dotProduct_single_one] at h5
    exact h5
  obtain ⟨⟨v, hv⟩, hgen⟩ := (finrank_le_one_iff (K := F) (V := LinearMap.range T)).mp hle
  obtain ⟨φ, hφ⟩ := eq_vecMulVec_of_forall_mulVec (M := M) (v := v) fun x => by
    obtain ⟨c', hc'⟩ := hgen ⟨M *ᵥ x, x, rfl⟩
    exact ⟨c', (congrArg Subtype.val hc').symm⟩
  have hM0 : M ≠ 0 := by
    intro hM0
    apply hgs κ
    rw [hgM, hM0, add_zero]
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hM0
    rw [hφ]
    ext i j
    simp
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    apply hM0
    rw [hφ]
    ext i j
    simp
  refine ⟨κ, v, φ, hκ0, hv0, hφ0, ?_, by rw [hgM, hφ]⟩
  intro hφv
  have hMM : M * M = 0 := by
    rw [hφ, vecMulVec_mul_vecMulVec, hφv, zero_smul]
    ext i j
    simp
  rw [hMM, mul_zero, smul_zero, add_zero, zero_add] at hM3
  exact hM0 ((smul_eq_zero.mp hM3).resolve_left (pow_ne_zero 2 hκ0))

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
