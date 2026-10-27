module

public import CFSG.RankThree.SteinbergR3ECoprimeRankOne
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSubfieldCentralizer

public section

namespace CFSG.RankThree.LinearTwo

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer (upperGL
  coordinateGLAction_upperGL)
open CFSG.RankThree.Automorphisms (isCyclic_of_le_range_of_inf_map_ker_eq_bot
  inf_eq_bot_of_isPGroup_of_coprime)
open CFSG.LinearGroups (coordinateU_eq_range coordinateU_fixed_points translation_mem_coordinateU
  coordinateU_le_coordinateG card_coordinateU)

universe u

section Matrices

variable {K : Type*} [Field K]

theorem mul_self_eq_trace_smul_sub_det_smul (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem det_smul_one_add_smul (M : Matrix (Fin 2) (Fin 2) K) (x y : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • M).det = x ^ 2 + x * y * M.trace + y ^ 2 * M.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

theorem smul_one_add_smul_mul (M : Matrix (Fin 2) (Fin 2) K) (x y x' y' : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • M) * (x' • 1 + y' • M) =
      (x * x' - y * y' * M.det) • (1 : Matrix (Fin 2) (Fin 2) K) +
        (x * y' + x' * y + y * y' * M.trace) • M := by
  have h := mul_self_eq_trace_smul_sub_det_smul M
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, h, smul_sub, smul_smul]
  module

theorem exists_eq_smul_one_add_smul {M N : Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ c : K, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) (h : N * M = M * N) :
    ∃ x y : K, N = x • (1 : Matrix (Fin 2) (Fin 2) K) + y • M := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases hb : M 0 1 = 0
  · by_cases hc : M 1 0 = 0
    · have had : M 0 0 - M 1 1 ≠ 0 := by
        intro h0
        apply hM (M 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc, sub_eq_zero.mp h0]
      have h01 : N 0 1 = 0 := by
        have : N 0 1 * (M 0 0 - M 1 1) = 0 := by rw [hb] at e01; linear_combination -e01
        exact (mul_eq_zero.mp this).resolve_right had
      have h10 : N 1 0 = 0 := by
        have : N 1 0 * (M 0 0 - M 1 1) = 0 := by rw [hc] at e10; linear_combination e10
        exact (mul_eq_zero.mp this).resolve_right had
      refine ⟨N 0 0 - (N 0 0 - N 1 1) / (M 0 0 - M 1 1) * M 0 0,
        (N 0 0 - N 1 1) / (M 0 0 - M 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, h01, h10]
      field_simp
      ring
    · have h01 : N 0 1 = 0 := by
        have : N 0 1 * M 1 0 = 0 := by rw [hb] at e00; linear_combination e00
        exact (mul_eq_zero.mp this).resolve_right hc
      refine ⟨N 0 0 - N 1 0 / M 1 0 * M 0 0, N 1 0 / M 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, h01]
      · field_simp
      · field_simp
        linear_combination e10
  · refine ⟨N 0 0 - N 0 1 / M 0 1 * M 0 0, N 0 1 / M 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · field_simp
    · field_simp
      linear_combination -e00
    · field_simp
      linear_combination -e01

theorem eq_of_smul_one_add_smul_eq {M : Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ c : K, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) {x y x' y' : K}
    (h : x • (1 : Matrix (Fin 2) (Fin 2) K) + y • M = x' • 1 + y' • M) : x = x' ∧ y = y' := by
  have hy : y = y' := by
    by_contra hne
    apply hM ((x' - x) / (y - y'))
    have hsub : y - y' ≠ 0 := sub_ne_zero.mpr hne
    have h2 : (y - y') • M = (x' - x) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h' := sub_eq_zero.mpr h
      rw [sub_smul, sub_smul, ← sub_eq_zero]
      convert h' using 1
      abel
    rw [div_eq_inv_mul, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hsub, one_smul]
  subst hy
  refine ⟨?_, rfl⟩
  have h00 := congrFun (congrFun h 0) 0
  simpa using h00

end Matrices

section Lift

variable {K : Type*} [Field K]

theorem mul_scalar_eq_smul (B : Matrix (Fin 2) (Fin 2) K) (c : K) :
    B * Matrix.scalar (Fin 2) c = c • B := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

theorem commute_of_mk_commute {A N : GL (Fin 2) K}
    (hA2 : ProjGenLinGroup.mk A ^ 2 ≠ 1)
    (h : ProjGenLinGroup.mk N * ProjGenLinGroup.mk A =
      ProjGenLinGroup.mk A * ProjGenLinGroup.mk N) : N * A = A * N := by
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  set Nm : Matrix (Fin 2) (Fin 2) K := (N : Matrix (Fin 2) (Fin 2) K) with hNm
  set Ni : Matrix (Fin 2) (Fin 2) K := ((N⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    with hNi_def
  set Am : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hAm
  have hNi : Nm * Ni = 1 := by rw [hNm, hNi_def, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiN : Ni * Nm = 1 := by rw [hNm, hNi_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmat : (u : K) • (Nm * Am) = Am * Nm := by
    have := congrArg (fun B : GL (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K)) hu
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [mul_scalar_eq_smul] at this
    exact this
  have hconj : (u : K) • (Nm * Am * Ni) = Am := by
    rw [← Matrix.smul_mul, hmat, Matrix.mul_assoc, hNi, Matrix.mul_one]
  have htr : (u : K) * Matrix.trace Am = Matrix.trace Am := by
    have h3 := congrArg Matrix.trace hconj
    rw [Matrix.trace_smul, Matrix.trace_mul_cycle, hiN, Matrix.one_mul, smul_eq_mul] at h3
    exact h3
  have hu1 : u = 1 := by
    by_contra hne
    have htr0 : Matrix.trace Am = 0 := by
      have : ((u : K) - 1) * Matrix.trace Am = 0 := by linear_combination htr
      exact (mul_eq_zero.mp this).resolve_left (fun h0 => hne (Units.ext (sub_eq_zero.mp h0)))
    apply hA2
    rw [← map_pow, ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨-Am.det, ?_⟩
    rw [Units.val_pow_eq_pow_val, sq, ← hAm, mul_self_eq_trace_smul_sub_det_smul, htr0, zero_smul,
      zero_sub, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, neg_smul]
  rw [hu1, map_one, mul_one] at hu
  exact hu

end Lift

section Roots

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

theorem exists_charRoot [IsAlgClosed L] (M : Matrix (Fin 2) (Fin 2) K) :
    ∃ r : L, r ^ 2 - algebraMap K L M.trace * r + algebraMap K L M.det = 0 := by
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C (algebraMap K L M.trace) * Polynomial.X +
      Polynomial.C (algebraMap K L M.det)).degree = 2 := by compute_degree!
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 - Polynomial.C (algebraMap K L M.trace) * Polynomial.X +
      Polynomial.C (algebraMap K L M.det)) (by rw [hdeg]; decide)
  refine ⟨r, ?_⟩
  simpa [Polynomial.IsRoot] using hr

abbrev matL (M : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) L :=
  (algebraMap K L).mapMatrix M

theorem trace_matL (M : Matrix (Fin 2) (Fin 2) K) :
    (matL L M).trace = algebraMap K L M.trace := by
  simp [Matrix.trace_fin_two]

theorem det_matL (M : Matrix (Fin 2) (Fin 2) K) :
    (matL L M).det = algebraMap K L M.det := by
  simp [Matrix.det_fin_two]

end Roots

section Cyclic

variable {K : Type u} [Field K]

theorem not_scalar_of_mk_ne_one {A : GL (Fin 2) K} (hA : ProjGenLinGroup.mk A ≠ 1) :
    ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro c hc
  apply hA
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact ⟨c, by rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem mk_eq_one_of_matL_eq (L : Type*) [Field L] [Algebra K L] {B : GL (Fin 2) K} {s : L}
    (h : matL L (B : Matrix (Fin 2) (Fin 2) K) = s • (1 : Matrix (Fin 2) (Fin 2) L)) :
    ProjGenLinGroup.mk B = 1 := by
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e00 := congrFun (congrFun h 0) 0
  have e11 := congrFun (congrFun h 1) 1
  simp at e01 e10 e00 e11
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨(B : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
  have h11 : (B : Matrix (Fin 2) (Fin 2) K) 1 1 = (B : Matrix (Fin 2) (Fin 2) K) 0 0 :=
    (algebraMap K L).injective (e11.trans e00.symm)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, e01, e10, h11]

theorem charRoots_ne_of_orderOf [Finite K] (L : Type*) [Field L] [IsAlgClosed L] [Algebra K L]
    {A : GL (Fin 2) K} {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ringChar K)
    (hA : orderOf (ProjGenLinGroup.mk A) = p) {r : L}
    (hr : r ^ 2 - algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).trace * r +
      algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).det = 0) :
    r ≠ algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).trace - r := by
  intro hrr
  set ℓ := ringChar K with hℓdef
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP L ℓ := (Algebra.charP_iff K L ℓ).mp inferInstance
  set N : Matrix (Fin 2) (Fin 2) L :=
    matL L (A : Matrix (Fin 2) (Fin 2) K) - r • (1 : Matrix (Fin 2) (Fin 2) L) with hN
  have htr : algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).trace = 2 * r := by
    linear_combination -hrr
  have hdet : algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).det = r ^ 2 := by
    linear_combination hr - r * hrr
  have hN2 : N * N = 0 := by
    have hch := mul_self_eq_trace_smul_sub_det_smul (matL L (A : Matrix (Fin 2) (Fin 2) K))
    rw [trace_matL, det_matL, htr, hdet] at hch
    rw [hN, sub_mul, mul_sub, mul_sub, hch, smul_mul_smul_comm, one_mul, smul_one_mul,
      mul_smul_one]
    module
  have hNpow : N ^ ℓ = 0 := by
    obtain ⟨m, hm⟩ : ∃ m, ℓ = m + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩
    rw [hm, pow_add, sq, hN2, mul_zero]
  have hcomm : Commute (r • (1 : Matrix (Fin 2) (Fin 2) L)) N :=
    (Commute.one_left N).smul_left r
  have hpow : matL L ((A ^ ℓ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      r ^ ℓ • (1 : Matrix (Fin 2) (Fin 2) L) := by
    rw [Units.val_pow_eq_pow_val]
    change (algebraMap K L).mapMatrix ((A : Matrix (Fin 2) (Fin 2) K) ^ ℓ) = _
    rw [map_pow,
      show (algebraMap K L).mapMatrix (A : Matrix (Fin 2) (Fin 2) K) = r • 1 + N by
        rw [hN]; abel,
      add_pow_char_of_commute ℓ hcomm, hNpow, add_zero, smul_pow, one_pow]
  have h1 : ProjGenLinGroup.mk A ^ ℓ = 1 := by
    rw [← map_pow]
    exact mk_eq_one_of_matL_eq L hpow
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hA] at hdvd
  exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp hdvd)

theorem exists_coords {A : GL (Fin 2) K}
    (hAns : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K))
    (N : Subgroup.centralizer ({A} : Set (GL (Fin 2) K))) :
    ∃ xy : K × K, ((N : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      xy.1 • (1 : Matrix (Fin 2) (Fin 2) K) + xy.2 • (A : Matrix (Fin 2) (Fin 2) K) := by
  have hcomm : (N : GL (Fin 2) K) * A = A * N := Subgroup.mem_centralizer_singleton_iff.mp N.2
  have hm : ((N : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * ((N : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← Units.val_mul, hcomm, Units.val_mul]
  obtain ⟨x, y, hxy⟩ := exists_eq_smul_one_add_smul hAns hm
  exact ⟨(x, y), hxy⟩

@[expose] noncomputable def evRoot (L : Type*) [Field L] [Algebra K L] {A : GL (Fin 2) K}
    (hAns : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K))
    (r : L) (N : Subgroup.centralizer ({A} : Set (GL (Fin 2) K))) : L :=
  algebraMap K L (exists_coords hAns N).choose.1 +
    algebraMap K L (exists_coords hAns N).choose.2 * r

theorem evRoot_eq (L : Type*) [Field L] [Algebra K L] {A : GL (Fin 2) K}
    (hAns : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K))
    (r : L) (N : Subgroup.centralizer ({A} : Set (GL (Fin 2) K))) {x y : K}
    (h : ((N : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (A : Matrix (Fin 2) (Fin 2) K)) :
    evRoot L hAns r N = algebraMap K L x + algebraMap K L y * r := by
  obtain ⟨hx, hy⟩ :=
    eq_of_smul_one_add_smul_eq hAns ((exists_coords hAns N).choose_spec.symm.trans h)
  rw [evRoot, hx, hy]

theorem evRoot_ne_zero (L : Type*) [Field L] [Algebra K L] {A : GL (Fin 2) K}
    (hAns : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K))
    {r : L} (hr : r ^ 2 - algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).trace * r +
      algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).det = 0)
    (N : Subgroup.centralizer ({A} : Set (GL (Fin 2) K))) : evRoot L hAns r N ≠ 0 := by
  obtain ⟨⟨x, y⟩, hxy⟩ := exists_coords hAns N
  rw [evRoot_eq L hAns r N hxy]
  intro h0
  have hdet := det_smul_one_add_smul (A : Matrix (Fin 2) (Fin 2) K) x y
  rw [← hxy] at hdet
  have hdetL := congrArg (algebraMap K L) hdet
  have hfac : algebraMap K L (((N : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) =
      (algebraMap K L x + algebraMap K L y * r) *
        (algebraMap K L x + algebraMap K L y *
          (algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).trace - r)) := by
    rw [hdetL]
    simp only [map_add, map_mul, map_pow]
    linear_combination (algebraMap K L y) ^ 2 * hr
  rw [h0, zero_mul] at hfac
  exact ((N : GL (Fin 2) K)).det_ne_zero ((algebraMap K L).injective (hfac.trans (map_zero _).symm))

@[expose] noncomputable def evRootHom (L : Type*) [Field L] [Algebra K L] {A : GL (Fin 2) K}
    (hAns : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K))
    {r : L} (hr : r ^ 2 - algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).trace * r +
      algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).det = 0) :
    Subgroup.centralizer ({A} : Set (GL (Fin 2) K)) →* Lˣ where
  toFun N := Units.mk0 (evRoot L hAns r N) (evRoot_ne_zero L hAns hr N)
  map_one' := by
    refine Units.ext ?_
    rw [Units.val_mk0, Units.val_one, evRoot_eq L hAns r 1 (x := 1) (y := 0) (by simp)]
    simp
  map_mul' N₁ N₂ := by
    refine Units.ext ?_
    obtain ⟨⟨x₁, y₁⟩, h₁⟩ := exists_coords hAns N₁
    obtain ⟨⟨x₂, y₂⟩, h₂⟩ := exists_coords hAns N₂
    have h12 : (((N₁ * N₂ : Subgroup.centralizer ({A} : Set (GL (Fin 2) K))) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = (x₁ * x₂ - y₁ * y₂ * (A : Matrix (Fin 2) (Fin 2) K).det) •
          (1 : Matrix (Fin 2) (Fin 2) K) +
          (x₁ * y₂ + x₂ * y₁ + y₁ * y₂ * (A : Matrix (Fin 2) (Fin 2) K).trace) •
            (A : Matrix (Fin 2) (Fin 2) K) := by
      rw [Subgroup.coe_mul, Units.val_mul, h₁, h₂, smul_one_add_smul_mul]
    rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0, evRoot_eq L hAns r _ h12,
      evRoot_eq L hAns r _ h₁, evRoot_eq L hAns r _ h₂]
    simp only [map_add, map_mul, map_sub]
    linear_combination (-(algebraMap K L y₁ * algebraMap K L y₂)) * hr

theorem isCyclic_centralizer_of_ne_ringChar [Finite K] {A : GL (Fin 2) K} {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ringChar K) (hA : orderOf (ProjGenLinGroup.mk A) = p) :
    IsCyclic (Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (PGL2 K))) := by
  classical
  set L := AlgebraicClosure K
  have hA2 : ProjGenLinGroup.mk A ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hA] at this
    have := Nat.le_of_dvd two_pos this
    omega
  have hA1 : ProjGenLinGroup.mk A ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hA
    exact hp.one_lt.ne hA
  have hAns := not_scalar_of_mk_ne_one hA1
  obtain ⟨r, hr⟩ := exists_charRoot L (A : Matrix (Fin 2) (Fin 2) K)
  set s := algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).trace - r with hs
  have hs_root : s ^ 2 - algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).trace * s +
      algebraMap K L (A : Matrix (Fin 2) (Fin 2) K).det = 0 := by
    rw [hs]; linear_combination hr
  have hrs : r ≠ s := charRoots_ne_of_orderOf L hp hpℓ hA hr
  set ψ := evRootHom L hAns hr / evRootHom L hAns hs_root with hψ
  set κ : Subgroup.centralizer ({A} : Set (GL (Fin 2) K)) →* PGL2 K :=
    ProjGenLinGroup.mk.comp (Subgroup.centralizer ({A} : Set (GL (Fin 2) K))).subtype with hκ
  have hrange : Subgroup.centralizer ({ProjGenLinGroup.mk A} : Set (PGL2 K)) ≤ κ.range := by
    intro g hg
    obtain ⟨N, rfl⟩ := ProjGenLinGroup.mk_surjective g
    have hcomm := commute_of_mk_commute hA2 (Subgroup.mem_centralizer_singleton_iff.mp hg)
    exact ⟨⟨N, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩, rfl⟩
  have hker : ψ.ker.map κ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨N, hN, rfl⟩
    rw [Subgroup.mem_bot]
    obtain ⟨⟨x, y⟩, hxy⟩ := exists_coords hAns N
    have h1 : evRootHom L hAns hr N = evRootHom L hAns hs_root N := by
      have := (MonoidHom.mem_ker).mp hN
      rw [hψ, MonoidHom.div_apply, div_eq_one] at this
      exact this
    have h2 := congrArg Units.val h1
    change evRoot L hAns r N = evRoot L hAns s N at h2
    rw [evRoot_eq L hAns r N hxy, evRoot_eq L hAns s N hxy] at h2
    have hy : y = 0 := by
      have : algebraMap K L y * (r - s) = 0 := by linear_combination h2
      have := (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hrs)
      exact (algebraMap K L).injective (this.trans (map_zero _).symm)
    change ProjGenLinGroup.mk (N : GL (Fin 2) K) = 1
    rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨x, ?_⟩
    rw [hxy, hy, zero_smul, add_zero, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have : Finite (GL (Fin 2) K) := inferInstance
  have : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hψcyc : IsCyclic ψ.range :=
    isCyclic_of_injective_ringHom ((Units.coeHom L).comp ψ.range.subtype)
      (Units.val_injective.comp Subtype.val_injective)
  exact isCyclic_of_le_range_of_inf_map_ker_eq_bot κ ψ hψcyc hrange (by rw [hker, inf_bot_eq])

end Cyclic

section Unipotent

variable {K : Type u} [Field K]

theorem eq_translation_of_commute {π : Equiv.Perm (Omega K)}
    (h : ∀ b : K, π * translation K b = translation K b * π) :
    ∃ b₀ : K, π = translation K b₀ := by
  have hinf : π none = none := by
    have hfix : π none ∈ {x : Omega K | ∀ u ∈ coordinateU K, u x = x} := by
      intro u hu
      rw [coordinateU_eq_range] at hu
      obtain ⟨b, rfl⟩ := hu
      have := congrArg (fun f : Equiv.Perm (Omega K) => f none) (h b.toAdd)
      simp only [Equiv.Perm.mul_apply, translation_none] at this
      exact this.symm
    rw [coordinateU_fixed_points] at hfix
    exact hfix
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, π (some 0) = some b₀ := by
    cases h0 : π (some 0) with
    | none =>
      exact absurd (π.injective (h0.trans hinf.symm)) (Option.some_ne_none 0)
    | some b₀ => exact ⟨b₀, rfl⟩
  refine ⟨b₀, Equiv.ext fun x => ?_⟩
  cases x with
  | none => rw [hinf, translation_none]
  | some x =>
    have := congrArg (fun f : Equiv.Perm (Omega K) => f (some 0)) (h x)
    simp only [Equiv.Perm.mul_apply, translation_some, zero_add, hb₀] at this
    rw [this, translation_some, add_comm]

theorem centralizer_coordinateU :
    Subgroup.centralizer (coordinateU K : Set (Equiv.Perm (Omega K))) = coordinateU K := by
  apply le_antisymm
  · intro π hπ
    obtain ⟨b₀, rfl⟩ := eq_translation_of_commute fun b =>
      (Subgroup.mem_centralizer_iff.mp hπ _ (translation_mem_coordinateU b)).symm
    exact translation_mem_coordinateU b₀
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [coordinateU_eq_range] at hu hv
    obtain ⟨b, rfl⟩ := hu
    obtain ⟨c, rfl⟩ := hv
    rw [← map_mul, ← map_mul, mul_comm]

theorem mem_coordinateU_of_commute {d : Equiv.Perm (Omega K)} (hd : d ∈ coordinateD K)
    (h : d * translation K 1 = translation K 1 * d) : d ∈ coordinateU K := by
  rw [← coordinateGLAction_range_eq_D] at hd
  obtain ⟨A, rfl⟩ := hd
  change coordinateGLAction K A ∈ coordinateU K
  have hp1 : ∀ x, coordinateGLAction K A (translation K 1 x) =
      translation K 1 (coordinateGLAction K A x) := fun x => congrArg (fun f => f x) h
  have hinf : coordinateGLAction K A none = none := by
    have h1 := hp1 none
    rw [translation_none] at h1
    cases hω : coordinateGLAction K A none with
    | none => rfl
    | some y =>
      rw [hω, translation_some] at h1
      have := Option.some_injective _ h1
      have h10 : (1 : K) = 0 := by linear_combination -this
      exact absurd h10 one_ne_zero
  have hc : A.val 1 0 = 0 := by
    by_contra hc
    rw [coordinateGLAction_infinity K A hc] at hinf
    exact Option.some_ne_none _ hinf
  have hdet : A.val 0 0 * A.val 1 1 ≠ 0 := by
    have h := (GeneralLinearGroup.det A).ne_zero
    change A.val.det ≠ 0 at h
    rw [det_fin_two, hc, mul_zero, sub_zero] at h
    exact h
  have hd0 : A.val 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hfin : ∀ x : K, coordinateGLAction K A (some x) =
      some ((A.val 0 0 * x + A.val 0 1) / A.val 1 1) := by
    intro x
    rw [coordinateGLAction_finite K A x (by rw [hc, zero_mul, zero_add]; exact hd0), hc, zero_mul,
      zero_add]
  have ha : A.val 0 0 = A.val 1 1 := by
    have h1 := hp1 (some 0)
    rw [translation_some, hfin, hfin, translation_some] at h1
    have := Option.some_injective _ h1
    field_simp at this
    linear_combination this
  have heq : coordinateGLAction K A = translation K (A.val 0 1 / A.val 1 1) := by
    apply Equiv.ext
    intro x
    cases x with
    | none => rw [hinf, translation_none]
    | some x =>
      rw [hfin, translation_some, ha]
      congr 1
      field_simp
  rw [heq]
  exact translation_mem_coordinateU _

theorem sq_sub_half_trace_eq_zero (hℓ : ringChar K ≠ 2) (M : Matrix (Fin 2) (Fin 2) K)
    (hns : ∀ c : K, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) (hp : (ringChar K).Prime)
    {c : K} (hpow : M ^ ringChar K = c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    (M - (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) K)) *
      (M - (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) K)) = 0 := by
  set ℓ := ringChar K with hℓdef
  have : Fact ℓ.Prime := ⟨hp⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hℓ
  set lam := M.trace / 2 with hlam
  set N := M - lam • (1 : Matrix (Fin 2) (Fin 2) K) with hN
  set δ := lam ^ 2 - M.det with hδ
  have hN2 : N * N = δ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have hch := mul_self_eq_trace_smul_sub_det_smul M
    have htr : M.trace = 2 * lam := by rw [hlam]; field_simp
    rw [hN, sub_mul, mul_sub, mul_sub, hch, smul_mul_smul_comm, one_mul, smul_one_mul,
      mul_smul_one, htr, hδ]
    module
  have hcomm : Commute (lam • (1 : Matrix (Fin 2) (Fin 2) K)) N :=
    (Commute.one_left N).smul_left lam
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ
  obtain ⟨m, hm⟩ := hodd
  have hNpow : N ^ ℓ = δ ^ m • N := by
    rw [hm, pow_succ, pow_mul, sq, hN2, smul_pow, one_pow, smul_mul_assoc, one_mul]
  have hMpow : M ^ ℓ = lam ^ ℓ • (1 : Matrix (Fin 2) (Fin 2) K) + δ ^ m • N := by
    rw [show M = lam • (1 : Matrix (Fin 2) (Fin 2) K) + N by rw [hN]; abel,
      add_pow_char_of_commute ℓ hcomm, smul_pow, one_pow, hNpow]
  have hδm : δ ^ m = 0 := by
    by_contra hne
    apply hns (lam + (c - lam ^ ℓ) / δ ^ m)
    have h1 : δ ^ m • N = (c - lam ^ ℓ) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [sub_smul, ← hpow, hMpow]
      abel
    have h2' : N = ((c - lam ^ ℓ) / δ ^ m) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [add_smul, ← h2', hN]
    abel
  have hδ0 : δ = 0 := pow_eq_zero_iff (n := m) (by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm
      have := hp.two_le
      omega
    · exact h.ne') |>.mp hδm
  rw [hN2, hδ0, zero_smul]

end Unipotent

section Conjugation

variable {K : Type u} [Field K]

theorem exists_mul_eq_mul_smul_upper {M : Matrix (Fin 2) (Fin 2) K}
    (hns : ∀ c : K, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) {lam : K} (hlam : lam ≠ 0)
    (hN : (M - lam • (1 : Matrix (Fin 2) (Fin 2) K)) * (M - lam • 1) = 0) :
    ∃ H : Matrix (Fin 2) (Fin 2) K, H.det ≠ 0 ∧ M * H = H * (lam • !![1, 1; 0, 1]) := by
  have e00 := congrFun (congrFun hN 0) 0
  have e01 := congrFun (congrFun hN 0) 1
  have e11 := congrFun (congrFun hN 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at e00 e01 e11
  by_cases hb : M 0 1 = 0
  ·
    have ha : M 0 0 = lam := by
      have h0 : (M 0 0 - lam) * (M 0 0 - lam) = 0 := by rw [hb] at e00; linear_combination e00
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)
    have hd : M 1 1 = lam := by
      have h0 : (M 1 1 - lam) * (M 1 1 - lam) = 0 := by rw [hb] at e11; linear_combination e11
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)
    have hc : M 1 0 ≠ 0 := by
      intro hc
      apply hns lam
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    refine ⟨!![0, 1; M 1 0 / lam, 0], ?_, ?_⟩
    · simp [Matrix.det_fin_two, hc, hlam]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hd] <;>
        field_simp
  ·
    have hsum : M 0 0 - lam + (M 1 1 - lam) = 0 := by
      have h0 : M 0 1 * (M 0 0 - lam + (M 1 1 - lam)) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp h0).resolve_left hb
    refine ⟨!![M 0 1 / lam, 0; -(M 0 0 - lam) / lam, 1], ?_, ?_⟩
    · simp [Matrix.det_fin_two, hb, hlam]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp <;>
        first
          | ring1
          | linear_combination e00 + (lam - M 0 0) * hsum
          | linear_combination hsum

theorem exists_conj_eq_upperGL_one {A : GL (Fin 2) K} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p = ringChar K) (hA : orderOf (ProjGenLinGroup.mk A) = p) :
    ∃ H : GL (Fin 2) K, ProjGenLinGroup.mk (H⁻¹ * A * H) = ProjGenLinGroup.mk (upperGL 1) := by
  have hA1 : ProjGenLinGroup.mk A ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hA
    exact hp.one_lt.ne hA
  have hAns := not_scalar_of_mk_ne_one hA1
  have hℓ2 : ringChar K ≠ 2 := by omega
  have hpow1 : ProjGenLinGroup.mk (A ^ ringChar K) = 1 := by
    rw [map_pow, ← hpℓ, ← hA, pow_orderOf_eq_one]
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    at hpow1
  obtain ⟨c, hc⟩ := hpow1
  have hpow : (A : Matrix (Fin 2) (Fin 2) K) ^ ringChar K = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← Units.val_pow_eq_pow_val, ← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hN := sq_sub_half_trace_eq_zero hℓ2 (A : Matrix (Fin 2) (Fin 2) K) hAns (hpℓ ▸ hp) hpow
  set lam := (A : Matrix (Fin 2) (Fin 2) K).trace / 2 with hlam
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul, sub_zero] at hN
    have := congrArg Matrix.det hN
    rw [Matrix.det_mul, Matrix.det_zero, mul_self_eq_zero] at this
    exact A.det_ne_zero this
  obtain ⟨H, hHdet, hAH⟩ := exists_mul_eq_mul_smul_upper hAns hlam0 hN
  set Hg : GL (Fin 2) K := GeneralLinearGroup.mkOfDetNeZero H hHdet
  refine ⟨Hg, ?_⟩
  have hGL : A * Hg =
      Hg * (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 lam hlam0) * upperGL 1) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    change (A : Matrix (Fin 2) (Fin 2) K) * H = H * (Matrix.scalar (Fin 2) lam * !![1, 1; 0, 1])
    rw [hAH, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_one_mul]
  have hconj : Hg⁻¹ * A * Hg =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 lam hlam0) * upperGL 1 := by
    rw [mul_assoc, hGL, inv_mul_cancel_left]
  rw [hconj, map_mul, ProjGenLinGroup.mk_scalar, one_mul]

end Conjugation

theorem linear_two_inner_prime_centralizer_alternatives (K : Type u) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {a : Equiv.Perm (Omega K)} (haD : a ∈ coordinateD K)
    (ha : orderOf a = p) :
    (p ≠ ringChar K →
      IsCyclic (coordinateD K ⊓ Subgroup.centralizer {a} : Subgroup (Equiv.Perm (Omega K)))) ∧
    (p = ringChar K → ∃ h ∈ coordinateD K, h * a * h⁻¹ = translation K 1 ∧
      coordinateD K ⊓ Subgroup.centralizer {a} = (coordinateU K).map (MulAut.conj h⁻¹).toMonoidHom ∧
      IsPGroup p (coordinateD K ⊓ Subgroup.centralizer {a} : Subgroup (Equiv.Perm (Omega K))) ∧
      ((coordinateD K ⊓ Subgroup.centralizer {a}).subgroupOf
        (coordinateE K ⊓ Subgroup.centralizer {a})).Normal ∧
      coordinateD K ⊓ Subgroup.centralizer {a} ≤ coordinateG K ∧
      coordinateE K ⊓ Subgroup.centralizer
          ((coordinateD K ⊓ Subgroup.centralizer {a} : Subgroup (Equiv.Perm (Omega K))) :
            Set (Equiv.Perm (Omega K))) =
        coordinateD K ⊓ Subgroup.centralizer {a} ∧
      ∀ B : Subgroup (Equiv.Perm (Omega K)), coordinateG K ≤ B → B ≤ coordinateE K → a ∈ B →
        ∀ R : Subgroup (Equiv.Perm (Omega K)), R ≤ B ⊓ Subgroup.centralizer {a} →
          (R.subgroupOf (B ⊓ Subgroup.centralizer {a})).Normal →
            Nat.Coprime (Nat.card R) p → R = ⊥) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rw [← coordinatePGLAction_range_eq_D] at haD
  obtain ⟨g, rfl⟩ := haD
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  have hinj := coordinatePGLAction_injective K
  have hg : orderOf (ProjGenLinGroup.mk A) = p := by rwa [orderOf_injective _ hinj] at ha
  set a := coordinatePGLAction K (ProjGenLinGroup.mk A) with ha_def
  have hcent : coordinateD K ⊓ Subgroup.centralizer {a} =
      (Subgroup.centralizer {ProjGenLinGroup.mk A}).map (coordinatePGLAction K) := by
    ext x
    constructor
    · rintro ⟨hxD, hxa⟩
      rw [← coordinatePGLAction_range_eq_D] at hxD
      obtain ⟨y, rfl⟩ := hxD
      refine ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr (hinj ?_), rfl⟩
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hxa
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨by rw [← coordinatePGLAction_range_eq_D]; exact ⟨y, rfl⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hy]
  refine ⟨fun hpℓ => ?_, fun hpℓ => ?_⟩
  ·
    have := isCyclic_centralizer_of_ne_ringChar hp hp3 hpℓ hg
    rw [hcent]
    exact isCyclic_of_surjective _ ((coordinatePGLAction K).subgroupMap_surjective _)
  obtain ⟨H, hH⟩ := exists_conj_eq_upperGL_one hp hp3 hpℓ hg
  set h := coordinatePGLAction K (ProjGenLinGroup.mk H⁻¹) with hh
  have hhD : h ∈ coordinateD K := by
    rw [← coordinatePGLAction_range_eq_D]
    exact ⟨_, rfl⟩
  have hconj : h * a * h⁻¹ = translation K 1 := by
    rw [hh, ha_def, ← map_inv, ← map_inv, inv_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      hH, ← coordinateGLAction_upperGL]
    rfl
  have hcomm_iff : ∀ x : Equiv.Perm (Omega K), x * a = a * x ↔
      (h * x * h⁻¹) * translation K 1 = translation K 1 * (h * x * h⁻¹) := by
    intro x
    rw [← hconj]
    constructor
    · intro hx
      calc h * x * h⁻¹ * (h * a * h⁻¹) = h * (x * a) * h⁻¹ := by group
        _ = h * (a * x) * h⁻¹ := by rw [hx]
        _ = h * a * h⁻¹ * (h * x * h⁻¹) := by group
    · intro hx
      have h2 : h * (x * a) * h⁻¹ = h * (a * x) * h⁻¹ := by
        calc h * (x * a) * h⁻¹ = h * x * h⁻¹ * (h * a * h⁻¹) := by group
          _ = h * a * h⁻¹ * (h * x * h⁻¹) := hx
          _ = h * (a * x) * h⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
  set Q := coordinateD K ⊓ Subgroup.centralizer {a} with hQ
  have hQU : Q = (coordinateU K).map (MulAut.conj h⁻¹).toMonoidHom := by
    ext x
    constructor
    · rintro ⟨hxD, hxa⟩
      have hy : h * x * h⁻¹ ∈ coordinateU K :=
        mem_coordinateU_of_commute (mul_mem (mul_mem hhD hxD) (inv_mem hhD))
          ((hcomm_iff x).mp (Subgroup.mem_centralizer_singleton_iff.mp hxa))
      refine ⟨_, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    · rintro ⟨u, hu, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hhD)
        (coordinateG_le_D K (coordinateU_le_coordinateG hu))) hhD,
        Subgroup.mem_centralizer_singleton_iff.mpr ((hcomm_iff _).mpr ?_)⟩
      have hu' : u * translation K 1 = translation K 1 * u := by
        rw [← centralizer_coordinateU] at hu
        exact Subgroup.mem_centralizer_iff.mp hu _ (translation_mem_coordinateU 1) |>.symm
      calc h * (h⁻¹ * u * h) * h⁻¹ * translation K 1 = u * translation K 1 := by group
        _ = translation K 1 * u := hu'
        _ = translation K 1 * (h * (h⁻¹ * u * h) * h⁻¹) := by group
  have hQp : IsPGroup p Q := by
    obtain ⟨n, -, hKn⟩ := finiteField_primePower K
    refine IsPGroup.of_card (n := n) ?_
    rw [hQU, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, card_coordinateU, hKn,
      hpℓ]
  have hQnormal : (Q.subgroupOf (coordinateE K ⊓ Subgroup.centralizer {a})).Normal := by
    constructor
    intro n hn e
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnD, hna⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨heE, hea⟩ := Subgroup.mem_inf.mp e.2
    have hD := (coordinateD_normal_in_E K).conj_mem ⟨n, coordinateD_le_E K hnD⟩
      (Subgroup.mem_subgroupOf.mpr hnD) ⟨e, heE⟩
    rw [Subgroup.mem_subgroupOf] at hD
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hD
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        mul_mem (mul_mem hea hna) (inv_mem hea)
  have hQG : Q ≤ coordinateG K := by
    rw [hQU]
    rintro _ ⟨u, hu, rfl⟩
    have hG := (coordinateG_normal_in_D K).conj_mem
      ⟨u, coordinateG_le_D K (coordinateU_le_coordinateG hu)⟩
      (Subgroup.mem_subgroupOf.mpr (coordinateU_le_coordinateG hu)) ⟨h⁻¹, inv_mem hhD⟩
    rw [Subgroup.mem_subgroupOf] at hG
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] using hG
  have hQcent : coordinateE K ⊓ Subgroup.centralizer (Q : Set (Equiv.Perm (Omega K))) = Q := by
    apply le_antisymm
    · rintro x ⟨-, hx⟩
      have hy : h * x * h⁻¹ ∈ coordinateU K := by
        rw [← centralizer_coordinateU, Subgroup.mem_centralizer_iff]
        intro u hu
        have huQ : h⁻¹ * u * h ∈ Q := by
          rw [hQU]
          exact ⟨u, hu, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
        have := Subgroup.mem_centralizer_iff.mp hx _ huQ
        calc u * (h * x * h⁻¹) = h * ((h⁻¹ * u * h) * x) * h⁻¹ := by group
          _ = h * (x * (h⁻¹ * u * h)) * h⁻¹ := by rw [this]
          _ = h * x * h⁻¹ * u := by group
      rw [hQU]
      exact ⟨_, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group⟩
    · intro x hx
      refine ⟨coordinateD_le_E K hx.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [hQU] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have huv : u * v = v * u := by
        rw [← centralizer_coordinateU] at hu
        exact (Subgroup.mem_centralizer_iff.mp hu _ hv).symm
      calc h⁻¹ * v * h * (h⁻¹ * u * h) = h⁻¹ * (v * u) * h := by group
        _ = h⁻¹ * (u * v) * h := by rw [huv]
        _ = h⁻¹ * u * h * (h⁻¹ * v * h) := by group
  refine ⟨h, hhD, hconj, hQU, hQp, hQnormal, hQG, hQcent, ?_⟩
  intro B hGB hBE haB R hRB hRnormal hRcop
  have hQB : Q ≤ B ⊓ Subgroup.centralizer {a} := fun x hx => ⟨hGB (hQG hx), hx.2⟩
  have hRQ : Q ⊓ R = ⊥ := inf_eq_bot_of_isPGroup_of_coprime hQp hRcop
  rw [eq_bot_iff]
  intro r hr
  have hrB := hRB hr
  have hrQ : r ∈ Q := by
    rw [← hQcent]
    refine ⟨hBE hrB.1, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hqB := hQB hq
    have h1 : q * r * q⁻¹ ∈ R := by
      have := hRnormal.conj_mem ⟨r, hrB⟩ (Subgroup.mem_subgroupOf.mpr hr) ⟨q, hqB⟩
      rwa [Subgroup.mem_subgroupOf] at this
    have h2 : r * q * r⁻¹ ∈ Q := by
      have := hQnormal.conj_mem ⟨q, hBE hqB.1, hqB.2⟩ (Subgroup.mem_subgroupOf.mpr hq)
        ⟨r, hBE hrB.1, hrB.2⟩
      rwa [Subgroup.mem_subgroupOf] at this
    have hcQ : q * r * q⁻¹ * r⁻¹ ∈ Q := by
      have : q * r * q⁻¹ * r⁻¹ = q * (r * q * r⁻¹)⁻¹ := by group
      rw [this]
      exact mul_mem hq (inv_mem h2)
    have hcR : q * r * q⁻¹ * r⁻¹ ∈ R := mul_mem h1 (inv_mem hr)
    have hc : q * r * q⁻¹ * r⁻¹ ∈ Q ⊓ R := ⟨hcQ, hcR⟩
    rw [hRQ, Subgroup.mem_bot] at hc
    have : q * r = r * q := by
      have := mul_eq_one_iff_eq_inv.mp hc
      rw [inv_inv] at this
      calc q * r = q * r * q⁻¹ * q := by group
        _ = r * q := by rw [this]
    exact this
  have hmem : r ∈ Q ⊓ R := ⟨hrQ, hr⟩
  rwa [hRQ] at hmem

end CFSG.RankThree.LinearTwo
