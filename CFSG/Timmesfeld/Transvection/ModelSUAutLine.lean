module

public import CFSG.Timmesfeld.Transvection.ModelSULine
public import CFSG.Timmesfeld.Transvection.ModelSUAut

import CFSG.GH74.GLS.Stage2.OddAut.CoprimeCrit
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

private theorem eigen_eq_of_uForm_ne_zero [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a d : Fin m → F} {M : Matrix (Fin m) (Fin m) F}
    (hM : ∀ u ∈ perpPair σ a d, uForm σ u u = 0 → ∃ μ : F, M *ᵥ u = μ • u)
    {v w : Fin m → F} (hv : v ∈ perpPair σ a d) (hw : w ∈ perpPair σ a d)
    (hvv : uForm σ v v = 0) (hww : uForm σ w w = 0) (hvw : uForm σ v w ≠ 0)
    {μ ν : F} (hμ : M *ᵥ v = μ • v) (hν : M *ᵥ w = ν • w) : μ = ν := by
  have hσc : σ (uForm σ v w) ≠ 0 := by
    intro h
    exact hvw (σ.injective (by rw [h, map_zero]))
  have hsumP : v + (uForm σ v w)⁻¹ • w ∈ perpPair σ a d :=
    (perpPair σ a d).add_mem hv ((perpPair σ a d).smul_mem _ hw)
  have hsum_iso : uForm σ (v + (uForm σ v w)⁻¹ • w) (v + (uForm σ v w)⁻¹ • w) = 0 := by
    rw [uForm_add_left, uForm_add_right, uForm_add_right, uForm_smul_left, uForm_smul_left,
      uForm_smul_right, uForm_smul_right, hvv, hww,
      show uForm σ w v = σ (uForm σ v w) from (uForm_conj σ hσ v w).symm]
    simp only [mul_zero, add_zero, zero_add]
    rw [map_inv₀, inv_mul_cancel₀ hvw, inv_mul_cancel₀ hσc]
    exact CharTwo.add_self_eq_zero 1
  obtain ⟨κ, hκ⟩ := hM _ hsumP hsum_iso
  have hMv : M *ᵥ (v + (uForm σ v w)⁻¹ • w) =
      μ • v + ((uForm σ v w)⁻¹ * ν) • w := by
    rw [mulVec_add, mulVec_smul, hμ, hν, smul_smul]
  have he : μ • v + ((uForm σ v w)⁻¹ * ν) • w =
      κ • v + (κ * (uForm σ v w)⁻¹) • w := by
    calc μ • v + ((uForm σ v w)⁻¹ * ν) • w =
        M *ᵥ (v + (uForm σ v w)⁻¹ • w) := hMv.symm
      _ = κ • (v + (uForm σ v w)⁻¹ • w) := hκ
      _ = κ • v + (κ * (uForm σ v w)⁻¹) • w := by rw [smul_add, smul_smul]
  have hμκ : μ = κ := by
    have h := congrArg (fun x => uForm σ x w) he
    simp only [uForm_add_left, uForm_smul_left, hww, mul_zero, add_zero] at h
    exact σ.injective (mul_right_cancel₀ hvw h)
  have hwv : uForm σ w v ≠ 0 := by
    rw [← uForm_conj σ hσ v w]
    exact hσc
  have hνκ : ν = κ := by
    have h := congrArg (fun x => uForm σ x v) he
    simp only [uForm_add_left, uForm_smul_left, hvv, mul_zero, zero_add] at h
    have h' : (uForm σ v w)⁻¹ * ν = κ * (uForm σ v w)⁻¹ :=
      σ.injective (mul_right_cancel₀ hwv h)
    calc ν = uForm σ v w * ((uForm σ v w)⁻¹ * ν) := by
          rw [← mul_assoc, mul_inv_cancel₀ hvw, one_mul]
      _ = uForm σ v w * (κ * (uForm σ v w)⁻¹) := by rw [h']
      _ = κ := by field_simp [hvw]
  rw [hμκ, hνκ]

private theorem eigen_eq_of_isotropic [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a d : Fin m → F} (G : SUGeomFacts σ a d) {M : Matrix (Fin m) (Fin m) F}
    (hM : ∀ u ∈ perpPair σ a d, uForm σ u u = 0 → ∃ μ : F, M *ᵥ u = μ • u)
    {v w : Fin m → F} (hv : v ∈ perpPair σ a d) (hw : w ∈ perpPair σ a d)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hvv : uForm σ v v = 0) (hww : uForm σ w w = 0)
    {μ ν : F} (hμ : M *ᵥ v = μ • v) (hν : M *ᵥ w = ν • w) : μ = ν := by
  obtain ⟨y, hyP, hyy, hvy, hwy⟩ := G.both hv hw hv0 hw0 hvv hww
  obtain ⟨κ, hκ⟩ := hM y hyP hyy
  have hμκ : μ = κ := eigen_eq_of_uForm_ne_zero hσ hM hv hyP hvv hyy hvy hμ hκ
  have hνκ : ν = κ := eigen_eq_of_uForm_ne_zero hσ hM hw hyP hww hyy hwy hν hκ
  rw [hμκ, hνκ]

theorem exists_smul_of_forall_isotropic_eigen [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) (hnorm : ∀ c, σ c = c → ∃ l, σ l * l = c)
    (hm : 4 ≤ m) {a d : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) (M : Matrix (Fin m) (Fin m) F)
    (hM : ∀ u ∈ perpPair σ a d, uForm σ u u = 0 → ∃ μ : F, M *ᵥ u = μ • u) :
    ∃ l : F, ∀ u ∈ perpPair σ a d, M *ᵥ u = l • u := by
  classical
  have G : SUGeomFacts σ a d := suGeomFacts_holds hσ htr hnorm hm haa hdd had
  obtain ⟨e₀, he₀P, he₀0, he₀iso⟩ := G.exists_iso
  obtain ⟨l, hl⟩ := hM e₀ he₀P he₀iso
  refine ⟨l, fun u hu => ?_⟩
  obtain ⟨e₁, he₁P, e₂, he₂P, he₁iso, he₂iso, rfl⟩ := G.sum hu
  have h1 : M *ᵥ e₁ = l • e₁ := by
    by_cases h : e₁ = 0
    · rw [h, mulVec_zero, smul_zero]
    · obtain ⟨μ, hμ⟩ := hM e₁ he₁P he₁iso
      have hμl : μ = l :=
        eigen_eq_of_isotropic hσ G hM he₁P he₀P h he₀0 he₁iso he₀iso hμ hl
      rwa [hμl] at hμ
  have h2 : M *ᵥ e₂ = l • e₂ := by
    by_cases h : e₂ = 0
    · rw [h, mulVec_zero, smul_zero]
    · obtain ⟨ν, hν⟩ := hM e₂ he₂P he₂iso
      have hνl : ν = l :=
        eigen_eq_of_isotropic hσ G hM he₂P he₀P h he₀0 he₂iso he₀iso hν hl
      rwa [hνl] at hν
  rw [mulVec_add, h1, h2, smul_add]

private theorem conjTr_pow_mul_antidiag {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : conjTr σ M * antidiag n * M = antidiag n) (k : ℕ) :
    conjTr σ (M ^ k) * antidiag n * M ^ k = antidiag n := by
  induction k with
  | zero => simp [conjTr_one]
  | succ k ih =>
    rw [pow_succ, conjTr_mul]
    calc conjTr σ M * conjTr σ (M ^ k) * antidiag n * (M ^ k * M) =
        conjTr σ M * (conjTr σ (M ^ k) * antidiag n * M ^ k) * M := by
          simp only [Matrix.mul_assoc]
      _ = conjTr σ M * antidiag n * M := by rw [ih]
      _ = antidiag n := hM

private theorem exists_smul_sub_of_det_ne_zero {a d z w : Fin m → F} {x y x' y' : F}
    (hz : z = x • a + y • d) (hw : w = x' • a + y' • d) (hD : x * y' - y * x' ≠ 0) :
    a = (x * y' - y * x')⁻¹ • (y' • z - y • w) ∧
      d = (x * y' - y * x')⁻¹ • (x • w - x' • z) := by
  constructor
  · rw [hz, hw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h : y' * (x * a i + y * d i) - y * (x' * a i + y' * d i) =
        (x * y' - y * x') * a i := by ring
    rw [h, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  · rw [hz, hw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h : x * (x' * a i + y' * d i) - x' * (x * a i + y * d i) =
        (x * y' - y * x') * d i := by ring
    rw [h, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]

private theorem exists_eq_smul_of_det_eq_zero {x y x' y' : F}
    (hD : x * y' - y * x' = 0) (h : x ≠ 0 ∨ y ≠ 0) :
    ∃ l : F, x' = l * x ∧ y' = l * y := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      rcases h with h' | h'
      · exact absurd hx h'
      · exact h'
    have hx' : x' = 0 := by
      rw [hx] at hD
      have h0 : y * x' = 0 := by linear_combination -hD
      exact (mul_eq_zero.mp h0).resolve_left hy
    refine ⟨y' / y, ?_, ?_⟩
    · rw [hx', hx, mul_zero]
    · exact (div_mul_cancel₀ y' hy).symm
  · have hD' : x * y' = y * x' := sub_eq_zero.mp hD
    refine ⟨x' / x, ?_, ?_⟩
    · exact (div_mul_cancel₀ x' hx).symm
    · rw [div_mul_eq_mul_div, eq_div_iff hx]
      linear_combination hD'

private theorem projPair_eq_zero_of_mulVec_eq_add [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a d z w : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) {M : Matrix (Fin m) (Fin m) F}
    (hMiso : conjTr σ M * antidiag m * M = antidiag m)
    (hMP : ∀ u ∈ perpPair σ a d, M *ᵥ u = u) (hMw : M *ᵥ w = z + w) :
    projPair σ a d z = 0 := by
  have hPz : ∀ u ∈ perpPair σ a d, uForm σ u z = 0 := by
    intro u hu
    have h1 : uForm σ u (M *ᵥ w) = uForm σ u w := by
      have h := uForm_mulVec_of_isometry hMiso u w
      rwa [hMP u hu] at h
    rw [hMw, uForm_add_right] at h1
    exact add_right_cancel (h1.trans (zero_add _).symm)
  apply eq_zero_of_forall_uForm_eq_zero
  intro v
  rw [eq_projPair_add (σ := σ) a d v, uForm_add_right, uForm_add_right, uForm_smul_right,
    uForm_smul_right]
  have hq : projPair σ a d v ∈ perpPair σ a d := projPair_mem hσ haa hdd had v
  have hzq : uForm σ z (projPair σ a d v) = 0 := by
    rw [← uForm_conj σ hσ, hPz _ hq, map_zero]
  have hpP : projPair σ a d z ∈ perpPair σ a d := projPair_mem hσ haa hdd had z
  have hpq : uForm σ (projPair σ a d z) (projPair σ a d v) = 0 := by
    have hpz : projPair σ a d z = z - uForm σ d z • a - uForm σ a z • d := rfl
    rw [hpz, uForm_sub_left, uForm_sub_left, uForm_smul_left, uForm_smul_left,
      hzq, hq.1, hq.2]
    ring
  have hpa : uForm σ (projPair σ a d z) a = 0 := by
    have h := uForm_conj σ hσ (projPair σ a d z) a
    rw [hpP.1] at h
    exact σ.injective (by rw [h, map_zero])
  have hpd : uForm σ (projPair σ a d z) d = 0 := by
    have h := uForm_conj σ hσ (projPair σ a d z) d
    rw [hpP.2] at h
    exact σ.injective (by rw [h, map_zero])
  rw [hpq, hpa, hpd]
  ring

private theorem uForm_self_eq_zero_of_mulVec_eq_add [CharP F 2] {z w : Fin m → F}
    {M : Matrix (Fin m) (Fin m) F} (hMiso : conjTr σ M * antidiag m * M = antidiag m)
    (hMz : M *ᵥ z = z) (hMw : M *ᵥ w = z + w) : uForm σ z z = 0 := by
  have h := uForm_mulVec_of_isometry hMiso w z
  rw [hMw, hMz, uForm_add_left] at h
  exact add_right_cancel (h.trans (zero_add _).symm)

private theorem eq_one_of_mem_lineSL_of_coords [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a d z : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) {s : SU σ m} (hs : s ∈ lineSL σ a d)
    (hse : ∀ (u : Fin m → F) (l : F), uForm σ u u = 0 → u ∉ perpPair σ a d →
      suMat σ m s *ᵥ u ≠ l • u)
    {M : Matrix (Fin m) (Fin m) F} (hMP : ∀ u ∈ perpPair σ a d, M *ᵥ u = u)
    (hz0 : z ≠ 0) (hzz : uForm σ z z = 0) (hzP : z ∉ perpPair σ a d)
    (hp : projPair σ a d z = 0) (hMz : M *ᵥ z = z)
    (hMsz : M *ᵥ (suMat σ m s *ᵥ z) = suMat σ m s *ᵥ z) : M = 1 := by
  have hzdecomp : z = uForm σ d z • a + uForm σ a z • d := by
    have h := eq_projPair_add (σ := σ) a d z
    rw [hp] at h
    simpa using h
  obtain ⟨hsP, α, β, γ, δ, hα, hβ, hγ, hδ, hdet, hsa, hsd⟩ := hs
  have hsz : suMat σ m s *ᵥ z =
      (uForm σ d z * α + uForm σ a z * γ) • a +
        (uForm σ d z * β + uForm σ a z * δ) • d := by
    conv_lhs => rw [hzdecomp]
    rw [mulVec_add, mulVec_smul, mulVec_smul, hsa, hsd]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  set x := uForm σ d z with hx
  set y := uForm σ a z with hy
  set x' := x * α + y * γ with hx'
  set y' := x * β + y * δ with hy'
  have hsz' : suMat σ m s *ᵥ z = x' • a + y' • d := hsz
  have hz' : z = x • a + y • d := hzdecomp
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    apply hz0
    rw [hz', h.1, h.2, zero_smul, zero_smul, add_zero]
  by_cases hD : x * y' - y * x' = 0
  · obtain ⟨l, hl1, hl2⟩ := exists_eq_smul_of_det_eq_zero hD hxy
    have hszl : suMat σ m s *ᵥ z = l • z := by
      rw [hsz', hz', hl1, hl2, smul_add, smul_smul, smul_smul]
    exact absurd hszl (hse z l hzz hzP)
  · obtain ⟨ha, hd⟩ := exists_smul_sub_of_det_ne_zero hz' hsz' hD
    have hMa : M *ᵥ a = a := by
      rw [ha, mulVec_smul, mulVec_sub, mulVec_smul, mulVec_smul, hMz, hMsz]
    have hMd : M *ᵥ d = d := by
      rw [hd, mulVec_smul, mulVec_sub, mulVec_smul, mulVec_smul, hMz, hMsz]
    exact eq_one_of_mulVec_eq hσ haa hdd had hMa hMd hMP

theorem eq_one_of_commute_of_mem_lineSL [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a d : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) {s : SU σ m} (hs : s ∈ lineSL σ a d)
    (hse : ∀ (u : Fin m → F) (l : F), uForm σ u u = 0 → u ∉ perpPair σ a d →
      suMat σ m s *ᵥ u ≠ l • u)
    {M : Matrix (Fin m) (Fin m) F} {k : ℕ} (hMk : M ^ 2 ^ k = 1)
    (hMiso : conjTr σ M * antidiag m * M = antidiag m)
    (hMP : ∀ u ∈ perpPair σ a d, M *ᵥ u = u) (hMs : M * suMat σ m s = suMat σ m s * M) :
    M = 1 := by
  classical
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : uForm σ (0 : Fin m → F) d = 0 := by simp [uForm]
    rw [h0] at had
    exact zero_ne_one had
  haveI : Nonempty (Fin m) := by
    obtain ⟨i, _⟩ := Function.ne_iff.1 ha0
    exact ⟨i⟩
  haveI : CharP (Matrix (Fin m) (Fin m) F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (Matrix (Fin m) (Fin m) F)).injective 2
  have hN : (M - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute (p := 2) (n := k) (Commute.one_right M), one_pow,
      hMk, sub_self]
  by_contra hMne
  have hNne : M - 1 ≠ 0 := sub_ne_zero.mpr hMne
  obtain ⟨z, hz0, hNz, w, hwz⟩ :=
    CFSG.GH74.GLS.Stage2.OddAut.exists_mem_ker_range_of_nilpotent hN hNne
  have hMw : M *ᵥ w = z + w := by
    have h : M *ᵥ w - w = z := by
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hwz
    rw [← h]
    abel
  have hMz : M *ᵥ z = z := by
    have h : M *ᵥ z - z = 0 := by
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hNz
    exact sub_eq_zero.mp h
  have hp := projPair_eq_zero_of_mulVec_eq_add hσ haa hdd had hMiso hMP hMw
  have hzz := uForm_self_eq_zero_of_mulVec_eq_add hMiso hMz hMw
  have hzP : z ∉ perpPair σ a d := by
    intro hz
    apply hz0
    rw [← projPair_of_mem hz, hp]
  have hMsz : M *ᵥ (suMat σ m s *ᵥ z) = suMat σ m s *ᵥ z := by
    rw [Matrix.mulVec_mulVec, hMs, ← Matrix.mulVec_mulVec, hMz]
  exact hMne (eq_one_of_mem_lineSL_of_coords hσ haa hdd had hs hse hMP hz0 hzz hzP hp hMz hMsz)

private theorem IsSemilinearLift.iterate {n : ℕ} {K : Type*} [Group K]
    {Φ : SU σ n →* K} {y : K} {A : GL (Fin n) F} {φ : F ≃+* F}
    {α : SU σ n →* SU σ n} (hL : IsSemilinearLift Φ y A φ α) (hφ : ∀ c, φ c = c)
    (k : ℕ) (g : SU σ n) :
    suMat σ n (α^[k] g) * ((A : Matrix (Fin n) (Fin n) F) ^ k) =
        ((A : Matrix (Fin n) (Fin n) F) ^ k) * suMat σ n g ∧
      Φ (α^[k] g) = y ^ k * Φ g * (y ^ k)⁻¹ := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    constructor
    · have hmat := hL.mat (α^[k] g)
      have hmap : (suMat σ n (α^[k] g)).map φ = suMat σ n (α^[k] g) := by
        ext i j
        simp only [Matrix.map_apply, hφ]
      rw [hmap] at hmat
      rw [pow_succ']
      calc suMat σ n (α (α^[k] g)) * ((A : Matrix (Fin n) (Fin n) F) *
            (A : Matrix (Fin n) (Fin n) F) ^ k) =
          (suMat σ n (α (α^[k] g)) * (A : Matrix (Fin n) (Fin n) F)) *
            (A : Matrix (Fin n) (Fin n) F) ^ k := by rw [Matrix.mul_assoc]
        _ = ((A : Matrix (Fin n) (Fin n) F) * suMat σ n (α^[k] g)) *
            (A : Matrix (Fin n) (Fin n) F) ^ k := by rw [hmat]
        _ = (A : Matrix (Fin n) (Fin n) F) *
            (suMat σ n (α^[k] g) * (A : Matrix (Fin n) (Fin n) F) ^ k) := by
          rw [Matrix.mul_assoc]
        _ = (A : Matrix (Fin n) (Fin n) F) *
            ((A : Matrix (Fin n) (Fin n) F) ^ k * suMat σ n g) := by rw [(ih g).1]
        _ = ((A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) ^ k) *
            suMat σ n g := by rw [Matrix.mul_assoc]
    · rw [pow_succ', hL.conj, (ih g).2]
      group

private theorem exists_scalar_of_semilinear_on_perpPair [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 4 ≤ n) {K : Type*} [Group K]
    {Φ : SU (unitaryInvolution F 2 f) n →* K} {y : K} {A : GL (Fin n) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) n →* SU (unitaryInvolution F 2 f) n}
    (hL : IsSemilinearLift Φ y A φ α) (hφ : ∀ c, φ c = c)
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) {a d : Fin n → F}
    (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1)
    (hP : ∀ u ∈ perpPair (unitaryInvolution F 2 f) a d,
      uForm (unitaryInvolution F 2 f) u u = 0 → ∀ t, suMat (unitaryInvolution F 2 f) n t =
        uTrans (unitaryInvolution F 2 f) u 1 → y * Φ t = Φ t * y) :
    ∃ lam : F, lam ≠ 0 ∧ unitaryInvolution F 2 f lam * lam = 1 ∧
      ∀ u ∈ perpPair (unitaryInvolution F 2 f) a d,
        (A : Matrix (Fin n) (Fin n) F) *ᵥ u = lam • u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c →
      ∃ e, e + unitaryInvolution F 2 f e = c := fun c hc => exists_add_unitaryInvolution_eq hF hc
  have hnorm : ∀ c, unitaryInvolution F 2 f c = c →
      ∃ l, unitaryInvolution F 2 f l * l = c := fun c hc => exists_sigma_mul_self_eq hF hc
  have G : SUGeomFacts (unitaryInvolution F 2 f) a d :=
    suGeomFacts_holds hσ htr hnorm hn haa hdd had
  have hAeig : ∀ u ∈ perpPair (unitaryInvolution F 2 f) a d,
      uForm (unitaryInvolution F 2 f) u u = 0 →
      ∃ μ : F, (A : Matrix (Fin n) (Fin n) F) *ᵥ u = μ • u := by
    intro u hu huu
    obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans (σ := unitaryInvolution F 2 f) hσ huu
      (c := 1) (by rw [map_one]; exact CharTwo.add_self_eq_zero 1)
    have hyt : y * Φ t = Φ t * y := hP u hu huu t ht
    obtain ⟨μ, hμ⟩ := hL.exists_smul hker huu ht hyt
    refine ⟨μ, ?_⟩
    have hphiu : (fun i => φ (u i)) = u := by
      funext i
      exact hφ (u i)
    rwa [hphiu] at hμ
  obtain ⟨lam, hlam⟩ := exists_smul_of_forall_isotropic_eigen hσ htr hnorm hn haa hdd had
    (A : Matrix (Fin n) (Fin n) F) hAeig
  have hlamnorm : unitaryInvolution F 2 f lam * lam = 1 := by
    obtain ⟨e, heP, he0, hee⟩ := G.exists_iso
    obtain ⟨e', he'P, he'e', hee'⟩ := G.partner heP he0 hee
    have h1 := uForm_mulVec_of_isometry hL.isometry e e'
    rw [hlam e heP, hlam e' he'P, uForm_smul_left, uForm_smul_right, hee'] at h1
    simpa using h1
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hlamnorm
    exact zero_ne_one hlamnorm
  exact ⟨lam, hlam0, hlamnorm, hlam⟩

private theorem exists_semilinearLift_fixes_perpPair [Finite F] [CharP F 2] {f n : ℕ}
    {K : Type*} [Group K] {Φ : SU (unitaryInvolution F 2 f) n →* K} {y : K}
    {A : GL (Fin n) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) n →* SU (unitaryInvolution F 2 f) n}
    (hL : IsSemilinearLift Φ y A φ α) {a d : Fin n → F} {lam : F}
    (hlam0 : lam ≠ 0) (hlamnorm : unitaryInvolution F 2 f lam * lam = 1)
    (hlam : ∀ u ∈ perpPair (unitaryInvolution F 2 f) a d,
      (A : Matrix (Fin n) (Fin n) F) *ᵥ u = lam • u) :
    ∃ A' : GL (Fin n) F, IsSemilinearLift Φ y A' φ α ∧
      ∀ v ∈ perpPair (unitaryInvolution F 2 f) a d,
        ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = v := by
  let u : Fˣ := Units.mk0 lam⁻¹ (inv_ne_zero hlam0)
  have hu : unitaryInvolution F 2 f (u : F) * (u : F) = 1 := by
    change unitaryInvolution F 2 f (lam⁻¹) * lam⁻¹ = 1
    rw [map_inv₀, ← _root_.mul_inv_rev, mul_comm, hlamnorm, inv_one]
  let A' : GL (Fin n) F := Matrix.GeneralLinearGroup.scalar (Fin n) u * A
  have hL' : IsSemilinearLift Φ y A' φ α := hL.smul u hu
  have hcoe : ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (Matrix.scalar (Fin n) lam⁻¹) * (A : Matrix (Fin n) (Fin n) F) := by
    rw [show A' = Matrix.GeneralLinearGroup.scalar (Fin n) u * A from rfl, Units.val_mul,
      Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  refine ⟨A', hL', fun v hv => ?_⟩
  rw [hcoe, ← Matrix.mulVec_mulVec, Matrix.scalar_apply, Matrix.diagonal_const_mulVec,
    hlam v hv, smul_smul, inv_mul_cancel₀ hlam0, one_smul]

private theorem mul_comm_of_mem_lineSL [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hn : 4 ≤ n) {K : Type*} [Group K]
    {Φ : SU (unitaryInvolution F 2 f) n →* K} {y : K} {A' : GL (Fin n) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) n →* SU (unitaryInvolution F 2 f) n}
    (hL' : IsSemilinearLift Φ y A' φ α) (hφ : ∀ c, φ c = c)
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) {a d : Fin n → F}
    (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1) {s : SU (unitaryInvolution F 2 f) n}
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) a d)
    (hys : y * Φ s = Φ s * y)
    (hA'P : ∀ v ∈ perpPair (unitaryInvolution F 2 f) a d,
      ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = v) :
    ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        suMat (unitaryInvolution F 2 f) n s =
      suMat (unitaryInvolution F 2 f) n s *
        ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have hzker : α s * s⁻¹ ∈ Φ.ker := by
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_inv, hL'.conj s, hys]
    group
  have hzc : α s * s⁻¹ ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n) := hker hzker
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨rfl, h⟩
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hF (by omega) hq hzc
  have hαs : suMat (unitaryInvolution F 2 f) n (α s) =
      c • suMat (unitaryInvolution F 2 f) n s := by
    rw [show α s = (α s * s⁻¹) * s from by group, map_mul]
    rw [hc, Matrix.smul_mul, Matrix.one_mul]
  have hmap : ∀ x : SU (unitaryInvolution F 2 f) n,
      (suMat (unitaryInvolution F 2 f) n x).map φ =
        suMat (unitaryInvolution F 2 f) n x := by
    intro x
    ext i j
    simp only [Matrix.map_apply, hφ]
  obtain ⟨e, heP, he0, hee⟩ := (suGeomFacts_holds hσ
    (fun c hc => exists_add_unitaryInvolution_eq hF hc)
    (fun c hc => exists_sigma_mul_self_eq hF hc) hn haa hdd had).exists_iso
  have hA'e : ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ e = e := hA'P e heP
  have hseP : suMat (unitaryInvolution F 2 f) n s *ᵥ e = e := (mem_lineSL.1 hs).1 e heP
  have hc1 : c = 1 := by
    have hmat := hL'.mat s
    rw [hαs, hmap s, Matrix.smul_mul] at hmat
    have h1 : ((c • (suMat (unitaryInvolution F 2 f) n s *
        ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))) *ᵥ e) = c • e := by
      rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hA'e, hseP]
    have h2 : ((((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        suMat (unitaryInvolution F 2 f) n s) *ᵥ e) = e := by
      rw [← Matrix.mulVec_mulVec, hseP, hA'e]
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M *ᵥ e) hmat
    rw [h1, h2] at h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 he0
    have hh := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    exact mul_right_cancel₀ hi (by simpa using hh)
  have hmat := hL'.mat s
  rw [hαs, hmap s, hc1, one_smul] at hmat
  exact hmat.symm

private theorem exists_odd_pow_eq_one_of_commute [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {K : Type*} [Group K]
    {Φ : SU (unitaryInvolution F 2 f) n →* K} {y : K} {A' : GL (Fin n) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) n →* SU (unitaryInvolution F 2 f) n}
    (hL' : IsSemilinearLift Φ y A' φ α) {a d : Fin n → F}
    (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1) {s : SU (unitaryInvolution F 2 f) n}
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) a d) (hord : orderOf (Φ s) = 2 ^ f + 1)
    (hA'P : ∀ v ∈ perpPair (unitaryInvolution F 2 f) a d,
      ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = v)
    (hAs : ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        suMat (unitaryInvolution F 2 f) n s =
      suMat (unitaryInvolution F 2 f) n s *
        ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    ∃ m₀ : ℕ, Odd m₀ ∧
      ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ m₀ = 1 := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨k, m₀, hodd, hordA⟩ :=
    Nat.exists_eq_two_pow_mul_odd (IsOfFinOrder.orderOf_pos (isOfFinOrder_of_finite A')).ne'
  let M : Matrix (Fin n) (Fin n) F := ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ m₀
  have hMk : M ^ 2 ^ k = 1 := by
    have hpow : ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ orderOf A' = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    rw [show M = ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ m₀ from rfl, ← pow_mul,
      Nat.mul_comm m₀ (2 ^ k), ← hordA]
    exact hpow
  have hMiso : conjTr (unitaryInvolution F 2 f) M * antidiag n * M = antidiag n := by
    rw [show M = ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ m₀ from rfl]
    exact conjTr_pow_mul_antidiag hL'.isometry m₀
  have hMPow : ∀ j : ℕ, ∀ v ∈ perpPair (unitaryInvolution F 2 f) a d,
      (((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ j) *ᵥ v = v := by
    intro j
    induction j with
    | zero => intro v hv; rw [pow_zero, Matrix.one_mulVec]
    | succ j ih =>
      intro v hv
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih v hv, hA'P v hv]
  have hMs : M * suMat (unitaryInvolution F 2 f) n s =
      suMat (unitaryInvolution F 2 f) n s * M :=
    (show Commute (((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (suMat (unitaryInvolution F 2 f) n s) from hAs).pow_left m₀
  have hM1 : M = 1 :=
    eq_one_of_commute_of_mem_lineSL hσ haa hdd had hs
      (fun u l huu hu => mulVec_ne_smul_of_orderOf hF hf Φ haa hdd had hs hord huu hu l)
      hMk hMiso (hMPow m₀) hMs
  exact ⟨m₀, hodd, hM1⟩

private theorem mem_centralizer_range_of_pow_odd_eq_one {n : ℕ} {K : Type*} [Group K]
    {Φ : SU σ n →* K} {y : K} {A' : GL (Fin n) F} {φ : F ≃+* F}
    {α : SU σ n →* SU σ n} (hL' : IsSemilinearLift Φ y A' φ α) (hφ : ∀ c, φ c = c)
    (hy2 : IsPGroup 2 (Subgroup.zpowers y)) {m₀ : ℕ} (hodd : Odd m₀)
    (hpow : ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ m₀ = 1) :
    y ∈ Subgroup.centralizer (Φ.range : Set K) := by
  have hiter := fun g => IsSemilinearLift.iterate hL' hφ m₀ g
  have hαid : ∀ g : SU σ n, α^[m₀] g = g := by
    intro g
    have h := (hiter g).1
    rw [hpow, Matrix.mul_one, Matrix.one_mul] at h
    exact suMat_injective σ h
  have hconj_id : ∀ g : SU σ n, Φ g = y ^ m₀ * Φ g * (y ^ m₀)⁻¹ := by
    intro g
    have h := (hiter g).2
    rw [hαid g] at h
    exact h
  have hycentral : ∀ x ∈ Φ.range, x * y ^ m₀ = y ^ m₀ * x := by
    intro x hx
    obtain ⟨g, rfl⟩ := hx
    have h := hconj_id g
    calc Φ g * y ^ m₀ = (y ^ m₀ * Φ g * (y ^ m₀)⁻¹) * y ^ m₀ := by
          conv_lhs => rw [h]
      _ = y ^ m₀ * Φ g := by group
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hy2) ⟨y, Subgroup.mem_zpowers y⟩
  have hordy : orderOf y = 2 ^ j := by
    simpa [Subgroup.orderOf_coe] using hj
  have hcop : Nat.Coprime m₀ (orderOf y) := by
    rw [hordy]
    exact (Nat.coprime_two_right.mpr hodd).pow_right j
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [← hr]
  exact (show Commute x (y ^ m₀) from hycentral x hx).pow_right r

theorem IsSemilinearLift.mem_centralizer_range [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hn : 4 ≤ n) {K : Type*} [Group K]
    {Φ : SU (unitaryInvolution F 2 f) n →* K} {y : K} {A : GL (Fin n) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) n →* SU (unitaryInvolution F 2 f) n}
    (hL : IsSemilinearLift Φ y A φ α) (hφ : ∀ c, φ c = c)
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) {a d : Fin n → F}
    (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1) {s : SU (unitaryInvolution F 2 f) n}
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) a d) (hord : orderOf (Φ s) = 2 ^ f + 1)
    (hy2 : IsPGroup 2 (Subgroup.zpowers y)) (hys : y * Φ s = Φ s * y)
    (hP : ∀ u ∈ perpPair (unitaryInvolution F 2 f) a d,
      uForm (unitaryInvolution F 2 f) u u = 0 → ∀ t, suMat (unitaryInvolution F 2 f) n t =
        uTrans (unitaryInvolution F 2 f) u 1 → y * Φ t = Φ t * y) :
    y ∈ Subgroup.centralizer (Φ.range : Set K) := by
  obtain ⟨lam, hlam0, hlamnorm, hlam⟩ :=
    exists_scalar_of_semilinear_on_perpPair hF hn hL hφ hker haa hdd had hP
  obtain ⟨A', hL', hA'P⟩ :=
    exists_semilinearLift_fixes_perpPair hL hlam0 hlamnorm hlam
  have hAs := mul_comm_of_mem_lineSL hF hf hn hL' hφ hker haa hdd had hs hys hA'P
  obtain ⟨m₀, hodd, hpow⟩ :=
    exists_odd_pow_eq_one_of_commute hF hf hL' haa hdd had hs hord hA'P hAs
  exact mem_centralizer_range_of_pow_odd_eq_one hL' hφ hy2 hodd hpow

end ModelRank

end CFSG.Timmesfeld.Transvection
