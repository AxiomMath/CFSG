module

public import CFSG.RankThree.PartOne.SEITZU49.Circ
public import CFSG.RankThree.PartOne.SEITZU49.Stmt
public import CFSG.RankThree.PartOne.SEITZU49.Norm
public import CFSG.RankThree.PartOne.CTP.SeitzU5Span

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Root

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.CTP.U5Gen (dgSU mat hSU Cset Cset_smul comm_mem ne_zero_of_norm_one
  two_eq_zero tv_congr)
open CFSG.RankThree.PartOne.SEITZU49.Frame (shiftZ)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

local notation "σ" => unitaryInvolution K 2 f

theorem even_of_five_dvd (h5 : 5 ∣ 2 ^ f + 1) : Even f := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨g, rfl⟩ := hodd
  have h4g : ∀ g : ℕ, 4 ^ g % 5 = 1 ∨ 4 ^ g % 5 = 4 := by
    intro g
    induction g with
    | zero => left; norm_num
    | succ g ih => rw [pow_succ]; omega
  have e : 2 ^ (2 * g + 1) = 2 * 4 ^ g := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [e] at h5
  rcases h4g g with h | h <;> omega

theorem exists_omega (hK : Nat.card K = (2 ^ f) ^ 2) (hf : Even f) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 ∧ σ ω = ω := by
  classical
  obtain ⟨g, hg⟩ := hf
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [card_units_of_card hK]
    have : (2 ^ f) ^ 2 = 4 ^ f := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 f
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hω3 : (x : K) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    have := congrArg (fun u : Kˣ => (u : K)) this
    simpa using this
  have hω1 : (x : K) ≠ 1 := by
    intro h
    have : x = 1 := Units.ext h
    rw [this, orderOf_one] at hx
    omega
  refine ⟨(x : K), ?_, ?_⟩
  · have : ((x : K) - 1) * ((x : K) ^ 2 + (x : K) + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  · rw [unitaryInvolution_apply]
    have h4 : ∀ k : ℕ, (x : K) ^ (4 ^ k) = (x : K) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, pow_mul, ih]; linear_combination (x : K) * hω3
    have : 2 ^ f = 4 ^ g := by rw [hg, ← two_mul, pow_mul]; norm_num
    rw [this, h4]

theorem iterate_mem {M : Subgroup (SUid σ 5)} {g : Matrix (Fin 5) (Fin 5) K}
    {hg : conjTr σ g * g = 1} (hS : ∀ x ∈ M, Eich.conjU σ g hg x ∈ M) (k : ℕ) {x : SUid σ 5}
    (hx : x ∈ M) : (Eich.conjU σ g hg)^[k] x ∈ M := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (hS x hx)

theorem mat_iterate (g : Matrix (Fin 5) (Fin 5) K) (hg : conjTr σ g * g = 1) (k : ℕ)
    (x : SUid σ 5) :
    mat σ ((Eich.conjU σ g hg)^[k] x) = g ^ k * mat σ x * conjTr σ g ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, Eich.mat_conjU, pow_succ g k, pow_succ' (conjTr σ g) k]
    simp only [Matrix.mul_assoc]

theorem mat_inv (x : SUid σ 5) : mat σ x⁻¹ = conjTr σ (mat σ x) := by
  have h1 : conjTr σ (mat σ x) * mat σ x = 1 := x.2.2
  have h2 : mat σ x * mat σ x⁻¹ = 1 := by
    rw [← CFSG.RankThree.PartOne.CTP.U5Gen.mat_mul, mul_inv_cancel]
    rfl
  calc mat σ x⁻¹ = (conjTr σ (mat σ x) * mat σ x) * mat σ x⁻¹ := by rw [h1, Matrix.one_mul]
    _ = conjTr σ (mat σ x) * (mat σ x * mat σ x⁻¹) := by rw [Matrix.mul_assoc]
    _ = conjTr σ (mat σ x) := by rw [h2, Matrix.mul_one]

omit [Finite K] [CharP K 2] in
theorem det_shiftZ (z : K) : (shiftZ z).det = z := by
  rw [shiftZ, Matrix.det_mul, Matrix.det_diagonal]
  have : (CFSG.RankThree.PartOne.CTP.U5Eigen.shiftMat : Matrix (Fin 5) (Fin 5) K).det = 1 := by
    rw [CFSG.RankThree.PartOne.CTP.U5Eigen.shiftMat, Matrix.det_permutation, map_inv,
      sign_finRotate]
    norm_num
  rw [this, one_mul]
  simp [Fin.prod_univ_five]

theorem Gs_pow_mul_G_pow {z : K} (hz : σ z * z = 1) (k : ℕ) :
    conjTr σ (shiftZ z) ^ k * shiftZ z ^ k = 1 := by
  have hGsG : conjTr σ (shiftZ z) * shiftZ z = 1 := Circ.conjTr_shiftZ_mul σ z hz
  have hcomm : Commute (conjTr σ (shiftZ z)) (shiftZ z) :=
    hGsG.trans (Circ.shiftZ_mul_conjTr σ z hz).symm
  rw [← hcomm.mul_pow, hGsG, one_pow]

theorem G_pow_mul_Gs_pow {z : K} (hz : σ z * z = 1) (k : ℕ) :
    shiftZ z ^ k * conjTr σ (shiftZ z) ^ k = 1 := by
  have hGGs : shiftZ z * conjTr σ (shiftZ z) = 1 := Circ.shiftZ_mul_conjTr σ z hz
  have hcomm : Commute (shiftZ z) (conjTr σ (shiftZ z)) :=
    hGGs.trans (Circ.conjTr_shiftZ_mul σ z hz).symm
  rw [← hcomm.mul_pow, hGGs, one_pow]

theorem conjTr_Gs_pow (hσ : ∀ c, σ (σ c) = c) (z : K) (k : ℕ) :
    conjTr σ (conjTr σ (shiftZ z) ^ k) = shiftZ z ^ k := by
  rw [Circ.conjTr_pow', Circ.conjTr_conjTr' σ hσ]

theorem exists_u1 (hσ : ∀ c, σ (σ c) = c) {z : K} (hz : σ z * z = 1)
    {h1 : Matrix (Fin 5) (Fin 5) K} (hu : conjTr σ h1 * h1 = 1) {k : ℕ} {u : K}
    (hu1 : σ u * u = 1) (hdet : h1.det = z ^ k * u ^ 5) :
    ∃ U : SUid σ 5, mat σ U = u⁻¹ • (h1 * conjTr σ (shiftZ z) ^ k) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu1
  have huσ : σ u⁻¹ * u⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hu1, inv_one]
  have hGGs : shiftZ z * conjTr σ (shiftZ z) = 1 := Circ.shiftZ_mul_conjTr σ z hz
  set Um : Matrix (Fin 5) (Fin 5) K := u⁻¹ • (h1 * conjTr σ (shiftZ z) ^ k) with hUm
  have hunit : conjTr σ Um * Um = 1 := by
    have e1 : conjTr σ Um = σ u⁻¹ • (shiftZ z ^ k * conjTr σ h1) := by
      rw [hUm, Circ.conjTr_smul', conjTr_mul, conjTr_Gs_pow hσ]
    rw [e1, hUm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, huσ, one_smul]
    calc shiftZ z ^ k * conjTr σ h1 * (h1 * conjTr σ (shiftZ z) ^ k)
        = shiftZ z ^ k * (conjTr σ h1 * h1) * conjTr σ (shiftZ z) ^ k := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu, Matrix.mul_one, G_pow_mul_Gs_pow hz]
  have hdetU : Um.det = 1 := by
    rw [hUm, Matrix.det_smul, Matrix.det_mul, Matrix.det_pow, Fintype.card_fin, hdet]
    have hGs : (conjTr σ (shiftZ z)).det = σ z := by
      rw [Eich.det_conjTr, det_shiftZ]
    rw [hGs]
    have : (u⁻¹) ^ 5 * (z ^ k * u ^ 5 * σ z ^ k) = (σ z * z) ^ k * (u⁻¹ * u) ^ 5 := by
      rw [mul_pow, mul_pow]; ring
    rw [this, hz, inv_mul_cancel₀ hu0]
    simp
  exact ⟨mkSU σ Um hdetU (Eich.isom_of_conjTr σ hunit), rfl⟩

theorem exists_H (hK : Nat.card K = (2 ^ f) ^ 2) (hf6 : 6 ≤ f) (h5 : 5 ∣ 2 ^ f + 1)
    {z : K} (hz : σ z * z = 1) (hnz : ¬ ∃ u : K, σ u * u = 1 ∧ u ^ 5 = z)
    {M : Subgroup (SUid σ 5)} (hM : GenHyp σ z hz M) :
    ∃ (ω : K) (H : SUid σ 5) (lam κ : K), ω ^ 2 + ω + 1 = 0 ∧ σ ω = ω ∧ H ∈ M ∧
      σ lam * lam = 1 ∧ κ ≠ 0 ∧
      H • (![1, 0, 0, 0, 0] : Fin 5 → K) = lam • (![1, 0, 0, 0, 0] + κ • ![0, ω, ω, 1, 1]) := by
  classical
  have h2 : (2 : K) = 0 := CFSG.RankThree.PartOne.CTP.U5Gen.two_eq_zero
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  obtain ⟨ω, hω, hσω⟩ := exists_omega hK (even_of_five_dvd h5)
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hDne : 1 + ω ^ 2 * σ z ≠ 0 := by
    intro h
    have h1 : σ z = ω := by linear_combination ω * h - σ z * hω3 - ω * h2
    have hz' : z = ω := by rw [← hσ z, h1, hσω]
    rw [h1, hz'] at hz
    have hω0 : ω = 0 := by linear_combination hω - hz - h2
    rw [hω0] at hω3
    norm_num at hω3
  obtain ⟨h1, c0, κ', hu, hcomm1, hu3, hc0, hc0ne, hκ'ne⟩ := Circ.exists_h1 h2 hσ hz hω hσω hDne
  obtain ⟨γ, hγ, hord, hgen⟩ := Norm.exists_generator hK
  have hdetn : σ h1.det * h1.det = 1 := Eich.norm_det_of_conjTr σ hu
  obtain ⟨k, u, hu1, hdet⟩ := Norm.exists_decomp hγ hord hgen h5 hz hnz hdetn
  obtain ⟨U1, hU1⟩ := exists_u1 hσ hz hu hu1 hdet
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu1
  set G := shiftZ z with hG
  have hG' : conjTr σ G * G = 1 := Circ.conjTr_shiftZ_mul σ z hz
  have hGGs : G * conjTr σ G = 1 := Circ.shiftZ_mul_conjTr σ z hz
  have hU1M : U1 ∈ M := by
    apply hM.cent
    rw [hU1]
    have hc1 : Commute h1 G := hcomm1
    have hc2 : Commute (conjTr σ G ^ k) G :=
      (show Commute (conjTr σ G) G from hG'.trans hGGs.symm).pow_left k
    exact (((hc1.mul_left hc2).smul_left u⁻¹)).eq
  obtain ⟨ρ0, ⟨η, hη, rfl⟩, hρord⟩ := CFSG.RankThree.PartOne.CTP.U5Span.exists_mem_G5_orderOf hK h5
  have hη0 : η ≠ 0 := by
    rintro rfl
    simp at hη
  have hη5 : η ^ 5 ≠ 1 := by
    intro h
    rw [h, inv_one, orderOf_one] at hρord
    have : 64 ≤ 2 ^ f := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf6
    omega
  have hηn : ∀ n : ℕ, σ (η ^ n) * η ^ n = 1 := fun n => by
    rw [map_pow, ← mul_pow, hη, one_pow]
  have hηn' : σ ((η ^ 2)⁻¹) * (η ^ 2)⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hηn 2, inv_one]
  set t : Fin 5 → K := ![η ^ 3, (η ^ 2)⁻¹, (η ^ 2)⁻¹, η ^ 3, (η ^ 2)⁻¹] with ht
  have htn : ∀ i, σ (t i) * t i = 1 := by
    intro i
    fin_cases i
    · exact hηn 3
    · exact hηn'
    · exact hηn'
    · exact hηn 3
    · exact hηn'
  have htdet : ∏ i, t i = 1 := by
    simp only [ht, Fin.prod_univ_five]
    simp
    field_simp
  set d'' : SUid σ 5 := dgSU σ t htn htdet with hd''
  have hd''M : d'' ∈ M := hM.diag t htn htdet
  set d₃ : SUid σ 5 := (Eich.conjU σ G hG')^[k] d'' with hd₃
  have hd₃M : d₃ ∈ M := iterate_mem hM.stab k hd''M
  set H : SUid σ 5 := U1 * d₃ * U1⁻¹ with hH
  have hHM : H ∈ M := M.mul_mem (M.mul_mem hU1M hd₃M) (M.inv_mem hU1M)
  have hmatH : mat σ H = h1 * Matrix.diagonal t * conjTr σ h1 := by
    have e1 : mat σ H = mat σ U1 * mat σ d₃ * mat σ U1⁻¹ := rfl
    have e2 : mat σ d₃ = G ^ k * Matrix.diagonal t * conjTr σ G ^ k := by
      rw [hd₃, mat_iterate G hG' k d'']
      rfl
    have e3 : conjTr σ (u⁻¹ • (h1 * conjTr σ G ^ k)) = σ u⁻¹ • (G ^ k * conjTr σ h1) := by
      rw [Circ.conjTr_smul', conjTr_mul, conjTr_Gs_pow hσ]
    have huσ : σ u⁻¹ * u⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, hu1, inv_one]
    rw [e1, e2, mat_inv, hU1, e3]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have e4 : h1 * conjTr σ G ^ k * (G ^ k * Matrix.diagonal t * conjTr σ G ^ k) *
        (G ^ k * conjTr σ h1) = h1 * Matrix.diagonal t * conjTr σ h1 := by
      calc h1 * conjTr σ G ^ k * (G ^ k * Matrix.diagonal t * conjTr σ G ^ k) *
            (G ^ k * conjTr σ h1)
          = h1 * (conjTr σ G ^ k * G ^ k) * Matrix.diagonal t *
              (conjTr σ G ^ k * G ^ k) * conjTr σ h1 := by simp only [Matrix.mul_assoc]
        _ = h1 * Matrix.diagonal t * conjTr σ h1 := by
          rw [Gs_pow_mul_G_pow hz k, Matrix.mul_one, Matrix.mul_one]
    rw [e4, huσ, one_smul]
  set a : K := η ^ 5 + 1 with ha
  set lam : K := (η ^ 2)⁻¹ with hlam
  set Pm : Matrix (Fin 5) (Fin 5) K := Matrix.diagonal ![1, 0, 0, 1, 0] with hPm
  have hdiag : Matrix.diagonal t = lam • (1 + a • Pm) := by
    have e1 : lam • (1 + a • Pm) =
        Matrix.diagonal (fun i => lam * (1 + a * ![1, 0, 0, 1, 0] i)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hPm]
      · simp [hPm, hij]
    rw [e1]
    congr 1
    funext i
    have e0 : lam * (1 + a * 1) = η ^ 3 := by
      rw [hlam, ha]
      field_simp
      linear_combination h2
    fin_cases i
    · simpa [ht] using e0.symm
    · simp [ht, hlam]
    · simp [ht, hlam]
    · simpa [ht] using e0.symm
    · simp [ht, hlam]
  have hh1c : h1 * conjTr σ h1 = 1 := mul_eq_one_comm.mp hu
  have hQ : h1 * Matrix.diagonal t * conjTr σ h1 = lam • (1 + a • (h1 * Pm * conjTr σ h1)) := by
    rw [hdiag]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      hh1c]
  have hrow : conjTr σ h1 *ᵥ ![1, 0, 0, 0, 0] = fun j => σ (h1 0 j) := by
    ext j
    simp [conjTr, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  have hP : ∀ w : Fin 5 → K, Pm *ᵥ w = ![w 0, 0, 0, w 3, 0] := by
    intro w
    ext i
    fin_cases i <;> simp [hPm, Matrix.mulVec_diagonal]
  have hsum : h1 0 0 + h1 0 3 = 0 := by
    have := congrFun hu3 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_five] using this
  have h03 : h1 0 3 = h1 0 0 := by linear_combination hsum - (h1 0 0) * h2
  have hc00 : h1 0 0 = c0 := by
    rw [← hc0]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  have hvec : Pm *ᵥ (conjTr σ h1 *ᵥ ![1, 0, 0, 0, 0]) = σ c0 • ![1, 0, 0, 1, 0] := by
    rw [hP, hrow]
    ext i
    fin_cases i <;> simp [h03, hc00]
  have hHe0 : H • (![1, 0, 0, 0, 0] : Fin 5 → K) =
      lam • (![1, 0, 0, 0, 0] + (a * (σ c0 * κ')) • ![0, ω, ω, 1, 1]) := by
    show mat σ H *ᵥ _ = _
    rw [hmatH, hQ, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvec,
      Matrix.mulVec_smul, hu3, smul_smul, smul_smul, mul_assoc]
  refine ⟨ω, H, lam, a * (σ c0 * κ'), hω, hσω, hHM, ?_, ?_, hHe0⟩
  · rw [hlam]
    exact hηn'
  · have ha0 : a ≠ 0 := by
      intro h
      apply hη5
      linear_combination h - h2
    exact mul_ne_zero ha0 (mul_ne_zero ((map_ne_zero σ).mpr hc0ne) hκ'ne)

open CFSG.RankThree.PartOne.CTP.U5Span (G5 L5 L5_eq_top)

variable (K f) in
@[expose] def B1 : AddSubgroup K :=
  AddSubgroup.closure {x | ∃ ρ ∈ G5 K f, ∃ ρ' ∈ G5 K f,
    x = σ (ρ + 1) * (ρ' + 1) + σ (ρ' + 1) * (ρ + 1)}

theorem mem_B1_of_fixed (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 6 ≤ f) (h5 : 5 ∣ 2 ^ f + 1)
    {b : K} (hb : σ b = b) : b ∈ B1 K f := by
  have hL := L5_eq_top hK hf h5
  have key : ∀ u v : K, σ u * v + σ v * u ∈ B1 K f := by
    intro u v
    have hu : u ∈ L5 K f := by rw [hL]; trivial
    have hv : v ∈ L5 K f := by rw [hL]; trivial
    induction hu using AddSubgroup.closure_induction with
    | mem x hx =>
      induction hv using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨ρ, hρ, rfl⟩ := hx
        obtain ⟨ρ', hρ', rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨ρ, hρ, ρ', hρ', rfl⟩
      | zero => simp
      | add y y' _ _ hy hy' =>
        have : σ x * (y + y') + σ (y + y') * x = (σ x * y + σ y * x) + (σ x * y' + σ y' * x) := by
          rw [map_add]; ring
        rw [this]
        exact add_mem hy hy'
      | neg y _ hy =>
        have : σ x * (-y) + σ (-y) * x = -(σ x * y + σ y * x) := by rw [map_neg]; ring
        rw [this]
        exact neg_mem hy
    | zero => simp
    | add x x' _ _ hx hx' =>
      have : σ (x + x') * v + σ v * (x + x') = (σ x * v + σ v * x) + (σ x' * v + σ v * x') := by
        rw [map_add]; ring
      rw [this]
      exact add_mem hx hx'
    | neg x _ hx =>
      have : σ (-x) * v + σ v * (-x) = -(σ x * v + σ v * x) := by rw [map_neg]; ring
      rw [this]
      exact neg_mem hx
  have hσi := isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK
  obtain ⟨c, hc⟩ := hσi.trace_surj b hb
  have := key 1 c
  rw [map_one, one_mul, mul_one] at this
  rw [← hc]
  exact this

section Vec

omit [Finite K] [CharP K 2]

variable (τ : K ≃+* K)

theorem herm_e0_e0 : herm τ (![1, 0, 0, 0, 0] : Fin 5 → K) ![1, 0, 0, 0, 0] = 1 := by
  simp [herm, Fin.sum_univ_five]

theorem herm_e0_Y (ω κ : K) :
    herm τ (![1, 0, 0, 0, 0] : Fin 5 → K) (κ • ![0, ω, ω, 1, 1]) = 0 := by
  simp [herm, Fin.sum_univ_five]

theorem herm_Y_e0 (ω κ : K) :
    herm τ (κ • ![0, ω, ω, 1, 1] : Fin 5 → K) ![1, 0, 0, 0, 0] = 0 := by
  simp [herm, Fin.sum_univ_five]

theorem herm_Y_Y (h2 : (2 : K) = 0) (ω κ : K) :
    herm τ (κ • ![0, ω, ω, 1, 1] : Fin 5 → K) (κ • ![0, ω, ω, 1, 1]) = 0 := by
  simp [herm, Fin.sum_univ_five]
  linear_combination (τ κ * τ ω * (κ * ω) + τ κ * κ) * h2

theorem herm_e0_left (v : Fin 5 → K) : herm τ (![1, 0, 0, 0, 0] : Fin 5 → K) v = v 0 := by
  simp [herm, Fin.sum_univ_five]

theorem hSU_smul (h2 : (2 : K) = 0) {γ : K} (hγ : τ γ * γ = 1) (v : Fin 5 → K) :
    hSU τ γ hγ • v =
      γ • (v + (((γ ^ 5)⁻¹ + 1) * herm τ (![1, 0, 0, 0, 0] : Fin 5 → K) v) •
        (![1, 0, 0, 0, 0] : Fin 5 → K)) := by
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    simp at hγ
  show Matrix.diagonal ![(γ ^ 4)⁻¹, γ, γ, γ, γ] *ᵥ v = _
  rw [herm_e0_left]
  ext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i
  · simp [Matrix.vecHead, Matrix.vecTail]
    field_simp
    linear_combination (-(γ ^ 5 * v 0)) * h2
  all_goals simp [Matrix.vecHead, Matrix.vecTail]

end Vec

theorem trace_aux (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) = 0) (x y : K) :
    (σ x * y + σ y * x) + σ (σ x * y + σ y * x) = 0 := by
  rw [map_add, map_mul, map_mul, hσ, hσ]
  linear_combination (σ x * y + σ y * x) * h2

theorem Y_mem_Cset (hK : Nat.card K = (2 ^ f) ^ 2) (hf6 : 6 ≤ f) (h5 : 5 ∣ 2 ^ f + 1)
    {z : K} (hz : σ z * z = 1) (hnz : ¬ ∃ u : K, σ u * u = 1 ∧ u ^ 5 = z)
    {M : Subgroup (SUid σ 5)} (hM : GenHyp σ z hz M) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 ∧ σ ω = ω ∧
      (![0, ω, ω, 1, 1] : Fin 5 → K) ∈ Cset (unitaryInvolution_involutive hK) M := by
  classical
  have h2 : (2 : K) = 0 := two_eq_zero
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  obtain ⟨ω, H, lam, κ, hω, hσω, hHM, hlam, hκ, hHe0⟩ := exists_H hK hf6 h5 hz hnz hM
  refine ⟨ω, hω, hσω, ?_⟩
  have haa := herm_e0_e0 σ
  have hay := herm_e0_Y σ ω κ
  have hya := herm_Y_e0 σ ω κ
  have hyy := herm_Y_Y σ h2 ω κ
  have hE : ∀ (γ : K) (hγ : σ γ * γ = 1), ∃ E : SUid σ 5, E ∈ M ∧
      Eich.IsEich σ (![1, 0, 0, 0, 0] : Fin 5 → K) (κ • ![0, ω, ω, 1, 1])
        ((γ ^ 5)⁻¹ + 1) (σ ((γ ^ 5)⁻¹) + 1) E := by
    intro γ hγ
    have hγ0 : γ ≠ 0 := ne_zero_of_norm_one σ hγ
    have hδ : σ ((γ ^ 5)⁻¹) * (γ ^ 5)⁻¹ = 1 := by
      rw [map_inv₀, map_pow, ← mul_inv, ← mul_pow, hγ, one_pow, inv_one]
    exact ⟨_, comm_mem M (hM.diag _ _ _) hHM,
      Eich.eich_comm h2 haa hay H (hSU σ γ hγ) hlam hδ hγ0 hHe0 (hSU_smul σ h2 hγ)⟩
  have hcl : ∀ b ∈ B1 K f, ∃ hb : b + σ b = 0, tv hσ hyy hb ∈ M := by
    intro b hb
    induction hb using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨ρ, ⟨γ, hγ, rfl⟩, ρ', ⟨γ', hγ', rfl⟩, rfl⟩ := hx
      obtain ⟨E, hEM, hEe⟩ := hE γ hγ
      obtain ⟨E', hE'M, hE'e⟩ := hE γ' hγ'
      have hc := trace_aux hσ h2 ((γ ^ 5)⁻¹ + 1) ((γ' ^ 5)⁻¹ + 1)
      refine ⟨hc, ?_⟩
      rw [← Eich.eich_commutator h2 hσ haa hay hya hyy hEe hE'e hc]
      exact comm_mem M hEM hE'M
    | zero =>
      have h0 : (0 : K) + σ 0 = 0 := by simp
      exact ⟨h0, by rw [tv_zero hσ hyy h0]; exact M.one_mem⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨hcx, hmx⟩ := ihx
      obtain ⟨hcx', hmx'⟩ := ihx'
      have hcxx : (x + x') + σ (x + x') = 0 := by rw [map_add]; linear_combination hcx + hcx'
      exact ⟨hcxx, by rw [← tv_mul_tv hσ hyy hcx hcx' hcxx]; exact M.mul_mem hmx hmx'⟩
    | neg x _ ihx =>
      obtain ⟨hcx, hmx⟩ := ihx
      have e : -x = x := CharTwo.neg_eq x
      have hcn : -x + σ (-x) = 0 := by rw [e]; exact hcx
      exact ⟨hcn, by rw [tv_congr σ hσ hyy e hcn hcx]; exact hmx⟩
  have hy : (κ • ![0, ω, ω, 1, 1] : Fin 5 → K) ∈ Cset hσ M := by
    refine ⟨hyy, fun c hc => ?_⟩
    have hfix : σ c = c := by
      have : σ c = -c := by linear_combination hc
      rw [this]
      exact CharTwo.neg_eq c
    exact (hcl c (mem_B1_of_fixed hK hf6 h5 hfix)).2
  have := Cset_smul hσ M hy κ⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this

end CFSG.RankThree.PartOne.SEITZU49.Root
