module

public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRelOneAt
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxMod
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxMinkowski

public section

namespace CFSG.StandardType.RCKRP
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.SeitzGeneration CFSG.StandardType.ExcMaxToral CFSG.RankThree.E6
open scoped Matrix

theorem rckCL_finrank_ge_of_card {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) {lam : K} {k : ℕ}
    (hge : Nat.card K ^ k ≤ Nat.card {z : Fin n → K // M *ᵥ z = lam • z}) :
    k ≤ Module.finrank K (LinearMap.ker (M - lam • 1).mulVecLin) := by
  have hker : ∀ z : Fin n → K,
      (M *ᵥ z = lam • z) ↔ z ∈ LinearMap.ker (M - lam • 1).mulVecLin := by
    intro z
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
  have hcard : Nat.card {z : Fin n → K // M *ᵥ z = lam • z} =
      Nat.card (LinearMap.ker (M - lam • 1).mulVecLin) :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hpow : Nat.card (LinearMap.ker (M - lam • 1).mulVecLin) =
      Nat.card K ^ Module.finrank K (LinearMap.ker (M - lam • 1).mulVecLin) :=
    Module.natCard_eq_pow_finrank
  rw [hcard, hpow] at hge
  have hK : 1 < Nat.card K := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  exact (Nat.pow_le_pow_iff_right hK).mp hge

theorem rckCL_sub_smul_one_mul {K : Type*} [CommRing K] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (a b : K) :
    (N - a • 1) * (N - b • 1) = N * N - (a + b) • N + (a * b) • 1 := by
  simp only [sub_mul, mul_sub, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  module

theorem rckCL_quadratic_of_isometry {K : Type*} [Field K] [Fintype K]
    (B N N' : Matrix (Fin 8) (Fin 8) K) (hBdet : B.det ≠ 0)
    (hiso : Nᵀ * B * N = B) (hNN' : N * N' = 1) (hN'N : N' * N = 1)
    {lam : K} (hlam0 : lam ≠ 0) (hlam2 : lam * lam ≠ 1)
    (h4 : 4 ≤ Module.finrank K (LinearMap.ker (Nᵀ - lam • 1).mulVecLin)) :
    N * N - (lam + lam⁻¹) • N + 1 = 0 := by
  classical
  let β : LinearMap.BilinForm K (Fin 8 → K) := Matrix.toBilin' B
  have hβnd : β.Nondegenerate := by
    dsimp only [β]
    exact LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' B hBdet
  have hNB : Nᵀ * B = B * N' := by
    calc Nᵀ * B = Nᵀ * B * 1 := (mul_one _).symm
      _ = Nᵀ * B * (N * N') := by rw [hNN']
      _ = (Nᵀ * B * N) * N' := by noncomm_ring
      _ = B * N' := by rw [hiso]
  have hisot : ∀ x y, β (N *ᵥ x) (N *ᵥ y) = β x y := by
    intro x y
    dsimp only [β]
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
    rw [Matrix.mulVec_mulVec]
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
    rw [Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, hiso]
  have hsm1 : ∀ (a : K) (n x : Fin 8 → K), β (a • n) x = a * β n x := by
    intro a n x
    dsimp only [β]
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', smul_dotProduct, smul_eq_mul]
  have hsm : ∀ (a : K) (n x : Fin 8 → K), β (a • n) (a • x) = (a * a) * β n x := by
    intro a n x
    dsimp only [β]
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_smul, smul_eq_mul]
  have hne2 : lam⁻¹ * lam⁻¹ ≠ 1 := by
    intro h
    apply hlam2
    have h1 : lam * lam * (lam⁻¹ * lam⁻¹) = lam * lam * 1 := by rw [h]
    rw [show lam * lam * (lam⁻¹ * lam⁻¹) = (lam * lam⁻¹) * (lam * lam⁻¹) by ring,
      mul_inv_cancel₀ hlam0, one_mul, mul_one] at h1
    exact h1.symm
  set U' : Submodule K (Fin 8 → K) := LinearMap.ker (N - lam⁻¹ • 1).mulVecLin with hU'
  have hU'le : U' ≤ β.orthogonal U' := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have hx' : N *ᵥ x = lam⁻¹ • x := by
      have h := hx
      rw [hU', LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at h
      exact h
    have hn' : N *ᵥ n = lam⁻¹ • n := by
      have h := hn
      rw [hU', LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at h
      exact h
    have his := hisot n x
    rw [hn', hx', hsm] at his
    have hfac : (lam⁻¹ * lam⁻¹ - 1) * β n x = 0 := by
      rw [sub_mul, one_mul, his, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne2)
  have hB_inj : Function.Injective B.mulVecLin := by
    intro x y h
    have h0 : B.mulVecLin (x - y) = 0 := by rw [map_sub, h, sub_self]
    have h1 : B *ᵥ (x - y) = 0 := by rwa [Matrix.mulVecLin_apply] at h0
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hBdet h1)
  have hker_transpose : ∀ a : K, Module.finrank K (LinearMap.ker (Nᵀ - a • 1).mulVecLin) =
      Module.finrank K (LinearMap.ker (N - a • 1).mulVecLin) := by
    intro a
    have h1 := LinearMap.finrank_range_add_finrank_ker (N - a • 1).mulVecLin
    have h2 := LinearMap.finrank_range_add_finrank_ker (Nᵀ - a • 1).mulVecLin
    rw [Module.finrank_fin_fun K] at h1 h2
    have htrans : (Nᵀ - a • 1) = (N - a • 1)ᵀ := by
      rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    have hr : (Nᵀ - a • 1).rank = (N - a • 1).rank := by rw [htrans, Matrix.rank_transpose]
    simp only [Matrix.rank] at hr
    omega
  have hmap : ∀ (a : K) (ha : a ≠ 0) (x : Fin 8 → K),
      x ∈ LinearMap.ker (N - a • 1).mulVecLin →
      B *ᵥ x ∈ LinearMap.ker (Nᵀ - a⁻¹ • 1).mulVecLin := by
    intro a ha x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
    have hx' : x = a⁻¹ • (N *ᵥ x) := by rw [hx, smul_smul, inv_mul_cancel₀ ha, one_smul]
    have hN'x : N' *ᵥ x = a⁻¹ • x := by
      have h1 : N' *ᵥ (N *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, hN'N, Matrix.one_mulVec]
      calc N' *ᵥ x = N' *ᵥ (a⁻¹ • (N *ᵥ x)) := by conv_lhs => rw [hx']
        _ = a⁻¹ • (N' *ᵥ (N *ᵥ x)) := by rw [Matrix.mulVec_smul]
        _ = a⁻¹ • x := by rw [h1]
    calc Nᵀ *ᵥ (B *ᵥ x) = (Nᵀ * B) *ᵥ x := by rw [Matrix.mulVec_mulVec]
      _ = (B * N') *ᵥ x := by rw [hNB]
      _ = B *ᵥ (N' *ᵥ x) := by rw [Matrix.mulVec_mulVec]
      _ = B *ᵥ (a⁻¹ • x) := by rw [hN'x]
      _ = a⁻¹ • (B *ᵥ x) := by rw [Matrix.mulVec_smul]
  have hfinmap : ∀ a : K, Module.finrank K ((LinearMap.ker (N - a • 1).mulVecLin).map B.mulVecLin) =
      Module.finrank K (LinearMap.ker (N - a • 1).mulVecLin) := by
    intro a
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective B.mulVecLin hB_inj _)).symm
  have hfin_eq : Module.finrank K (LinearMap.ker (Nᵀ - lam • 1).mulVecLin) =
      Module.finrank K U' := by
    have hle1 : (LinearMap.ker (N - lam • 1).mulVecLin).map B.mulVecLin ≤
        LinearMap.ker (Nᵀ - lam⁻¹ • 1).mulVecLin := by
      rintro y ⟨x, hx, rfl⟩
      exact hmap lam hlam0 x hx
    have h1 : Module.finrank K (LinearMap.ker (N - lam • 1).mulVecLin) ≤
        Module.finrank K (LinearMap.ker (Nᵀ - lam⁻¹ • 1).mulVecLin) := by
      calc Module.finrank K (LinearMap.ker (N - lam • 1).mulVecLin)
          = Module.finrank K ((LinearMap.ker (N - lam • 1).mulVecLin).map B.mulVecLin) :=
            (hfinmap lam).symm
        _ ≤ Module.finrank K (LinearMap.ker (Nᵀ - lam⁻¹ • 1).mulVecLin) :=
            Submodule.finrank_mono hle1
    have hle2 : (LinearMap.ker (N - lam⁻¹ • 1).mulVecLin).map B.mulVecLin ≤
        LinearMap.ker (Nᵀ - lam • 1).mulVecLin := by
      rintro y ⟨x, hx, rfl⟩
      have h := hmap lam⁻¹ (inv_ne_zero hlam0) x hx
      rwa [inv_inv] at h
    have h2 : Module.finrank K (LinearMap.ker (N - lam⁻¹ • 1).mulVecLin) ≤
        Module.finrank K (LinearMap.ker (Nᵀ - lam • 1).mulVecLin) := by
      calc Module.finrank K (LinearMap.ker (N - lam⁻¹ • 1).mulVecLin)
          = Module.finrank K ((LinearMap.ker (N - lam⁻¹ • 1).mulVecLin).map B.mulVecLin) :=
            (hfinmap lam⁻¹).symm
        _ ≤ Module.finrank K (LinearMap.ker (Nᵀ - lam • 1).mulVecLin) :=
            Submodule.finrank_mono hle2
    rw [← hker_transpose lam⁻¹] at h2
    rw [hker_transpose lam] at h2
    rw [hU', hker_transpose lam, ← hker_transpose lam⁻¹]
    exact le_antisymm h1 h2
  have hfin_orth : Module.finrank K (β.orthogonal U') = 8 - Module.finrank K U' := by
    have := LinearMap.BilinForm.finrank_orthogonal hβnd U'
    rwa [Module.finrank_fin_fun] at this
  have hfinU' : Module.finrank K U' = 4 := by
    have hmono : Module.finrank K U' ≤ Module.finrank K (β.orthogonal U') :=
      Submodule.finrank_mono hU'le
    have h4' : 4 ≤ Module.finrank K U' := by rw [← hfin_eq]; exact h4
    omega
  have horth : β.orthogonal U' = U' := by
    refine (Submodule.eq_of_le_of_finrank_eq hU'le ?_).symm
    rw [hfin_orth, hfinU']
  have hquad : (N - lam⁻¹ • 1) * (N - lam • 1) = 0 := by
    have hcol : ∀ v : Fin 8 → K, (N - lam⁻¹ • 1) *ᵥ ((N - lam • 1) *ᵥ v) = 0 := by
      intro v
      have hw : (N - lam • 1) *ᵥ v ∈ U' := by
        rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
        intro u hu
        have hu' : N *ᵥ u = lam⁻¹ • u := by
          have h := hu
          rw [hU', LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
            Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
          exact h
        have h1 : β u (N *ᵥ v) = lam * β u v := by
          have his := hisot u v
          rw [hu', hsm1] at his
          have h2 := congrArg (fun z => lam * z) his
          rw [← mul_assoc, mul_inv_cancel₀ hlam0, one_mul] at h2
          exact h2
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, map_sub, map_smul]
        rw [h1, smul_eq_mul, sub_self]
      have hw' := hw
      rw [hU', LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at hw'
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hw', sub_self]
    ext i j
    have h := congrFun (hcol (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] at h
    exact h
  have hmain : N * N - (lam + lam⁻¹) • N + 1 = 0 := by
    have hsub := rckCL_sub_smul_one_mul N lam⁻¹ lam
    rw [hsub] at hquad
    rw [inv_mul_cancel₀ hlam0, one_smul, add_comm (lam⁻¹) lam] at hquad
    exact hquad
  exact hmain

theorem rckCL_exists_smul_of_dvd {n : ℕ} {d : ℤ} (hd : d ≠ 0)
    {Y : Matrix (Fin n) (Fin n) ℤ} (hY : ∀ i j, d ∣ Y i j) :
    ∃ Z : Matrix (Fin n) (Fin n) ℤ, Y = d • Z := by
  refine ⟨Matrix.of fun i j => Y i j / d, ?_⟩
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
  exact (Int.ediv_mul_cancel (hY i j)).symm

theorem rckCL_pow_dvd_of_mul_sq {p m n : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m)
    {Y A : Matrix (Fin n) (Fin n) ℤ} (hY : ∀ i j, (p : ℤ) ∣ Y i j)
    (h : (m : ℤ) • Y = A * Y * Y) :
    ∀ k : ℕ, ∀ i j, ((p : ℤ) ^ (k + 1)) ∣ Y i j := by
  have hpnz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro k
  induction k with
  | zero => intro i j; simpa using hY i j
  | succ k ih =>
    intro i j
    obtain ⟨Z, hZ⟩ := rckCL_exists_smul_of_dvd (d := (p:ℤ)^(k+1)) (pow_ne_zero _ hpnz) ih
    have h' : (m : ℤ) • Z = ((p:ℤ)^(k+1)) • (A * Z * Z) := by
      have hsub : (m : ℤ) • Y = A * Y * Y := h
      rw [hZ] at hsub
      simp only [smul_smul, Matrix.mul_smul, Matrix.smul_mul] at hsub
      rw [show (m : ℤ) * (p:ℤ)^(k+1) = ((p:ℤ)^(k+1)) * (m : ℤ) by ring,
        ← smul_smul, ← smul_smul] at hsub
      ext i j
      have hc : ((p:ℤ)^(k+1)) ≠ 0 := pow_ne_zero _ hpnz
      have hentry : ((p:ℤ)^(k+1)) * ((m : ℤ) * Z i j) =
          ((p:ℤ)^(k+1)) * (((p:ℤ)^(k+1)) * (A * Z * Z) i j) := by
        have h := congrFun (congrFun hsub i) j
        simpa only [Matrix.smul_apply, smul_eq_mul] using h
      have hcancel := mul_left_cancel₀ hc hentry
      simpa only [Matrix.smul_apply, smul_eq_mul] using hcancel
    rw [hZ, Matrix.smul_apply, smul_eq_mul]
    have hentry : (m : ℤ) * Z i j = ((p:ℤ)^(k+1)) * (A * Z * Z) i j := by
      have := congrFun (congrFun h' i) j
      simpa [Matrix.smul_apply, smul_eq_mul] using this
    have hpdvd : (p : ℤ) ∣ (m : ℤ) * Z i j := by
      rw [hentry]
      exact dvd_mul_of_dvd_left (by simpa using pow_dvd_pow (p:ℤ) (show 1 ≤ k + 1 by omega)) _
    have hmZ : ¬ (p : ℤ) ∣ (m : ℤ) := fun hh => hm (by exact_mod_cast hh)
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpZ : (p : ℤ) ∣ Z i j := (hpp.dvd_mul.mp hpdvd).resolve_left hmZ
    have hdvd := mul_dvd_mul_left ((p:ℤ)^(k+1)) hpZ
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    exact hdvd

theorem rckCL_eq_zero_of_forall_pow_dvd {p n : ℕ} (hp : p.Prime)
    {Y : Matrix (Fin n) (Fin n) ℤ} (h : ∀ k : ℕ, ∀ i j, (p:ℤ)^(k+1) ∣ Y i j) :
    Y = 0 := by
  ext i j
  by_contra hne
  have hne' : (Y i j).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hne
  have hdvd := h (Y i j).natAbs i j
  have hdvdN : p^((Y i j).natAbs + 1) ∣ (Y i j).natAbs := by
    have h1 : (((p:ℤ)^((Y i j).natAbs+1)).natAbs) ∣ (Y i j).natAbs :=
      Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at h1
  have hle : p^((Y i j).natAbs + 1) ≤ (Y i j).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hne') hdvdN
  have hlt : (Y i j).natAbs < p^((Y i j).natAbs + 1) := by
    calc (Y i j).natAbs < (Y i j).natAbs + 1 := Nat.lt_succ_self _
      _ < 2^((Y i j).natAbs + 1) := Nat.lt_two_pow_self
      _ ≤ p^((Y i j).natAbs + 1) := Nat.pow_le_pow_left hp.two_le _
  omega

theorem rckCL_descent {p d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : d = 3 ∨ d = 4 ∨ d = 6)
    {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ} (hMd : M ^ d = 1)
    (hcong : ∀ i j, (p : ℤ) ∣ (M * M - (rckChebC d) • M + 1) i j) :
    M * M - (rckChebC d) • M + 1 = 0 := by
  rcases hd with rfl | rfl | rfl
  · rw [show (rckChebC 3 : ℤ) = -1 by norm_num [rckChebC], neg_one_smul, sub_neg_eq_add]
      at hcong ⊢
    set Y : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := M * M + M + 1 with hYdef
    have hYdiv : ∀ i j, (p : ℤ) ∣ Y i j := by
      intro i j; rw [hYdef]; exact hcong i j
    have hRY : (M - 1) * Y = 0 := by
      have hpoly : (M - 1) * Y = M^3 - 1 := by rw [hYdef]; noncomm_ring
      rw [hpoly, hMd, sub_self]
    have hBez : (3 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) =
        1 * Y + (-(M + 2)) * (M - 1) := by
      rw [hYdef]
      noncomm_ring
      all_goals decide
    have hkey : (3:ℤ) • Y = (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) * Y * Y := by
      calc (3:ℤ) • Y = (3 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) * Y := by
            rw [show (3 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) =
              (3:ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) by
              exact (zsmul_one 3).symm, Matrix.smul_mul, Matrix.one_mul]
        _ = (1 * Y + (-(M + 2)) * (M - 1)) * Y := by rw [hBez]
        _ = 1 * Y * Y + (-(M + 2)) * ((M - 1) * Y) := by noncomm_ring
        _ = 1 * Y * Y := by rw [hRY, mul_zero, add_zero]
    have hm : ¬ p ∣ 3 := by
      intro hh; have := Nat.le_of_dvd (by norm_num) hh; omega
    exact rckCL_eq_zero_of_forall_pow_dvd hp (rckCL_pow_dvd_of_mul_sq hp hm hYdiv hkey)
  · rw [show (rckChebC 4 : ℤ) = 0 by norm_num [rckChebC], zero_smul, sub_zero] at hcong ⊢
    set Y : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := M * M + 1 with hYdef
    have hYdiv : ∀ i j, (p : ℤ) ∣ Y i j := by
      intro i j; rw [hYdef]; exact hcong i j
    have hMd4 : M ^ 4 = 1 := hMd
    have hRY : (M * M - 1) * Y = 0 := by
      have hpoly : (M * M - 1) * Y = M^4 - 1 := by rw [hYdef]; noncomm_ring
      rw [hpoly, hMd4, sub_self]
    have hBez : (2 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) =
        1 * Y + (-1) * (M * M - 1) := by
      rw [hYdef]
      noncomm_ring
      all_goals decide
    have hkey : (2:ℤ) • Y = (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) * Y * Y := by
      calc (2:ℤ) • Y = (2 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) * Y := by
            rw [show (2 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) =
              (2:ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) by
              exact (zsmul_one 2).symm, Matrix.smul_mul, Matrix.one_mul]
        _ = (1 * Y + (-1) * (M * M - 1)) * Y := by rw [hBez]
        _ = 1 * Y * Y + (-1) * ((M * M - 1) * Y) := by noncomm_ring
        _ = 1 * Y * Y := by rw [hRY, mul_zero, add_zero]
    have hm : ¬ p ∣ 2 := by
      intro hh; have := Nat.le_of_dvd (by norm_num) hh; omega
    exact rckCL_eq_zero_of_forall_pow_dvd hp (rckCL_pow_dvd_of_mul_sq hp hm hYdiv hkey)
  · rw [show (rckChebC 6 : ℤ) = 1 by norm_num [rckChebC], one_smul] at hcong ⊢
    set Y : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := M * M - M + 1 with hYdef
    have hYdiv : ∀ i j, (p : ℤ) ∣ Y i j := by
      intro i j; rw [hYdef]; exact hcong i j
    have hMd6 : M ^ 6 = 1 := hMd
    have hRY : (M^4 + M^3 - M - 1) * Y = 0 := by
      have hpoly : (M^4 + M^3 - M - 1) * Y = M^6 - 1 := by rw [hYdef]; noncomm_ring
      rw [hpoly, hMd6, sub_self]
    have hBez : (6 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) =
        (-(M^3 - 3 * M - 4)) * Y + (M - 2) * (M^4 + M^3 - M - 1) := by
      rw [hYdef]
      noncomm_ring
      all_goals decide
    have hkey : (6:ℤ) • Y =
        (-(M^3 - 3 * M - 4)) * Y * Y := by
      calc (6:ℤ) • Y = (6 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) * Y := by
            rw [show (6 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) =
              (6:ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) by
              exact (zsmul_one 6).symm, Matrix.smul_mul, Matrix.one_mul]
        _ = ((-(M^3 - 3 * M - 4)) * Y + (M - 2) * (M^4 + M^3 - M - 1)) * Y := by rw [hBez]
        _ = (-(M^3 - 3 * M - 4)) * Y * Y
              + (M - 2) * ((M^4 + M^3 - M - 1) * Y) := by noncomm_ring
        _ = (-(M^3 - 3 * M - 4)) * Y * Y := by rw [hRY, mul_zero, add_zero]
    have hm : ¬ p ∣ 6 := by
      intro hh
      have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hh
      interval_cases p
      · norm_num at hh
      · exact absurd hp (by norm_num)
    exact rckCL_eq_zero_of_forall_pow_dvd hp (rckCL_pow_dvd_of_mul_sq hp hm hYdiv hkey)


theorem rckCL_modMat_mul {τ : Tag} (p : ℕ) (A B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    modMat p (A * B) = modMat p A * modMat p B := by
  simp only [modMat, Matrix.map_mul]

theorem rckCL_modMat_one {τ : Tag} (p : ℕ) :
    modMat p (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) = 1 := by
  simpa [modMat] using Matrix.map_one (Int.castRingHom (ZMod p)) (by simp) (by simp)

theorem rckCL_modMat_add {τ : Tag} (p : ℕ) (A B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    modMat p (A + B) = modMat p A + modMat p B := by
  ext i j
  simp only [modMat, Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, map_add]

theorem rckCL_modMat_sub {τ : Tag} (p : ℕ) (A B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    modMat p (A - B) = modMat p A - modMat p B := by
  ext i j
  simp only [modMat, Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, map_sub]

theorem rckCL_modMat_smul {τ : Tag} (p : ℕ) (c : ℤ) (A : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    modMat p (c • A) = (c : ZMod p) • modMat p A := by
  ext i j
  simp only [modMat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rfl

theorem rckCL_modMat_pow {τ : Tag} (p n : ℕ) (A : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    modMat p (A ^ n) = (modMat p A) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact rckCL_modMat_one p
  | succ n ih => rw [pow_succ, rckCL_modMat_mul, ih, pow_succ]

theorem rckCL_modMat_quadratic {τ : Tag} (p : ℕ)
    (A : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (c : ℤ) :
    modMat p (A * A - c • A + 1) =
      modMat p A * modMat p A - (c : ZMod p) • modMat p A + 1 := by
  rw [rckCL_modMat_add, rckCL_modMat_sub, rckCL_modMat_mul, rckCL_modMat_smul, rckCL_modMat_one]

theorem rckCL_lam_facts {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : d = 3 ∨ d = 4 ∨ d = 6) {lam : ZMod p} (hlam : orderOf lam = d) :
    lam ≠ 0 ∧ lam * lam ≠ 1 ∧ lam + lam⁻¹ = (rckChebC d : ZMod p) ∧ 5 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : lam ^ d = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : d ≠ 0)] at hpow
    exact zero_ne_one hpow
  have hlam2 : lam * lam ≠ 1 := by
    intro h2
    have hdvd2 : d ∣ 2 := by
      rw [← hlam]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
    rcases hd with rfl | rfl | rfl <;> norm_num at hdvd2
  have hpdvd : d ∣ p - 1 := by
    rw [← hlam]
    exact orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one hlam0)
  have hp5 : 5 ≤ p := by
    rcases hd with rfl | rfl | rfl
    · have h3 : 3 ∣ p - 1 := hpdvd
      have h2le := hp.two_le
      by_contra hcon
      have hp4 : p ≤ 4 := by omega
      interval_cases p
      · exact hp2 rfl
      · norm_num at h3
      · exact absurd hp (by norm_num)
    · have h4 : 4 ∣ p - 1 := hpdvd
      have h2le := hp.two_le
      by_contra hcon
      have hp4 : p ≤ 4 := by omega
      interval_cases p
      · exact hp2 rfl
      · norm_num at h4
      · exact absurd hp (by norm_num)
    · have h6 : 6 ∣ p - 1 := hpdvd
      have h2le := hp.two_le
      by_contra hcon
      have hp4 : p ≤ 4 := by omega
      interval_cases p
      · exact hp2 rfl
      · norm_num at h6
      · exact absurd hp (by norm_num)
  have hPhi : lam * lam - (rckChebC d : ZMod p) * lam + 1 = 0 := by
    rcases hd with rfl | rfl | rfl
    · have h3 : lam ^ 3 = 1 := hpow
      have hl1 : lam - 1 ≠ 0 := by
        intro h
        have hlam1 : lam = 1 := sub_eq_zero.mp h
        rw [hlam1, orderOf_one] at hlam
        norm_num at hlam
      have hfac : (lam - 1) * (lam * lam + lam + 1) = 0 := by
        have hpoly : (lam - 1) * (lam * lam + lam + 1) = lam ^ 3 - 1 := by ring
        rw [hpoly, h3, sub_self]
      have h0 := (mul_eq_zero.mp hfac).resolve_left hl1
      rw [show (rckChebC 3 : ZMod p) = -1 by norm_num [rckChebC]]
      simpa only [neg_mul, one_mul, sub_neg_eq_add] using h0
    · have h4 : lam ^ 4 = 1 := hpow
      have hl : lam * lam - 1 ≠ 0 := sub_ne_zero.mpr hlam2
      have hfac : (lam * lam - 1) * (lam * lam + 1) = 0 := by
        have hpoly : (lam * lam - 1) * (lam * lam + 1) = lam ^ 4 - 1 := by ring
        rw [hpoly, h4, sub_self]
      have h0 := (mul_eq_zero.mp hfac).resolve_left hl
      rw [show (rckChebC 4 : ZMod p) = 0 by norm_num [rckChebC]]
      simpa only [zero_mul, sub_zero] using h0
    · have h6 : lam ^ 6 = 1 := hpow
      have hl3 : lam ^ 3 - 1 ≠ 0 := by
        intro h
        have h3eq : lam ^ 3 = 1 := sub_eq_zero.mp h
        have hdvd3 : (6 : ℕ) ∣ 3 := by
          rw [← hlam]; exact orderOf_dvd_iff_pow_eq_one.mpr h3eq
        norm_num at hdvd3
      have hfac1 : (lam ^ 3 - 1) * (lam ^ 3 + 1) = 0 := by
        have hpoly : (lam ^ 3 - 1) * (lam ^ 3 + 1) = lam ^ 6 - 1 := by ring
        rw [hpoly, h6, sub_self]
      have hl3p : lam ^ 3 + 1 = 0 := (mul_eq_zero.mp hfac1).resolve_left hl3
      have hl1 : lam + 1 ≠ 0 := by
        intro h
        have hle : lam = -1 := eq_neg_of_add_eq_zero_left h
        apply hlam2
        rw [hle]; ring
      have hfac2 : (lam + 1) * (lam * lam - lam + 1) = 0 := by
        have hpoly : (lam + 1) * (lam * lam - lam + 1) = lam ^ 3 + 1 := by ring
        rw [hpoly, hl3p]
      have h0 := (mul_eq_zero.mp hfac2).resolve_left hl1
      rw [show (rckChebC 6 : ZMod p) = 1 by norm_num [rckChebC]]
      simpa only [one_mul] using h0
  have hsum : lam + lam⁻¹ = (rckChebC d : ZMod p) := by
    have hPhi' : lam * lam + 1 = (rckChebC d : ZMod p) * lam := by
      linear_combination hPhi
    apply mul_right_cancel₀ hlam0
    rw [add_mul, inv_mul_cancel₀ hlam0, hPhi']
  exact ⟨hlam0, hlam2, hsum, hp5⟩

end CFSG.StandardType.RCKRP
