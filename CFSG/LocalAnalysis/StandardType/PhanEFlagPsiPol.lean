module

public import CFSG.LocalAnalysis.StandardType.PhanELocalFlag
public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma
public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ}

private def q2cFS_blockDot (n lo hi : ℕ) : LinearMap.BilinForm K (Fin n → K) :=
  LinearMap.mk₂ K
    (fun x y => ∑ i ∈ Finset.univ.filter (fun i : Fin n => lo ≤ i.val ∧ i.val < hi), x i * y i)
    (fun x y z => by
      simp only [Pi.add_apply]
      rw [Finset.sum_congr rfl (fun i _ => add_mul (x i) (y i) (z i)), Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun i _ => mul_assoc c (x i) (y i)), Finset.mul_sum])
    (fun x y z => by
      simp only [Pi.add_apply]
      rw [Finset.sum_congr rfl (fun i _ => mul_add (x i) (y i) (z i)), Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun i _ => mul_left_comm (x i) c (y i)), Finset.mul_sum])

private theorem q2cFS_blockDot_apply {lo hi : ℕ} (x y : Fin n → K) :
    q2cFS_blockDot n lo hi x y =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => lo ≤ i.val ∧ i.val < hi), x i * y i :=
  rfl

private theorem q2cFS_hermLin_apply (lo hi : ℕ) (u v : Fin n → K) :
    hermLin K f n lo hi u v =
      ∑ i : Fin n, if lo ≤ i.val ∧ i.val < hi then sg K f (u i) * v i else 0 := by
  rw [hermLin, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by by_cases h : lo ≤ i.val ∧ i.val < hi <;> simp [h]

private theorem q2cFS_hermLin_eq_blockDot (lo hi : ℕ) (u v : Fin n → K) :
    hermLin K f n lo hi u v = q2cFS_blockDot n lo hi (sgv K f n u) v := by
  rw [q2cFS_blockDot_apply, q2cFS_hermLin_apply, Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => by rw [sgv_apply]

private theorem q2cFS_hermLin_symm (hK : Nat.card K = (2 ^ f) ^ 2) (lo hi : ℕ) (u v : Fin n → K) :
    hermLin K f n lo hi v u = sg K f (hermLin K f n lo hi u v) := by
  rw [q2cFS_hermLin_apply, q2cFS_hermLin_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : lo ≤ i.val ∧ i.val < hi
    · rw [if_pos h, if_pos h, map_mul, sg_sg hK]; exact mul_comm _ _
    · rw [if_neg h, if_neg h, map_zero]

private theorem q2cFS_mem_blockDot_ker {lo hi : ℕ} {x : Fin n → K} :
    x ∈ LinearMap.ker (q2cFS_blockDot n lo hi) ↔
      ∀ i : Fin n, lo ≤ i.val → i.val < hi → x i = 0 := by
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  constructor
  · intro h i hlo hhi
    have h1 := h (Pi.single i (1 : K) : Fin n → K)
    rw [q2cFS_blockDot_apply,
      Finset.sum_eq_single_of_mem i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlo, hhi⟩)] at h1
    · simpa using h1
    · intro j _ hji; rw [Pi.single_eq_of_ne hji, mul_zero]
  · intro h y
    rw [q2cFS_blockDot_apply]
    exact Finset.sum_eq_zero fun j hj => by
      rw [Finset.mem_filter] at hj; rw [h j hj.2.1 hj.2.2, zero_mul]

private theorem q2cFS_perpB_eq_orthogonal (hK : Nat.card K = (2 ^ f) ^ 2) (lo hi : ℕ)
    (U : Submodule K (Fin n → K)) :
    perpB K f n lo hi U = (q2cFS_blockDot n lo hi).orthogonal (sgS K f n U) := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h w hw
    have hw' : sgv K f n w ∈ U := (mem_sgS (U := U)).mp hw
    have hh := h (sgv K f n w) hw'
    rwa [q2cFS_hermLin_eq_blockDot, sgv_sgv hK] at hh
  · intro h u hu
    have hu' : sgv K f n u ∈ sgS K f n U := by rw [mem_sgS, sgv_sgv hK]; exact hu
    have hh := h (sgv K f n u) hu'
    rwa [← q2cFS_hermLin_eq_blockDot] at hh

theorem q2cFS_le_perpB_of_Vsub {lo hi : ℕ} (U : Submodule K (Fin n → K)) :
    Vsub n lo ≤ perpB K f n lo hi U := by
  intro v hv
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u _
  rw [q2cFS_hermLin_apply]
  exact Finset.sum_eq_zero fun i _ => by
    by_cases h : lo ≤ i.val ∧ i.val < hi
    · simp [h, hv i h.1]
    · simp [h]

theorem q2cFS_perpB_Vsub_lo_eq_top {lo hi : ℕ} :
    perpB K f n lo hi (Vsub n lo) = ⊤ := by
  rw [eq_top_iff]; intro v _
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u hu
  rw [q2cFS_hermLin_apply]
  exact Finset.sum_eq_zero fun i _ => by
    by_cases h : lo ≤ i.val ∧ i.val < hi
    · simp [h, hu i h.1]
    · simp [h]

theorem q2cFS_perpB_antitone {lo hi : ℕ} {U U' : Submodule K (Fin n → K)} (h : U ≤ U') :
    perpB K f n lo hi U' ≤ perpB K f n lo hi U := by
  intro v hv; simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
  exact fun u hu => hv u (h hu)

private theorem q2cFS_hermLin_single {lo hi : ℕ} {j : Fin n} (hlj : lo ≤ j.val)
    (hjh : j.val < hi) (v : Fin n → K) :
    hermLin K f n lo hi (Pi.single j (1 : K)) v = v j := by
  rw [q2cFS_hermLin_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp [hlj, hjh]
  · intro i _ hij
    by_cases h : lo ≤ i.val ∧ i.val < hi
    · rw [if_pos h, Pi.single_eq_of_ne' hij.symm]; simp
    · simp [h]

theorem q2cFS_perpB_Vsub_inf {lo hi : ℕ} (hlh : lo ≤ hi) :
    Vsub n hi ⊓ perpB K f n lo hi (Vsub n hi) = Vsub n lo := by
  refine le_antisymm ?_ ?_
  · intro v hv; rw [Submodule.mem_inf] at hv
    obtain ⟨hvh, hperp⟩ := hv
    simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker] at hperp
    intro j hj; by_cases hjh : j.val < hi
    · have hmem : (Pi.single j (1 : K) : Fin n → K) ∈ Vsub n hi := by
        intro k hk; rw [Pi.single_eq_of_ne (show k ≠ j by rintro rfl; omega)]
      have h := hperp (Pi.single j (1 : K)) hmem
      rw [q2cFS_hermLin_single hj hjh v] at h
      exact h
    · exact hvh j (le_of_not_gt hjh)
  · intro v hv; rw [Submodule.mem_inf]
    exact ⟨Vsub_mono hlh hv, q2cFS_le_perpB_of_Vsub _ hv⟩

private theorem q2cFS_perpB_sup_Vsub {lo hi : ℕ} (U : Submodule K (Fin n → K)) :
    perpB K f n lo hi U ⊔ Vsub n hi = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hw : (fun i : Fin n => if i.val < hi then v i else 0) ∈ Vsub n hi := by
    intro j hj; exact if_neg (not_lt.mpr hj)
  have hv : v - (fun i : Fin n => if i.val < hi then v i else 0) ∈ perpB K f n lo hi U := by
    simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]
    intro u _
    rw [q2cFS_hermLin_apply]
    exact Finset.sum_eq_zero fun i _ => by
      by_cases h : lo ≤ i.val ∧ i.val < hi
      · rw [if_pos h, Pi.sub_apply, if_pos h.2, sub_self, mul_zero]
      · rw [if_neg h]
  exact Submodule.mem_sup.mpr ⟨_, hv, _, hw, sub_add_cancel v _⟩

private theorem q2cFS_sgS_inf_ker_blockDot {lo hi : ℕ} {U : Submodule K (Fin n → K)}
    (hlo : Vsub n lo ≤ U) (hhi : U ≤ Vsub n hi) :
    sgS K f n U ⊓ LinearMap.ker (q2cFS_blockDot n lo hi) = Vsub n lo := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvsg, hvker⟩ := hv
    rw [q2cFS_mem_blockDot_ker] at hvker
    have hvsghi : v ∈ Vsub n hi := by
      have h := sgS_mono hhi hvsg; rwa [sgS_Vsub] at h
    intro i hi'; by_cases hih : i.val < hi
    · exact hvker i hi' hih
    · exact hvsghi i (le_of_not_gt hih)
  · intro v hv; rw [Submodule.mem_inf]
    exact ⟨sgS_mono hlo (by rw [sgS_Vsub]; exact hv),
      (q2cFS_mem_blockDot_ker).mpr fun i hi' _ => hv i hi'⟩

private theorem q2cFS_finrank_perpB (hK : Nat.card K = (2 ^ f) ^ 2) {lo hi : ℕ} (hlo_n : lo ≤ n)
    {U : Submodule K (Fin n → K)} (hlo : Vsub n lo ≤ U) (hhi : U ≤ Vsub n hi) :
    finrank K (perpB K f n lo hi U) = n + lo - finrank K U := by
  have hspec := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := q2cFS_blockDot n lo hi) (W := sgS K f n U)
  rw [Module.finrank_fin_fun, ← q2cFS_perpB_eq_orthogonal (hK := hK) lo hi U,
    finrank_sgS hK U, q2cFS_sgS_inf_ker_blockDot hlo hhi, finrank_Vsub hlo_n] at hspec
  have hUle : finrank K U ≤ n := by simpa using Submodule.finrank_le U
  omega

theorem q2cFS_finrank_perpB_inf_Vsub (hK : Nat.card K = (2 ^ f) ^ 2) {lo hi : ℕ}
    (hlh : lo ≤ hi) (hhi_n : hi ≤ n) {U : Submodule K (Fin n → K)} (hlo : Vsub n lo ≤ U)
    (hhi : U ≤ Vsub n hi) :
    finrank K (perpB K f n lo hi U ⊓ Vsub n hi : Submodule K (Fin n → K)) =
      lo + hi - finrank K U := by
  have h1 := q2cFS_finrank_perpB (hK := hK) (lo := lo) (hi := hi) (le_trans hlh hhi_n) hlo hhi
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (perpB K f n lo hi U) (Vsub n hi)
  rw [q2cFS_perpB_sup_Vsub, finrank_top, Module.finrank_fin_fun, finrank_Vsub hhi_n] at h2
  have hUle : finrank K U ≤ hi := by
    calc finrank K U ≤ finrank K (Vsub n hi) := Submodule.finrank_mono hhi
      _ = hi := finrank_Vsub hhi_n
  omega

theorem q2cFS_perpB_inf_Vsub_inf_perpB (hK : Nat.card K = (2 ^ f) ^ 2) {lo hi : ℕ}
    (hlh : lo ≤ hi) (hhi_n : hi ≤ n) {U : Submodule K (Fin n → K)} (hlo : Vsub n lo ≤ U)
    (hhi : U ≤ Vsub n hi) :
    perpB K f n lo hi (perpB K f n lo hi U ⊓ Vsub n hi) ⊓ Vsub n hi = U := by
  have hPlo : Vsub n lo ≤ perpB K f n lo hi U ⊓ Vsub n hi :=
    le_inf (q2cFS_le_perpB_of_Vsub _) (le_trans hlo hhi)
  have hPhi : perpB K f n lo hi U ⊓ Vsub n hi ≤ Vsub n hi := inf_le_right
  have hUP : U ≤ perpB K f n lo hi (perpB K f n lo hi U ⊓ Vsub n hi) ⊓ Vsub n hi := by
    refine le_inf ?_ hhi; intro u hu
    simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]
    intro w hw
    have hwU : w ∈ perpB K f n lo hi U := hw.1
    simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker] at hwU
    rw [q2cFS_hermLin_symm (hK := hK) (lo := lo) (hi := hi), hwU u hu, map_zero]
  have hdimP := q2cFS_finrank_perpB_inf_Vsub (hK := hK) (lo := lo) (hi := hi) hlh hhi_n hlo hhi
  have hdimQ := q2cFS_finrank_perpB_inf_Vsub (hK := hK) (lo := lo) (hi := hi) hlh hhi_n hPlo hPhi
  have hfin : finrank K U =
      finrank K (perpB K f n lo hi (perpB K f n lo hi U ⊓ Vsub n hi) ⊓ Vsub n hi :
        Submodule K (Fin n → K)) := by
    have hUle : finrank K U ≤ lo + hi := by
      calc finrank K U ≤ finrank K (Vsub n hi) := Submodule.finrank_mono hhi
        _ = hi := finrank_Vsub hhi_n
        _ ≤ lo + hi := Nat.le_add_left _ _
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hUP hfin).symm

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
