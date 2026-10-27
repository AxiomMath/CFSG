module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofFix
public import CFSG.LieType.SeitzGeneration.OuterCoreProof
public import CFSG.LieType.SeitzGeneration.OuterSmallCases
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofNorm
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofLinear
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldFour

public section

namespace CFSG.RankThree.PartTwo.Sec14

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC hS heisD)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

namespace L3PGLU

variable {K : Type} [Field K]

section Matrices

variable {τ : K} (hτ : τ ^ 3 = 1) (β : K)

theorem heisC_mul_diagTau_pow_three :
    (heisC β * ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 3 =
      β • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [coe_diagTau, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination β * hτ

theorem heisC_mul_diagTau_sq_pow_three :
    (heisC β * ((diagTau hτ ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 3 =
      β • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [Units.val_pow_eq_pow_val, coe_diagTau, pow_three, sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (β * τ ^ 3 + β) * hτ

theorem diagTau_mul_heisC_mul_pow (n : ℕ) :
    ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (heisC β * ((diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      τ • ((heisC β * ((diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [← Matrix.mul_assoc, L3PGL.diagTau_mul_heisC hτ β, Matrix.smul_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul, ← pow_succ', ← pow_succ]

theorem heisC_mul_heisC_mul_pow (n : ℕ) :
    heisC β * (heisC β * ((diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      (τ ^ 2) ^ n • ((heisC β * ((diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        heisC β) := by
  have h' : heisC β * ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ n =
      (τ ^ 2) ^ n • (((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ n * heisC β) := by
    have hd := pow_mul_eq_smul (L3PGL.diagTau_mul_heisC hτ β) n
    have hτ2 : τ ^ n * (τ ^ 2) ^ n = 1 := by
      rw [← pow_mul, ← pow_add, pow_eq_pow_of_mod hτ (show (n + 2 * n) % 3 = 0 % 3 by omega),
        pow_zero]
    rw [hd, smul_smul, mul_comm, hτ2, one_smul]
  rw [Units.val_pow_eq_pow_val, Matrix.mul_assoc, h', Matrix.mul_smul]

theorem heisD_eq_smul :
    heisD τ = τ ^ 2 • ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [coe_diagTau_eq_diagonal, heisD, Matrix.smul_eq_diagonal_mul, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp <;>
    first | ring1 | linear_combination (-1 : K) * hτ | linear_combination (-τ) * hτ

theorem heisC_mul_diag_inv {β : K} (hβ : β ≠ 0) :
    heisC β * diagonal ![1, 1, β⁻¹] = hS := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisC, hS, Matrix.mul_apply, Fin.sum_univ_three, hβ]

end Matrices

theorem conj_eq_scalar_mul {A L : GL (Fin 3) K} {s : Kˣ}
    (h : (A : Matrix (Fin 3) (Fin 3) K) * L = (s : K) • ((L : Matrix (Fin 3) (Fin 3) K) * A)) :
    A * L * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) s * L := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, h,
    Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
    Matrix.smul_mul]

theorem conj_diagUnits_heisC {β : K} {cβ : GL (Fin 3) K}
    (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) (a b c : Kˣ) :
    cβ * diagUnits a b c * cβ⁻¹ = diagUnits c a b := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagUnits, coe_diagUnits, hcβm, heisC_mul_diagonal]

theorem diagUnits_pow (a b c : Kˣ) (n : ℕ) :
    diagUnits a b c ^ n = diagUnits (a ^ n) (b ^ n) (c ^ n) := by
  induction n with
  | zero =>
    apply Units.ext
    rw [pow_zero, pow_zero, pow_zero, pow_zero, Units.val_one, coe_diagUnits, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl
  | succ n ih => rw [pow_succ, ih, diagUnits_mul, pow_succ, pow_succ, pow_succ]

theorem three_mul_mU {q : ℕ} (hq : q % 3 = 2) (h9 : q % 9 ≠ 8) : q + 1 = 3 * mU q := by
  have hn : q + 1 ≠ 0 := Nat.succ_ne_zero q
  have h1 : 1 ≤ (q + 1).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn).mp (by rw [pow_one]; omega)
  have h2 : ¬ 2 ≤ (q + 1).factorization 3 := fun h =>
    h9 (by
      have := (Nat.prime_three.pow_dvd_iff_le_factorization hn).mpr h
      omega)
  have hf : (q + 1).factorization 3 = 1 := by omega
  have h3 : 3 ^ (q + 1).factorization 3 * mU q = q + 1 := Nat.ordProj_mul_ordCompl_eq_self (q + 1) 3
  rw [hf, pow_one] at h3
  exact h3.symm

section Main

variable {p f : ℕ} [Finite K] (hπ : false = false → UnitaryFieldData p f K)
  (hK : PiField false p f K) (hq : ModThree false (p ^ f))
  {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {β : K} {cβ : GL (Fin 3) K}
  (hcβ : cβ ∈ glPi false 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi false 3 (p ^ f) K)
  (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β)

include hK hq hτ1 hcβm in
theorem diagUnits_mem_normGU {x : Kˣ} (hx : x ^ (3 * mU (p ^ f)) = 1) :
    diagUnits 1 1 x ∈
      normGU hπ (sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd))) := by
  set N := sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) with hN
  set Q := normGU hπ N with hQ
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu' : (τu : K) = τ := rfl
  have hτR : τu ∈ rootsOfUnity (qSubPi false (p ^ f)) K := by
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hτu', Units.val_one]
    exact pow_succ_eq_one_of_modThree hq hτ
  have hD₁ : diagUnits 1 τu 1 ∈ glPi false 3 (p ^ f) K :=
    diagUnits_mem_glPi hK (one_mem _) hτR (one_mem _)
  have hE : diagUnits 1 1 τu ∈ Q := by
    rw [← conj_diagUnits_heisC hcβm 1 τu 1]
    have hc := cβ_mem_normGU hπ hτ hcβ hd
    exact Q.mul_mem (Q.mul_mem hc (d₁_mem_normGU hπ hτ hcβ hd hcβm hτu' hD₁)) (Q.inv_mem hc)
  obtain ⟨u, v, huv⟩ : IsCoprime ((3 : ℕ) : ℤ) (mU (p ^ f) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (coprime_mU (p ^ f)).symm
  have hzpow : ∀ (y : Kˣ) (z : ℤ), y ^ (3 * mU (p ^ f)) = 1 → y ^ (z * 3 * mU (p ^ f)) = 1 := by
    intro y z hy
    rw [show z * 3 * (mU (p ^ f) : ℤ) = ((3 * mU (p ^ f) : ℕ) : ℤ) * z by
      push_cast; ring, _root_.zpow_mul, zpow_natCast, hy, _root_.one_zpow]
  have hsplit : x = x ^ (u * 3) * x ^ (v * mU (p ^ f)) := by
    rw [← _root_.zpow_add]
    push_cast at huv
    rw [huv, zpow_one]
  have h3 : diagUnits 1 1 (x ^ (v * mU (p ^ f))) ∈ Q := by
    have hx3 : ((x ^ (v * mU (p ^ f)) : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul,
        show v * (mU (p ^ f) : ℤ) * ((3 : ℕ) : ℤ) = v * 3 * mU (p ^ f) by push_cast; ring,
        hzpow x v hx, Units.val_one]
    obtain ⟨k, hk⟩ := exists_pow_eq_of_cube hτ hτ1 hx3
    have hk' : x ^ (v * mU (p ^ f)) = τu ^ k :=
      Units.ext (by rw [hk, Units.val_pow_eq_pow_val, hτu'])
    rw [hk', show diagUnits (1 : Kˣ) 1 (τu ^ k) = diagUnits 1 1 τu ^ k by
      rw [diagUnits_pow, one_pow]]
    exact Q.pow_mem hE k
  have hm3 : ∀ y : Kˣ, y ^ (3 * mU (p ^ f)) = 1 → (y ^ (u * 3)) ^ mU (p ^ f) = 1 := by
    intro y hy
    rw [← zpow_natCast, ← _root_.zpow_mul]
    exact hzpow y u hy
  set c := x ^ (u * 3) with hc
  have hcm : c ^ mU (p ^ f) = 1 := hm3 x hx
  set c' := c ^ u with hc'
  have hc'm : c' ^ mU (p ^ f) = 1 := by
    rw [hc', ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hcm,
      _root_.one_zpow]
  have hc'3 : c' ^ 3 = c := by
    have e : c' ^ 3 = c ^ (u * 3) := by
      rw [hc', ← zpow_natCast, ← _root_.zpow_mul]
      norm_num
    rw [e]
    have : c ^ (u * 3) = c ^ ((1 : ℤ) - v * mU (p ^ f)) := by
      congr 1
      push_cast at huv
      linarith
    rw [this, _root_.zpow_sub, zpow_one, show v * (mU (p ^ f) : ℤ) = ((mU (p ^ f) : ℕ) : ℤ) * v
      by ring, _root_.zpow_mul, zpow_natCast, hcm, _root_.one_zpow, inv_one, mul_one]
  have hmd : mU (p ^ f) ∣ p ^ f + 1 := mU_dvd (p ^ f)
  have hc'q : c' ^ (p ^ f + 1) = 1 := by
    obtain ⟨r, hr⟩ := hmd
    rw [hr, pow_mul, hc'm, one_pow]
  have hc'iR : c'⁻¹ ∈ rootsOfUnity (qSubPi false (p ^ f)) K := by
    rw [mem_rootsOfUnity, inv_pow]
    change (c' ^ (p ^ f + 1))⁻¹ = 1
    rw [hc'q, inv_one]
  have hc'iM : c'⁻¹ ∈ rootsOfUnity (mU (p ^ f)) K := by
    rw [mem_rootsOfUnity, inv_pow, hc'm, inv_one]
  have hT : torusHom (c'⁻¹, c'⁻¹) ∈ slPi false 3 (p ^ f) K := torusHom_mem_slPi hK hc'iR hc'iR
  have hTN : (torusHom (c'⁻¹, c'⁻¹) : GL (Fin 3) K) ∈ Q := by
    have hmem := mem_normGU_of_projOf_mem hπ (N := N)
      (x := (⟨torusHom (c'⁻¹, c'⁻¹), hT⟩ : slPi false 3 (p ^ f) K))
      (le_sSup (diagMuU_mem_invSet142 hπ hτ hcβ hd hcβm)
        ⟨_, mem_diagMuU.mpr ⟨c'⁻¹, c'⁻¹, hc'iM, hc'iM, rfl⟩, rfl⟩)
    exact hmem
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 3) c' ∈ Q :=
    scalar_mem_normGU hπ ((scalar_mem_glPi_false_iff (hπ rfl) c').mpr
      (by rw [← Units.val_pow_eq_pow_val, hc'q, Units.val_one]))
  have hcdiag : diagUnits 1 1 c =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c' * torusHom (c'⁻¹, c'⁻¹) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_torusHom, coe_diagUnits,
      Matrix.scalar_apply, diagonal_mul_diagonal, ← hc'3]
    congr 1
    funext i
    fin_cases i <;> simp
    ring
  have h3' : diagUnits 1 1 c ∈ Q := by
    rw [hcdiag]
    exact Q.mul_mem hsc hTN
  rw [hsplit, show diagUnits (1 : Kˣ) 1 (c * x ^ (v * mU (p ^ f))) =
    diagUnits 1 1 c * diagUnits 1 1 (x ^ (v * mU (p ^ f))) by
      rw [diagUnits_mul, one_mul]]
  exact Q.mul_mem h3' h3

include hK hq hτ1 hcβm in
theorem genStdU_of_not_nine
    (h9 : p ^ f % 9 ≠ 8)
    (hperf : Group.IsPerfect (projImage (slPi false 3 (p ^ f) K))) (hβ : ¬ ∃ μ : K, μ ^ 3 = β) :
    sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤ := by
  have h := hπ rfl
  have hfin := finite_pgl (K := K)
  have := hperf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) with hN
  set ρ := projOf (slPi false 3 (p ^ f) K) with hρ
  have hq' : p ^ f % 3 = 2 := hq
  have hq3 : 3 ∣ p ^ f + 1 := by omega
  have hm := three_mul_mU hq' h9
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu' : (τu : K) = τ := rfl
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hβ ⟨0, by ring⟩
  have hβN : β ^ (p ^ f + 1) = 1 := by
    have hU := (mem_glPi_false h).mp hcβ
    have e := congrFun (congrFun hU 2) 2
    rw [hcβm] at e
    simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] at e
    rw [pow_succ, ← h.bar_apply]
    exact e
  have hdSL : diagTau hτ ∈ slPi false 3 (p ^ f) K := diagTau_mem_slPi hπ (fun _ => hq) hτ
  set D : slPi false 3 (p ^ f) K := ⟨diagTau hτ, hdSL⟩ with hDdef
  obtain ⟨s₀, hs₀⟩ := CFSG.LieType.SeitzGeneration.exists_shift_su h
  set s : slPi false 3 (p ^ f) K := ⟨(s₀ : GL (Fin 3) K), s₀.2⟩ with hsdef
  have hs : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS := hs₀
  have hq2 : p ^ f ≠ 2 := by
    intro h2
    have hsolv := Sec13.isSolvable_projImage_slPi_two hK h2
    have hρD : ρ D ≠ 1 := fun e =>
      diagTau_not_mem_statedScalars hτ hτ1 ((projOf_eq_one_iff D).mp e)
    have : Nontrivial (projImage (slPi false 3 (p ^ f) K)) := ⟨⟨ρ D, 1, hρD⟩⟩
    exact Group.IsPerfect.not_isSolvable _ hsolv
  have hdL : ∀ n : ℕ, ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((cβ * diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      τ • (((cβ * diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    intro n
    rw [Units.val_mul, hcβm]
    exact diagTau_mul_heisC_mul_pow hτ β n
  have hT : ∀ n : ℕ, n < 3 →
      (torusU false p f K (cβ * diagTau hτ ^ n)).map ρ ≤ N := by
    intro n hn
    have hL3 : ((cβ * diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        β • 1 := by
      rw [Units.val_mul, hcβm]
      interval_cases n
      · rw [pow_zero, Units.val_one, Matrix.mul_one]
        exact L3PGL.heisC_pow_three β
      · rw [pow_one]
        exact heisC_mul_diagTau_pow_three hτ β
      · exact heisC_mul_diagTau_sq_pow_three hτ β
    have h1 : cβ * (cβ * diagTau hτ ^ n) * cβ⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ((τu ^ 2) ^ n) * (cβ * diagTau hτ ^ n) := by
      refine conj_eq_scalar_mul ?_
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hτu', Units.val_mul, hcβm]
      exact heisC_mul_heisC_mul_pow hτ β n
    have h2 : diagTau hτ * (cβ * diagTau hτ ^ n) * (diagTau hτ)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) τu * (cβ * diagTau hτ ^ n) :=
      conj_eq_scalar_mul (by rw [hτu']; exact hdL n)
    exact le_sSup (torusU_mem_invSet142 hπ hτ hτ1 h3 hcβ hd hL3 hβ h1 h2)
  have hDm : (diagMuU p f K).map ρ ≤ N := le_sSup (diagMuU_mem_invSet142 hπ hτ hcβ hd hcβm)
  have hβi : (Units.mk0 β hβ0)⁻¹ ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hβN, inv_one,
      Units.val_one]
  have hSQ : (s : GL (Fin 3) K) ∈ normGU hπ N := by
    have e : (s : GL (Fin 3) K) =
        cβ * diagUnits 1 1 (Units.mk0 β hβ0)⁻¹ := by
      apply Units.ext
      rw [hs, Units.val_mul, hcβm, coe_diagUnits, ← heisC_mul_diag_inv hβ0]
      congr 2
    rw [e]
    exact (normGU hπ N).mul_mem (cβ_mem_normGU hπ hτ hcβ hd)
      (diagUnits_mem_normGU hπ hK hq hτ hτ1 hcβ hd hcβm (by rw [← hm]; exact hβi))
  have hdQ : diagTau hτ ∈ normGU hπ N := d_mem_normGU hπ hτ hcβ hd
  have ha : N.map (MulAut.conj (ρ D)).toMonoidHom ≤ N := by
    rw [← conjM'_eq_conj hπ D]
    exact map_le_of_mem_normGU hπ _ hdQ
  have hb : N.map (MulAut.conj (ρ s)).toMonoidHom ≤ N := by
    rw [← conjM'_eq_conj hπ s]
    exact map_le_of_mem_normGU hπ _ hSQ
  have hab : ρ D * ρ s = ρ s * ρ D := by
    have e : (s : GL (Fin 3) K) * diagTau hτ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * (diagTau hτ * (s : GL (Fin 3) K)) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hs,
        hS_mul_diagTau hτ, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
        Matrix.one_mul, Units.val_pow_eq_pow_val, hτu']
    apply Subtype.ext
    show ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk (s : GL (Fin 3) K) =
      ProjGenLinGroup.mk (s : GL (Fin 3) K) * ProjGenLinGroup.mk (diagTau hτ)
    rw [← map_mul, ← map_mul, e,
      map_mul ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 3) (τu ^ 2)),
      mk_eq_one_iff_mem_statedScalars.mpr ⟨_, rfl⟩, one_mul]
  have hprim : IsPrimitiveRoot τ 3 := by
    have ho : orderOf τ = 3 := orderOf_eq_prime hτ hτ1
    rw [← ho]
    exact IsPrimitiveRoot.orderOf τ
  have hcore := LieType.SeitzGeneration.unitaryOuterHeisCore_of_finite_cases
      LieType.SeitzGeneration.HeisSmall.outerB12AtCard_five
      LieType.SeitzGeneration.HeisSmall.outerB12AtCard_eight
      LieType.SeitzGeneration.HeisSmall.outerB12AtCard_eleven p f K h hq3 hq2 τ β hprim hβN hβ
  set T := N ⊔ (Subgroup.zpowers (ρ D) ⊔ Subgroup.zpowers (ρ s)) with hTdef
  have hline : ∀ n : ℕ, n < 3 → ∀ (g : slPi false 3 (p ^ f) K) (c : K),
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((cβ * diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        c • (((cβ * diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) → ρ g ∈ T := by
    intro n hn g c hg
    have hL3 : ((cβ * diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        β • 1 := by
      rw [Units.val_mul, hcβm]
      interval_cases n
      · rw [pow_zero, Units.val_one, Matrix.mul_one]
        exact L3PGL.heisC_pow_three β
      · rw [pow_one]
        exact heisC_mul_diagTau_pow_three hτ β
      · exact heisC_mul_diagTau_sq_pow_three hτ β
    have hmem := projOf_mem_of_fix_line hτ hτ1 hdSL hβ0 hL3 (hdL n) (hT n hn) hg
    exact (sup_le_sup_left le_sup_left N) hmem
  have hle : Subgroup.closure {g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3 |
      ∃ M ∈ CFSG.LieType.SeitzGeneration.outerHeisLines τ β,
        g ∈ CFSG.LieType.SeitzGeneration.FixU p f K M} ≤ T.comap (suToPsu p f K) := by
    rw [Subgroup.closure_le]
    rintro g ⟨M, hM, hgM⟩
    simp only [CFSG.LieType.SeitzGeneration.outerHeisLines, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hM
    have hτ2 : (τ ^ 2 : K) ≠ 0 := pow_ne_zero 2 hτ0
    set g' : slPi false 3 (p ^ f) K := ⟨(g : GL (Fin 3) K), g.2⟩ with hg'
    have hgg : suToPsu p f K g = ρ g' := Subtype.ext rfl
    change suToPsu p f K g ∈ T
    rw [hgg]
    rcases hM with rfl | rfl | rfl | rfl
    · obtain ⟨c, hc⟩ := hgM
      refine hline 0 (by norm_num) g' c ?_
      rw [pow_zero, mul_one, hcβm]
      exact hc
    · rw [heisD_eq_smul hτ, CFSG.LieType.SeitzGeneration.mem_FixU_smul hτ2] at hgM
      obtain ⟨c, hc⟩ := hgM
      exact projOf_mem_of_fix_d hK hq hτ hτ1 hdSL (g := g') hs hm hDm hc
    · rw [heisD_eq_smul hτ, Matrix.mul_smul,
        CFSG.LieType.SeitzGeneration.mem_FixU_smul hτ2] at hgM
      obtain ⟨c, hc⟩ := hgM
      refine hline 1 (by norm_num) g' c ?_
      rw [pow_one, Units.val_mul, hcβm]
      exact hc
    · rw [heisD_eq_smul hτ, smul_pow, Matrix.mul_smul,
        CFSG.LieType.SeitzGeneration.mem_FixU_smul (pow_ne_zero 2 hτ2)] at hgM
      obtain ⟨c, hc⟩ := hgM
      refine hline 2 (by norm_num) g' c ?_
      rw [Units.val_mul, Units.val_pow_eq_pow_val, hcβm]
      exact hc
  rw [hcore] at hle
  have htop : T = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨x, rfl⟩ := suToPsu_surjective (p := p) (f := f) (K := K) m
    exact hle (Subgroup.mem_top x)
  exact eq_top_of_sup_zpowers_two hab ha hb htop

end Main

end L3PGLU

theorem ks142L3PGLGenStdU_of_nine
    (h9 : KS142L3PGLGenStdUNine) : KS142L3PGLGenStdU := by
  intro p f K _ hπ hK hq hperf τ hτ hτ1 β cβ hcβ hd hcβm hβ
  by_cases h9' : p ^ f % 9 = 8
  · exact h9 p f K hπ hK hq h9' hperf τ hτ hτ1 β cβ hcβ hd hcβm hβ
  · have := hK.finite
    exact L3PGLU.genStdU_of_not_nine hπ hK hq hτ hτ1 hcβ hd hcβm h9' hperf hβ

end CFSG.RankThree.PartTwo.Sec14
