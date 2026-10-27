module

public import CFSG.RankThree.PartOne.CTP.SeitzU5Heis
public import CFSG.RankThree.PartOne.SEITZU49.Norm

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Pair

open Matrix CFSG CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCEvenUnitaryFive
  CFSG.RankThree.PartOne.CTP
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr SUid)
open CFSG.RankThree.PartOne.CTP.U5Heis
open CFSG.RankThree.PartOne.SEITZU49

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

theorem pow_mul_comm_smul {X Y : Matrix ι ι R} {c : R} (hc : Y * X = c • (X * Y)) (n : ℕ) :
    Y ^ n * X = c ^ n • (X * Y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc Y ^ (n + 1) * X = Y * (Y ^ n * X) := by rw [pow_succ', Matrix.mul_assoc]
      _ = Y * (c ^ n • (X * Y ^ n)) := by rw [ih]
      _ = c ^ n • ((Y * X) * Y ^ n) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = c ^ n • ((c • (X * Y)) * Y ^ n) := by rw [hc]
      _ = c ^ (n + 1) • (X * Y ^ (n + 1)) := by
        rw [Matrix.smul_mul, smul_smul, ← pow_succ, Matrix.mul_assoc, ← pow_succ']

theorem mul_pow_smul {X Y : Matrix ι ι R} {c : R} (hc : Y * X = c • (X * Y)) (n : ℕ) :
    (X * Y) ^ n = c ^ n.choose 2 • (X ^ n * Y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (X * Y) ^ (n + 1) = (X * Y) ^ n * (X * Y) := by rw [pow_succ]
      _ = (c ^ n.choose 2 • (X ^ n * Y ^ n)) * (X * Y) := by rw [ih]
      _ = c ^ n.choose 2 • (X ^ n * ((Y ^ n * X) * Y)) := by
        rw [Matrix.smul_mul]
        congr 1
        simp only [Matrix.mul_assoc]
      _ = c ^ n.choose 2 • (X ^ n * ((c ^ n • (X * Y ^ n)) * Y)) := by
        rw [pow_mul_comm_smul hc]
      _ = c ^ (n + 1).choose 2 • (X ^ (n + 1) * Y ^ (n + 1)) := by
        have hch : (n + 1).choose 2 = n + n.choose 2 := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
        rw [hch, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, add_comm]
        congr 1
        simp only [pow_succ, Matrix.mul_assoc]

end Abstract

section Bridge

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem ker_scalar (hq3 : 3 < 2 ^ f) {z : primeFormUnitary h (idGram K 5)}
    (hz : z ∈ (primeFormConjHom h (idGram K 5)).ker) :
    ∃ c : K, unitaryInvolution K 2 f c * c = 1 ∧
      ((z : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = c • (1 : Matrix (Fin 5) (Fin 5) K) := by
  obtain ⟨c, hc, hz'⟩ := (primeFormConjHom_eq_one_iff (by norm_num) hq3 z).mp
    (MonoidHom.mem_ker.mp hz)
  refine ⟨c, ?_, ?_⟩
  · have := congrArg (fun x : Kˣ => (x : K)) hc
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [unitaryInvolution_apply, ← pow_succ]
    exact this
  · rw [hz', GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem scalar_mem_ker (hq3 : 3 < 2 ^ f) {c : K} (hc : unitaryInvolution K 2 f c * c = 1) :
    ∃ z ∈ (primeFormConjHom h (idGram K 5)).ker,
      ((z : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = c • (1 : Matrix (Fin 5) (Fin 5) K) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  set c' : Kˣ := Units.mk0 c hc0 with hc'
  have hN : h.norm (c' : K) = 1 := by
    rw [UnitaryFieldData.norm, hc', Units.val_mk0, bar_apply_eq h, mul_comm]
    exact hc
  have hmem := scalar_mem_primeFormUnitary_one (n := 5) h hN
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, primeFormConjHom_eq_one_iff (by norm_num) hq3]
    refine ⟨c', ?_, rfl⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hc', Units.val_mk0, pow_succ,
      ← unitaryInvolution_apply]
    exact hc
  · rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rfl

end Bridge

section Extract

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

omit [Finite K] [CharP K 2] in
theorem coe_pow_matrix (x : primeFormUnitary h (idGram K 5)) (n : ℕ) :
    (((x ^ n : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ n := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

omit [Finite K] [CharP K 2] in
theorem coe_mul_matrix (x y : primeFormUnitary h (idGram K 5)) :
    (((x * y : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  rw [Subgroup.coe_mul, Units.val_mul]

variable {h}

omit [Finite K] [CharP K 2] in
theorem pow_five_mem_ker {A : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hAel : IsElementaryAbelian 5 A) {x : primeFormUnitary h (idGram K 5)}
    (hx : primeFormConjHom h (idGram K 5) x ∈ A) :
    x ^ 5 ∈ (primeFormConjHom h (idGram K 5)).ker := by
  have := hAel
  rw [MonoidHom.mem_ker, map_pow]
  exact elemPow_eq_one_of_isElementaryAbelian (A := A) _ hx

theorem comm_scalar (hq3 : 3 < 2 ^ f) {A : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hAel : IsElementaryAbelian 5 A) {x y : primeFormUnitary h (idGram K 5)}
    (hx : primeFormConjHom h (idGram K 5) x ∈ A) (hy : primeFormConjHom h (idGram K 5) y ∈ A) :
    ∃ c : K, c ^ 5 = 1 ∧ unitaryInvolution K 2 f c * c = 1 ∧
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * ((y : GL (Fin 5) K) : Matrix _ _ K) =
        c • (((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((x : GL (Fin 5) K) : Matrix _ _ K)) := by
  classical
  set ρ := primeFormConjHom h (idGram K 5) with hρ
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have hc : IsMulCommutative A := hAel.toIsMulCommutative
    exact congrArg Subtype.val (hc.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hκ : x * y * x⁻¹ * y⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm _ hx _ hy]
    group
  obtain ⟨c, hcn, hcm⟩ := ker_scalar h hq3 hκ
  have hmat : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * ((y : GL (Fin 5) K) : Matrix _ _ K)
      = c • (((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((x : GL (Fin 5) K) : Matrix _ _ K)) := by
    have h1 : (x * y * x⁻¹ * y⁻¹ : primeFormUnitary h (idGram K 5)) * (y * x) = x * y := by
      group
    have h2 := congrArg (fun m : primeFormUnitary h (idGram K 5) =>
      ((m : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) h1
    rw [coe_mul_matrix h, coe_mul_matrix h y x, hcm, coe_mul_matrix h x y] at h2
    rw [← h2, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨c, ?_, hcn, hmat⟩
  obtain ⟨b, hbn, hb⟩ := ker_scalar h hq3 (pow_five_mem_ker hAel hy)
  rw [coe_pow_matrix] at hb
  have h3 := U5Eigen.pow_mul_comm hmat 5
  rw [hb, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at h3
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hbn
  have h4 : b • ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (c ^ 5 * b) • ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := h3
  have h5 : c ^ 5 • ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    have := congrArg (fun m => b⁻¹ • m) h4
    simp only [smul_smul, inv_mul_cancel₀ hb0, one_smul] at this
    rw [mul_comm (c ^ 5) b, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul] at this
    exact this.symm
  exact eq_one_of_smul_eq (x : GL (Fin 5) K) h5

theorem mul_pow_five (hq3 : 3 < 2 ^ f) {A : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hAel : IsElementaryAbelian 5 A) {x y : primeFormUnitary h (idGram K 5)}
    (hx : primeFormConjHom h (idGram K 5) x ∈ A) (hy : primeFormConjHom h (idGram K 5) y ∈ A) :
    (((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * ((y : GL (Fin 5) K) : Matrix _ _ K)) ^ 5 =
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 *
        ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 := by
  obtain ⟨c, hc5, hcn, hmat⟩ := comm_scalar hq3 hAel hx hy
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hcn
  have hinv : ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((x : GL (Fin 5) K) : Matrix _ _ K) =
      c⁻¹ • (((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((y : GL (Fin 5) K) : Matrix _ _ K)) := by
    rw [hmat, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [mul_pow_smul hinv 5]
  have : c⁻¹ ^ Nat.choose 5 2 = 1 := by
    rw [show Nat.choose 5 2 = 5 * 2 by decide, pow_mul, inv_pow, hc5, inv_one, one_pow]
  rw [this, one_smul]

def Good (h : UnitaryFieldData 2 f K) (x : primeFormUnitary h (idGram K 5)) : Prop :=
  ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧
    ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 = u ^ 5 • (1 : Matrix (Fin 5) (Fin 5) K)

theorem good_iff_ker (hq3 : 3 < 2 ^ f) (x : primeFormUnitary h (idGram K 5)) :
    Good h x ↔ ∃ z ∈ (primeFormConjHom h (idGram K 5)).ker, x ^ 5 = z ^ 5 := by
  constructor
  · rintro ⟨u, hu, hx⟩
    obtain ⟨z, hz, hzm⟩ := scalar_mem_ker h hq3 hu
    refine ⟨z, hz, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_pow_matrix, coe_pow_matrix, hx, hzm, smul_pow, one_pow]
  · rintro ⟨z, hz, hxz⟩
    obtain ⟨c, hc, hzm⟩ := ker_scalar h hq3 hz
    refine ⟨c, hc, ?_⟩
    have := congrArg (fun m : primeFormUnitary h (idGram K 5) =>
      ((m : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) hxz
    simp only [coe_pow_matrix] at this
    rw [this, hzm, smul_pow, one_pow]

theorem good_of_mul (hq3 : 3 < 2 ^ f) {A : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hAel : IsElementaryAbelian 5 A) {x y : primeFormUnitary h (idGram K 5)}
    (hx : primeFormConjHom h (idGram K 5) x ∈ A) (hy : primeFormConjHom h (idGram K 5) y ∈ A)
    (gx : Good h x) (gxy : Good h (x * y)) : Good h y := by
  obtain ⟨u, hu, hxu⟩ := gx
  obtain ⟨w, hw, hxyw⟩ := gxy
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  refine ⟨w * u⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv₀]
    have hu' : unitaryInvolution K 2 f u = u⁻¹ := eq_inv_of_mul_eq_one_left hu
    rw [hu', inv_inv]
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    calc unitaryInvolution K 2 f w * u * (w * u⁻¹)
          = (unitaryInvolution K 2 f w * w) * (u * u⁻¹) := by
          ring
      _ = 1 := by rw [hw, mul_inv_cancel₀ hu0, mul_one]
  · rw [coe_mul_matrix, mul_pow_five hq3 hAel hx hy, hxu, Matrix.smul_mul,
      Matrix.one_mul] at hxyw
    have hu5 : u ^ 5 ≠ 0 := pow_ne_zero _ hu0
    have : ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 =
        (u ^ 5)⁻¹ • (w ^ 5 • (1 : Matrix (Fin 5) (Fin 5) K)) := by
      rw [← hxyw, smul_smul, inv_mul_cancel₀ hu5, one_smul]
    rw [this, smul_smul, mul_pow, inv_pow, mul_comm]

theorem exists_good_mul_pow (hq3 : 3 < 2 ^ f) (h5 : 5 ∣ 2 ^ f + 1)
    (hK : Nat.card K = (2 ^ f) ^ 2) {A : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hAel : IsElementaryAbelian 5 A) {x y : primeFormUnitary h (idGram K 5)}
    (hx : primeFormConjHom h (idGram K 5) x ∈ A) (hy : primeFormConjHom h (idGram K 5) y ∈ A)
    (bx : ¬ Good h x) (bY : ¬ Good h y) : ∃ k : ℕ, Good h (x * y ^ k) := by
  obtain ⟨γ, hγ, hord, hgen⟩ := Norm.exists_generator hK
  obtain ⟨a, ha, hxa⟩ := ker_scalar h hq3 (pow_five_mem_ker hAel hx)
  obtain ⟨b, hb, hyb⟩ := ker_scalar h hq3 (pow_five_mem_ker hAel hy)
  rw [coe_pow_matrix] at hxa hyb
  have hna : ¬ ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ u ^ 5 = a := fun ⟨u, hu, hu5⟩ =>
    bx ⟨u, hu, by rw [hxa, hu5]⟩
  have hnb : ¬ ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ u ^ 5 = b := fun ⟨u, hu, hu5⟩ =>
    bY ⟨u, hu, by rw [hyb, hu5]⟩
  obtain ⟨k, u, hu, hu5⟩ := Norm.exists_good_mul hγ hord hgen h5 ha hb hna hnb
  refine ⟨k, u, hu, ?_⟩
  have hyk : primeFormConjHom h (idGram K 5) (y ^ k) ∈ A := by
    rw [map_pow]
    exact A.pow_mem hy k
  rw [coe_mul_matrix, mul_pow_five hq3 hAel hx hyk, hxa, coe_pow_matrix, ← pow_mul,
    mul_comm k 5, pow_mul, hyb, smul_pow, one_pow, Matrix.smul_mul, Matrix.one_mul,
    smul_smul, hu5]

theorem exists_good_bad (hq3 : 3 < 2 ^ f) (h5 : 5 ∣ 2 ^ f + 1)
    (hK : Nat.card K = (2 ^ f) ^ 2) {A : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hAel : IsElementaryAbelian 5 A)
    (hnab : ¬ ∀ x y : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
        x * y = y * x)
    (hshape : ∃ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ A ∧
      ∀ z ∈ (primeFormConjHom h (idGram K 5)).ker, x ^ 5 ≠ z ^ 5) :
    ∃ e g : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) e ∈ A ∧
      primeFormConjHom h (idGram K 5) g ∈ A ∧ Good h e ∧ ¬ Good h g ∧ e * g ≠ g * e := by
  obtain ⟨x₀, hx₀, hx₀bad⟩ := hshape
  have hbad₀ : ¬ Good h x₀ := fun hg => by
    obtain ⟨z, hz, hz5⟩ := (good_iff_ker hq3 x₀).mp hg
    exact hx₀bad z hz hz5
  push Not at hnab
  obtain ⟨x, y, hx, hy, hxy⟩ := hnab
  have memA : ∀ a b : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) a ∈ A →
      primeFormConjHom h (idGram K 5) b ∈ A → primeFormConjHom h (idGram K 5) (a * b) ∈ A :=
    fun a b ha hb => by rw [map_mul]; exact A.mul_mem ha hb
  by_cases hgx : Good h x <;> by_cases hgy : Good h y
  · by_cases hcom : x * x₀ = x₀ * x
    · refine ⟨x, y * x₀, hx, memA y x₀ hy hx₀, hgx, fun hgood => hbad₀ ?_, fun hc => hxy ?_⟩
      · exact good_of_mul hq3 hAel hy hx₀ hgy hgood
      · have h1 : x * y * x₀ = y * x * x₀ := by
          calc x * y * x₀ = x * (y * x₀) := by rw [mul_assoc]
            _ = y * x₀ * x := hc
            _ = y * (x₀ * x) := by rw [mul_assoc]
            _ = y * (x * x₀) := by rw [hcom]
            _ = y * x * x₀ := by rw [mul_assoc]
        exact mul_right_cancel h1
    · exact ⟨x, x₀, hx, hx₀, hgx, hbad₀, hcom⟩
  · exact ⟨x, y, hx, hy, hgx, hgy, hxy⟩
  · exact ⟨y, x, hy, hx, hgy, hgx, fun hc => hxy hc.symm⟩
  · obtain ⟨k, hk⟩ := exists_good_mul_pow hq3 h5 hK hAel hx hy hgx hgy
    have hyk : primeFormConjHom h (idGram K 5) (y ^ k) ∈ A := by
      rw [map_pow]
      exact A.pow_mem hy k
    refine ⟨x * y ^ k, y, memA x (y ^ k) hx hyk, hy, hk, hgy, fun hc => hxy ?_⟩
    have h1 : x * y * y ^ k = y * x * y ^ k := by
      calc x * y * y ^ k = x * (y * y ^ k) := by rw [mul_assoc]
        _ = x * y ^ k * y := by rw [← pow_succ', pow_succ, mul_assoc]
        _ = y * (x * y ^ k) := hc
        _ = y * x * y ^ k := by rw [mul_assoc]
    exact mul_right_cancel h1

theorem exists_heis_pair49 (hq3 : 3 < 2 ^ f) (h5 : 5 ∣ 2 ^ f + 1)
    (hK : Nat.card K = (2 ^ f) ^ 2) {A : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hAel : IsElementaryAbelian 5 A)
    (hnab : ¬ ∀ x y : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
        x * y = y * x)
    (hshape : ∃ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ A ∧
      ∀ z ∈ (primeFormConjHom h (idGram K 5)).ker, x ^ 5 ≠ z ^ 5) :
    ∃ (e g : primeFormUnitary h (idGram K 5)) (ζ zz : K),
      primeFormConjHom h (idGram K 5) e ∈ A ∧ primeFormConjHom h (idGram K 5) g ∈ A ∧
      ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 = 1 ∧
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 = zz • (1 : Matrix (Fin 5) (Fin 5) K) ∧
      unitaryInvolution K 2 f zz * zz = 1 ∧
      (∀ u : K, unitaryInvolution K 2 f u * u = 1 → u ^ 5 ≠ zz) ∧ ζ ^ 5 = 1 ∧ ζ ≠ 1 ∧
      ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * ((g : GL (Fin 5) K) : Matrix _ _ K) =
        ζ • (((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((e : GL (Fin 5) K) : Matrix _ _ K)) := by
  obtain ⟨e₀, g, he₀, hg, ⟨u, hu, hEu⟩, bg, hnc⟩ := exists_good_bad hq3 h5 hK hAel hnab hshape
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hu' : unitaryInvolution K 2 f u⁻¹ * u⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hu, inv_one]
  obtain ⟨z', hz', hz'm⟩ := scalar_mem_ker h hq3 hu'
  set ρ := primeFormConjHom h (idGram K 5) with hρ
  set e : primeFormUnitary h (idGram K 5) := e₀ * z' with he
  have hρe : ρ e ∈ A := by
    rw [he, map_mul, MonoidHom.mem_ker.mp hz', mul_one]
    exact he₀
  have hMe : ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      u⁻¹ • ((e₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    rw [he, coe_mul_matrix, hz'm, Matrix.mul_smul, Matrix.mul_one]
  have he5 : ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ 5 = 1 := by
    rw [hMe, smul_pow, hEu, smul_smul, ← mul_pow, inv_mul_cancel₀ hu0, one_pow, one_smul]
  have hnc' : e * g ≠ g * e := by
    intro hc
    apply hnc
    have hcz := commute_of_mem_ker h hq3 hz'
    have h1 : e₀ * g * z' = g * e₀ * z' := by
      calc e₀ * g * z' = e₀ * (g * z') := by rw [mul_assoc]
        _ = e₀ * (z' * g) := by rw [(hcz g).eq.symm]
        _ = e₀ * z' * g := by rw [mul_assoc]
        _ = g * (e₀ * z') := hc
        _ = g * e₀ * z' := by rw [mul_assoc]
    exact mul_right_cancel h1
  obtain ⟨c, hc5, hcn, hmat⟩ := comm_scalar hq3 hAel hρe hg
  have hc1 : c ≠ 1 := by
    intro hc1
    apply hnc'
    rw [hc1, one_smul] at hmat
    exact Subtype.ext (Units.ext hmat)
  obtain ⟨zz, hzz, hzzm⟩ := ker_scalar h hq3 (pow_five_mem_ker hAel hg)
  rw [coe_pow_matrix] at hzzm
  refine ⟨e, g, c, zz, hρe, hg, he5, hzzm, hzz, fun w hw hw5 => bg ⟨w, hw, ?_⟩, hc5, hc1, hmat⟩
  rw [hzzm, hw5]

end Extract

end CFSG.RankThree.PartOne.SEITZU49.Pair
