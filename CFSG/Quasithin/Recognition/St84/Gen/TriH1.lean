module

public import CFSG.RankThree.GF2n.Smith81.TiD3Hyp
public import CFSG.Quasithin.Background.JonesParshallOrthogonal
import CFSG.LocalAnalysis.EvenBN.TwoF4.TwistedAdditive
public import CFSG.RankThree.GF2n.Smith81.TiD3Quad

public noncomputable section

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.D3
open CFSG.Quasithin.JonesParshall
open CFSG.LocalAnalysis.EvenBN.TwoF4
open scoped MatrixGroups

namespace CFSG.Quasithin.F112R.St84

private def hypMatrix {F : Type} [Field F] (τ : F →+* F) (g : Mat2 F) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) F :=
  fun p q => g p.1 q.1 * τ (g p.2.1 q.2.1) * τ (τ (g p.2.2 q.2.2))

private theorem act_eq_mulVec {F : Type} [Field F] (τ : F →+* F) (g : Mat2 F) (x : Hyp F)
    (i j k : Fin 2) :
    act τ g x i j k =
      Matrix.mulVec (hypMatrix τ g) (fun p : Fin 2 × Fin 2 × Fin 2 =>
        x p.1 p.2.1 p.2.2) (i, j, k) := by
  simp [act, hypMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

private theorem hypMatrix_mul {F : Type} [Field F] (τ : F →+* F) (g h : Mat2 F) :
    hypMatrix τ (g * h) = hypMatrix τ g * hypMatrix τ h := by
  ext p q
  conv_rhs =>
    rw [Matrix.mul_apply]
    simp only [Fintype.sum_prod_type]
  simp only [hypMatrix, Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm]
  let f : Fin 2 → Fin 2 → Fin 2 → F := fun a b c =>
    g p.1 a * (h a q.1 * (τ (g p.2.1 b) * (τ (h b q.2.1) *
      (τ (τ (g p.2.2 c)) * τ (τ (h c q.2.2))))))
  change (∑ a, ∑ b, ∑ c, f c a b) = ∑ a, ∑ b, ∑ c, f a b c
  calc (∑ a, ∑ b, ∑ c, f c a b)
      = ∑ a, ∑ c, ∑ b, f c a b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, f c a b := by rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ c, f a b c := rfl

theorem _root_.CFSG.RankThree.GF2n.Smith81.D3.act_mul {F : Type} [Field F]
    (τ : F →+* F) (g h : Mat2 F) (x : Hyp F) :
    act τ (g * h) x = act τ g (act τ h x) := by
  funext i j k
  calc act τ (g * h) x i j k
      = Matrix.mulVec (hypMatrix τ (g * h)) (fun p : Fin 2 × Fin 2 × Fin 2 =>
          x p.1 p.2.1 p.2.2) (i, j, k) := act_eq_mulVec τ (g * h) x i j k
    _ = Matrix.mulVec (hypMatrix τ g * hypMatrix τ h)
          (fun p : Fin 2 × Fin 2 × Fin 2 => x p.1 p.2.1 p.2.2) (i, j, k) := by
          rw [hypMatrix_mul]
    _ = Matrix.mulVec (hypMatrix τ g) (Matrix.mulVec (hypMatrix τ h)
          (fun p : Fin 2 × Fin 2 × Fin 2 => x p.1 p.2.1 p.2.2)) (i, j, k) := by
          rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (hypMatrix τ g) (fun p : Fin 2 × Fin 2 × Fin 2 =>
          act τ h x p.1 p.2.1 p.2.2) (i, j, k) := by
          congr 1
          funext p
          exact (act_eq_mulVec τ h x p.1 p.2.1 p.2.2).symm
    _ = act τ g (act τ h x) i j k := (act_eq_mulVec τ g (act τ h x) i j k).symm

theorem _root_.CFSG.RankThree.GF2n.Smith81.D3.act_one {F : Type} [Field F]
    (τ : F →+* F) (x : Hyp F) :
    act τ (1 : Mat2 F) x = x := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [act, Fin.sum_univ_two, Matrix.one_apply]

@[expose] def kFormAct {K F : Type} [Field K] [Field F] [Algebra K F] (τ : F →ₐ[K] F)
    (hτ3 : ∀ a, τ (τ (τ a)) = a) : SL(2, F) →* AddMonoid.End ↥(kForm τ) where
  toFun g :=
    { toFun := fun x => ⟨act (τ : F →+* F) (g : Mat2 F) (x : Hyp F),
        act_mem_kForm τ hτ3 (g : Mat2 F) x.2⟩
      map_zero' := by
        apply Subtype.ext
        funext i j k
        simp [act]
      map_add' := fun x y => by
        apply Subtype.ext
        exact act_add (τ : F →+* F) (g : Mat2 F) (x : Hyp F) (y : Hyp F) }
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    funext i j k
    exact congrFun (congrFun (congrFun (act_one (τ : F →+* F) (x : Hyp F)) i) j) k
  map_mul' := fun g h => by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    funext i j k
    exact congrFun (congrFun (congrFun
      (act_mul (τ : F →+* F) (g : Mat2 F) (h : Mat2 F) (x : Hyp F)) i) j) k

theorem kFormAct_apply {K F : Type} [Field K] [Field F] [Algebra K F]
    (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (g : SL(2, F)) (x : ↥(kForm τ)) :
    ((kFormAct τ hτ3 g x : ↥(kForm τ)) : Hyp F) =
      act (τ : F →+* F) (g : Mat2 F) (x : Hyp F) := rfl

theorem zmod_ne_two_pow_of_two_pow_mul_odd {n a u : ℕ} (hn : 2 ≤ n) (hu : Odd u) (hu1 : 1 < u)
    (hlt : 2 ^ a * u < 2 ^ n - 1) (k : ℕ) :
    ((2 ^ a * u : ℕ) : ZMod (2 ^ n - 1)) ≠ 2 ^ k := by
  intro hk
  have hpow_lt : 2 ^ (k % n) < 2 ^ n - 1 := by
    have h1 : 2 ^ (k % n) ≤ 2 ^ (n - 1) := by
      have hkmod : k % n ≤ n - 1 := by
        have := Nat.mod_lt k (by omega : 0 < n)
        omega
      exact Nat.pow_le_pow_right (by norm_num) hkmod
    have h2 : 2 ^ (n - 1) < 2 ^ n - 1 := by
      have hn1 : 1 ≤ n := by omega
      have h3 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hn1]
      have h4 : 2 ≤ 2 ^ (n - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [h3]
      omega
    exact lt_of_le_of_lt h1 h2
  have hk' : ((2 ^ a * u : ℕ) : ZMod (2 ^ n - 1)) =
      ((2 ^ (k % n) : ℕ) : ZMod (2 ^ n - 1)) := by
    rw [hk, ← zmod_two_pow_mod n k]
    have h2 : (2 : ZMod (2 ^ n - 1)) = ((2 : ℕ) : ZMod (2 ^ n - 1)) := by norm_num
    rw [h2, ← Nat.cast_pow]
  have heq : 2 ^ a * u = 2 ^ (k % n) := by
    have h := congrArg ZMod.val hk'
    rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_natCast_of_lt hpow_lt] at h
  have hdvd : u ∣ 2 ^ (k % n) := by
    rw [← heq]
    exact Nat.dvd_mul_left u (2 ^ a)
  obtain ⟨p, hp, hpu⟩ := Nat.exists_prime_and_dvd (by omega : u ≠ 1)
  have hpdvd : p ∣ 2 ^ (k % n) := hpu.trans hdvd
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpdvd)
  exact hu.not_two_dvd_nat (hp2 ▸ hpu)

private theorem zmod_weight_ne_two_pow {n N : ℕ} (hN : N = 2 ^ n - 1) (hn : 2 ≤ n)
    {w : ℤ} {W a u : ℕ} (hW : W = 2 ^ a * u) (hu : Odd u) (hu1 : 1 < u)
    (hlt : W < N) (hcong : ((W : ℕ) : ZMod N) = (w : ZMod N)) :
    ∀ k : ℕ, (w : ZMod N) ≠ ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N) := by
  subst N
  intro k
  have h2 : ((2 : ℤ) : ZMod (2 ^ n - 1)) = ((2 : ℕ) : ZMod (2 ^ n - 1)) := by norm_num
  rw [h2, ← pow_succ]
  intro hk
  have hlt' : 2 ^ a * u < 2 ^ n - 1 := by rwa [hW] at hlt
  have hne := zmod_ne_two_pow_of_two_pow_mul_odd (n := n) (a := a) (u := u)
    hn hu hu1 hlt' (k + 1)
  apply hne
  rw [← hW, hcong]
  exact hk

private theorem weight_hab {q f N : ℕ} (hN : N = 2 ^ (3 * f) - 1) (hq : q = 2 ^ f)
    (hf : 2 ≤ f) :
    (∀ k : ℕ, ((-1 - (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ZMod N) ≠
        ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N)) ∧
    (∀ k : ℕ, ((1 - (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ZMod N) ≠
        ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N)) ∧
    (∀ k : ℕ, ((1 + (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ZMod N) ≠
        ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N)) ∧
    (∀ k : ℕ, ((1 + (q : ℤ) + (q : ℤ) ^ 2 : ℤ) : ZMod N) ≠
        ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N)) := by
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq3 : q ^ 3 = 2 ^ (3 * f) := by
    rw [hq, ← pow_mul]
    congr 1
    ring
  have hN_eq : N = q ^ 3 - 1 := by rw [hN, ← hq3]
  have hq_even : Even q := by
    rw [hq]
    exact (Nat.even_pow (m := 2) (n := f)).mpr ⟨even_two, by omega⟩
  have hq2_even : Even (q ^ 2) := hq_even.pow_of_ne_zero (by norm_num)
  have hq_le_q2 : q ≤ q ^ 2 := by nlinarith [hq4]
  have hqsub_eq : q ^ 2 - q = q * (q - 1) := by
    have h : q ^ 2 - q = q * q - q * 1 := by rw [pow_two, mul_one]
    rw [h, ← Nat.mul_sub_left_distrib]
  have hqsub_even : Even (q ^ 2 - q) :=
    (Nat.even_sub hq_le_q2).mpr (iff_of_true hq2_even hq_even)
  have hqsub_ge : 1 ≤ q ^ 2 - q := by
    have hq1 : 3 ≤ q - 1 := by omega
    have h : 12 ≤ q * (q - 1) := by
      calc 12 = 4 * 3 := by norm_num
        _ ≤ q * (q - 1) := Nat.mul_le_mul hq4 hq1
    rw [hqsub_eq]
    linarith
  have hqsub_odd : Odd (q ^ 2 - q - 1) :=
    Nat.Even.sub_odd hqsub_ge hqsub_even ⟨0, by norm_num⟩
  have hqsub1_odd : Odd (q ^ 2 - q + 1) := Even.add_one hqsub_even
  have hqsum_odd : Odd (q ^ 2 + q + 1) := Even.add_one (Even.add hq2_even hq_even)
  have hq3pos : 1 ≤ q ^ 3 := by
    have : 0 < q ^ 3 := pow_pos (by omega : 0 < q) 3
    omega
  have hpow_sub_odd : Odd (2 ^ (f - 1) - 1) := by
    have hle : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
    have heven : Even (2 ^ (f - 1)) :=
      (Nat.even_pow (m := 2) (n := f - 1)).mpr ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd hle heven ⟨0, by norm_num⟩
  have hpow_sub_ge : 1 ≤ 2 ^ (f - 1) - 1 := by
    have h2' : 2 ≤ 2 ^ (f - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (f - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set u1 : ℕ := (2 ^ (f - 1) - 1) * (q ^ 2 + q + 1) with hu1
  set W1 : ℕ := (q - 2) * (q ^ 2 + q + 1) with hW1
  have hW1_eq : W1 = 2 * u1 := by
    rw [hW1, hu1]
    have hq_eq : q = 2 * 2 ^ (f - 1) := by
      rw [hq]
      have hf1 : 1 ≤ f := by omega
      calc 2 ^ f = 2 ^ (f - 1 + 1) := by rw [Nat.sub_add_cancel hf1]
        _ = 2 ^ (f - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (f - 1) := by ring
    have hq_sub : q - 2 = 2 * (2 ^ (f - 1) - 1) := by
      rw [hq_eq]
      omega
    rw [hq_sub]
    ring
  have hu1_odd : Odd u1 := by
    rw [hu1]
    exact Nat.odd_mul.mpr ⟨hpow_sub_odd, hqsum_odd⟩
  have hu1_gt1 : 1 < u1 := by
    rw [hu1]
    have hB : 2 ≤ q ^ 2 + q + 1 := by nlinarith [hq4]
    calc 1 < 2 := by norm_num
      _ ≤ q ^ 2 + q + 1 := hB
      _ = 1 * (q ^ 2 + q + 1) := (one_mul _).symm
      _ ≤ (2 ^ (f - 1) - 1) * (q ^ 2 + q + 1) := Nat.mul_le_mul_right _ hpow_sub_ge
  have hW1lt : W1 < N := by
    rw [hN_eq, hW1]
    zify [show 2 ≤ q by omega, hq3pos]
    nlinarith only [hq4]
  have hW1int : (W1 : ℤ) = (-1 - (q : ℤ) - (q : ℤ) ^ 2) + (N : ℤ) := by
    rw [hW1, hN_eq]
    zify [show 2 ≤ q by omega, hq3pos]
    ring
  have hW1cast : ((W1 : ℕ) : ZMod N) = ((-1 - (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ZMod N) := by
    have h' : ((W1 : ℤ) : ZMod N) =
        (((-1 - (q : ℤ) - (q : ℤ) ^ 2) + (N : ℤ) : ℤ) : ZMod N) := by rw [hW1int]
    simpa using h'
  have hab1 : ∀ k : ℕ, ((-1 - (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ZMod N) ≠
      ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N) :=
    zmod_weight_ne_two_pow (a := 1) hN (by omega) (by simpa [pow_one] using hW1_eq)
      hu1_odd hu1_gt1 hW1lt hW1cast
  set u2 : ℕ := q ^ 2 - q - 1 with hu2
  set W2 : ℕ := q * u2 with hW2
  have hu2_gt1 : 1 < u2 := by
    rw [hu2, hqsub_eq]
    have hq1 : 3 ≤ q - 1 := by omega
    have h : 2 < q * (q - 1) := by
      calc 2 < 4 * 3 := by norm_num
        _ ≤ q * (q - 1) := Nat.mul_le_mul hq4 hq1
    omega
  have hW2lt : W2 < N := by
    rw [hN_eq, hW2, hu2]
    zify [hqsub_ge, hq_le_q2, hq3pos]
    nlinarith only [hq4]
  have hW2int : (W2 : ℤ) = (1 - (q : ℤ) - (q : ℤ) ^ 2) + (N : ℤ) := by
    rw [hW2, hu2, hN_eq]
    zify [hqsub_ge, hq_le_q2, hq3pos]
    ring
  have hW2cast : ((W2 : ℕ) : ZMod N) = ((1 - (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ZMod N) := by
    have h' : ((W2 : ℤ) : ZMod N) =
        (((1 - (q : ℤ) - (q : ℤ) ^ 2) + (N : ℤ) : ℤ) : ZMod N) := by rw [hW2int]
    simpa using h'
  have hab2 : ∀ k : ℕ, ((1 - (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ZMod N) ≠
      ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N) :=
    zmod_weight_ne_two_pow (a := f) hN (by omega) (by rw [hW2, hq])
      hqsub_odd hu2_gt1 hW2lt hW2cast
  set u3 : ℕ := q ^ 2 - q + 1 with hu3
  set W3 : ℕ := q * u3 with hW3
  have hu3_gt1 : 1 < u3 := by
    rw [hu3, hqsub_eq]
    nlinarith [hq4]
  have hW3lt : W3 < N := by
    rw [hN_eq, hW3, hu3]
    zify [hq_le_q2, hq3pos]
    nlinarith only [hq4]
  have hW3int : (W3 : ℤ) = (1 + (q : ℤ) - (q : ℤ) ^ 2) + (N : ℤ) := by
    rw [hW3, hu3, hN_eq]
    zify [hq_le_q2, hq3pos]
    ring
  have hW3cast : ((W3 : ℕ) : ZMod N) = ((1 + (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ZMod N) := by
    have h' : ((W3 : ℤ) : ZMod N) =
        (((1 + (q : ℤ) - (q : ℤ) ^ 2) + (N : ℤ) : ℤ) : ZMod N) := by rw [hW3int]
    simpa using h'
  have hab3 : ∀ k : ℕ, ((1 + (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ZMod N) ≠
      ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N) :=
    zmod_weight_ne_two_pow (a := f) hN (by omega) (by rw [hW3, hq])
      hqsub1_odd hu3_gt1 hW3lt hW3cast
  set W4 : ℕ := q ^ 2 + q + 1 with hW4
  have hW4_odd : Odd W4 := by rw [hW4]; exact hqsum_odd
  have hW4_gt1 : 1 < W4 := by rw [hW4]; nlinarith [hq4]
  have hW4lt : W4 < N := by
    rw [hN_eq, hW4]
    zify [hq3pos]
    nlinarith only [hq4]
  have hW4int : (W4 : ℤ) = 1 + (q : ℤ) + (q : ℤ) ^ 2 := by
    rw [hW4]
    push_cast
    ring
  have hW4cast : ((W4 : ℕ) : ZMod N) = ((1 + (q : ℤ) + (q : ℤ) ^ 2 : ℤ) : ZMod N) := by
    have h' : ((W4 : ℤ) : ZMod N) = ((1 + (q : ℤ) + (q : ℤ) ^ 2 : ℤ) : ZMod N) := by
      rw [hW4int]
    simpa using h'
  have hab4 : ∀ k : ℕ, ((1 + (q : ℤ) + (q : ℤ) ^ 2 : ℤ) : ZMod N) ≠
      ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N) :=
    zmod_weight_ne_two_pow (a := 0) hN (by omega) (by rw [hW4, pow_zero, one_mul])
      hW4_odd hW4_gt1 hW4lt hW4cast
  exact ⟨hab1, hab2, hab3, hab4⟩

private def torusExp : Fin 2 → ℤ := ![1, -1]

private theorem torusExp_zero : torusExp 0 = 1 := rfl

private theorem torusExp_one : torusExp 1 = -1 := rfl

private theorem act_tMat {F : Type} [Field F] (τ : F →+* F) (e : Fin 2 → ℤ)
    (he0 : e 0 = 1) (he1 : e 1 = -1) (c : F) (hc : c ≠ 0) (y : Hyp F)
    (i j k : Fin 2) :
    (act τ (tMat c hc) y) i j k =
      c ^ (e i) * τ (c ^ (e j)) * τ (τ (c ^ (e k))) * y i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [act, Fin.sum_univ_two, tMat_coe, he0, he1, map_inv₀]

private theorem tMat_coord_zpow {F : Type} [Field F] (τ : F →+* F) (q : ℕ)
    (hτ : ∀ a, τ a = a ^ q) (e : Fin 2 → ℤ) (c : F) (hc : c ≠ 0) (i j k : Fin 2) :
    c ^ (e i) * τ (c ^ (e j)) * τ (τ (c ^ (e k))) =
      c ^ (e i + (q : ℤ) * e j + (q : ℤ) ^ 2 * e k) := by
  have hτz : ∀ m : ℤ, τ (c ^ m) = c ^ ((q : ℤ) * m) := by
    intro m
    rw [map_zpow₀ (τ : F →+* F), show τ c = c ^ (q : ℤ) by rw [hτ c, ← zpow_natCast],
      ← zpow_mul]
  rw [hτz (e j), hτz (e k), hτz ((q : ℤ) * e k)]
  rw [← zpow_add₀ hc, ← zpow_add₀ hc]
  congr 1
  ring

private theorem act_tMat_zpow {F : Type} [Field F] (τ : F →+* F) (q : ℕ)
    (hτ : ∀ a, τ a = a ^ q) (e : Fin 2 → ℤ) (he0 : e 0 = 1) (he1 : e 1 = -1)
    (c : F) (hc : c ≠ 0) (y : Hyp F) (i j k : Fin 2) :
    (act τ (tMat c hc) y) i j k =
      c ^ (e i + (q : ℤ) * e j + (q : ℤ) ^ 2 * e k) * y i j k := by
  rw [act_tMat τ e he0 he1 c hc y i j k, tMat_coord_zpow τ q hτ e c hc i j k]

private theorem torus_coord {K F : Type} [Field K] [Field F] [Algebra K F]
    {τ : F →ₐ[K] F} {hτ3 : ∀ a, τ (τ (τ a)) = a}
    {ψ : SL(2, F) → ↥(kForm τ)}
    (htor : ∀ (c : F) (hc : c ≠ 0) (t : F),
      ψ (JonesParshall.uMat (c ^ 2 * t)) =
        kFormAct τ hτ3 (tMat c hc) (ψ (JonesParshall.uMat t)))
    {q : ℕ} (hτ : ∀ a, τ a = a ^ q) (e : Fin 2 → ℤ) (he0 : e 0 = 1) (he1 : e 1 = -1)
    (c : F) (hc : c ≠ 0) (t : F) (i j k : Fin 2) :
    (ψ (JonesParshall.uMat (c ^ 2 * t)) : Hyp F) i j k =
      c ^ (e i + (q : ℤ) * e j + (q : ℤ) ^ 2 * e k) *
        (ψ (JonesParshall.uMat t) : Hyp F) i j k := by
  have h := congrArg (fun x : ↥(kForm τ) => (x : Hyp F) i j k) (htor c hc t)
  rw [h, kFormAct_apply,
    act_tMat_zpow (τ : F →+* F) q hτ e he0 he1 c hc (ψ (JonesParshall.uMat t)) i j k]

private theorem coordinate_vanishes {F : Type} [Field F] [Fintype F] [CharP F 2]
    {n N : ℕ} (hN : N = 2 ^ n - 1) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    {φ : F → F} (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    {w : ℤ} (htor : ∀ (c : F), c ≠ 0 → ∀ t, φ (c ^ 2 * t) = c ^ w * φ t)
    (hab : ∀ k : ℕ, (w : ZMod N) ≠ ((2 : ℕ) : ZMod N) ^ k * ((2 : ℤ) : ZMod N))
    (x : F) : φ x = 0 := by
  subst N
  refine twisted_zpow_eq_zero (K := F) (p := 2) (n := n) Nat.prime_two hn hF
    (a := 2) (b := w) hadd ?_ hab x
  intro u x
  have h := htor (u : F) u.ne_zero x
  rwa [← Units.val_pow_eq_pow_val, ← Units.val_zpow_eq_zpow_val] at h

private theorem unipotent_vanishes {K F : Type} [Field K] [Field F] [Fintype F] [CharP F 2]
    [Algebra K F] {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ (3 * f))
    (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ 2 ^ f) (hτ3 : ∀ a, τ (τ (τ a)) = a)
    {ψ : SL(2, F) → ↥(kForm τ)} (hψ : ψ ∈ Z1A (kFormAct τ hτ3))
    (heq : ∀ (s : Fˣ) (g : SL(2, F)),
      ψ (torusHom s * g * (torusHom s)⁻¹) = kFormAct τ hτ3 (torusHom s) (ψ g)) :
    ∀ t : F, ψ (JonesParshall.uMat t) = 0 := by
  classical
  set q : ℕ := 2 ^ f with hq
  set N : ℕ := 2 ^ (3 * f) - 1 with hN
  obtain ⟨hab1, hab2, hab3, hab4⟩ := weight_hab hN hq hf
  have hτq : ∀ a, τ a = a ^ q := by
    intro a
    rw [hτ a, hq]
  have hcoc : ∀ s t, ψ (JonesParshall.uMat (s + t)) =
      ψ (JonesParshall.uMat s) +
        kFormAct τ hτ3 (JonesParshall.uMat s) (ψ (JonesParshall.uMat t)) := fun s t => by
    rw [← uMat_mul]
    exact hψ _ _
  have huMat_eq_uSL : ∀ s : F, JonesParshall.uMat s = D2.uSL s := fun s => Subtype.ext rfl
  have hu111 : ∀ (s : F) (y : Hyp F),
      (act (τ : F →+* F) (JonesParshall.uMat s) y) 1 1 1 = y 1 1 1 := by
    intro s y
    simp [act, Fin.sum_univ_two, uMat_coe]
  have hu011 : ∀ (s : F) (y : Hyp F),
      (act (τ : F →+* F) (JonesParshall.uMat s) y) 0 1 1 = y 0 1 1 + s * y 1 1 1 := by
    intro s y
    simp [act, Fin.sum_univ_two, uMat_coe]
  have hu001 : ∀ (s : F) (y : Hyp F),
      (act (τ : F →+* F) (JonesParshall.uMat s) y) 0 0 1 =
        y 0 0 1 + s * y 1 0 1 + (τ : F →+* F) s * y 0 1 1 +
          s * (τ : F →+* F) s * y 1 1 1 := by
    intro s y
    simp [act, Fin.sum_univ_two, uMat_coe]
    ring
  have hu000 : ∀ (s : F) (y : Hyp F),
      (act (τ : F →+* F) (JonesParshall.uMat s) y) 0 0 0 =
        y 0 0 0 + s * y 1 0 0 + (τ : F →+* F) s * y 0 1 0 +
          s * (τ : F →+* F) s * y 1 1 0 +
          (τ : F →+* F) ((τ : F →+* F) s) * y 0 0 1 +
          s * (τ : F →+* F) ((τ : F →+* F) s) * y 1 0 1 +
          (τ : F →+* F) s * (τ : F →+* F) ((τ : F →+* F) s) * y 0 1 1 +
          s * (τ : F →+* F) s * (τ : F →+* F) ((τ : F →+* F) s) * y 1 1 1 := by
    intro s y
    rw [huMat_eq_uSL s]
    exact act_uSL_000 (τ : F →+* F) s y
  have htor : ∀ (c : F) (hc : c ≠ 0) (t : F),
      ψ (JonesParshall.uMat (c ^ 2 * t)) =
        kFormAct τ hτ3 (tMat c hc) (ψ (JonesParshall.uMat t)) := fun c hc t => by
    rw [← tMat_conj c hc t, ← torusHom_mk0 c hc]
    exact heq _ _
  have hcoe : ∀ (x y : ↥(kForm τ)) (i j k : Fin 2),
      ((x + y : ↥(kForm τ)) : Hyp F) i j k = (x : Hyp F) i j k + (y : Hyp F) i j k :=
    fun x y i j k => rfl
  have hadd111 : ∀ s t, (ψ (JonesParshall.uMat (s + t)) : Hyp F) 1 1 1 =
      (ψ (JonesParshall.uMat s) : Hyp F) 1 1 1 +
        (ψ (JonesParshall.uMat t) : Hyp F) 1 1 1 := by
    intro s t
    have h := congrArg (fun x : ↥(kForm τ) => (x : Hyp F) 1 1 1) (hcoc s t)
    rw [h, hcoe, kFormAct_apply, hu111]
  have h111zero : ∀ t, (ψ (JonesParshall.uMat t) : Hyp F) 1 1 1 = 0 := by
    intro t
    refine coordinate_vanishes (φ := fun t => (ψ (JonesParshall.uMat t) : Hyp F) 1 1 1)
      (n := 3 * f) (N := N) hN (by omega)
      (by rw [Nat.card_eq_fintype_card, hF]) ?_ ?_ hab1 t
    · intro x y
      exact hadd111 x y
    · intro c hc u
      have h := torus_coord htor hτq torusExp torusExp_zero torusExp_one c hc u 1 1 1
      rw [show torusExp 1 + (q : ℤ) * torusExp 1 + (q : ℤ) ^ 2 * torusExp 1 =
          -1 - (q : ℤ) - (q : ℤ) ^ 2 by simp [torusExp]; ring] at h
      exact h
  have hadd011 : ∀ s t, (ψ (JonesParshall.uMat (s + t)) : Hyp F) 0 1 1 =
      (ψ (JonesParshall.uMat s) : Hyp F) 0 1 1 +
        (ψ (JonesParshall.uMat t) : Hyp F) 0 1 1 := by
    intro s t
    have h := congrArg (fun x : ↥(kForm τ) => (x : Hyp F) 0 1 1) (hcoc s t)
    rw [h, hcoe, kFormAct_apply, hu011, h111zero t, mul_zero, add_zero]
  have h011zero : ∀ t, (ψ (JonesParshall.uMat t) : Hyp F) 0 1 1 = 0 := by
    intro t
    refine coordinate_vanishes (φ := fun t => (ψ (JonesParshall.uMat t) : Hyp F) 0 1 1)
      (n := 3 * f) (N := N) hN (by omega)
      (by rw [Nat.card_eq_fintype_card, hF]) ?_ ?_ hab2 t
    · intro x y
      exact hadd011 x y
    · intro c hc u
      have h := torus_coord htor hτq torusExp torusExp_zero torusExp_one c hc u 0 1 1
      rw [show torusExp 0 + (q : ℤ) * torusExp 1 + (q : ℤ) ^ 2 * torusExp 1 =
          1 - (q : ℤ) - (q : ℤ) ^ 2 by simp [torusExp]; ring] at h
      exact h
  have hkForm : ∀ (t : F) (i j k : Fin 2),
      (ψ (JonesParshall.uMat t) : Hyp F) k i j =
        (τ : F →+* F) ((ψ (JonesParshall.uMat t) : Hyp F) i j k) :=
    fun t i j k => (ψ (JonesParshall.uMat t)).2 i j k
  have h101zero : ∀ t, (ψ (JonesParshall.uMat t) : Hyp F) 1 0 1 = 0 := by
    intro t
    have h := hkForm t 0 1 1
    rw [h, h011zero t, map_zero]
  have h110zero : ∀ t, (ψ (JonesParshall.uMat t) : Hyp F) 1 1 0 = 0 := by
    intro t
    have h := hkForm t 1 0 1
    rw [h, h101zero t, map_zero]
  have hadd001 : ∀ s t, (ψ (JonesParshall.uMat (s + t)) : Hyp F) 0 0 1 =
      (ψ (JonesParshall.uMat s) : Hyp F) 0 0 1 +
        (ψ (JonesParshall.uMat t) : Hyp F) 0 0 1 := by
    intro s t
    have h := congrArg (fun x : ↥(kForm τ) => (x : Hyp F) 0 0 1) (hcoc s t)
    rw [h, hcoe, kFormAct_apply, hu001, h101zero t, h011zero t, h111zero t]
    simp
  have h001zero : ∀ t, (ψ (JonesParshall.uMat t) : Hyp F) 0 0 1 = 0 := by
    intro t
    refine coordinate_vanishes (φ := fun t => (ψ (JonesParshall.uMat t) : Hyp F) 0 0 1)
      (n := 3 * f) (N := N) hN (by omega)
      (by rw [Nat.card_eq_fintype_card, hF]) ?_ ?_ hab3 t
    · intro x y
      exact hadd001 x y
    · intro c hc u
      have h := torus_coord htor hτq torusExp torusExp_zero torusExp_one c hc u 0 0 1
      rw [show torusExp 0 + (q : ℤ) * torusExp 0 + (q : ℤ) ^ 2 * torusExp 1 =
          1 + (q : ℤ) - (q : ℤ) ^ 2 by simp [torusExp]; ring] at h
      exact h
  have h100zero : ∀ t, (ψ (JonesParshall.uMat t) : Hyp F) 1 0 0 = 0 := by
    intro t
    have h := hkForm t 0 0 1
    rw [h, h001zero t, map_zero]
  have h010zero : ∀ t, (ψ (JonesParshall.uMat t) : Hyp F) 0 1 0 = 0 := by
    intro t
    have h := hkForm t 1 0 0
    rw [h, h100zero t, map_zero]
  have hadd000 : ∀ s t, (ψ (JonesParshall.uMat (s + t)) : Hyp F) 0 0 0 =
      (ψ (JonesParshall.uMat s) : Hyp F) 0 0 0 +
        (ψ (JonesParshall.uMat t) : Hyp F) 0 0 0 := by
    intro s t
    have h := congrArg (fun x : ↥(kForm τ) => (x : Hyp F) 0 0 0) (hcoc s t)
    rw [h, hcoe, kFormAct_apply, hu000, h100zero t, h010zero t, h110zero t,
      h001zero t, h101zero t, h011zero t, h111zero t]
    simp
  have h000zero : ∀ t, (ψ (JonesParshall.uMat t) : Hyp F) 0 0 0 = 0 := by
    intro t
    refine coordinate_vanishes (φ := fun t => (ψ (JonesParshall.uMat t) : Hyp F) 0 0 0)
      (n := 3 * f) (N := N) hN (by omega)
      (by rw [Nat.card_eq_fintype_card, hF]) ?_ ?_ hab4 t
    · intro x y
      exact hadd000 x y
    · intro c hc u
      have h := torus_coord htor hτq torusExp torusExp_zero torusExp_one c hc u 0 0 0
      rw [show torusExp 0 + (q : ℤ) * torusExp 0 + (q : ℤ) ^ 2 * torusExp 0 =
          1 + (q : ℤ) + (q : ℤ) ^ 2 by simp [torusExp]] at h
      exact h
  intro t
  apply Subtype.ext
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [h111zero t, h011zero t, h101zero t, h110zero t,
      h001zero t, h100zero t, h010zero t, h000zero t]

theorem mem_B1A_kFormAct {K F : Type} [Field K] [Field F] [Fintype F] [CharP F 2]
    [Algebra K F] {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ (3 * f))
    (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ 2 ^ f) (hτ3 : ∀ a, τ (τ (τ a)) = a)
    {φ : SL(2, F) → ↥(kForm τ)} (hφ : φ ∈ Z1A (kFormAct τ hτ3)) :
    φ ∈ B1A (kFormAct τ hτ3) := by
  classical
  have h2 : ∀ m : ↥(kForm τ), m + m = 0 := fun m => by
    apply Subtype.ext
    funext i j k
    exact CharTwo.add_self_eq_zero (m.1 i j k)
  have hodd : Odd (Fintype.card Fˣ) := by
    rw [Fintype.card_units, hF]
    obtain ⟨k, hk⟩ : ∃ k, 3 * f = k + 1 := ⟨3 * f - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k - 1, by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega⟩
  obtain ⟨ψ, hψ, hφψ, heq⟩ :=
    exists_equivariant (μ := kFormAct τ hτ3) (torusHom (F := F)) hodd h2 hφ
  suffices hψB : ψ ∈ B1A (kFormAct τ hτ3) by
    have := add_mem hφψ hψB
    rwa [sub_add_cancel] at this
  have hvan := unipotent_vanishes hf hF τ hτ hτ3 hψ heq
  refine mem_B1A_of_vanish h2 (odd_index_stab_e1 (n := 3 * f) hF (by omega)) hψ ?_
  intro g hg
  rw [eq_uMat_of_mem_stab hg]
  exact hvan _

theorem mem_B1_of_kFormAct {K F : Type} [Field K] [Field F] [Fintype F] [CharP F 2]
    [Algebra K F] {Γ W : Type*} [Group Γ] [AddCommGroup W] [Module (ZMod 2) W]
    {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ (3 * f)) (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ 2 ^ f) (hτ3 : ∀ a, τ (τ (τ a)) = a)
    (ρ : Representation (ZMod 2) Γ W) (θ : Γ ≃* SL(2, F)) (σ : F ≃+* F)
    (β : W ≃+ ↥(kForm τ))
    (hβ : ∀ γ w, β (ρ γ w) = kFormAct τ hτ3 (D2.slMap σ (θ γ)) (β w))
    {φ : Γ → W} (hφ : φ ∈ Z1 ρ) : φ ∈ B1 ρ := by
  let s : SL(2, F) ≃* SL(2, F) :=
    { toFun := D2.slMap σ
      invFun := D2.slMap σ.symm
      left_inv := fun g => by simpa using D2.slMap_symm_apply σ.symm g
      right_inv := fun g => D2.slMap_symm_apply σ g
      map_mul' := map_mul (D2.slMap σ) }
  have hβ' : ∀ γ w, β (ρ γ w) = kFormAct τ hτ3 ((θ.trans s) γ) (β w) := by
    intro γ w
    change β (ρ γ w) = kFormAct τ hτ3 (D2.slMap σ (θ γ)) (β w)
    exact hβ γ w
  have hZ : transportFun (θ.trans s) β φ ∈ Z1A (kFormAct τ hτ3) :=
    (transport_mem_Z1A (ρ := ρ) (μ := kFormAct τ hτ3) (θ := θ.trans s) (β := β)
      hβ').mpr hφ
  have hB : transportFun (θ.trans s) β φ ∈ B1A (kFormAct τ hτ3) :=
    mem_B1A_kFormAct hf hF τ hτ hτ3 hZ
  exact (transport_mem_B1A (ρ := ρ) (μ := kFormAct τ hτ3) (θ := θ.trans s) (β := β)
    hβ').mp hB

theorem finrank_H1_eq_zero_of_kFormAct {K F : Type} [Field K] [Field F] [Fintype F]
    [CharP F 2] [Algebra K F] {Γ W : Type*} [Group Γ] [AddCommGroup W]
    [Module (ZMod 2) W] {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ (3 * f))
    (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ 2 ^ f) (hτ3 : ∀ a, τ (τ (τ a)) = a)
    (ρ : Representation (ZMod 2) Γ W) (θ : Γ ≃* SL(2, F)) (σ : F ≃+* F)
    (β : W ≃+ ↥(kForm τ))
    (hβ : ∀ γ w, β (ρ γ w) = kFormAct τ hτ3 (D2.slMap σ (θ γ)) (β w)) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  have hZ : Z1 ρ = B1 ρ := by
    ext φ
    exact ⟨fun hφ => mem_B1_of_kFormAct hf hF τ hτ hτ3 ρ θ σ β hβ hφ,
      fun hφ => B1_le_Z1 ρ hφ⟩
  have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  apply finrank_H1_of_card
  have hcard := card_H1_mul ρ
  rw [hZ] at hcard
  have hBpos : 0 < Nat.card (B1 ρ) := Nat.card_pos
  have hH : Nat.card (H1 ρ) = 1 := by
    have h' : Nat.card (H1 ρ) * Nat.card (B1 ρ) = 1 * Nat.card (B1 ρ) := by
      simpa using hcard
    exact Nat.eq_of_mul_eq_mul_right hBpos h'
  rw [hH, pow_zero]

end CFSG.Quasithin.F112R.St84

end
