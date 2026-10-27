module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertVec

public section

namespace CFSG.StandardType.StepTwoToralCert

variable {p n : ℕ}

theorem tcEncFrom_lt (hp : 0 < p) (a : Array ℤ) (s k : ℕ) : tcEncFrom p a s k < p ^ k := by
  induction k generalizing s with
  | zero => simp [tcEncFrom]
  | succ k ih =>
    simp only [tcEncFrom, pow_succ]
    have h1 : (tcEnt a s % (p : ℤ)).toNat < p := by
      have h2 : 0 ≤ tcEnt a s % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
      have h3 : tcEnt a s % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
      omega
    have h4 := ih (s + 1)
    nlinarith

theorem tcEnc_lt (hp : 0 < p) (a : Array ℤ) : tcEnc p n a < p ^ n := tcEncFrom_lt hp a 0 n

theorem tcEncFrom_digit (hp : 0 < p) (a : Array ℤ) (s k i : ℕ) (hi : i < k) :
    tcEncFrom p a s k / p ^ i % p = (tcEnt a (s + i) % (p : ℤ)).toNat := by
  induction k generalizing s i with
  | zero => omega
  | succ k ih =>
    simp only [tcEncFrom]
    have h1 : (tcEnt a s % (p : ℤ)).toNat < p := by
      have h2 : 0 ≤ tcEnt a s % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
      have h3 : tcEnt a s % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
      omega
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one, Nat.add_zero]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt h1
    | succ i =>
      have h5 : ((tcEnt a s % (p : ℤ)).toNat + p * tcEncFrom p a (s + 1) k) / p ^ (i + 1) =
          tcEncFrom p a (s + 1) k / p ^ i := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul]
        rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h1, zero_add]
      rw [h5, ih (s + 1) i (by omega)]
      congr 3
      omega

theorem tcEnt_tcDec_tcEnc (hp : 0 < p) (a : Array ℤ) {i : ℕ} (hi : i < n) :
    tcEnt (tcDec p n (tcEnc p n a)) i = tcEnt a i % (p : ℤ) := by
  have h := tcEncFrom_digit hp a 0 n i hi
  simp only [Nat.zero_add] at h
  have hnn : 0 ≤ tcEnt a i % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have : tcEnt (tcDec p n (tcEnc p n a)) i = ((tcEnc p n a / p ^ i % p : ℕ) : ℤ) := by
    simp only [tcDec, tcEnt]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp [hi]
  rw [this, tcEnc, h]
  omega

theorem tcVec_tcDec_tcEnc (hp : 0 < p) (a : Array ℤ) :
    tcVec p n (tcDec p n (tcEnc p n a)) = tcVec p n a := by
  funext i
  simp only [tcVec]
  rw [tcEnt_tcDec_tcEnc hp a i.2, ZMod.intCast_mod]

theorem tcEncFrom_congr (a b : Array ℤ) (s k : ℕ)
    (h : ∀ i, s ≤ i → i < s + k → tcEnt a i % (p : ℤ) = tcEnt b i % (p : ℤ)) :
    tcEncFrom p a s k = tcEncFrom p b s k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [tcEncFrom]
    rw [h s le_rfl (by omega), ih (s + 1) (fun i hi1 hi2 => h i (by omega) (by omega))]

theorem tcEnc_congr {a b : Array ℤ} (h : tcVec p n a = tcVec p n b) :
    tcEnc p n a = tcEnc p n b := by
  apply tcEncFrom_congr
  intro i _ hi
  have := congrFun h ⟨i, by omega⟩
  simp only [tcVec] at this
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this

end CFSG.StandardType.StepTwoToralCert
