module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFBase

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

@[expose] def twistM {j n : ℕ} (f : (Fin j → ZMod 2) →+ ZMod 2) (w₀ : Fin j → ZMod 2)
    (Y : Fin j → Fin n → ZMod 2) : Fin j → Fin n → ZMod 2 :=
  Y + tens (∑ i, f (Pi.single i 1) • Y i) w₀

theorem fnl_apply_nsbftw {j : ℕ} (f : (Fin j → ZMod 2) →+ ZMod 2) (x : Fin j → ZMod 2) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  have hsc : ∀ (i : Fin j) (c : ZMod 2), f (Pi.single i c) = c * f (Pi.single i 1) := by
    intro i c
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · simp
    · simp
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => hsc i (x i)

theorem tens_smul_right_nsbftw {j n : ℕ} (a : Fin n → ZMod 2) (c : ZMod 2) (w : Fin j → ZMod 2) :
    tens a (c • w) = tens (c • a) w := by
  funext i
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  rw [mul_smul]
  rw [smul_comm]

theorem twistM_add {j n : ℕ} (f : (Fin j → ZMod 2) →+ ZMod 2) (w₀ : Fin j → ZMod 2)
    (Y Y' : Fin j → Fin n → ZMod 2) :
    twistM f w₀ (Y + Y') = twistM f w₀ Y + twistM f w₀ Y' := by
  unfold twistM
  have h : ∑ i, f (Pi.single i 1) • (Y + Y') i =
      ∑ i, f (Pi.single i 1) • Y i + ∑ i, f (Pi.single i 1) • Y' i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [smul_add]
  rw [h, tens_add_left]
  abel

theorem twistM_zero {j n : ℕ} (f : (Fin j → ZMod 2) →+ ZMod 2) (w₀ : Fin j → ZMod 2) :
    twistM f w₀ (0 : Fin j → Fin n → ZMod 2) = 0 := by
  unfold twistM
  simp [tens_zero_left]

theorem twistM_tens {j n : ℕ} (f : (Fin j → ZMod 2) →+ ZMod 2) (w₀ : Fin j → ZMod 2)
    (a : Fin n → ZMod 2) (x : Fin j → ZMod 2) :
    twistM f w₀ (tens a x) = tens a (x + f x • w₀) := by
  unfold twistM
  have h : ∑ i, f (Pi.single i 1) • tens a x i = f x • a := by
    rw [fnl_apply_nsbftw f x, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [tens, smul_smul]
    rw [mul_comm]
  rw [h, tens_add_right, tens_smul_right_nsbftw]

theorem twistM_def {j n : ℕ} (f : (Fin j → ZMod 2) →+ ZMod 2) (w₀ : Fin j → ZMod 2)
    (Y : Fin j → Fin n → ZMod 2) :
    twistM f w₀ Y = Y + tens (∑ i, f (Pi.single i 1) • Y i) w₀ := rfl

theorem twistM_twistM {j n : ℕ} (f : (Fin j → ZMod 2) →+ ZMod 2) {w₀ : Fin j → ZMod 2}
    (hf : f w₀ = 0) (Y : Fin j → Fin n → ZMod 2) :
    twistM f w₀ (twistM f w₀ Y) = Y := by
  have hsum : ∑ i, f (Pi.single i 1) • twistM f w₀ Y i = ∑ i, f (Pi.single i 1) • Y i := by
    have h1 : ∀ i, twistM f w₀ Y i = Y i + w₀ i • ∑ i', f (Pi.single i' 1) • Y i' := by
      intro i
      simp [twistM, tens]
    simp only [h1, smul_add, Finset.sum_add_distrib]
    have h2 : ∑ i, f (Pi.single i 1) • (w₀ i • ∑ i', f (Pi.single i' 1) • Y i') =
        f w₀ • ∑ i', f (Pi.single i' 1) • Y i' := by
      rw [fnl_apply_nsbftw f w₀, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm]
    rw [h2, hf, zero_smul, add_zero]
  rw [twistM_def f w₀ (twistM f w₀ Y), hsum, twistM_def f w₀ Y, add_assoc, tm_add_self, add_zero]

theorem twistM_actM {j n : ℕ} (f : (Fin j → ZMod 2) →+ ZMod 2) (w₀ : Fin j → ZMod 2)
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) (Y : Fin j → Fin n → ZMod 2) :
    twistM f w₀ (actM B Y) = actM B (twistM f w₀ Y) := by
  unfold twistM
  rw [actM_add, actM_tens]
  congr 2
  simp only [actM, Matrix.mulVec_sum, Matrix.mulVec_smul]

end CFSG.Quasithin.H13.Ch4.NSB
