module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_pow_two_eq_of_le_of_lt_two_mul {k m : ℕ} (h1 : 2 ^ k ≤ 2 ^ m)
    (h2 : 2 ^ m < 2 * 2 ^ k) : 2 ^ k = 2 ^ m := by
  rcases lt_trichotomy k m with h | h | h
  · have h3 : 2 ^ (k + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    rw [pow_succ] at h3
    have h3' : 2 * 2 ^ k ≤ 2 ^ m := by rw [mul_comm]; exact h3
    omega
  · rw [h]
  · have h3 : 2 ^ m < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) h
    omega

theorem str86_two_dvd_sub_one {k m : ℕ} (hk : 2 ≤ k) (hdvd : 2 ^ m - 1 ∣ 2 ^ k - 1)
    (hle : (2 ^ k) ^ 2 ≤ 2 ^ m) : False := by
  have hq2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hlt : 2 ^ k < (2 ^ k) ^ 2 := by nlinarith
  have hlt' : 2 ^ k < 2 ^ m := lt_of_lt_of_le hlt hle
  have hpos : 0 < 2 ^ k - 1 := by omega
  have hle' : 2 ^ m - 1 ≤ 2 ^ k - 1 := Nat.le_of_dvd hpos hdvd
  omega

theorem str86_two_dvd_add_one {k m : ℕ} (hk : 2 ≤ k) (hdvd : 2 ^ m - 1 ∣ 2 ^ k + 1)
    (hle : 2 ^ k ≤ 2 ^ m) (hlt : 2 ^ m < 2 * 2 ^ k) : False := by
  have heq : 2 ^ k = 2 ^ m := str86_pow_two_eq_of_le_of_lt_two_mul hle hlt
  have hq2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hq1 : 1 ≤ 2 ^ k := by omega
  have hdvd' : 2 ^ k - 1 ∣ 2 ^ k + 1 := by rw [← heq] at hdvd; exact hdvd
  have h2 : 2 ^ k - 1 ∣ 2 := by
    have h := Nat.dvd_sub hdvd' (dvd_refl (2 ^ k - 1))
    rwa [show 2 ^ k + 1 - (2 ^ k - 1) = 2 by omega] at h
  have hle2 : 2 ^ k - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have hge : 3 ≤ 2 ^ k - 1 := by
    have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    omega
  omega

theorem commutator_mul_eq (s k x : G) :
    ⁅s * k, x⁆ = s * ⁅k, x⁆ * s⁻¹ * ⁅s, x⁆ := by
  simp only [commutatorElement_def]
  group

theorem isChiefSeriesFrom_zero_of_le_centralizer {H U N : Subgroup G}
    (hHN : H ≤ Subgroup.centralizer (N : Set G)) {n : ℕ}
    (h : IsChiefSeriesFrom H U N n) : n = 0 := by
  revert hHN
  induction h with
  | bot => intro _; rfl
  | central hstep _ _ ih =>
    intro hHN
    exact ih (hHN.trans (Subgroup.centralizer_le hstep.2.2.1.le))
  | noncentral hstep hnc _ _ =>
    intro hHN
    refine absurd ?_ hnc
    intro g hg x hx
    have hcomm : g * x = x * g :=
      (Subgroup.mem_centralizer_iff.mp (hHN hg) x hx).symm
    have h1 : g * x * g⁻¹ * x⁻¹ = 1 := by rw [hcomm]; group
    rw [h1]
    exact Subgroup.one_mem _

end CFSG.Quasithin.Stroth
