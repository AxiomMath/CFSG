module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Unitary.Model
import all CFSG.Fischer.F4
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary
open CFSG.Fischer
open CFSG.Blueprint.Fischer (K)

private noncomputable def vecF4 {n : ℕ} (x : Fin n → F4) : Fin n → K :=
  fun i => eF4 (x i)

private noncomputable def padF4 {k : ℕ} (x : Fin 5 → F4) : Fin (5 + k) → K :=
  vecF4 (Fin.append x fun _ => 0)

private theorem herm_vecF4 {n : ℕ} (x y : Fin n → F4) :
    herm frob (vecF4 x) (vecF4 y) = eF4 (∑ i : Fin n, x i * x i * y i) := by
  rw [herm_def]
  simp only [vecF4]
  have h : ∀ i, frob (eF4 (x i)) * eF4 (y i) = eF4 (x i * x i * y i) := fun i => by
    rw [frob_eF4, pow_two, ← map_mul]
  simp only [h]
  rw [← map_sum]

private theorem herm_padF4 {k : ℕ} (x y : Fin 5 → F4) :
    herm frob (padF4 (k := k) x) (padF4 (k := k) y) =
      eF4 (∑ i : Fin 5, x i * x i * y i) := by
  simp only [padF4]
  rw [herm_vecF4, Fin.sum_univ_add]
  have hzero : (∑ i : Fin k,
      Fin.append x (fun _ : Fin k => 0) (Fin.natAdd 5 i) *
        Fin.append x (fun _ : Fin k => 0) (Fin.natAdd 5 i) *
        Fin.append y (fun _ : Fin k => 0) (Fin.natAdd 5 i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [Fin.append_right, Fin.append_right]
    simp
  rw [hzero, add_zero, eF4_inj]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.append_left, Fin.append_left]

private theorem herm_padF4_eq {k : ℕ} (x y : Fin 5 → F4) (c : F4)
    (h : (∑ i : Fin 5, x i * x i * y i) = c) :
    herm frob (padF4 (k := k) x) (padF4 (k := k) y) = eF4 c := by
  rw [herm_padF4, h]

private theorem padF4_add_smul {k : ℕ} (x y : Fin 5 → F4) (c : F4) :
    padF4 (k := k) x + eF4 c • padF4 (k := k) y =
      padF4 (k := k) (x + c • y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [padF4, vecF4, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.append_left,
      map_add, map_mul]
  · simp only [padF4, vecF4, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.append_right,
      map_zero]
    simp

private theorem eF4_ne_zero_of_ne_zero {c : F4} (hc : c ≠ 0) : eF4 c ≠ 0 := by
  rw [Ne, ← map_zero eF4, eF4_inj]
  exact hc

private abbrev fiveA : Fin 5 → F4 := ![0, 0, 0, 1, 1]

private abbrev fiveB : Fin 5 → F4 := ![0, 0, 1, 0, 1]

private abbrev fiveC : Fin 5 → F4 := ![0, 0, 0, 1, F4.ω]

private abbrev fiveD : Fin 5 → F4 := ![1, 1, 1, 0, 1]

private abbrev fiveAC : Fin 5 → F4 := ![0, 0, 0, F4.ω * F4.ω, F4.ω]

private abbrev fiveBA : Fin 5 → F4 := ![0, 0, 1, 1, 0]

private abbrev fiveDC : Fin 5 → F4 := ![F4.ω, F4.ω, F4.ω, 1, 0]

private theorem herm_fiveA_self {k : ℕ} :
    herm frob (padF4 (k := k) fiveA) (padF4 (k := k) fiveA) = 0 := by
  rw [herm_padF4_eq fiveA fiveA 0 (by decide), map_zero]

private theorem herm_fiveB_self {k : ℕ} :
    herm frob (padF4 (k := k) fiveB) (padF4 (k := k) fiveB) = 0 := by
  rw [herm_padF4_eq fiveB fiveB 0 (by decide), map_zero]

private theorem herm_fiveC_self {k : ℕ} :
    herm frob (padF4 (k := k) fiveC) (padF4 (k := k) fiveC) = 0 := by
  rw [herm_padF4_eq fiveC fiveC 0 (by decide), map_zero]

private theorem herm_fiveD_self {k : ℕ} :
    herm frob (padF4 (k := k) fiveD) (padF4 (k := k) fiveD) = 0 := by
  rw [herm_padF4_eq fiveD fiveD 0 (by decide), map_zero]

private theorem herm_fiveA_fiveB {k : ℕ} :
    herm frob (padF4 (k := k) fiveA) (padF4 (k := k) fiveB) = eF4 1 :=
  herm_padF4_eq fiveA fiveB 1 (by decide)

private theorem herm_fiveA_fiveC {k : ℕ} :
    herm frob (padF4 (k := k) fiveA) (padF4 (k := k) fiveC) = eF4 (F4.ω * F4.ω) :=
  herm_padF4_eq fiveA fiveC (F4.ω * F4.ω) (by decide)

private theorem herm_fiveA_fiveD {k : ℕ} :
    herm frob (padF4 (k := k) fiveA) (padF4 (k := k) fiveD) = eF4 1 :=
  herm_padF4_eq fiveA fiveD 1 (by decide)

private theorem herm_fiveB_fiveC {k : ℕ} :
    herm frob (padF4 (k := k) fiveB) (padF4 (k := k) fiveC) = eF4 F4.ω :=
  herm_padF4_eq fiveB fiveC F4.ω (by decide)

private theorem herm_fiveB_fiveD {k : ℕ} :
    herm frob (padF4 (k := k) fiveB) (padF4 (k := k) fiveD) = 0 := by
  rw [herm_padF4_eq fiveB fiveD 0 (by decide), map_zero]

private theorem herm_fiveC_fiveD {k : ℕ} :
    herm frob (padF4 (k := k) fiveC) (padF4 (k := k) fiveD) = eF4 (F4.ω * F4.ω) :=
  herm_padF4_eq fiveC fiveD (F4.ω * F4.ω) (by decide)

private theorem herm_fiveC_fiveA {k : ℕ} :
    herm frob (padF4 (k := k) fiveC) (padF4 (k := k) fiveA) = eF4 F4.ω :=
  herm_padF4_eq fiveC fiveA F4.ω (by decide)

private theorem herm_fiveB_fiveA {k : ℕ} :
    herm frob (padF4 (k := k) fiveB) (padF4 (k := k) fiveA) = eF4 1 :=
  herm_padF4_eq fiveB fiveA 1 (by decide)

private theorem herm_fiveD_fiveC {k : ℕ} :
    herm frob (padF4 (k := k) fiveD) (padF4 (k := k) fiveC) = eF4 F4.ω :=
  herm_padF4_eq fiveD fiveC F4.ω (by decide)

private theorem herm_fiveAC_fiveB {k : ℕ} :
    herm frob (padF4 (k := k) fiveAC) (padF4 (k := k) fiveB) = eF4 (F4.ω * F4.ω) :=
  herm_padF4_eq fiveAC fiveB (F4.ω * F4.ω) (by decide)

private theorem herm_fiveAC_fiveD {k : ℕ} :
    herm frob (padF4 (k := k) fiveAC) (padF4 (k := k) fiveD) = eF4 (F4.ω * F4.ω) :=
  herm_padF4_eq fiveAC fiveD (F4.ω * F4.ω) (by decide)

private theorem herm_fiveBA_fiveDC {k : ℕ} :
    herm frob (padF4 (k := k) fiveBA) (padF4 (k := k) fiveDC) = eF4 (F4.ω * F4.ω) :=
  herm_padF4_eq fiveBA fiveDC (F4.ω * F4.ω) (by decide)

private theorem herm_fiveAC_self {k : ℕ} :
    herm frob (padF4 (k := k) fiveAC) (padF4 (k := k) fiveAC) = 0 := by
  rw [herm_padF4_eq fiveAC fiveAC 0 (by decide), map_zero]

private theorem herm_fiveBA_self {k : ℕ} :
    herm frob (padF4 (k := k) fiveBA) (padF4 (k := k) fiveBA) = 0 := by
  rw [herm_padF4_eq fiveBA fiveBA 0 (by decide), map_zero]

private theorem herm_fiveDC_self {k : ℕ} :
    herm frob (padF4 (k := k) fiveDC) (padF4 (k := k) fiveDC) = 0 := by
  rw [herm_padF4_eq fiveDC fiveDC 0 (by decide), map_zero]

private theorem herm_fiveA_fiveB_ne_zero {k : ℕ} :
    herm frob (padF4 (k := k) fiveA) (padF4 (k := k) fiveB) ≠ 0 := by
  rw [herm_fiveA_fiveB, map_one]
  exact one_ne_zero

private theorem herm_fiveA_fiveC_ne_zero {k : ℕ} :
    herm frob (padF4 (k := k) fiveA) (padF4 (k := k) fiveC) ≠ 0 := by
  rw [herm_fiveA_fiveC]
  exact eF4_ne_zero_of_ne_zero (by decide : F4.ω * F4.ω ≠ 0)

private theorem herm_fiveA_fiveD_ne_zero {k : ℕ} :
    herm frob (padF4 (k := k) fiveA) (padF4 (k := k) fiveD) ≠ 0 := by
  rw [herm_fiveA_fiveD, map_one]
  exact one_ne_zero

private theorem herm_fiveB_fiveC_ne_zero {k : ℕ} :
    herm frob (padF4 (k := k) fiveB) (padF4 (k := k) fiveC) ≠ 0 := by
  rw [herm_fiveB_fiveC]
  exact eF4_ne_zero_of_ne_zero (by decide : F4.ω ≠ 0)

private theorem herm_fiveC_fiveD_ne_zero {k : ℕ} :
    herm frob (padF4 (k := k) fiveC) (padF4 (k := k) fiveD) ≠ 0 := by
  rw [herm_fiveC_fiveD]
  exact eF4_ne_zero_of_ne_zero (by decide : F4.ω * F4.ω ≠ 0)

private theorem herm_fiveAC_fiveB_ne_zero {k : ℕ} :
    herm frob (padF4 (k := k) fiveAC) (padF4 (k := k) fiveB) ≠ 0 := by
  rw [herm_fiveAC_fiveB]
  exact eF4_ne_zero_of_ne_zero (by decide : F4.ω * F4.ω ≠ 0)

private theorem herm_fiveAC_fiveD_ne_zero {k : ℕ} :
    herm frob (padF4 (k := k) fiveAC) (padF4 (k := k) fiveD) ≠ 0 := by
  rw [herm_fiveAC_fiveD]
  exact eF4_ne_zero_of_ne_zero (by decide : F4.ω * F4.ω ≠ 0)

private theorem herm_fiveBA_fiveDC_ne_zero {k : ℕ} :
    herm frob (padF4 (k := k) fiveBA) (padF4 (k := k) fiveDC) ≠ 0 := by
  rw [herm_fiveBA_fiveDC]
  exact eF4_ne_zero_of_ne_zero (by decide : F4.ω * F4.ω ≠ 0)

private theorem fiveD_not_proportional_fiveB {k : ℕ} :
    ¬ ∃ c : K, padF4 (k := k) fiveD = c • padF4 (k := k) fiveB := by
  rintro ⟨c, hc⟩
  have h0 : eF4 (fiveD ⟨0, by omega⟩) = c * eF4 (fiveB ⟨0, by omega⟩) := by
    simpa only [padF4, vecF4, Pi.smul_apply, smul_eq_mul, Fin.append_left] using
      congrFun hc (Fin.castAdd k ⟨0, by omega⟩)
  simp [fiveD, fiveB] at h0

private theorem tvU_fiveC_smul_fiveA {k : ℕ}
    (hc : herm frob (padF4 (k := k) fiveC) (padF4 (k := k) fiveC) = 0) :
    tvU (padF4 (k := k) fiveC) • padF4 (k := k) fiveA =
      padF4 (k := k) fiveAC := by
  rw [tvU_smul hc, herm_fiveC_fiveA, padF4_add_smul]
  apply congrArg (padF4 (k := k))
  decide

private theorem tvU_fiveB_smul_fiveA {k : ℕ}
    (hb : herm frob (padF4 (k := k) fiveB) (padF4 (k := k) fiveB) = 0) :
    tvU (padF4 (k := k) fiveB) • padF4 (k := k) fiveA =
      padF4 (k := k) fiveBA := by
  rw [tvU_smul hb, herm_fiveB_fiveA, padF4_add_smul]
  apply congrArg (padF4 (k := k))
  decide

private theorem tvU_fiveD_smul_fiveC {k : ℕ}
    (hd : herm frob (padF4 (k := k) fiveD) (padF4 (k := k) fiveD) = 0) :
    tvU (padF4 (k := k) fiveD) • padF4 (k := k) fiveC =
      padF4 (k := k) fiveDC := by
  rw [tvU_smul hd, herm_fiveD_fiveC, padF4_add_smul]
  apply congrArg (padF4 (k := k))
  decide

private theorem tqU_mul_self_of_isotropic {m : ℕ} {x : Fin m → K} (hx : herm frob x x = 0) :
    tqU x * tqU x = 1 := by
  change (u2Equiv m).symm (tq x) * (u2Equiv m).symm (tq x) = 1
  rw [← map_mul, tq_mul_self hx, map_one]

private theorem orderOf_tqU_mul_tqU_mem {m : ℕ} {x y : Fin m → K}
    (hx : herm frob x x = 0) (hy : herm frob y y = 0) :
    orderOf (tqU x * tqU y) ∈ ({1, 2, 3} : Set ℕ) := by
  have e : orderOf (tqU x * tqU y) = orderOf (tq x * tq y) := by
    change orderOf ((u2Equiv m).symm (tq x) * (u2Equiv m).symm (tq y)) = _
    rw [← map_mul, MulEquiv.orderOf_eq]
  rw [e]
  exact orderOf_tq_mul_tq_mem hx hy

private theorem orderOf_tqU_mul_tqU_eq_three {m : ℕ} (hm : 3 ≤ m) {x y : Fin m → K}
    (hx0 : x ≠ 0) (hx : herm frob x x = 0) (hy0 : y ≠ 0) (hy : herm frob y y = 0)
    (hxy : herm frob x y ≠ 0) : orderOf (tqU x * tqU y) = 3 := by
  rcases (by simpa using orderOf_tqU_mul_tqU_mem hx hy :
    orderOf (tqU x * tqU y) = 1 ∨ orderOf (tqU x * tqU y) = 2 ∨
      orderOf (tqU x * tqU y) = 3) with h | h | h
  · exfalso
    have h1 : tqU x * tqU y = 1 := orderOf_eq_one_iff.1 h
    have hc : tqU x * tqU y = tqU y * tqU x := by
      rw [h1, eq_inv_of_mul_eq_one_right h1, inv_mul_cancel]
    exact hxy ((tqU_commute_iff hm hx0 hx hy0 hy).1 hc)
  · exfalso
    have h2 : (tqU x * tqU y) ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, h]
    have h2' : (tqU x * tqU y) * (tqU x * tqU y) = 1 := by rwa [pow_two] at h2
    have h2'' : tqU x * tqU y * tqU x * tqU y = 1 := by simpa [mul_assoc] using h2'
    have e1 : tqU x * tqU y * tqU x = tqU y := by
      calc tqU x * tqU y * tqU x = tqU x * tqU y * tqU x * (tqU y * tqU y) := by
            rw [tqU_mul_self_of_isotropic hy, mul_one]
        _ = (tqU x * tqU y * tqU x * tqU y) * tqU y := by group
        _ = 1 * tqU y := by rw [h2'']
        _ = tqU y := by rw [one_mul]
    have hc : tqU x * tqU y = tqU y * tqU x := by
      calc tqU x * tqU y = tqU x * tqU y * (tqU x * tqU x) := by
            rw [tqU_mul_self_of_isotropic hx, mul_one]
        _ = (tqU x * tqU y * tqU x) * tqU x := by group
        _ = tqU y * tqU x := by rw [e1]
    exact hxy ((tqU_commute_iff hm hx0 hx hy0 hy).1 hc)
  · exact h

private theorem orderOf_tqU_mul_tqU_eq_two {m : ℕ} (hm : 3 ≤ m) {x y : Fin m → K}
    (hx0 : x ≠ 0) (hx : herm frob x x = 0) (hy0 : y ≠ 0) (hy : herm frob y y = 0)
    (hxy : herm frob x y = 0) (hnp : ¬ ∃ c : K, y = c • x) :
    orderOf (tqU x * tqU y) = 2 := by
  have hcomm : tqU x * tqU y = tqU y * tqU x :=
    (tqU_commute_iff hm hx0 hx hy0 hy).2 hxy
  have hc : Commute (tqU x) (tqU y) := hcomm
  have h2 : (tqU x * tqU y) ^ 2 = 1 := by
    rw [hc.mul_pow, pow_two (tqU x), pow_two (tqU y), tqU_mul_self_of_isotropic hx,
      tqU_mul_self_of_isotropic hy, one_mul]
  have hdv : orderOf (tqU x * tqU y) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdv with h | h
  · exfalso
    have h1 : tqU x * tqU y = 1 := orderOf_eq_one_iff.1 h
    have heq : tqU x = tqU y := by
      calc tqU x = tqU x * (tqU x * tqU y) := by rw [h1, mul_one]
        _ = tqU y := by rw [← mul_assoc, tqU_mul_self_of_isotropic hx, one_mul]
    exact hnp ((tqU_eq_tqU_iff hm hx0 hx hy0 hy).1 heq)
  · exact h

theorem exists_unitaryFourConfig_DU {m : ℕ} (hm : 5 ≤ m) :
    ∃ a b c d : U2 m, UnitaryFourConfig (DU m) a b c d := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 5 + k := ⟨m - 5, (Nat.add_sub_cancel' hm).symm⟩
  let A : Fin (5 + k) → K := padF4 (k := k) fiveA
  let B : Fin (5 + k) → K := padF4 (k := k) fiveB
  let C : Fin (5 + k) → K := padF4 (k := k) fiveC
  let D : Fin (5 + k) → K := padF4 (k := k) fiveD
  let AC : Fin (5 + k) → K := padF4 (k := k) fiveAC
  let BA : Fin (5 + k) → K := padF4 (k := k) fiveBA
  let DC : Fin (5 + k) → K := padF4 (k := k) fiveDC
  have hAA : herm frob A A = 0 := herm_fiveA_self
  have hBB : herm frob B B = 0 := herm_fiveB_self
  have hCC : herm frob C C = 0 := herm_fiveC_self
  have hDD : herm frob D D = 0 := herm_fiveD_self
  have hBD : herm frob B D = 0 := herm_fiveB_fiveD
  have hACiso : herm frob AC AC = 0 := herm_fiveAC_self
  have hBAiso : herm frob BA BA = 0 := herm_fiveBA_self
  have hDCiso : herm frob DC DC = 0 := herm_fiveDC_self
  have hAB0 : herm frob A B ≠ 0 := herm_fiveA_fiveB_ne_zero
  have hAC0' : herm frob A C ≠ 0 := herm_fiveA_fiveC_ne_zero
  have hAD0 : herm frob A D ≠ 0 := herm_fiveA_fiveD_ne_zero
  have hBC0 : herm frob B C ≠ 0 := herm_fiveB_fiveC_ne_zero
  have hCD0 : herm frob C D ≠ 0 := herm_fiveC_fiveD_ne_zero
  have hACB0 : herm frob AC B ≠ 0 := herm_fiveAC_fiveB_ne_zero
  have hACD0 : herm frob AC D ≠ 0 := herm_fiveAC_fiveD_ne_zero
  have hBADC0 : herm frob BA DC ≠ 0 := herm_fiveBA_fiveDC_ne_zero
  have hA0 : A ≠ 0 := fun h => hAB0 (by rw [h, herm_zero_left])
  have hB0 : B ≠ 0 := fun h => hAB0 (by rw [h, herm_zero_right])
  have hC0 : C ≠ 0 := fun h => hAC0' (by rw [h, herm_zero_right])
  have hD0 : D ≠ 0 := fun h => hAD0 (by rw [h, herm_zero_right])
  have hAC0 : AC ≠ 0 := fun h => hACB0 (by rw [h, herm_zero_left])
  have hBA0 : BA ≠ 0 := fun h => hBADC0 (by rw [h, herm_zero_left])
  have hDC0 : DC ≠ 0 := fun h => hBADC0 (by rw [h, herm_zero_right])
  have hBDnp : ¬ ∃ c : K, D = c • B := fiveD_not_proportional_fiveB
  have oAB : orderOf (tqU A * tqU B) = 3 :=
    orderOf_tqU_mul_tqU_eq_three (by omega) hA0 hAA hB0 hBB hAB0
  have oAC : orderOf (tqU A * tqU C) = 3 :=
    orderOf_tqU_mul_tqU_eq_three (by omega) hA0 hAA hC0 hCC hAC0'
  have oAD : orderOf (tqU A * tqU D) = 3 :=
    orderOf_tqU_mul_tqU_eq_three (by omega) hA0 hAA hD0 hDD hAD0
  have oBC : orderOf (tqU B * tqU C) = 3 :=
    orderOf_tqU_mul_tqU_eq_three (by omega) hB0 hBB hC0 hCC hBC0
  have oCD : orderOf (tqU C * tqU D) = 3 :=
    orderOf_tqU_mul_tqU_eq_three (by omega) hC0 hCC hD0 hDD hCD0
  have oBD : orderOf (tqU B * tqU D) = 2 :=
    orderOf_tqU_mul_tqU_eq_two (by omega) hB0 hBB hD0 hDD hBD hBDnp
  have oCAB : orderOf (tqU C * tqU A * tqU C * tqU B) = 3 := by
    rw [tqU_mul_tqU_mul_tqU hCC hAA, tvU_fiveC_smul_fiveA hCC]
    exact orderOf_tqU_mul_tqU_eq_three (by omega) hAC0 hACiso hB0 hBB hACB0
  have oCAD : orderOf (tqU C * tqU A * tqU C * tqU D) = 3 := by
    rw [tqU_mul_tqU_mul_tqU hCC hAA, tvU_fiveC_smul_fiveA hCC]
    exact orderOf_tqU_mul_tqU_eq_three (by omega) hAC0 hACiso hD0 hDD hACD0
  have oLast : orderOf (tqU B * tqU A * tqU B * (tqU D * tqU C * tqU D)) = 3 := by
    rw [tqU_mul_tqU_mul_tqU hBB hAA, tvU_fiveB_smul_fiveA hBB,
      tqU_mul_tqU_mul_tqU hDD hCC, tvU_fiveD_smul_fiveC hDD]
    exact orderOf_tqU_mul_tqU_eq_three (by omega) hBA0 hBAiso hDC0 hDCiso hBADC0
  refine ⟨tqU A, tqU B, tqU C, tqU D, ?_⟩
  unfold UnitaryFourConfig
  exact ⟨tqU_mem_DU hA0 hAA, tqU_mem_DU hB0 hBB, tqU_mem_DU hC0 hCC,
    tqU_mem_DU hD0 hDD, oAB, oAC, oAD, oBC, oCD, oBD, oCAB, oCAD, Or.inl oLast⟩

end CFSG.StandardType.ZS
