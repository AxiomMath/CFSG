module

public import CFSG.RankThree.PartOne.SEITZ2.G2F2Close
public import CFSG.RankThree.PartOne.SEITZ2.G2F2CaseA

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
open scoped commutatorElement Matrix

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem core_cases {k : Subfield K} (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hK : Nat.card K = Nat.card k ^ d) {H : Subgroup (adjointGroup .G2 K)}
    (hRH : ∀ p < 12, ∀ c ∈ k, xp p c ∈ H) {c : ℕ → K} (hc1 : c 1 = 0) {μ : K} (hμk : μ ∉ k)
    (hy : ordProd c * xp 10 μ * (ordProd c)⁻¹ ∈ H) : H = ⊤ := by
  have hμ0 : μ ≠ 0 := fun h => hμk (h ▸ k.zero_mem)
  have hμ1 : μ ≠ 1 := fun h => hμk (h ▸ k.one_mem)
  obtain ⟨hw0, hw1⟩ := weyl_mem_of_rational hRH
  have fin3 : Full H 3 → H = ⊤ := fun h3 =>
    eq_top_of_full_seven_f2 hRH (h3.conj e0 (by norm_num) reflect_3' hw0) hμ0 hμ1
  have caseA : ∀ {c : ℕ → K}, c 1 = 0 → ordProd c * xp 10 μ * (ordProd c)⁻¹ ∈ H →
      ¬ (c 0 ∈ k ∧ c 4 ∈ k) → H = ⊤ := fun hc1 hy hirr =>
    fin3 (caseA_full_three hk hd hd2 hK hRH hc1 hμ0 hy hirr)
  by_cases hA : ¬ (c 0 ∈ k ∧ c 4 ∈ k)
  · exact caseA hc1 hy hA
  by_cases hA' : ¬ (c 3 ∈ k ∧ c 8 ∈ k)
  · have hy' : ordProd (mk6 (c 3) 0 (c 8) (c 4) (c 0) (c 7 + c 4 * c 8 + c 0 * c 3)) *
        xp 10 μ * (ordProd (mk6 (c 3) 0 (c 8) (c 4) (c 0) (c 7 + c 4 * c 8 + c 0 * c 3)))⁻¹ ∈
          H := by
      have h := H.mul_mem (H.mul_mem hw1 hy) (H.inv_mem hw1)
      rwa [show weylElement .G2 K e1 * (ordProd c * xp 10 μ * (ordProd c)⁻¹) *
          (weylElement .G2 K e1)⁻¹ = (weylElement .G2 K e1 * ordProd c * (weylElement .G2 K e1)⁻¹) *
            (weylElement .G2 K e1 * xp 10 μ * (weylElement .G2 K e1)⁻¹) *
              (weylElement .G2 K e1 * ordProd c * (weylElement .G2 K e1)⁻¹)⁻¹ by group,
        n1_conj_ordProd c hc1, weylElement_conj_xp e1 (by norm_num) rf_e1_10] at h
    exact caseA (by simp [mk6]) hy' (by simpa [mk6] using hA')
  push Not at hA hA'
  obtain ⟨hc0k, hc4k⟩ := hA
  obtain ⟨hc3k, hc8k⟩ := hA'
  set q0 : adjointGroup .G2 K := xp 0 (c 0) * xp 4 (c 4) * xp 8 (c 8) * xp 3 (c 3) with hq0def
  have hq0 : q0 ∈ H := H.mul_mem (H.mul_mem (H.mul_mem (hRH 0 (by norm_num) _ hc0k)
    (hRH 4 (by norm_num) _ hc4k)) (hRH 8 (by norm_num) _ hc8k)) (hRH 3 (by norm_num) _ hc3k)
  have hP : ordProd c = q0 * xp 7 (c 7) := by
    simp only [ordProd, hc1, xp_zero, mul_one, hq0def]
  have hy1 : xp 7 (c 7) * xp 10 μ * (xp 7 (c 7))⁻¹ ∈ H := by
    have h := H.mul_mem (H.mul_mem (H.inv_mem hq0) hy) hq0
    rwa [hP, show q0⁻¹ * (q0 * xp 7 (c 7) * xp 10 μ * (q0 * xp 7 (c 7))⁻¹) * q0 =
      xp 7 (c 7) * xp 10 μ * (xp 7 (c 7))⁻¹ by group] at h
  by_cases h7k : c 7 ∈ k
  · have h7 : xp 7 (c 7) ∈ H := hRH 7 (by norm_num) _ h7k
    have h10 : xp 10 μ ∈ H := by
      have h := H.mul_mem (H.mul_mem (H.inv_mem h7) hy1) h7
      rwa [show (xp 7 (c 7))⁻¹ * (xp 7 (c 7) * xp 10 μ * (xp 7 (c 7))⁻¹) * xp 7 (c 7) =
        xp 10 μ by group] at h
    exact eq_top_of_full_seven_f2 hRH
      (full_seven_of_full_ten hw0 hw1 (full_ten_of_irrational hk hd hK hRH hμk h10)) hμ0 hμ1
  · have h6 : xp 6 (1 : K) ∈ H := hRH 6 (by norm_num) 1 k.one_mem
    have hy2 := H.mul_mem (H.mul_mem h6 hy1) (H.inv_mem h6)
    have e : xp 6 1 * (xp 7 (c 7) * xp 10 μ * (xp 7 (c 7))⁻¹) * (xp 6 1)⁻¹ =
        ordProd (mk6 (c 7) 0 0 0 0 (c 7)) * xp 10 μ * (ordProd (mk6 (c 7) 0 0 0 0 (c 7)))⁻¹ := by
      rw [ordProd_mk6]
      simp only [xp_zero, mul_one]
      rw [show xp 6 1 * (xp 7 (c 7) * xp 10 μ * (xp 7 (c 7))⁻¹) * (xp 6 1)⁻¹ =
        (xp 6 1 * xp 7 (c 7) * (xp 6 1)⁻¹) * (xp 6 1 * xp 10 μ * (xp 6 1)⁻¹) *
          (xp 6 1 * xp 7 (c 7) * (xp 6 1)⁻¹)⁻¹ by group, x6_conj_x7, (commute_6_10 1 μ).eq]
      group
    rw [e] at hy2
    exact caseA (by simp [mk6]) hy2 (by simpa [mk6] using h7k)

end CFSG.RankThree.PartOne.SEITZ2
