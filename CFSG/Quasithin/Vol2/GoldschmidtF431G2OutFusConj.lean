module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2UNorm

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Conj

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem conj_xa_R (m ρ β γ : K) :
    nf m 0 0 0 0 0 * nf 0 ρ (m*ρ) (m*ρ^2) β γ =
      nf 0 ρ 0 0 (β + m*ρ^3) (β*m + γ + m^2*ρ^3) * nf m 0 0 0 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · ring
  · linear_combination (-m*ρ^3) * h2
  · linear_combination (-β*m - m^2*ρ^3) * h2

theorem conj_xv_R (y ρ β γ : K) :
    nf 0 0 0 y 0 0 * nf 0 ρ 0 0 β γ =
      nf 0 ρ 0 0 (β + ρ*y) γ * nf 0 0 0 y 0 0 := by
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · ring
  · ring
  · ring

theorem conj_xuv_R (w ρ γ : K) :
    nf 0 0 w (ρ*w) 0 0 * nf 0 ρ 0 0 0 γ =
      nf 0 ρ 0 0 0 (γ + ρ*w^2) * nf 0 0 w (ρ*w) 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · ring
  · linear_combination (ρ^2*w) * h2
  · ring

theorem conj_xr_S (s α ν γ : K) :
    nf 0 s 0 0 0 0 * nf α 0 (α*s) ν (ν*s) γ =
      nf α 0 0 (α*s^2 + ν) 0 (α^2*s^3 + γ) * nf 0 s 0 0 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · linear_combination (α*s) * h2
  · ring
  · ring
  · ring

theorem conj_xb_S (t α γ : K) :
    nf 0 0 0 0 t 0 * nf α 0 0 0 0 γ =
      nf α 0 0 0 0 (α*t + γ) * nf 0 0 0 0 t 0 := by
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · ring
  · ring
  · ring

theorem conj_xr_T1 (s μ β γ : K) :
    nf 0 s 0 0 0 0 * nf 0 0 μ 0 β γ =
      nf 0 0 μ 0 (β + μ*s^2) (γ + μ^2*s) * nf 0 s 0 0 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · ring
  · linear_combination (-μ*s^2) * h2
  · linear_combination (-μ^2*s) * h2

theorem conj_xv_T1 (t μ γ : K) :
    nf 0 0 0 t 0 0 * nf 0 0 μ 0 0 γ =
      nf 0 0 μ 0 0 (γ + μ*t) * nf 0 0 0 t 0 0 := by
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · ring
  · ring
  · ring

theorem conj_xr_T2 (s ν β γ : K) :
    nf 0 s 0 0 0 0 * nf 0 0 0 ν β γ =
      nf 0 0 0 ν (β + ν*s) γ * nf 0 s 0 0 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · ring
  · linear_combination (-ν*s) * h2
  · ring

theorem conj_xu_T2 (w ν γ : K) :
    nf 0 0 w 0 0 0 * nf 0 0 0 ν 0 γ =
      nf 0 0 0 ν 0 (γ + ν*w) * nf 0 0 w 0 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · ring
  · ring
  · linear_combination (-ν*w) * h2

theorem conj_xa_T3 (t β γ : K) :
    nf t 0 0 0 0 0 * nf 0 0 0 0 β γ =
      nf 0 0 0 0 β (β*t + γ) * nf t 0 0 0 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · ring
  · ring
  · ring
  · ring
  · ring
  · linear_combination (-β*t) * h2

end Conj

end CFSG.Quasithin.H13.F431.G2
