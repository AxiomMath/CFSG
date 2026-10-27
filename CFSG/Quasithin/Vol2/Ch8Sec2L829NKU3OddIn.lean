module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Goldschmidt.Steps.Rank2List
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.SectionRank.ClassicalEven Matrix
open CFSG.Goldschmidt.Rank2List (d8GLB d8MatB d8MatB_mul_self d8GLB_mem_statedSU)

namespace U3Odd

section Matrices

variable {K : Type} [Field K]

theorem u3odd_u_sq : (d8GLB : GL (Fin 3) K) * d8GLB = 1 :=
  Units.ext d8MatB_mul_self

theorem u3odd_torus_inv (a : Kˣ) :
    (torusDiag ![a, a⁻¹, 1] : GL (Fin 3) K)⁻¹ = torusDiag ![a⁻¹, a, 1] := by
  rw [← map_inv]
  congr 1
  funext i
  fin_cases i <;> simp

theorem u3odd_u_mul_torus (a : Kˣ) :
    (d8GLB : GL (Fin 3) K) * torusDiag ![a, a⁻¹, 1] =
      (torusDiag ![a, a⁻¹, 1] : GL (Fin 3) K)⁻¹ * d8GLB := by
  rw [u3odd_torus_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d8GLB, d8MatB, coe_torusDiag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply]

theorem u3odd_uc_sq (a : Kˣ) :
    ((d8GLB : GL (Fin 3) K) * torusDiag ![a, a⁻¹, 1]) *
      ((d8GLB : GL (Fin 3) K) * torusDiag ![a, a⁻¹, 1]) = 1 := by
  calc ((d8GLB : GL (Fin 3) K) * torusDiag ![a, a⁻¹, 1]) *
          ((d8GLB : GL (Fin 3) K) * torusDiag ![a, a⁻¹, 1])
        = ((torusDiag ![a, a⁻¹, 1] : GL (Fin 3) K)⁻¹ * d8GLB) *
            ((d8GLB : GL (Fin 3) K) * torusDiag ![a, a⁻¹, 1]) := by
          rw [u3odd_u_mul_torus a]
    _ = (torusDiag ![a, a⁻¹, 1] : GL (Fin 3) K)⁻¹ *
          ((d8GLB : GL (Fin 3) K) * ((d8GLB : GL (Fin 3) K) * torusDiag ![a, a⁻¹, 1])) := by
          simp only [mul_assoc]
    _ = (torusDiag ![a, a⁻¹, 1] : GL (Fin 3) K)⁻¹ * torusDiag ![a, a⁻¹, 1] := by
          rw [← mul_assoc (d8GLB : GL (Fin 3) K) d8GLB, u3odd_u_sq, one_mul]
    _ = 1 := inv_mul_cancel _

end Matrices

section Order

variable {K : Type} [Field K]

theorem u3odd_exists_unit [Finite K] {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) :
    ∃ a : Kˣ, orderOf a = q + 1 := by
  have hcard : Nat.card Kˣ = (q + 1) * (q - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hdvd : q - 1 ∣ orderOf μ := by
    rw [hμ, hcard]
    exact dvd_mul_left _ _
  refine ⟨μ ^ (q - 1), ?_⟩
  rw [orderOf_pow_of_dvd (by omega) hdvd, hμ, hcard,
    Nat.mul_div_cancel (q + 1) (show 0 < q - 1 by omega)]

theorem u3odd_order_pair [Finite K] {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q)
    (hK : Nat.card K = q ^ 2) :
    ∃ z₁ z₂ : StatedProj (StatedSU 3 q K), orderOf z₁ = 2 ∧ orderOf z₂ = 2 ∧
      6 ≤ orderOf (z₁ * z₂) := by
  have hq0 : q ≠ 0 := by omega
  obtain ⟨a, ha⟩ := u3odd_exists_unit (K := K) (q := q) (by omega) hK
  have ha1 : a ^ (q + 1) = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have hd : ∏ i, (![a, a⁻¹, 1] : Fin 3 → Kˣ) i = 1 := by
    simp [Fin.prod_univ_three]
  have hdq : (![a, a⁻¹, 1] : Fin 3 → Kˣ) ^ (q + 1) = 1 := by
    funext i
    fin_cases i <;> simp [Pi.pow_apply, inv_pow, ha1]
  have hcSU : torusDiag ![a, a⁻¹, 1] ∈ StatedSU 3 q K := torusDiag_mem_SU hq0 hd hdq
  obtain ⟨uQ, huQ⟩ : ∃ x : StatedSU 3 q K, (x : GL (Fin 3) K) = d8GLB :=
    ⟨⟨d8GLB, d8GLB_mem_statedSU hq⟩, rfl⟩
  obtain ⟨cQ, hcQ⟩ : ∃ x : StatedSU 3 q K, (x : GL (Fin 3) K) = torusDiag ![a, a⁻¹, 1] :=
    ⟨⟨_, hcSU⟩, rfl⟩
  have huQ2 : uQ * uQ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, huQ, Subgroup.coe_one]
    exact u3odd_u_sq
  have hcQpow : cQ ^ (q + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hcQ, ← map_pow, hdq, map_one, Subgroup.coe_one]
  have hw2 : (uQ * cQ) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul, huQ, hcQ, Subgroup.coe_one, sq]
    exact u3odd_uc_sq a
  have hz1sq : (QuotientGroup.mk uQ : StatedProj (StatedSU 3 q K)) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, sq, huQ2, QuotientGroup.mk_one]
  have hz2sq : (QuotientGroup.mk (uQ * cQ) : StatedProj (StatedSU 3 q K)) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hw2, QuotientGroup.mk_one]
  have hprod : (QuotientGroup.mk uQ : StatedProj (StatedSU 3 q K)) *
      QuotientGroup.mk (uQ * cQ) = QuotientGroup.mk cQ := by
    rw [← QuotientGroup.mk_mul, ← mul_assoc, huQ2, one_mul]
  have hPcpow : (QuotientGroup.mk cQ : StatedProj (StatedSU 3 q K)) ^ (q + 1) = 1 := by
    rw [← QuotientGroup.mk_pow, hcQpow, QuotientGroup.mk_one]
  have hkey : ∀ k : ℕ, (QuotientGroup.mk cQ : StatedProj (StatedSU 3 q K)) ^ k = 1 →
      a ^ k = 1 := by
    intro k hk
    rw [← QuotientGroup.mk_pow] at hk
    have hmem := (QuotientGroup.eq_one_iff (cQ ^ k)).1 hk
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, hcQ, ← map_pow, StatedScalars,
      MonoidHom.mem_range] at hmem
    obtain ⟨s, hs⟩ := hmem
    rw [scalar_eq_torusDiag] at hs
    have hD := torusDiag_injective hs
    have h0 : s = a ^ k := by
      have := congrFun hD 0
      simpa [Pi.pow_apply] using this
    have h2 : s = 1 := by
      have := congrFun hD 2
      simpa [Pi.pow_apply] using this
    rw [← h0, h2]
  have hPc : orderOf (QuotientGroup.mk cQ : StatedProj (StatedSU 3 q K)) = q + 1 := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one hPcpow
    · rw [← ha]
      exact orderOf_dvd_of_pow_eq_one (hkey _ (pow_orderOf_eq_one _))
  have hz1ne : (QuotientGroup.mk uQ : StatedProj (StatedSU 3 q K)) ≠ 1 := by
    intro h
    have hmem := (QuotientGroup.eq_one_iff uQ).1 h
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
    obtain ⟨s, hs⟩ := hmem
    have h01 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) hs
    simp [huQ, d8GLB, d8MatB, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
  have hz2ne : (QuotientGroup.mk (uQ * cQ) : StatedProj (StatedSU 3 q K)) ≠ 1 := by
    intro h
    have hmem := (QuotientGroup.eq_one_iff (uQ * cQ)).1 h
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
    obtain ⟨s, hs⟩ := hmem
    have h10 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 0) hs
    have ha0 : (a : K) ≠ 0 := Units.ne_zero a
    simp [Subgroup.coe_mul, huQ, hcQ, d8GLB, d8MatB, coe_torusDiag, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.diagonal_apply, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ha0, ha0.symm] at h10
  have hz1 : orderOf (QuotientGroup.mk uQ : StatedProj (StatedSU 3 q K)) = 2 :=
    orderOf_eq_prime hz1sq hz1ne
  have hz2 : orderOf (QuotientGroup.mk (uQ * cQ) : StatedProj (StatedSU 3 q K)) = 2 :=
    orderOf_eq_prime hz2sq hz2ne
  refine ⟨QuotientGroup.mk uQ, QuotientGroup.mk (uQ * cQ), hz1, hz2, ?_⟩
  rw [hprod, hPc]
  omega

end Order

end U3Odd

theorem nk_u3odd_uin (p : ℕ) (hp : p.Prime) (h13 : 13 ≤ p) (h4 : p % 4 = 1)
    (X : Type) [Group X] (hX : IsPSU 3 p 1 X) : UIn X := by
  have hfin : Finite X := CFSG.LieType.Simplicity.finite_of_statedClassicalModel (t := .PSU) hX
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hconj, -⟩ := CFSG.Goldschmidt.Rank2List.psu3_concl X hp hp2 (le_refl 1) hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hodd : Odd (p ^ 1) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨z₁, z₂, hz₁, hz₂, h6⟩ :=
    U3Odd.u3odd_order_pair hodd (by rw [pow_one]; omega) hK
  have hx₁ : orderOf (e.symm z₁) = 2 := by rw [MulEquiv.orderOf_eq, hz₁]
  have hx₂ : orderOf (e.symm z₂) = 2 := by rw [MulEquiv.orderOf_eq, hz₂]
  obtain ⟨g, hg⟩ := isConj_iff.1 (hconj (e.symm z₁) (e.symm z₂) hx₁ hx₂)
  have hgg : g⁻¹⁻¹ * e.symm z₁ * g⁻¹ = e.symm z₂ := by
    rw [inv_inv]
    exact hg
  unfold UIn
  refine ⟨hconj, e.symm z₁, g⁻¹, hx₁, ?_⟩
  rw [hgg, ← map_mul e.symm, MulEquiv.orderOf_eq]
  exact h6

end CFSG.Quasithin.H13.L829NK
