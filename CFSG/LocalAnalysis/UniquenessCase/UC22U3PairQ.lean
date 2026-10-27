module

public import CFSG.LocalAnalysis.UniquenessCase.UC22U3Elt
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Pair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.U3Aut

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.Bender.Frame

variable {k : ℕ} {E : Type} [Field E]

theorem exists_orderOf_bar_eq (hU : UnitaryFieldData 2 k E) {q : ℕ} (hq : q.Prime)
    (hqk : q ∣ 2 ^ k - 1) : ∃ l : Eˣ, orderOf l = q ∧ hU.bar (l : E) = l := by
  haveI := hU.finite
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd : 2 ^ k - 1 ∣ Nat.card Eˣ := by
    rw [Nat.card_units, hU.card, pow_mul']
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ k) 1 2
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := Eˣ) q (hqk.trans hdvd)
  refine ⟨l, hl, ?_⟩
  have h1 : (l : E) ^ (2 ^ k - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, orderOf_dvd_iff_pow_eq_one.1 (hl ▸ hqk), Units.val_one]
  calc hU.bar (l : E) = (l : E) ^ (2 ^ k - 1 + 1) := by
        rw [UnitaryFieldData.bar_apply, Nat.sub_add_cancel Nat.one_le_two_pow]
    _ = l := by rw [pow_succ, h1, one_mul]

theorem exists_invPairOf_commute_line (hU : UnitaryFieldData 2 k E) {q : ℕ} (hq : q.Prime)
    (hqk : q ∣ 2 ^ k - 1) {d : frameTorusSU hU (fun i => Pi.single i 1)}
    (hd : frameEigHom (UCK.isOrthonormalFrame_single hU) 0 d =
      frameEigHom (UCK.isOrthonormalFrame_single hU) 1 d) :
    ∃ c s : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = q ∧ s * c * s⁻¹ = c⁻¹ ∧
      s ^ 2 = 1 ∧
      c * QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
        QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * c ∧
      s * QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
        QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * s := by
  haveI := hU.charP
  haveI : Fact q.Prime := ⟨hq⟩
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hv := UCK.isOrthonormalFrame_single (p := 2) hU
  obtain ⟨a, b, hab, hbl, hbb, haq, hbq, ha1⟩ : ∃ a b : E, a * b = 1 ∧ hU.bar a = a ∧
      hU.bar b = b ∧ a ^ q = 1 ∧ b ^ q = 1 ∧ a ≠ 1 := by
    obtain ⟨l, hl, hbl⟩ := exists_orderOf_bar_eq hU hq hqk
    refine ⟨l, ((l⁻¹ : Eˣ) : E), by rw [← Units.val_mul, mul_inv_cancel, Units.val_one], hbl,
      by rw [Units.val_inv_eq_inv_val, map_inv₀, hbl], ?_, ?_, fun h => ?_⟩
    · rw [← Units.val_pow_eq_pow_val, ← hl, pow_orderOf_eq_one, Units.val_one]
    · rw [← Units.val_pow_eq_pow_val, inv_pow, ← hl, pow_orderOf_eq_one, inv_one, Units.val_one]
    · rw [show l = 1 from Units.ext (by rw [h, Units.val_one]), orderOf_one] at hl
      exact hq.one_lt.ne hl
  obtain ⟨w, -, hw, -⟩ := exists_trace_norm hU
  have hwb : hU.bar w = w + 1 := by linear_combination hw - w * h2
  set V : Matrix (Fin 3) (Fin 3) E := !![1, w, 0; 1, w + 1, 0; 0, 0, 1] with hV
  set V' : Matrix (Fin 3) (Fin 3) E := !![w + 1, w, 0; 1, 1, 0; 0, 0, 1] with hV'
  set D : Matrix (Fin 3) (Fin 3) E := Matrix.diagonal ![a, b, 1] with hD
  set S : Matrix (Fin 3) (Fin 3) E := !![0, 1, 0; 1, 0, 0; 0, 0, 1] with hS
  have hVV' : V * V' = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hV, hV', Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination w * h2
        | linear_combination (w + 1) * h2
  have hV'V : V' * V = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hV, hV', Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination w * h2
        | linear_combination (w * (w + 1)) * h2
        | linear_combination h2
  have hVb : (V.map hU.bar)ᵀ * V = S := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hV, hS, hwb, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination h2
        | linear_combination w * h2
        | linear_combination (w + 1) * h2
        | linear_combination ((w + 1) * (w + 1)) * h2
  have hDS : (D.map hU.bar)ᵀ * S * D = S := by
    rw [hD, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hS, hbl, hbb, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;>
      linear_combination hab
  have hSS : S * S = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS, Matrix.mul_apply, Fin.sum_univ_three]
  have hSb : (S.map hU.bar)ᵀ * S * S = S := by
    have h : (S.map hU.bar)ᵀ = S := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hS]
    rw [h, hSS, Matrix.one_mul]
  have hSD : S * D = !![0, b, 0; a, 0, 0; 0, 0, 1] := by
    ext i j
    rw [hD, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [hS]
  have hSDSD : S * D * S * D = 1 := by
    rw [Matrix.mul_assoc (S * D), hSD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      linear_combination hab
  have hDq : D ^ q = 1 := by
    rw [hD, Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [haq, hbq]
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) E, V * X * V' * (V * Y * V') = V * (X * Y) * V' :=
    fun X Y => by
      calc V * X * V' * (V * Y * V') = V * X * (V' * V) * Y * V' := by
            simp only [Matrix.mul_assoc]
        _ = V * (X * Y) * V' := by
            rw [hV'V, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
  have hpow : ∀ j : ℕ, (V * D * V') ^ j = V * D ^ j * V' := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hVV']
    | succ j ih => rw [pow_succ, ih, hmul, ← pow_succ]
  have hbar1 : (V'.map hU.bar)ᵀ * (V.map hU.bar)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hVV', Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one]
  have hunit : ∀ X : Matrix (Fin 3) (Fin 3) E, (X.map hU.bar)ᵀ * S * X = S →
      ((V * X * V').map hU.bar)ᵀ * (V * X * V') = 1 := fun X hX => by
    calc ((V * X * V').map hU.bar)ᵀ * (V * X * V')
        = (V'.map hU.bar)ᵀ * ((X.map hU.bar)ᵀ * ((V.map hU.bar)ᵀ * V) * X) * V' := by
          simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (V'.map hU.bar)ᵀ * ((V.map hU.bar)ᵀ * V) * V' := by rw [hVb, hX]
      _ = (V'.map hU.bar)ᵀ * (V.map hU.bar)ᵀ * (V * V') := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hbar1, hVV', Matrix.mul_one]
  have hdetV : V.det * V'.det = 1 := by rw [← Matrix.det_mul, hVV', Matrix.det_one]
  have hdetC : (V * D * V').det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdetV, one_mul, hD, Matrix.det_diagonal,
      Fin.prod_univ_three]
    simpa using hab
  have hdetS : (V * S * V').det = 1 := by
    have h1 : S.det = -1 := by
      rw [Matrix.det_fin_three]
      simp [hS]
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdetV, one_mul, h1]
    linear_combination -h2
  obtain ⟨c, hc⟩ : ∃ c : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E),
      ((c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = V * D * V' :=
    ⟨⟨⟨V * D * V', ((V * D * V').map hU.bar)ᵀ, mul_eq_one_comm.mp (hunit D hDS),
      hunit D hDS⟩, mem_gramSU.mpr ⟨by rw [Matrix.mul_one]; exact hunit D hDS, hdetC⟩⟩, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E),
      ((s : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = V * S * V' :=
    ⟨⟨⟨V * S * V', ((V * S * V').map hU.bar)ᵀ, mul_eq_one_comm.mp (hunit S hSb),
      hunit S hSb⟩, mem_gramSU.mpr ⟨by rw [Matrix.mul_one]; exact hunit S hSb, hdetS⟩⟩, rfl⟩
  have hcq : c ^ q = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hc, hpow, hDq, Matrix.mul_one, hVV']
    rfl))
  have hss : s * s = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, hs, hmul, hSS, Matrix.mul_one, hVV']
    rfl))
  have hscsc : s * c * s * c = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
      Units.val_mul, hs, hc, hmul, hmul, hmul, hSDSD, Matrix.mul_one, hVV']
    rfl))
  have hsc : s * c * s⁻¹ = c⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hss]
    exact eq_inv_of_mul_eq_one_left hscsc
  have hw0 : w ≠ 0 := fun h0 => by
    rw [h0, map_zero, add_zero] at hw
    exact zero_ne_one hw
  have hab0 : a + b ≠ 0 := fun h0 => by
    have h1 : (a + 1) * (a + 1) = 0 := by linear_combination a * h0 - hab + a * h2
    exact ha1 (by linear_combination mul_self_eq_zero.1 h1 - h2)
  have hVD : V * D = !![a, w * b, 0; a, (w + 1) * b, 0; 0, 0, 1] := by
    ext i j
    rw [hD, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [hV]
  have hne : (QuotientGroup.mk c : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ≠ 1 := by
    intro h1
    obtain ⟨u, -, -, hu⟩ := (QuotientGroup.eq_one_iff c).1 h1
    have h01 : ((c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 0 1 =
        ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 0 1 := by
      rw [hu]
    rw [hc, GeneralLinearGroup.coe_scalar, hVD] at h01
    simp [hV', Matrix.mul_apply, Fin.sum_univ_three] at h01
    exact mul_ne_zero hw0 hab0 (by linear_combination h01)
  obtain ⟨μ, hDμ, hμ⟩ : ∃ μ : Fin 3 → E, (((d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal μ ∧ μ 0 = μ 1 := by
    refine ⟨_, ?_, (frameEigHom_eq_iff hv).1 hd⟩
    ext r t
    have h := congrFun (mulVec_frameEig hv d.2 t) r
    rw [Matrix.mulVec_single_one] at h
    by_cases hrt : r = t
    · subst hrt
      simpa using h
    · simpa [Matrix.diagonal_apply, hrt, Pi.single_apply] using h
  have hcomm : ∀ X : Matrix (Fin 3) (Fin 3) E, X * Matrix.diagonal μ = Matrix.diagonal μ * X →
      V * X * V' * Matrix.diagonal μ = Matrix.diagonal μ * (V * X * V') := fun X hX => by
    have hVd : V * Matrix.diagonal μ = Matrix.diagonal μ * V := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hV, hμ, mul_comm]
    have hV'd : V' * Matrix.diagonal μ = Matrix.diagonal μ * V' := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hV', hμ, mul_comm]
    calc V * X * V' * Matrix.diagonal μ = V * (X * Matrix.diagonal μ) * V' := by
          rw [Matrix.mul_assoc (V * X), hV'd]
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal μ * (V * X * V') := by
          rw [hX, ← Matrix.mul_assoc V, hVd]
          simp only [Matrix.mul_assoc]
  have hDd : D * Matrix.diagonal μ = Matrix.diagonal μ * D := by
    rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hSd : S * Matrix.diagonal μ = Matrix.diagonal μ * S := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS, hμ]
  have hcd : c * (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
      (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * c :=
    Subtype.ext (Units.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc, hDμ]
      exact hcomm D hDd))
  have hsd : s * (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
      (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * s :=
    Subtype.ext (Units.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hDμ]
      exact hcomm S hSd))
  refine ⟨QuotientGroup.mk c, QuotientGroup.mk s, orderOf_eq_prime ?_ hne, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, hcq, QuotientGroup.mk_one]
  · simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using
      congrArg (fun x : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E) =>
        (x : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) hsc
  · rw [← QuotientGroup.mk_pow, pow_two, hss, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, hcd, QuotientGroup.mk_mul]
  · rw [← QuotientGroup.mk_mul, hsd, QuotientGroup.mk_mul]

theorem exists_commute_invPairOf (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpk : p ∣ 2 ^ k + 1) {q : ℕ} (hq : q.Prime)
    (hqk : q ∣ 2 ^ k - 1) {J : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))}
    (hJ : ∀ x ∈ J, x ^ p = 1) (hJc : p ^ 2 ≤ Nat.card J) :
    ∃ t ∈ J, t ≠ 1 ∧ ∃ c s : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = q ∧
      s * c * s⁻¹ = c⁻¹ ∧ s ^ 2 = 1 ∧ c * t = t * c ∧ s * t = t * s := by
  obtain ⟨ℓ, g, hd, hℓ1, hJℓ⟩ := exists_conj_line_mem hU hk hp hp5 hpk hJ hJc
  obtain ⟨c, s, hc, hsc, hs2, hcd, hsd⟩ := exists_invPairOf_commute_line hU hq hqk hd
  have hconj : ∀ {a b : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)}, a * b = b * a →
      g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) := fun h => by
    simpa only [map_mul, MulAut.conj_apply] using congrArg (MulAut.conj g) h
  refine ⟨_, hJℓ, fun h => hℓ1 (by rwa [conj_eq_one_iff] at h), g * c * g⁻¹, g * s * g⁻¹,
    (MulEquiv.orderOf_eq (MulAut.conj g) c).trans hc, ?_, ?_, hconj hcd, hconj hsd⟩
  · simpa only [map_mul, map_inv, MulAut.conj_apply] using congrArg (MulAut.conj g) hsc
  · rw [conj_pow, hs2, mul_one, mul_inv_cancel]

end CFSG.LocalAnalysis.UniquenessCase.UC22.U3Aut

end
