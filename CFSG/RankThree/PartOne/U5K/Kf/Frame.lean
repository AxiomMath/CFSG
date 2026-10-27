module

public import CFSG.RankThree.PartOne.U5K.Kf.Zeta

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

theorem ZetaData.three_lt (Z : ZetaData h p) : 3 < 2 ^ f := by
  have := Nat.le_of_dvd (by positivity) Z.dvd
  have := Z.five_le
  omega

theorem ZetaData.conj_eq_one_iff (Z : ZetaData h p) (A : primeFormUnitary h (idGram K 5)) :
    primeFormConjHom h (idGram K 5) A = 1 ↔ A ∈ idScalarKernel h 5 :=
  primeFormConjHom_eq_one_iff (by norm_num) Z.three_lt A

theorem ZetaData.conj_dgU_eq_one_iff (Z : ZetaData h p) (a : Fin 5 → ZMod p) :
    primeFormConjHom h (idGram K 5) (Z.dgU a) = 1 ↔ ∀ s t, a s = a t := by
  rw [Z.conj_eq_one_iff]
  constructor
  · rintro ⟨c, -, hc⟩ s t
    have e : ∀ u : Fin 5, zp Z.ζ (a u) = (c : K) := by
      intro u
      have := congrFun (congrFun (congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K))
        hc) u) u
      simpa [ZetaData.dgU_val, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
    exact (zp_inj Z.prim).1 ((e s).trans (e t).symm)
  · intro hc
    have hq : (Units.mk0 (zp Z.ζ (a 0)) (zp_ne_zero Z.prim _)) ^ (2 ^ f + 1) = 1 := by
      apply Units.ext
      have := Z.bar_zp (a 0)
      rw [UnitaryFieldData.bar_apply] at this
      simpa [pow_succ] using this
    refine ⟨Units.mk0 (zp Z.ζ (a 0)) (zp_ne_zero Z.prim _), hq, ?_⟩
    apply Units.ext
    rw [ZetaData.dgU_val, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    congr 1
    funext s
    rw [hc s 0]
    rfl

@[expose] def ZetaData.Y (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5))
    (a : Fin 5 → ZMod p) : primeFormUnitary h (idGram K 5) :=
  P * Z.dgU a * P⁻¹

@[expose] noncomputable def ZetaData.par (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5))
    (a : Fin 5 → ZMod p) : MulAut (primeFormP h (idGram K 5)) :=
  primeFormConjHom h (idGram K 5) (Z.Y P a)

theorem ZetaData.Y_add (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5))
    (a b : Fin 5 → ZMod p) : Z.Y P (a + b) = Z.Y P a * Z.Y P b := by
  unfold ZetaData.Y
  rw [Z.dgU_add]
  group

theorem ZetaData.par_add (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5))
    (a b : Fin 5 → ZMod p) : Z.par P (a + b) = Z.par P a * Z.par P b := by
  unfold ZetaData.par
  rw [Z.Y_add, map_mul]

theorem ZetaData.par_eq_one_iff (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5))
    (a : Fin 5 → ZMod p) : Z.par P a = 1 ↔ ∀ s t, a s = a t := by
  rw [← Z.conj_dgU_eq_one_iff]
  unfold ZetaData.par ZetaData.Y
  rw [map_mul, map_mul, map_inv]
  constructor
  · intro hh
    have := congrArg (fun g => (primeFormConjHom h (idGram K 5) P)⁻¹ * g *
      primeFormConjHom h (idGram K 5) P) hh
    simpa [mul_assoc] using this
  · intro hh
    rw [hh]
    group

theorem bar_mul_of_diag {x : primeFormUnitary h (idGram K 5)} {μ : Fin 5 → K}
    (hd : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = diagonal μ) (s : Fin 5) :
    h.bar (μ s) * μ s = 1 := by
  have hm := mem_primeFormUnitary.1 x.2
  rw [hd] at hm
  have := congrFun (congrFun hm s) s
  simpa [idGram, Matrix.diagonal_map, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal] using this

theorem ZetaData.exists_par_eq (Z : ZetaData h p) (P x : primeFormUnitary h (idGram K 5))
    (μ : Fin 5 → K)
    (hd : (((P⁻¹ * x * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = diagonal μ)
    (hx : primeFormConjHom h (idGram K 5) x ^ p = 1) :
    ∃ a : Fin 5 → ZMod p, primeFormConjHom h (idGram K 5) x = Z.par P a := by
  classical
  have hn : ∀ s, h.bar (μ s) * μ s = 1 := fun s => bar_mul_of_diag hd s
  have hμ0 : ∀ s, μ s ≠ 0 := fun s => right_ne_zero_of_mul_eq_one (hn s)
  have hxp : x ^ p ∈ idScalarKernel h 5 := by
    rw [← Z.conj_eq_one_iff, map_pow]
    exact hx
  obtain ⟨κ, -, hκ⟩ := hxp
  have hpow : ∀ s, μ s ^ p = (κ : K) := by
    have e : (P⁻¹ * x * P : primeFormUnitary h (idGram K 5)) ^ p = P⁻¹ * x ^ p * P := by
      have := conj_pow (a := P⁻¹) (b := x) (i := p)
      simpa using this
    have e2 := congrArg (fun g : primeFormUnitary h (idGram K 5) =>
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) e
    have e3 : (((P⁻¹ * x ^ p * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = diagonal fun _ => (κ : K) := by
      have : (P : GL (Fin 5) K)⁻¹ * (x ^ p : primeFormUnitary h (idGram K 5)) * P =
          GeneralLinearGroup.scalar (Fin 5) κ := by
        rw [hκ, mul_assoc, ← (commute_scalar κ (P : GL (Fin 5) K)).eq, inv_mul_cancel_left]
      have := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K)) this
      simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hd, diagonal_pow] at e2
    rw [e3] at e2
    intro s
    have := congrFun (congrFun e2 s) s
    simpa using this
  have hν : ∀ s, (μ s / μ 0) ^ p = 1 := by
    intro s
    rw [div_pow, hpow s, hpow 0]
    exact div_self (Units.ne_zero κ)
  have hk : ∀ s, ∃ k < p, Z.ζ ^ k = μ s / μ 0 := fun s => Z.prim.eq_pow_of_pow_eq_one (hν s)
  choose k hk1 hk2 using hk
  set a : Fin 5 → ZMod p := fun s => (k s : ZMod p) with ha
  have hza : ∀ s, zp Z.ζ (a s) = μ s / μ 0 := by
    intro s
    unfold zp
    rw [ha]
    simp only [ZMod.val_natCast_of_lt (hk1 s)]
    exact hk2 s
  refine ⟨a, ?_⟩
  unfold ZetaData.par
  set c : Kˣ := Units.mk0 (μ 0) (hμ0 0) with hc
  have hDU : ((P : GL (Fin 5) K))⁻¹ * (x : GL (Fin 5) K) * (P : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) c * ((Z.dgU a : primeFormUnitary h (idGram K 5)) :
        GL (Fin 5) K) := by
    apply Units.ext
    have hμa : ∀ s, μ s = μ 0 * zp Z.ζ (a s) := by
      intro s
      rw [hza s]
      field_simp [hμ0 0]
    calc (((P : GL (Fin 5) K))⁻¹ * (x : GL (Fin 5) K) * (P : GL (Fin 5) K) :
          GL (Fin 5) K).val = diagonal μ := hd
      _ = diagonal (fun s => μ 0 * zp Z.ζ (a s)) := by
          congr 1
          funext s
          exact hμa s
      _ = ((GeneralLinearGroup.scalar (Fin 5) c * ((Z.dgU a : primeFormUnitary h (idGram K 5)) :
          GL (Fin 5) K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
          rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ZetaData.dgU_val,
            diagonal_mul_diagonal]
          rfl
  have hg : (x : GL (Fin 5) K) = (P : GL (Fin 5) K) *
      (GeneralLinearGroup.scalar (Fin 5) c * ((Z.dgU a : primeFormUnitary h (idGram K 5)) :
        GL (Fin 5) K)) * (P : GL (Fin 5) K)⁻¹ := by
    rw [← hDU]
    group
  have hsc : (x * (Z.Y P a)⁻¹ : primeFormUnitary h (idGram K 5)) ∈ idScalarKernel h 5 := by
    refine ⟨c, ?_, ?_⟩
    · have := hn 0
      rw [UnitaryFieldData.bar_apply] at this
      apply Units.ext
      simpa [hc, pow_succ] using this
    · have hcP : (P : GL (Fin 5) K) * GeneralLinearGroup.scalar (Fin 5) c *
          (P : GL (Fin 5) K)⁻¹ = GeneralLinearGroup.scalar (Fin 5) c := by
        rw [(commute_scalar c (P : GL (Fin 5) K)).eq, mul_inv_cancel_right]
      show (x : GL (Fin 5) K) * ((P : GL (Fin 5) K) * (Z.dgU a : GL (Fin 5) K) *
        (P : GL (Fin 5) K)⁻¹)⁻¹ = _
      rw [hg]
      calc (P : GL (Fin 5) K) * (GeneralLinearGroup.scalar (Fin 5) c *
          ((Z.dgU a : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K)) * (P : GL (Fin 5) K)⁻¹ *
            ((P : GL (Fin 5) K) * ((Z.dgU a : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) *
              (P : GL (Fin 5) K)⁻¹)⁻¹
          = (P : GL (Fin 5) K) * GeneralLinearGroup.scalar (Fin 5) c *
              (P : GL (Fin 5) K)⁻¹ := by group
        _ = _ := hcP
  have h1 := (Z.conj_eq_one_iff _).2 hsc
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

end CFSG.RankThree.PartOne.U5K.Kf
