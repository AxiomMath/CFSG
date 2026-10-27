module

public import CFSG.RankThree.GF2n.Smith81.S81UModel

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.BorelTits
open scoped commutatorElement

section TvAct

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K]
  {e : K ≃+* Fσ σ}

private theorem isTransvec_mul_self {g : GL (Fin 6) F} (h : IsTransvec F g) : g * g = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  exact sq_eq_one_of_sub_one_sq h.1

theorem eq_of_e3uWact_eq_of_isTransvec (hσ : IsUnitaryInvolution σ) {g₁ g₂ : SUid σ 6}
    (h₁ : IsTransvec F (g₁ : GL (Fin 6) F)) (h₂ : IsTransvec F (g₂ : GL (Fin 6) F))
    (h : e3uWact σ e g₁ = e3uWact σ e g₂) : g₁ = g₂ := by
  have hone : e3uWact σ e (g₁⁻¹ * g₂) = 1 := by
    rw [map_mul, map_inv, ← h, inv_mul_cancel]
  obtain ⟨l, hl3, hl⟩ := (e3uWact_eq_one_iff hσ (g₁⁻¹ * g₂)).mp hone
  have hv : ((g₂ : SUid σ 6) : GL (Fin 6) F) =
      (g₁ : GL (Fin 6) F) * ((g₁⁻¹ * g₂ : SUid σ 6) : GL (Fin 6) F) := by
    rw [← Subgroup.coe_mul, mul_inv_cancel_left]
  have hb : ((g₂ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      l • ((g₁ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    rw [hv, Units.val_mul, hl, Matrix.mul_smul, Matrix.mul_one]
  have hm₁ : ((g₁ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((g₁ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [← Units.val_mul, isTransvec_mul_self h₁, Units.val_one]
  have hm₂ : ((g₂ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((g₂ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [← Units.val_mul, isTransvec_mul_self h₂, Units.val_one]
  have hkey : (l * l) • (1 : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [hb, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm₁] at hm₂
    exact hm₂
  have hll : l * l = 1 := by
    have h00 := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M 0 0) hkey
    simpa using h00
  have hl1 : l = 1 := by
    calc l = l * (l * l) := by rw [hll, mul_one]
      _ = l ^ 3 := by ring
      _ = 1 := hl3
  apply Subtype.ext
  apply Units.ext
  rw [hb, hl1, one_smul]

end TvAct

end CFSG.RankThree.GF2n.Smith81
