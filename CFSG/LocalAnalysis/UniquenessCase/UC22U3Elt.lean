module

public import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.U3Aut

open Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.Uniqueness.Bender.Frame

variable {k : ℕ} {E : Type} [Field E]

theorem exists_trace_norm (hU : UnitaryFieldData 2 k E) :
    ∃ a b : E, a + hU.bar a = 1 ∧ a * hU.bar a + b * hU.bar b = 1 := by
  haveI := hU.charP
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  obtain ⟨s, hs⟩ := hU.exists_bar_ne
  have hs0 : s + hU.bar s ≠ 0 := fun h0 => hs (by linear_combination h0 - s * h2)
  have hbs : hU.bar (s + hU.bar s) = s + hU.bar s := by rw [map_add, hU.bar_bar, add_comm]
  have ha : s * (s + hU.bar s)⁻¹ + hU.bar (s * (s + hU.bar s)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, hbs, ← add_mul, mul_inv_cancel₀ hs0]
  set a := s * (s + hU.bar s)⁻¹ with hadef
  obtain ⟨b, hb⟩ := exists_norm_eq hU (c := 1 + a * hU.bar a) (by
    rw [map_add, map_one, map_mul, hU.bar_bar, mul_comm (hU.bar a)])
  refine ⟨a, b, ha, ?_⟩
  rw [UnitaryFieldData.norm] at hb
  linear_combination hb + (a * hU.bar a) * h2

theorem exists_orderOf_three_commute_line (hU : UnitaryFieldData 2 k E)
    {d : frameTorusSU hU (fun i => Pi.single i 1)}
    (hd : frameEigHom (UCK.isOrthonormalFrame_single hU) 0 d =
      frameEigHom (UCK.isOrthonormalFrame_single hU) 1 d) :
    ∃ c : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = 3 ∧
      c * QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
        QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * c := by
  haveI := hU.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hv := UCK.isOrthonormalFrame_single (p := 2) hU
  obtain ⟨a, b, ha, hab⟩ := exists_trace_norm hU
  set M : Matrix (Fin 3) (Fin 3) E := !![a, b, 0; hU.bar b, hU.bar a, 0; 0, 0, 1] with hM
  have hMs : (M.map hU.bar)ᵀ = !![hU.bar a, b, 0; hU.bar b, a, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, hU.bar_bar]
  have hMM : (M.map hU.bar)ᵀ * M = 1 := by
    rw [hMs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination hab
        | linear_combination (b * hU.bar a) * h2
        | linear_combination (a * hU.bar b) * h2
  have hdet : M.det = 1 := by
    rw [Matrix.det_fin_three]
    simp only [hM]
    simp
    linear_combination hab - (b * hU.bar b) * h2
  have hM2 : M * M = !![a + 1, b, 0; hU.bar b, hU.bar a + 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination hab + a * ha - a * hU.bar a * h2
        | linear_combination b * ha
        | linear_combination hU.bar b * ha
        | linear_combination hab + hU.bar a * ha - a * hU.bar a * h2
  have hM3 : M * (M * M) = 1 := by
    rw [hM2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination hab + a * ha + a * (1 - hU.bar a) * h2
        | linear_combination b * ha + b * h2
        | linear_combination hU.bar b * ha + hU.bar b * h2
        | linear_combination hab + hU.bar a * ha + hU.bar a * (1 - a) * h2
  obtain ⟨c, hc⟩ : ∃ c : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E),
      ((c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = M :=
    ⟨⟨⟨M, (M.map hU.bar)ᵀ, mul_eq_one_comm.mp hMM, hMM⟩,
      mem_gramSU.mpr ⟨by rw [Matrix.mul_one]; exact hMM, hdet⟩⟩, rfl⟩
  have hc3 : c ^ 3 = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hc, pow_three, hM3]
    rfl))
  have hne : (QuotientGroup.mk c : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ≠ 1 := by
    intro h1
    obtain ⟨u, -, -, hu⟩ := (QuotientGroup.eq_one_iff c).1 h1
    have h00 : ((c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 0 0 =
        ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 0 0 := by
      rw [hu]
    have h11 : ((c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 1 1 =
        ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 1 1 := by
      rw [hu]
    rw [hc, GeneralLinearGroup.coe_scalar] at h00 h11
    simp [hM] at h00 h11
    exact one_ne_zero (by rw [← ha, h11, h00, ← two_mul, h2, zero_mul] : (1 : E) = 0)
  obtain ⟨μ, hDμ, hμ⟩ : ∃ μ : Fin 3 → E, (((d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal μ ∧ μ 0 = μ 1 := by
    refine ⟨_, ?_, (frameEigHom_eq_iff hv).1 hd⟩
    ext r s
    have h := congrFun (mulVec_frameEig hv d.2 s) r
    rw [Matrix.mulVec_single_one] at h
    by_cases hrs : r = s
    · subst hrs
      simpa using h
    · simpa [Matrix.diagonal_apply, hrs, Pi.single_apply] using h
  have hcd : c * (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
      (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * c :=
    Subtype.ext (Units.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc, hDμ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hM, hμ, mul_comm]))
  refine ⟨QuotientGroup.mk c, orderOf_eq_prime ?_ hne, ?_⟩
  · rw [← QuotientGroup.mk_pow, hc3, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, hcd, QuotientGroup.mk_mul]

theorem exists_orderOf_three (hU : UnitaryFieldData 2 k E) :
    ∃ w : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf w = 3 := by
  obtain ⟨c, hc, -⟩ := exists_orderOf_three_commute_line hU (d := 1) (by rw [map_one, map_one])
  exact ⟨c, hc⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.U3Aut
