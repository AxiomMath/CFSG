module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C621Inv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Sporadic.Mathieu CFSG.Blueprint

@[expose] def m11U : NativeSporadic.M11 := m11a * m11b⁻¹ * m11a * m11b * m11a * m11b * m11b

theorem m11U_pow : m11U ^ 3 = 1 := by decide +kernel

theorem m11U_ne : m11U ≠ 1 := by decide +kernel

theorem m11_comm :
    m11U * (m11b * m11U * m11b⁻¹) = (m11b * m11U * m11b⁻¹) * m11U := by decide +kernel

theorem m11_ne_self : m11b * m11U * m11b⁻¹ ≠ m11U := by decide +kernel

theorem m11_ne_sq : m11b * m11U * m11b⁻¹ ≠ m11U ^ 2 := by decide +kernel

theorem m11_sq_inv : m11b * m11b * m11U * (m11b * m11b)⁻¹ = m11U⁻¹ := by decide +kernel

theorem invNormalizer_m11 : InvNormalizer 3 NativeSporadic.M11 :=
  invNormalizer_of_cycle (u := m11U) (v := m11b * m11U * m11b⁻¹) (x := m11b) (n := 880)
    (by rw [card_M11]) (by norm_num) m11U_pow m11U_ne rfl m11_comm m11_ne_self m11_ne_sq m11_sq_inv

theorem invNormalizer_of_isSpor_m11 {X : Type} [Group X]
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor X .M11) : InvNormalizer 3 X := by
  obtain ⟨e⟩ := h
  let e' : NativeSporadic.M11 ≃* X := e.symm
  haveI : Finite X := Finite.of_equiv NativeSporadic.M11 e'.toEquiv
  exact invNormalizer_m11.of_mulEquiv e'

end CFSG.LocalAnalysis.UniquenessCase.UC6
