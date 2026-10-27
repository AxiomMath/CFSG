module

public import CFSG.LocalAnalysis.StandardType.StarFour.HatSL
public import Mathlib.LinearAlgebra.SpecialLinearGroup

public section

namespace CFSG.StandardType.StarFour

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

theorem exists_sl_setup {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hcop : Nat.Coprime (m + 1) (Nat.card F - 1)) {X : Type} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (B : Subgroup X) (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB : ∀ b ∈ B, GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b) :
    ∃ (ψ' : SpecialLinearGroup F (Fin (m + 1) → F) →* X)
      (hat : B →* SpecialLinearGroup F (Fin (m + 1) → F)),
      Function.Injective ψ' ∧ ψ'.range = ψ.range ∧
      ∀ (b : B) (u : SpecialLinearGroup F (Fin (m + 1) → F)),
        (b : X) * ψ' u * (b : X)⁻¹ = ψ' (hat b * u * (hat b)⁻¹) := by
  classical
  obtain ⟨hat, hhat⟩ :=
    exists_hat_of_ggPsiInnerDiag hcop ψ hker B hBN hB
  let T : Matrix.SpecialLinearGroup (Fin (m + 1)) F ≃*
      SpecialLinearGroup F (Fin (m + 1) → F) :=
    Matrix.SpecialLinearGroup.toLin'_equiv
  let ψ' : SpecialLinearGroup F (Fin (m + 1) → F) →* X := ψ.comp T.symm.toMonoidHom
  let hat' : B →* SpecialLinearGroup F (Fin (m + 1) → F) := T.toMonoidHom.comp hat
  refine ⟨ψ', hat', ?_, ?_, ?_⟩
  · exact (psi_injective_of_ker_le_center hcop ψ hker).comp T.symm.injective
  · change (ψ.comp T.symm.toMonoidHom).range = ψ.range
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective T.symm.toMonoidHom T.symm.surjective,
      Subgroup.map_top]
  · intro b u
    have h := hhat.1 b (T.symm u)
    have hmap : T.symm (T (hat b) * u * (T (hat b))⁻¹) =
        hat b * T.symm u * (hat b)⁻¹ := by
      simp only [map_mul, map_inv, T.symm_apply_apply]
    calc (b : X) * ψ' u * (b : X)⁻¹
        = (b : X) * ψ (T.symm u) * (b : X)⁻¹ := rfl
      _ = ψ (hat b * T.symm u * (hat b)⁻¹) := h
      _ = ψ (T.symm (T (hat b) * u * (T (hat b))⁻¹)) := by rw [hmap]
      _ = ψ' (hat' b * u * (hat' b)⁻¹) := rfl

end CFSG.StandardType.StarFour
