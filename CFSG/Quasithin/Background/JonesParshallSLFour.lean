module

public import CFSG.Quasithin.Background.JonesParshallNatural
import CFSG.LinearAlgebra.RootGroupSL.CocycleNat

public section

namespace CFSG.Quasithin.JonesParshall

open Matrix

variable {F : Type} [Field F]

abbrev muSL (d : ℕ) (F : Type) [Field F] :
    SpecialLinearGroup (Fin d) F →* AddMonoid.End (Fin d → F) :=
  DistribMulAction.toAddMonoidEnd _ _

theorem Z1A_eq_B1A_muSL [Finite F] [CharP F 2] {d : ℕ} (hd : 4 ≤ d) :
    Z1A (muSL d F) = B1A (muSL d F) := by
  refine le_antisymm (fun f hf => ?_) (B1A_le_Z1A _)
  let e : SpecialLinearGroup (Fin d) F ≃* _root_.SpecialLinearGroup F (Fin d → F) :=
    Matrix.SpecialLinearGroup.toLin'_equiv
  have he : ∀ (M : SpecialLinearGroup (Fin d) F) (v : Fin d → F), e M v = M • v := by
    intro M v
    show Matrix.SpecialLinearGroup.toLin' M v = (M : Matrix (Fin d) (Fin d) F) *ᵥ v
    rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  let c : _root_.SpecialLinearGroup F (Fin d → F) → Fin d → F := fun u => f (e.symm u)
  have hc : ∀ u u' : _root_.SpecialLinearGroup F (Fin d → F), c (u * u') = c u + u (c u') := by
    intro u u'
    have h1 : u (c u') = e.symm u • c u' := by
      conv_lhs => rw [← e.apply_symm_apply u]
      exact he _ _
    rw [h1]
    exact (congrArg f (map_mul e.symm u u')).trans (hf _ _)
  have hdim : 4 ≤ Module.finrank F (Fin d → F) := by
    rwa [Module.finrank_fin_fun]
  obtain ⟨a, ha⟩ := CFSG.LinearAlgebra.RootGroupSL.exists_eq_sub_of_cocycle_natural hdim c hc
  refine ⟨a, funext fun M => ?_⟩
  have h : f M = e M a - a := by
    have h' := ha (e M)
    simp only [c, e.symm_apply_apply] at h'
    exact h'
  rw [coboundaryA_apply, h, he]
  rfl

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_SL_of_four_le [Fintype F] [CharP F 2] {ρ : Representation (ZMod 2) Γ W}
    {d : ℕ} (hd : 4 ≤ d) {ε : Explicit.NatDual} (h : Explicit.BinaryNaturalSL ρ d F ε) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  classical
  obtain ⟨θ, β, hβ⟩ := BinaryNaturalSL.intertwiner h
  have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  have hβ' : ∀ γ w, β (ρ γ w) = muSL d F (θ γ) (β w) := hβ
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ' (k := 1) (by rw [Z1A_eq_B1A_muSL hd, one_mul]), pow_zero]

end CFSG.Quasithin.JonesParshall
