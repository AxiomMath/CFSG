module

public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem isPSL_three_two_of_isPSL_two_seven {X : Type} [Group X] (h : IsPSL 2 7 1 X) :
    IsPSL 3 2 1 X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have h7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let φ : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  let e₁ : StatedProj (StatedSL 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ bijective_toGL_three_zmod_two
  obtain ⟨e₄⟩ := nonempty_GL_three_two_equiv_PSL_two_seven
  have e₅ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      StatedProj (StatedSL 3 (ZMod 2)) :=
    projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2)
  exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨(((((e.trans e₁).trans e₄.symm).trans e₃.symm).trans e₂.symm).trans e₅)⟩⟩

end CFSG.Quasithin.H13.L829N
