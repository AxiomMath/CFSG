module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple
public import CFSG.Sporadic.J3

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

theorem isSimple_J3Model' : IsSimpleGroup J3Model :=
  CFSG.Sporadic.J3.isSimpleGroup_J CFSG.Sporadic.J3.j3Facts (by decide) (by decide) (by decide)

theorem card_J3Model' : Nat.card J3Model = 50232960 := by
  rw [CFSG.Sporadic.J3.card_J CFSG.Sporadic.J3.j3Facts]
  decide

theorem nonabelian_J3Model : ∃ a b : J3Model, a * b ≠ b * a := by
  have := isSimple_J3Model'
  by_contra h
  push Not at h
  have hc : IsMulCommutative J3Model := ⟨⟨fun a b => h a b⟩⟩
  have hp : Nat.card J3Model = 50232960 := card_J3Model'
  have := IsSimpleGroup.prime_card (α := J3Model)
  rw [hp] at this
  exact absurd this (by norm_num)

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
