module

public import CFSG.Blueprint.SourceBinaryGolayCode
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.G11

abbrev GolayAmbient := Fin 24 → ZMod 2

@[expose] def golayConstantLine : Submodule (ZMod 2) GolayAmbient :=
  Submodule.span (ZMod 2) {fun _ : Fin 24 => (1 : ZMod 2)}

@[expose] def golayPairLine (first second : Fin 24) : Submodule (ZMod 2) GolayAmbient :=
  Submodule.span (ZMod 2) {fun coordinate : Fin 24 =>
    (if coordinate = first then 1 else 0) + (if coordinate = second then 1 else 0)}

@[expose] def golayPairKernel (first second : Fin 24) : Submodule (ZMod 2) GolayAmbient where
  carrier := {word | word first = word second}
  zero_mem' := rfl
  add_mem' := by
    intro left right left_mem right_mem
    change left first = left second at left_mem
    change right first = right second at right_mem
    change left first + right first = left second + right second
    rw [left_mem, right_mem]
  smul_mem' := by
    intro scalar word word_mem
    change word first = word second at word_mem
    change scalar • word first = scalar • word second
    rw [word_mem]

theorem mem_golayPairKernel (first second : Fin 24) (word : GolayAmbient) :
    word ∈ golayPairKernel first second ↔ word first = word second := Iff.rfl

@[expose] def IsGolaySectionModule {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) {Model : Type} [Group Model]
    (small : Bool) (numerator denominator : Submodule (ZMod 2) GolayAmbient) : Prop :=
  ∃ (marking : ↥H ≃* Model) (action : Model →* Equiv.Perm (Fin 24)),
    Function.Injective action ∧
    (∀ permutation : Equiv.Perm (Fin 24),
      (∃ model : Model, action model = permutation) ↔
        (∀ word : GolayAmbient,
          word ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
            permAct permutation word ∈ CFSG.Blueprint.EvenSource.sourceGolayCode) ∧
        (small = true → permutation 0 = 0 ∧ permutation 1 = 1)) ∧
    denominator ≤ numerator ∧
    (∀ (element : ↥H) (word : ↥numerator),
      permAct (action (marking element)) (word : GolayAmbient) ∈ numerator) ∧
    ∃ quotientMap : ↥numerator →ₗ[ZMod 2] V,
      Function.Surjective quotientMap ∧
      (∀ word : ↥numerator, quotientMap word = 0 ↔ (word : GolayAmbient) ∈ denominator) ∧
      ∀ (element : ↥H) (word image : ↥numerator),
        (image : GolayAmbient) = permAct (action (marking element)) (word : GolayAmbient) →
          quotientMap image = (element : GLV V) (quotientMap word)

theorem isGolaySectionModule_group {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Subgroup (GLV V)} {Model : Type} [Group Model] {small : Bool}
    {numerator denominator : Submodule (ZMod 2) GolayAmbient}
    (realization : IsGolaySectionModule (Model := Model) H small numerator denominator) :
    Nonempty (↥H ≃* Model) := by
  rcases realization with ⟨marking, remaining⟩
  exact ⟨marking⟩

@[expose] def IsMathieu24CodeOrCocode {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) : Prop :=
  IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M24) H false
      CFSG.Blueprint.EvenSource.sourceGolayCode golayConstantLine ∨
    IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M24) H false
      (permCore 24) CFSG.Blueprint.EvenSource.sourceGolayCode

@[expose] def IsMathieu22CodeOrCocode {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) : Prop :=
  IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M22) H true
      (CFSG.Blueprint.EvenSource.sourceGolayCode ⊓ golayPairKernel 0 1) golayConstantLine ∨
    IsGolaySectionModule (Model := ↥CFSG.Blueprint.NativeSporadic.M22) H true
      (permCore 24) (CFSG.Blueprint.EvenSource.sourceGolayCode ⊔ golayPairLine 0 1)

end CFSG.Quasithin.G11
