module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Mat

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] def IsRefl (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  ∃ v f : Fin 6 → ZMod 3, f ⬝ᵥ v = 1 ∧ M = 1 + Matrix.vecMulVec v f

@[expose] def ConjIn (H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)))
    (R Q : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  ∃ h ∈ H, h * Q = R * h

@[expose] def BadOver (H L : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))) : Prop :=
  ∃ M ∈ Submonoid.closure (H ∪ L), (∀ i : Fin 6, i ≠ 0 → M i 0 = 0) ∧ M ∉ H

@[expose] def ReflSet (H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)))
    (R : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
  {s | IsRefl s ∧ (s ∈ H ∨ ConjIn H R s)}

@[expose] def ReflCover (H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))) {m : ℕ}
    (good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  ∀ s, IsRefl s → s ∈ H ∨ BadOver H {s} ∨ ∃ c, ConjIn H (good c) s

@[expose] def ReflMix (H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))) {m : ℕ}
    (good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  ∀ c c' : Fin m, c ≠ c' → ∀ Q, ConjIn H (good c) Q → BadOver H {Q, good c'}

@[expose] def ReflLines (H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))) {m : ℕ}
    (good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  ∀ c : Fin m, ∀ x : Fin 6 → ZMod 3, x ≠ 0 →
    {s | s ∈ ReflSet H (good c) ∧ s *ᵥ x = x}.ncard =
        {s | s ∈ ReflSet H (good c) ∧ s *ᵥ Pi.single 0 1 = Pi.single 0 1}.ncard →
      ∃ M ∈ Submonoid.closure (H ∪ {good c}),
        M *ᵥ Pi.single 0 1 = x ∨ M *ᵥ Pi.single 0 1 = -x

@[expose] def r35 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  1 + Matrix.vecMulVec ![0, 0, 0, 0, 1, 1] ![1, 0, 0, 0, -1, -1]

@[expose] def rD6 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  1 + Matrix.vecMulVec ![1, 0, 0, 0, 0, -1] ![-1, 0, 0, 0, 0, 1]

@[expose] def goodFix : Fin 3 → Matrix (Fin 6) (Fin 6) (ZMod 3) := ![r35, rE6 1, rE6 (-1)]

@[expose] def goodAll : Fin 4 → Matrix (Fin 6) (Fin 6) (ZMod 3) := ![rD6, r35, rE6 1, rE6 (-1)]

@[expose] def T5ReflFix : Prop :=
  ReflCover (evenFix0 5) goodFix ∧ ReflMix (evenFix0 5) goodFix ∧ ReflLines (evenFix0 5) goodFix

@[expose] def T5ReflAll : Prop :=
  ReflCover (evenAll0 5) goodAll ∧ ReflMix (evenAll0 5) goodAll ∧ ReflLines (evenAll0 5) goodAll

end CFSG.StandardType.FrameRoute.FS81

end
