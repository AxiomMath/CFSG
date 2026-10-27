module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDADefs

public section

namespace CFSG.StandardType.SCFourCover

@[expose] def GGLinearOn {G : Type} [Group G] (J : Subgroup G) (t : MulAut G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (f m : ℕ),
    Nat.card F = 2 ^ f ∧ 1 ≤ f ∧ 1 ≤ m ∧ (m = 1 → 2 ≤ f) ∧
    ∃ φ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* ↥J, Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) ∧
      ∃ A : GL (Fin (m + 1)) F, ∀ B, t (φ B) = (φ (InnerDiagA.conjSL A B) : G)

@[expose] def GGInnerDiagOnComps (G : Type) [Group G] : Prop :=
  ∀ x y : G, x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 → x * y = y * x →
    ∀ J : Subgroup G, CFSG.Open.IsComponentOf J
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) →
      MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut J →
      GGInnerOn J (MulAut.conj y) ∨ GGUnitaryOn J (MulAut.conj y) ∨
        GGLinearOn J (MulAut.conj y)

end CFSG.StandardType.SCFourCover

end
