module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def e6ThreeVarpiOne : Fin Tag.E6.rank → ℤ := ![4, 3, 5, 6, 4, 2]

@[expose] def E6CosetW (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) : Prop :=
  ∀ k, ((ρ e6ThreeVarpiOne k - e6ThreeVarpiOne k : ℤ) : ZMod 3) = 0

@[expose] def E6SolvTwo (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (Ψ : Set (Fin Tag.E6.rank → ℤ)) : Prop :=
  (compRank Ψ = 1 ∧ componentOrbitLength ρ Ψ = 1) ∨
    (compRank Ψ = 2 ∧ Ψ.ncard = 6 ∧ componentOrbitLength ρ Ψ = 1 ∧
      ¬ twistInner Ψ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)))

@[expose] def E6RowTwoW (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (Ψ : Set (Fin Tag.E6.rank → ℤ)) : Prop :=
  (compRank Ψ = 5 ∧ Ψ.ncard = 30 ∧ componentOrbitLength ρ Ψ = 1 ∧
      twistInner Ψ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) ∨
    (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧ componentOrbitLength ρ Ψ = 1 ∧
      ¬ twistInner Ψ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ∧
      twistInner Ψ ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2])) ∨
    (compRank Ψ = 2 ∧ Ψ.ncard = 6 ∧ componentOrbitLength ρ Ψ = 2 ∧
      twistInner Ψ ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2]))

@[expose] def E6RowTwoT (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (Ψ : Set (Fin Tag.E6.rank → ℤ)) : Prop :=
  (compRank Ψ = 5 ∧ Ψ.ncard = 40 ∧ componentOrbitLength ρ Ψ = 1 ∧
      ¬ twistInner Ψ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) ∨
    (compRank Ψ = 4 ∧ Ψ.ncard = 20 ∧ componentOrbitLength ρ Ψ = 1 ∧
      ¬ twistInner Ψ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) ∨
    (compRank Ψ = 5 ∧ Ψ.ncard = 30 ∧ componentOrbitLength ρ Ψ = 1 ∧
      ¬ twistInner Ψ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) ∨
    (compRank Ψ = 2 ∧ Ψ.ncard = 6 ∧ componentOrbitLength ρ Ψ = 3 ∧
      ¬ twistInner Ψ ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3])) ∨
    (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧ componentOrbitLength ρ Ψ = 1 ∧
      twistInner Ψ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) ∨
    (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧ componentOrbitLength ρ Ψ = 1 ∧
      ¬ twistInner Ψ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ∧
      ¬ twistInner Ψ ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2]))

@[expose] def E6TableTTwoStmt : Prop :=
  ∀ (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (v : Fin Tag.E6.rank → ZMod 3),
    (∀ x y, ρ (x + y) = ρ x + ρ y) → (∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ)) →
    E6Admissible (fun i => ρ (Pi.single i 1)) v 2 → v ≠ 0 →
    ∀ Ψ : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ → ¬ E6SolvTwo ρ Ψ →
      (∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' →
        (∀ k : ℕ, (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] '' Ψ ≠ Ψ') → E6SolvTwo ρ Ψ') →
      (E6CosetW ρ → E6RowTwoW ρ Ψ) ∧ (¬ E6CosetW ρ → E6RowTwoT ρ Ψ)

@[expose] def E6TwoCompLabelW (lab : LargeEvenLabel) : Prop :=
  lab = ⟨.A, 5, 1⟩ ∨ lab = ⟨.twD, 4, 1⟩ ∨ lab = ⟨.A, 2, 2⟩

@[expose] def E6TwoCompLabelT (lab : LargeEvenLabel) : Prop :=
  lab = ⟨.twA, 5, 1⟩ ∨ lab = ⟨.D, 4, 1⟩ ∨ lab = ⟨.triD4, 0, 1⟩ ∨ lab = ⟨.twD, 5, 1⟩ ∨ lab = ⟨.twA, 4, 1⟩ ∨
    lab = ⟨.twA, 2, 3⟩ ∨ lab = ⟨.twD, 4, 1⟩

end CFSG.StandardType.TablePThreeKG

end
