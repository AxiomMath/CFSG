module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobDefs

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def e6Chi (v : Fin Tag.E6.rank → ZMod 3) :
    Multiplicative (Fin Tag.E6.rank → ℤ) →* Multiplicative (ZMod 3) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (∑ k, ((Multiplicative.toAdd x k : ℤ) : ZMod 3) * v k))
    (by intro x y; simp [add_mul, Finset.sum_add_distrib])

@[expose] def E6KerComponent (v : Fin Tag.E6.rank → ZMod 3) (Ψ : Set (Fin Tag.E6.rank → ℤ)) : Prop :=
  ∃ i : KernelComponent (e6Chi v), Ψ = componentRoots (e6Chi v) i

@[expose] def E6TableTStmt : Prop :=
  ∀ (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (v : Fin Tag.E6.rank → ZMod 3) (r : ZMod 3),
    (∀ x y, ρ (x + y) = ρ x + ρ y) → (∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ)) →
    E6Admissible (fun i => ρ (Pi.single i 1)) v r → v ≠ 0 →
    ∀ Ψ : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ →
      (∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' →
        ∃ k : ℕ, (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] '' Ψ = Ψ') →
      ((compRank Ψ = 5 ∧ Ψ.ncard = 40 ∧ componentOrbitLength ρ Ψ = 1) ∨
        (compRank Ψ = 5 ∧ Ψ.ncard = 30 ∧ componentOrbitLength ρ Ψ = 1) ∨
        (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧ componentOrbitLength ρ Ψ = 1) ∨
        (compRank Ψ = 2 ∧ Ψ.ncard = 6 ∧ componentOrbitLength ρ Ψ = 3 ∧
          (r = 1 → twistInner Ψ ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3])) ∧
          (r = 2 → ¬ twistInner Ψ ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3]))))

end CFSG.StandardType.TablePThreeKG

end
