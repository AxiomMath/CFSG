module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTDefs
public import Certificates.Data.E6TableT

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT

@[expose] def vecZ (x : Vec) : Fin Tag.E6.rank → ZMod 3 := fun i => ((x.getD i 0 : ℤ) : ZMod 3)

@[expose] def repZ (k : Fin 5) : Fin Tag.E6.rank → ZMod 3 := vecZ (reps.getD k [])

@[expose] def genActZ (j : Fin 7) (v : Fin Tag.E6.rank → ZMod 3) : Fin Tag.E6.rank → ZMod 3 :=
  fun k => if h : j.val < 6 then v k - ((Tag.E6.cartan ⟨j.val, h⟩ k : ℤ) : ZMod 3) * v ⟨j.val, h⟩ else - v k

@[expose] def classSet (l : List Vec) : Set (Fin Tag.E6.rank → ℤ) := {γ | List.ofFn γ ∈ l}

@[expose] def bList (b : Fin Tag.E6.rank → (Fin Tag.E6.rank → ℤ)) : List Vec := List.ofFn fun i => List.ofFn (b i)

@[expose] def E6TableTAt (v : Fin Tag.E6.rank → ZMod 3) : Prop :=
  ∀ (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (r : ZMod 3),
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

theorem e6TableTStmt_iff : E6TableTStmt ↔ ∀ v, E6TableTAt v :=
  ⟨fun h v ρ r hadd hroot hadm hv0 Ψ hΨ hs => h ρ v r hadd hroot hadm hv0 Ψ hΨ hs,
    fun h ρ v r hadd hroot hadm hv0 Ψ hΨ hs => h v ρ r hadd hroot hadm hv0 Ψ hΨ hs⟩


end CFSG.StandardType.TablePThreeKG

end
