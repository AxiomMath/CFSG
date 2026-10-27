module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallSem

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def Pt.Models (P : Pt) {V : Type} [AddCommGroup V] [Module (ZMod P.p) V] {n : ℕ}
    (e : V ≃ₗ[ZMod P.p] P.V) (h : Fin n → V) (α : Fin n → Module.Dual (ZMod P.p) V) (x : V)
    (ha : V) (αa : Module.Dual (ZMod P.p) V) : Prop :=
  P.nFrame = n ∧ P.gens.length = n + 1 ∧ e x = P.vec P.x ∧
  (∀ i : Fin n, e (h i) = P.vec (P.gens.getD i ⟨[], []⟩).h ∧
    ∀ w, α i w = P.dot (P.vec (P.gens.getD i ⟨[], []⟩).f) (e w)) ∧
  e ha = P.vec (P.gens.getD n ⟨[], []⟩).h ∧
  ∀ w, αa w = P.dot (P.vec (P.gens.getD n ⟨[], []⟩).f) (e w)

end CFSG.TwoNodeSmall
