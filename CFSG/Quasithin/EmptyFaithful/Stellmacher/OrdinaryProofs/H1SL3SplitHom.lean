module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

theorem hom_trivial_of_hom_zmod2 {L : Type} [Group L] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (hL2 : ∀ f : L →* Multiplicative (ZMod 2), f = 1)
    (f : L →* Multiplicative M) (l : L) : f l = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  haveI : Module.Projective (ZMod 2) M := Module.Projective.of_free
  have key : ∀ φ : Module.Dual (ZMod 2) M, φ (Multiplicative.toAdd (f l)) = 0 := by
    intro φ
    let g : L →* Multiplicative (ZMod 2) :=
      { toFun := fun x => Multiplicative.ofAdd (φ (Multiplicative.toAdd (f x)))
        map_one' := by simp
        map_mul' := by intro a b; simp }
    have hg : g = 1 := hL2 g
    have hl : Multiplicative.toAdd (g l) = Multiplicative.toAdd ((1 : L →* Multiplicative (ZMod 2)) l) :=
      congrArg (fun h : L →* Multiplicative (ZMod 2) => Multiplicative.toAdd (h l)) hg
    simpa [g] using hl
  have h0 : Multiplicative.toAdd (f l) = 0 :=
    (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp key
  exact toAdd_eq_zero.mp h0

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
