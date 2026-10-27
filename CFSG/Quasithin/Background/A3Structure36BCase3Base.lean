
module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import CFSG.Quasithin.Background.A3Structure36BBasic

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement
open CFSG.SectionRank CFSG.SectionRank.Ccomm

variable {X : Type} [Group X]

theorem naturalSL2Action_of_kernel (h : A36BHyp X) {p : ℕ} (hp : p.Prime)
    (hsl : IsSL2 p (X ⧸ CFSG.fittingSubgroup X))
    (e : ↥(CFSG.fittingSubgroup X) ≃* Multiplicative (Fin 2 → ZMod p))
    (hker : ∀ x : X, (∀ f : ↥(CFSG.fittingSubgroup X), MulAut.conjNormal x f = f) ↔
      x ∈ CFSG.fittingSubgroup X) :
    NaturalSL2Action p X (CFSG.fittingSubgroup X) := by
  have hfin : Finite X := h.finite
  have hperf : Group.IsPerfect X := isPerfect_of_hyp h
  have hfp : Fact p.Prime := ⟨hp⟩
  let g : X →* GL (Fin 2) (ZMod p) :=
    (elemAutEquivGL e).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut ↥(CFSG.fittingSubgroup X))
  have hdet : ∀ x : X, (g x : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    intro x
    have h1 := perfect_hom_eq_one (Matrix.GeneralLinearGroup.det.comp g) x
    have h2 := congrArg Units.val h1
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h2
  let ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    { toFun := fun x => ⟨(g x : Matrix (Fin 2) (Fin 2) (ZMod p)), hdet x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change ((g (x * y) : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
          (g x : Matrix (Fin 2) (Fin 2) (ZMod p)) * (g y : Matrix (Fin 2) (Fin 2) (ZMod p))
        rw [map_mul, Units.val_mul] }
  have hψker : ψ.ker = CFSG.fittingSubgroup X := by
    ext x
    rw [MonoidHom.mem_ker, ← hker]
    constructor
    · intro h1 f
      have h2 : g x = 1 := by
        apply Units.ext
        exact congrArg Subtype.val h1
      have h3 : (MulAut.conjNormal x : MulAut ↥(CFSG.fittingSubgroup X)) = 1 :=
        (elemAutEquivGL e).injective (by rw [map_one]; exact h2)
      rw [h3]
      rfl
    · intro h1
      apply Subtype.ext
      have h2 : (MulAut.conjNormal x : MulAut ↥(CFSG.fittingSubgroup X)) = 1 := by
        ext f
        exact congrArg Subtype.val (h1 f)
      change ((g x : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1
      have : g x = 1 := by
        show (elemAutEquivGL e) (MulAut.conjNormal x) = 1
        rw [h2, map_one]
      rw [this]
      rfl
  have hψsurj : Function.Surjective ψ := by
    obtain ⟨e₀⟩ := hsl
    have hcard : Nat.card ψ.range = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
      calc Nat.card ψ.range = Nat.card (X ⧸ ψ.ker) :=
            (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv).symm
        _ = Nat.card (X ⧸ CFSG.fittingSubgroup X) :=
            Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hψker).toEquiv
        _ = _ := Nat.card_congr e₀.toEquiv
    exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_card_eq _ hcard)
  refine ⟨e, ψ, hψsurj, hψker, fun x f => ?_⟩
  have h1 := elemAutEquivGL_mulVec e (MulAut.conjNormal x) f
  rw [← ofAdd_toAdd (e (MulAut.conjNormal x f)), ← h1]
  rfl

end CFSG.Quasithin.A36B
