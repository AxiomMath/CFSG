module

public import CFSG.Quasithin.MS93.MSPOrth
public import CFSG.Quasithin.MS93.M15Statement

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

theorem toAdd_omega5Act (g : Sp4 F) (y : Multiplicative (V4 F × F)) :
    Multiplicative.toAdd (omega5Act F g y) =
      (mat g *ᵥ (Multiplicative.toAdd y).1, (Multiplicative.toAdd y).2 +
        quad₀ (Multiplicative.toAdd y).1 + quad₀ (mat g *ᵥ (Multiplicative.toAdd y).1)) := rfl

theorem exists_isQuadOf_of_omega5_fix [Finite F] [CharP F 2]
    (f : Multiplicative (V4 F × F) →* Multiplicative (ZMod 2))
    (hf : ∃ y ∈ omega5Rad F, f y ≠ 1) :
    ∃ Q : V4 F → F, IsQuadOf Q ∧
      ∀ g : Sp4 F, (∀ y, f (omega5Act F g y) = f y) → g ∈ orthSp Q := by
  let f' : V4 F × F →+ ZMod 2 :=
    { toFun := fun x => Multiplicative.toAdd (f (Multiplicative.ofAdd x))
      map_zero' := by simp
      map_add' := fun x y => by rw [ofAdd_add, map_mul, toAdd_mul] }
  obtain ⟨y, hy, hfy⟩ := hf
  have hy0 : (Multiplicative.toAdd y).1 = 0 := hy
  obtain ⟨Q, hQ, hQg⟩ := exists_isQuadOf_of_fix f' ⟨(Multiplicative.toAdd y).2, fun h => hfy (by
    have : ((0 : V4 F), (Multiplicative.toAdd y).2) = Multiplicative.toAdd y :=
      Prod.ext hy0.symm rfl
    change Multiplicative.toAdd (f (Multiplicative.ofAdd _)) = 0 at h
    rw [this, ofAdd_toAdd] at h
    exact h)⟩
  refine ⟨Q, hQ, fun g hg => hQg g fun x s => ?_⟩
  have := hg (Multiplicative.ofAdd (x, s))
  change Multiplicative.toAdd (f (Multiplicative.ofAdd _)) =
    Multiplicative.toAdd (f (Multiplicative.ofAdd (x, s)))
  rw [← this]
  rfl

end CFSG.Quasithin.MS93.MSP
