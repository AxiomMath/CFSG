module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalCoord
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointForm

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem U4qCoordLeft.exists_pointFormData {F : Type*} [Field F] (c₁ : U4qCoordLeft L1 L2 S f F)
    (hD : U4qLocalData L1 L2 S f) :
    ∃ D : PointFormData (pCoreOf 2 L1) (centerOf (pCoreOf 2 L1)) L1 F,
      D.α = c₁.α ∧ D.β = c₁.β := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [c₁.card]; positivity)
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₁.card])
  refine hD.exists_pointFormData c₁.card c₁.α c₁.surjective_α c₁.β c₁.surjective_β c₁.ker_β
    c₁.equivariant (Pi.single 0 1) ?_ ?_
  · intro h
    simpa using congrFun h 0
  · rintro u ⟨m, hm⟩
    have h1 : Multiplicative.toAdd (c₁.β u) 1 = 0 := by
      rw [hm]
      funext j
      simp [vecMulVec_apply]
    have hsq := hD.isElemAbelian_right.2 _ ((c₁.mem_inf_iff u).mpr h1)
    rwa [pow_two] at hsq

end CFSG.Quasithin.F112R.St84

end
