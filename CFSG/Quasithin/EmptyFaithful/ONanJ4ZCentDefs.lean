module

public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentWords

public section

namespace CFSG.Quasithin.J4ZCent

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.ZCent
open CFSG.Quasithin.J4M2 (gE)

@[expose] noncomputable def b0El (i : ℕ) : J := evalW gE (g0W.getD i [])

@[expose] noncomputable def rEl (j : ℕ) : J := evalW b0El (rW.getD j [])

@[expose] noncomputable def tEl (i : ℕ) : J := evalW b0El (tW.getD i [])

@[expose] noncomputable def b0Gens : List J := (List.range 16).map b0El

@[expose] noncomputable def rGens : List J := (List.range 15).map rEl

@[expose] noncomputable def B0 : Subgroup J := Subgroup.closure {x | x ∈ b0Gens}

@[expose] noncomputable def R0 : Subgroup J := Subgroup.closure {x | x ∈ rGens}

structure R0Facts : Prop where
  card_R0 : Nat.card R0 = 2 ^ 15
  normal : ∀ b ∈ B0, ∀ r ∈ R0, b * r * b⁻¹ ∈ R0
  cover : ∀ x ∈ B0, ∃ i < 60, ∃ r ∈ R0, x = tEl i * r
  center : ∀ x ∈ R0, (∀ r ∈ R0, x * r = r * x) → ∀ b ∈ B0, x * b = b * x

end CFSG.Quasithin.J4ZCent
