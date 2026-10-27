module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.List.ProdSigma

public section

namespace CFSG.Certificates.Kernel.Card7H3

variable {G : Type*} [Group G] [DecidableEq G]

@[expose] def b0G (HL : List G) (T : G) : List G := HL.filter fun σ => decide (σ * T = T * σ)

@[expose] def ilG (B0 : List G) : List G := B0.filter fun σ => decide (σ * σ = 1 ∧ σ ≠ 1)

@[expose] def ccG (HL : List G) (σ ρ : G) : ℕ :=
  HL.countP fun c => decide (c * σ = σ * c ∧ c * ρ = ρ * c)

@[expose] def clG (HL : List G) (T : G) (IL : List G) (m : ℕ) : List G :=
  IL.filter fun σ => decide (ccG HL T σ = m)

@[expose] def classesAuxG (B0 : List G) : ℕ → List G → List (G × List G)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, r :: rest =>
    (r, (r :: rest).filter fun b => B0.any fun g => decide (g * r * g⁻¹ = b)) ::
      classesAuxG B0 n ((r :: rest).filter fun b => !(B0.any fun g => decide (g * r * g⁻¹ = b)))

@[expose] def zrG (R : List (G × List G)) (b : G) : Bool := R.any fun c => decide (b ∈ c.2)

@[expose] def yPowG (Y g : G) : Bool := (List.range 12).any fun k => decide (g ^ k = Y)

@[expose] def pairCountG (IL : List G) (Y : G) (R : List (G × List G)) : ℕ :=
  ((IL.filter (zrG R)) ×ˢ (IL.filter fun b => !zrG R b)).countP fun p => yPowG Y (p.1 * p.2)

@[expose] def classesCheckG (B0 IL : List G) (C : List (G × List G)) (Y : G) : Bool :=
  (IL.all fun b => C.any fun c => decide (b ∈ c.2)) &&
  (C.all fun c => c.2.all fun b => B0.any fun g => decide (g * c.1 * g⁻¹ = b)) &&
  decide (Y ∈ IL)

@[expose] def powCheckG (IL : List G) : Bool :=
  IL.all fun a => IL.all fun b => decide ((a * b) ^ 12 = 1)

@[expose] def ryCheckG (IL : List G) (C : List (G × List G)) (L96 L48 : List G) (Y : G) : Bool :=
  C.sublists.all fun R =>
    decide ((L96.filter (zrG R)).length = 6 → (L48.filter (zrG R)).length = 12 →
      zrG R Y = false → pairCountG IL Y R = 156)

end CFSG.Certificates.Kernel.Card7H3

end
