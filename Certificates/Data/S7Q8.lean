module

public import Certificates.Data.S5Rows

public section

namespace Certificates.S7Q8

open Certificates.S5Rows

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def inSpanB (i j x : M) : Bool :=
  decide (x ∈ q8Span i j)

@[expose] def normB (i j g : M) : Bool :=
  inSpanB i j (g * i * g⁻¹) && inSpanB i j (g * j * g⁻¹)

@[expose] def ord4B (u : M) : Bool :=
  decide (u * u * (u * u) = 1) && !decide (u * u = 1)

@[expose] def normVB (z w a : M) : Bool :=
  decide (a * z * a⁻¹ ∈ [1, z, w, z * w]) && decide (a * w * a⁻¹ ∈ [1, z, w, z * w])

@[expose] def classStepB (i j u x : M) : Bool :=
  let z := i * i
  let w := u * u
  let i' := x * i * x⁻¹
  let j' := x * j * x⁻¹
  decide (x * z * x⁻¹ = w) &&
    (!(inSpanB i' j' u && !(inSpanB i j i' && inSpanB i j j') &&
        !(normB i j i' && normB i j j')) ||
      (q8Span i j).any fun a => (q8Span i' j').any fun b =>
        normVB z w a && normVB z w b && inSpanB i' j' (a * b * i * (a * b)⁻¹) &&
          inSpanB i' j' (a * b * j * (a * b)⁻¹))

@[expose] def classCheck (i j : M) (S X : List M) : Bool :=
  S.all fun u => !ord4B u || X.any fun x => classStepB i j u x

@[expose] def normAllB (i j : M) (C : List M) : Bool :=
  C.all fun c => normB i j c

@[expose] def q8InCheck (L : List M) (i₁ j₁ i₂ j₂ : M) : Bool :=
  L.all fun a => L.all fun b => !q8RelB a b ||
    (inSpanB i₁ j₁ a && inSpanB i₁ j₁ b) || (inSpanB i₂ j₂ a && inSpanB i₂ j₂ b)

@[expose] def edgeB (i₁ j₁ i₂ j₂ e : M) : Bool :=
  let i' := e * i₂ * e⁻¹
  let j' := e * j₂ * e⁻¹
  (q8Span i' j').any (fun u => ord4B u && normB i₁ j₁ u) &&
    !(normB i₁ j₁ i' && normB i₁ j₁ j')

@[expose] def factB (i₁ j₁ i₂ j₂ : M) (E : List M) (g : M) (fs : List M) : Bool :=
  decide (fs.prod = g) && fs.all fun f =>
    decide (f ∈ E) || decide (f⁻¹ ∈ E) || normB i₁ j₁ f || normB i₂ j₂ f

end Certificates.S7Q8
