module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

theorem mem_stabilizer_subgroup_iff {Q : Type} [Group Q] {e : MulAut Q} {B : Subgroup Q} :
    e ∈ MulAction.stabilizer (MulAut Q) B ↔ B.map e.toMonoidHom = B := Iff.rfl

@[expose] def FactJ1Norm3312 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .J1 Q →
    ∀ (A S : Subgroup (MulAut Q)) (B : Subgroup Q),
      (MulAut.conj : Q →* MulAut Q).range ≤ A → IsSylowTwoOf S A → IsAlt 5 ↥B →
      S ≤ MulAction.stabilizer (MulAut Q) B →
      (∀ s ∈ S, ∃ b ∈ B, ∀ y ∈ B, (s : MulAut Q) y = b * y * b⁻¹) ∧
        ∀ α ∈ A, Odd (orderOf α) → (∀ y ∈ B, α y = y) → α = 1

@[expose] def FactJ2Norm3312 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .J2 Q →
    ∀ (A S : Subgroup (MulAut Q)) (B : Subgroup Q),
      (MulAut.conj : Q →* MulAut Q).range ≤ A → IsSylowTwoOf S A →
      IsExt ↥B (fun V _ => IsExtraspecial2 2 V) (fun Y _ => IsAlt 5 Y) →
      S ≤ MulAction.stabilizer (MulAut Q) B →
      ∀ d ∈ Subgroup.normalizer (S : Set (MulAut Q)) ⊓ A, Odd (orderOf d) →
        d ∈ MulAction.stabilizer (MulAut Q) B

@[expose] def FactLie2Norm3312 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsRank2LieChar2 Q →
    ∀ (A S : Subgroup (MulAut Q)) (P : Subgroup Q),
      (MulAut.conj : Q →* MulAut Q).range ≤ A → IsSylowTwoOf S A → IsMaxParabolic2 ⊤ P →
      S ≤ MulAction.stabilizer (MulAut Q) (perfectCore P) →
      ∀ d ∈ Subgroup.normalizer (S : Set (MulAut Q)) ⊓ A, Odd (orderOf d) →
        d ∈ MulAction.stabilizer (MulAut Q) (perfectCore P)

@[expose] def FactL3EpsNorm3312 : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (s : Bool) (Q : Type) [Group Q] [Finite Q],
    (IsPSLEps3 s p 1 Q ∨ IsSLEps3 s p Q) →
    ∀ (A S : Subgroup (MulAut Q)) (B : Subgroup Q),
      (MulAut.conj : Q →* MulAut Q).range ≤ A → IsSylowTwoOf S A → IsSL2 p ↥B →
      S ≤ MulAction.stabilizer (MulAut Q) B →
      ∀ d ∈ Subgroup.normalizer (S : Set (MulAut Q)) ⊓ A, Odd (orderOf d) →
        d ∈ MulAction.stabilizer (MulAut Q) B

end CFSG.Quasithin.H13
