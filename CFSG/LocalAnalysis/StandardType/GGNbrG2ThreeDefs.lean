module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def ggG2SL3Card (n : ℕ) : ℕ := (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)

@[expose] def GGNbrG2NotA2Line : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      Bs ≤ Subgroup.normalizer (K : Set G) → ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun lab _ _ I _ θ => lab.tag = .G2 → 6 ∣ lab.n →
          ggLAut K θ ⟨x, hxK⟩ ∈ I →
            Nat.card (ggFix (K.normalizerMonoidHom ⟨x, hxK⟩)) ≠ ggG2SL3Card lab.n

@[expose] def GGTorusNoLineFieldCompOff (p r : ℕ) (R : Type) [Group R] (I F : Set (MulAut R))
    (N : ℕ) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ (r + 1) ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ((∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          ∀ a₀ ∈ A, a₀ ≠ 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a₀ l)) → GGFixCompCyclic p a₀ →
            Nat.card (ggFix a₀) ≠ N →
            ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀)

@[expose] def GGNbrKGFieldG2Three : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .G2 → 6 ∣ lab.n →
    LargeEvenLabelAll lab (fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineComp 3 2 R I ∧ GGTorusNoLineFieldCompOff 3 2 R I F (ggG2SL3Card lab.n))

end CFSG.StandardType

end
