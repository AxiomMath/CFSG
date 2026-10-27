module

public import CFSG.Walter.Ree.T2Interface

public section

namespace CFSG.Walter.Ree.T2.Alg

variable {k : Type} [Field k]

@[expose] def FE1C (a : ℕ) (S : k → k × k × k) : Prop :=
  ∀ x : k, x + 1 ≠ 0 →
    S x = ((S ((1 - x) / (1 + x))).1 * ((x + 1) ^ a)⁻¹,
      (S ((1 - x) / (1 + x))).2.1 * ((x + 1) ^ 2)⁻¹ - (x + 1)⁻¹,
      (S ((1 - x) / (1 + x))).2.2 * ((x + 1) ^ (a + 2))⁻¹)

@[expose] def FE2C (σ : k ≃+* k) (d : k) (S : k → k × k × k) : Prop :=
  ∀ x : k, x - 1 ≠ 0 →
    S x = (-(S ((x + 1) / (x - 1))).1 - 1,
      (S ((x + 1) / (x - 1))).2.1 + (S ((x + 1) / (x - 1))).1 - σ (S ((x + 1) / (x - 1))).1,
      1 - d - (S ((x + 1) / (x - 1))).2.2 - (S ((x + 1) / (x - 1))).2.1 -
        σ (S ((x + 1) / (x - 1))).1 - (S ((x + 1) / (x - 1))).1 +
          (S ((x + 1) / (x - 1))).1 ^ 2)

@[expose] def GF3C (d : k) (S : k → k × k × k) : Prop :=
  S (-1) = (0, -1, 1) ∧ S 0 = (-1, -1, 1 - d) ∧ S 1 = (-1, 0, 1 - d)

@[expose] def T81C1 (σ : k ≃+* k) (S : k → k × k × k) : Prop :=
  ∀ z y u : k, z ≠ 0 → y ≠ 0 → (z, y, u) ∈ hopkinsE σ → (S u).1 * z = (S (-u)).1 * y + 1

@[expose] def T81C3 (σ : k ≃+* k) (d : k) (S : k → k × k × k) : Prop :=
  ∀ z y u : k, z ≠ 0 → y ≠ 0 → (z, y, u) ∈ hopkinsE σ →
    (S u).2.2 * (z ^ 2 * σ z) = d - 1 + (S (-u)).2.2 * (y ^ 2 * σ y) +
      (S (-u)).2.1 * (y * σ y) + σ ((S (-u)).1 * y) + (S (-u)).1 * y - ((S (-u)).1 * y) ^ 2

end CFSG.Walter.Ree.T2.Alg
