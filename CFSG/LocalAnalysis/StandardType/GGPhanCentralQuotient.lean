module

public import CFSG.LocalAnalysis.StandardType.GGPhanSuBridge

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

structure WeakPhanSL (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    {X : Type} [Group X] {ι : Type} (M : CoxeterMatrix ι) (U : ι → Subgroup X)
    (W : ι → ι → Subgroup X) : Prop where
  iso : ∀ i, Nonempty (Su K p f 2 ≃* U i)
  join : ∀ i j, i ≠ j → W i j = U i ⊔ U j
  comm : ∀ i j, M i j = 2 → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x
  pair : ∀ i j, M i j = 3 → UnitaryBlockStandardPair K p f (W i j) (U i) (U j)
  gen : ⨆ i, U i = ⊤

theorem WeakPhanSL.weakPhanA {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] {X : Type} [Group X] {n : ℕ} {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X} (h : WeakPhanSL K p f (CoxeterMatrix.A n) U W) :
    WeakPhanA K p f n U W where
  iso := h.iso
  join i j hij := h.join i j hij.ne
  comm i j hij := h.comm i j (by
    have hne : i ≠ j := fun e => by subst e; omega
    simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hne]
    rw [if_neg]; omega)
  pair i j hij := h.pair i j (by
    have hne : i ≠ j := fun e => by subst e; omega
    simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hne]
    rw [if_pos]; omega)
  gen := h.gen

@[expose] def IsCentralQuotientOf (Y : LieUniversal) (X : Type) [Group X] : Prop :=
  ∃ θ : Y.K →* X, Function.Surjective θ ∧ θ.ker ≤ Subgroup.center Y.K

theorem phanA_isCentralQuotientOf
    (K : Type) [Field K] [Finite K] (p f : ℕ) (hp : p.Prime) [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : 4 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (U : Fin n → Subgroup X) (W : Fin n → Fin n → Subgroup X)
    (hW : WeakPhanSL K p f (CoxeterMatrix.A n) U W) :
    IsCentralQuotientOf (lieUniversal .PSU (n + 1) p f hp) X :=
  weakPhanA_lieUniversalPSU hp K hK hq hn hW.weakPhanA

end CFSG.ClassicalInvolution.Phan
