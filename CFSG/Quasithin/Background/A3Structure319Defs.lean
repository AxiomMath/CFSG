module

public import CFSG.Quasithin.Background.A3Structure318Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

@[expose] def IsNaturalSum {H : Type} [Group H] (s : ℕ) (K : Type) [Field K] (L V : Subgroup H)
    (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)) : Prop :=
  ∃ W : Fin s → Subgroup H, (∀ i, W i ≤ V) ∧ V = ⨆ i, W i ∧ iSupIndep W ∧
    ∀ i, ∃ θ : ↥(W i) ≃* Multiplicative (Fin 3 → K), ∀ (l : ↥L) (v : ↥(W i)),
      ∃ v' : ↥(W i), (v' : H) = (l : H) * (v : H) * (l : H)⁻¹ ∧
        θ v' = Multiplicative.ofAdd
          ((((φ (QuotientGroup.mk l)).1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            Multiplicative.toAdd (θ v))

@[expose] def A319Hyp {H : Type} [Group H] (L V : Subgroup H) : Prop :=
  ∃ (n s : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
    (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)),
    Even n ∧ Nat.card K = 2 ^ n ∧ 1 ≤ s ∧ s ≤ 2 ∧ IsNaturalSum s K L V φ

@[expose] def A319PrintedHyp {H : Type} [Group H] (L V : Subgroup H) : Prop :=
  ∃ (n s : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
    (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)),
    Even n ∧ Nat.card K = 2 ^ n ∧ s ≤ 2 ∧ IsNaturalSum s K L V φ

theorem A319Hyp.printed {H : Type} [Group H] {L V : Subgroup H} (hHyp : A319Hyp L V) :
    A319PrintedHyp L V := by
  obtain ⟨n, s, K, fieldInstance, finiteInstance, φ, hn, hcard, _, hbound, hsum⟩ := hHyp
  exact ⟨n, s, K, fieldInstance, finiteInstance, φ, hn, hcard, hbound, hsum⟩

@[expose] def A319SL3Facts : Prop :=
  (∀ (K : Type) [Field K] [Finite K], 4 ≤ Nat.card K → CFSG.IsQuasisimple ↥(StatedSL 3 K)) ∧
  (∀ (K : Type) [Field K] [Finite K], Nat.card (Subgroup.center ↥(StatedSL 3 K)) ≤ 3) ∧
  (∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 3 K)))

@[expose] def A319CoreFact : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SQTKGroup H → ∀ (L V : Subgroup H),
    L ∈ cComp (⊤ : Subgroup H) → L.Normal → CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    V.Normal → IsElemAbelian 2 V → A319Hyp L V → A318Conclusion 3 L →
    ∀ h : H, (∃ k : ℕ, orderOf h = 3 ^ k) → h ^ 3 ∈ L → h ∈ L

structure A319Facts : Prop where
  sl3 : A319SL3Facts
  core : A319CoreFact

end CFSG.Quasithin
