module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlat

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

@[expose] def BMNoLiePComp (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ x : K, orderOf x = p → ∀ C : Subgroup K, LargeEvenPComponent p (Subgroup.centralizer {x}) C →
    ¬ StandardType.LargeEvenMarking
      ↥((C.subgroupOf (Subgroup.centralizer {x})).map
        (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({x} : Set K)))))
      (fun _ _ _ _ _ _ => True)

@[expose] def BMPPrimeCore (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ x : K, orderOf x = p →
    (∀ C : Subgroup K, ¬ LargeEvenPComponent p (Subgroup.centralizer {x}) C) →
      LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({x} : Set K)) = ⊥

@[expose] def BMCentreZ (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ x : K, orderOf x = p →
    (∀ C : Subgroup K, ¬ LargeEvenPComponent p (Subgroup.centralizer {x}) C) →
      ∀ A : Subgroup K, A ≤ Subgroup.centralizer {x} →
        (∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
          IsElemAbelian p A → A ≤ Subgroup.zpowers x

@[expose] def BMOrd (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ L : Subgroup K, IsSimpleGroup L → StandardType.LargeEvenMarking L (fun _ _ _ _ _ _ => True) →
    ¬ p ^ (Nat.card K).factorization p ∣ Nat.card (MulAut L)

@[expose] def BMElevenComp (K : Type) [Group K] [Finite K] : Prop :=
  ∀ x : K, orderOf x = 11 →
    ∃ C : Subgroup K, LargeEvenPComponent 11 (Subgroup.centralizer {x}) C ∧
      ¬ StandardType.LargeEvenMarking
        ↥((C.subgroupOf (Subgroup.centralizer {x})).map
          (QuotientGroup.mk' (LargeEvenPPrimeCore 11 ↥(Subgroup.centralizer ({x} : Set K)))))
        (fun _ _ _ _ _ _ => True)

@[expose] def BSevenComp (K : Type) [Group K] [Finite K] : Prop :=
  ∀ x : K, orderOf x = 7 → ∃ J : Subgroup K, IsComponentOf J (Subgroup.centralizer {x}) ∧
    (∀ J' : Subgroup K, IsComponentOf J' (Subgroup.centralizer {x}) → J' = J) ∧
    Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set K)) = 2 ∧
    LargeEvenPPrimeCore 7 ↥(Subgroup.centralizer ({x} : Set K)) =
      (J ⊓ Subgroup.centralizer (J : Set K)).subgroupOf (Subgroup.centralizer {x})

@[expose] def BSevenCentAbelian (K : Type) [Group K] [Finite K] : Prop :=
  ∀ E : Subgroup K, IsElemAbelian 7 E → Nat.card E = 49 →
    ∀ a ∈ Subgroup.centralizer (E : Set K), ∀ b ∈ Subgroup.centralizer (E : Set K), a * b = b * a

@[expose] def BSevenSpread (K : Type) [Group K] [Finite K] : Prop :=
  ∀ E : Subgroup K, IsElemAbelian 7 E → Nat.card E = 49 → ¬ ∃ t : K, t ≠ 1 ∧
    ∀ e ∈ E, e ≠ 1 → ∀ J : Subgroup K, IsComponentOf J (Subgroup.centralizer {e}) →
      t ∈ J ⊓ Subgroup.centralizer (J : Set K)

@[expose] noncomputable def BMOpCent (p : ℕ) {K : Type} [Group K] (x : K) : Subgroup K :=
  (CFSG.pCore p ↥(Subgroup.centralizer ({x} : Set K))).map
    (Subgroup.centralizer ({x} : Set K)).subtype

@[expose] def BMPCentralF1 (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ x : K, orderOf x = p →
    (∀ C : Subgroup K, ¬ LargeEvenPComponent p (Subgroup.centralizer {x}) C) →
      x ∈ BMOpCent p x ∧ ⁅BMOpCent p x, BMOpCent p x⁆ = Subgroup.zpowers x ∧
        BMOpCent p x ⊓ Subgroup.centralizer ((BMOpCent p x : Subgroup K) : Set K) =
          Subgroup.zpowers x ∧
        Subgroup.centralizer {x} ⊓ Subgroup.centralizer ((BMOpCent p x : Subgroup K) : Set K) ≤
          BMOpCent p x

@[expose] def BMPCentralF4 (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ x : K, orderOf x = p →
    (∀ C : Subgroup K, ¬ LargeEvenPComponent p (Subgroup.centralizer {x}) C) →
      ∀ N : Subgroup K, N ≤ Subgroup.centralizer {x} →
        (∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
          Subgroup.zpowers x ≤ N → N ≤ BMOpCent p x → N = Subgroup.zpowers x ∨ N = BMOpCent p x

end CFSG.StandardType.SporadicShape
