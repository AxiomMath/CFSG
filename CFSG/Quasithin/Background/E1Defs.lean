module

public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b
open scoped commutatorElement

instance instNormalPCore (p : ℕ) (Q : Type*) [Group Q] : (CFSG.Open.pCore p Q).Normal :=
  CFSG.LieType.BorelTits.pCore_normal p

instance instNormalOInftyE (Q : Type*) [Group Q] : (oInftyE Q).Normal := by
  unfold oInftyE
  have := CFSG.LocalCores.layer_characteristic (G := Q ⧸ CFSG.solvableRadical Q)
  exact Subgroup.normal_comap _

section TwoClosed

variable {G : Type*} [Group G]

@[expose] def IsTwoClosed (R : Subgroup G) : Prop :=
  ∃ P : Subgroup G, IsSylowIn 2 P R ∧ (P.subgroupOf R).Normal

end TwoClosed

section Tau

variable {G : Type*} [Group G]

@[expose] def tauOf (H T A : Subgroup G) : Subgroup G where
  carrier := {t | t ∈ T ∧ t ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) ∧
    ∀ a ∈ A, ⁅t, a⁆ ∈ pCoreOf 2 H}
  one_mem' := ⟨T.one_mem, Subgroup.one_mem _, fun a _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxT, hxN, hx⟩ ⟨hyT, hyN, hy⟩
    refine ⟨T.mul_mem hxT hyT, Subgroup.mul_mem _ hxN hyN, fun a ha => ?_⟩
    have h1 : ⁅x * y, a⁆ = x * ⁅y, a⁆ * x⁻¹ * ⁅x, a⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    refine Subgroup.mul_mem _ ?_ (hx a ha)
    have := (Subgroup.mem_normalizer_iff.mp hxN ⁅y, a⁆).mp (hy a ha)
    simpa [mul_assoc] using this
  inv_mem' := by
    rintro x ⟨hxT, hxN, hx⟩
    refine ⟨T.inv_mem hxT, Subgroup.inv_mem _ hxN, fun a ha => ?_⟩
    have h1 : ⁅x⁻¹, a⁆ = x⁻¹ * (⁅x, a⁆)⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [h1]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) (⁅x, a⁆)⁻¹).mp
      (Subgroup.inv_mem _ (hx a ha))
    simpa [mul_assoc] using this

theorem mem_tauOf {H T A : Subgroup G} {t : G} :
    t ∈ tauOf H T A ↔ t ∈ T ∧ t ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) ∧
      ∀ a ∈ A, ⁅t, a⁆ ∈ pCoreOf 2 H := Iff.rfl

theorem tauOf_le (H T A : Subgroup G) : tauOf H T A ≤ T := fun _ h => h.1

end Tau

section OSeries

variable (Q : Type*) [Group Q]

@[expose] def oTwoP (p : ℕ) : Subgroup Q :=
  (CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q)).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))

instance instNormalOTwoP (p : ℕ) : (oTwoP Q p).Normal := by
  unfold oTwoP
  exact Subgroup.normal_comap _

@[expose] def oTwoPTwo (p : ℕ) : Subgroup Q :=
  (CFSG.Open.pCore 2 (Q ⧸ oTwoP Q p)).comap (QuotientGroup.mk' (oTwoP Q p))

@[expose] def barO2 (B : Subgroup Q) : Subgroup (Q ⧸ CFSG.Open.pCore 2 Q) :=
  B.map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))

@[expose] def barRad (B : Subgroup Q) : Subgroup (Q ⧸ solvableRadical Q) :=
  B.map (QuotientGroup.mk' (solvableRadical Q))

end OSeries

section Conditions

variable (Q : Type*) [Group Q]

@[expose] def EOne (B : Subgroup Q) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ oTwoPTwo Q p = ⊤ ∧
    CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) ≠ ⊥ ∧
    CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) =
      ⁅CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q), barO2 Q B⁆ ∧
    Nat.card (barO2 Q B) = 2

@[expose] def ETwo (S B : Subgroup Q) : Prop :=
  IsTwoClosed (solvableRadical Q) ∧ CFSG.Open.pCore 2 (Q ⧸ oInftyE Q) = ⊤ ∧
    twoResidual (⊤ : Subgroup Q) = perfectCore (⊤ : Subgroup Q) ∧
    ∃ L : Subgroup (Q ⧸ solvableRadical Q), CFSG.IsComponent L ∧
      CFSG.layer (Q ⧸ solvableRadical Q) =
        ⨆ t ∈ (tauOf ⊤ S B).map (QuotientGroup.mk' (solvableRadical Q)), conjSub t L ∧
      (L = ⁅L, barRad Q B⁆ ∨
        (¬ barRad Q B ≤ Subgroup.normalizer (L : Set (Q ⧸ solvableRadical Q)) ∧
          Nat.card (barRad Q B) = 2))

end Conditions

section Families

variable {G : Type*} [Group G]

@[expose] def IsE (i : ℕ) (H T A K : Subgroup G) : Prop :=
  K ≤ H ∧ tauOf H T A ≤ T ⊓ K ∧ IsSylowIn 2 (T ⊓ K) K ∧
    ((EOne ↥K (A.subgroupOf K) ∧ Nat.card (barO2 ↥K (A.subgroupOf K)) ≤ 2 ^ i) ∨
     (ETwo ↥K ((T ⊓ K).subgroupOf K) (A.subgroupOf K) ∧
       Nat.card (barRad ↥K (A.subgroupOf K)) ≤ 2 ^ i))

@[expose] def IsEAny (H T A K : Subgroup G) : Prop := ∃ i : ℕ, IsE i H T A K

@[expose] def eGen (i : ℕ) (H T : Subgroup G) (Ω : Set (Subgroup G)) : Subgroup G :=
  ⨆ A ∈ Ω, ⨆ (_ : A ≤ T), ⨆ K ∈ {K : Subgroup G | IsE i H T A K}, K

@[expose] def weakClosure (X : Subgroup G) (Ω : Set (Subgroup G)) : Subgroup G :=
  ⨆ A ∈ Ω, ⨆ (_ : A ≤ X), A

structure IsInvColl (H : Subgroup G) (Ω : Set (Subgroup G)) : Prop where
  le : ∀ A ∈ Ω, A ≤ H
  isElemAbelian : ∀ A ∈ Ω, IsElemAbelian 2 A
  conj : ∀ A ∈ Ω, ∀ h ∈ H, conjSub h A ∈ Ω

@[expose] def InEFor (i : ℕ) (H T : Subgroup G) : Prop :=
  ∀ Ω : Set (Subgroup G), IsInvColl H Ω →
    eGen i H T Ω ⊔ (H ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) = H

@[expose] def InE (i : ℕ) (H : Subgroup G) : Prop :=
  ∀ T : Subgroup G, IsSylowIn 2 T H → InEFor i H T

@[expose] noncomputable def nParam (H : Subgroup G) : ℕ∞ :=
  if Odd (Nat.card H) then 0 else ⨅ i ∈ {i : ℕ | 0 < i ∧ InE i H}, (i : ℕ∞)

@[expose] def sFamily (T X Y : Subgroup G) : Set (Subgroup G) :=
  {K | K ≤ X ⊔ T ∧ T ≤ K ∧ X ⊔ T = K ⊔ Y ∧
    ∀ K' : Subgroup G, K' ≤ X ⊔ T → T ≤ K' → X ⊔ T = K' ⊔ Y → K' ≤ K → K' = K}

end Families

end E1

end CFSG.Quasithin
