module

public import CFSG.Quasithin.Background.A3Structure318Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

instance finite_zornAut' {F : Type*} [Field F] [Finite F] :
    Finite (quasithinZorn F ≃ₗ[F] quasithinZorn F) :=
  Finite.of_injective (fun g : quasithinZorn F ≃ₗ[F] quasithinZorn F =>
    (g : quasithinZorn F → quasithinZorn F)) (fun _ _ hgh => LinearEquiv.ext (congrFun hgh))

@[expose] def FactTorusRank : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n → ∀ p : ℕ, p.Prime →
    (p ∣ 2 ^ n - 1 →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))) ∧
    (p ∣ 2 ^ (2 * n) - 1 → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSp 2 K)) ∧
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥⁅quasithinG2 K, quasithinG2 K⁆))

@[expose] def FactA318Excl : Prop :=
  (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    Subgroup.center ↥(StatedSp 2 K) = ⊥ ∧ Subgroup.center ↥⁅quasithinG2 K, quasithinG2 K⁆ = ⊥ ∧
    ∀ (X : Type) [Group X] (s : Bool) (r e : ℕ), IsPSLEps3 s r e X →
      (∀ f : X →* ↥(StatedSp 2 K), ¬ Function.Surjective f) ∧
      (∀ f : X →* ↥⁅quasithinG2 K, quasithinG2 K⁆, ¬ Function.Surjective f)) ∧
  (∀ (X : Type) [Group X] [Finite X], A318Case3Group X → Nat.card (Subgroup.center X) = 3)

structure Facts04 : Prop where
  torus : FactTorusRank
  excl : FactA318Excl

end CFSG.Quasithin.Vol2.Ch11.SecA
