module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def ggJQAut {G : Type*} [Group G] (J : Subgroup G) (b : G)
    (hb : b ∈ Subgroup.normalizer (J : Set G)) : MulAut (↥J ⧸ Subgroup.center ↥J) :=
  (centerQuotAut J) (J.normalizerMonoidHom ⟨b, hb⟩)

@[expose] def GGInnDiagPSL3 (Q : ℕ) (X : Type) [Group X] (α : MulAut X) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : X ≃* projectiveSL 3 K),
    Nat.card K = Q ∧ MulAut.congr e α ∈ linearAutGroup 3 K

@[expose] def GGLarge3RankIn2Local {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ E U : Subgroup G, E ≤ L ∧ U ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ IsPGroup 2 U ∧
    U ≠ ⊥ ∧ E ≤ Subgroup.normalizer (U : Set G)

@[expose] def GGNbrG2KSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      Bs ≤ Subgroup.normalizer (K : Set G) → ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun lab _ _ I _ θ => lab.tag = .G2 → 6 ∣ lab.n →
          ggLAut K θ ⟨x, hxK⟩ ∈ I →
            Nat.card (ggFix (K.normalizerMonoidHom ⟨x, hxK⟩)) = ggG2SL3Card lab.n →
              Nat.card B = 3 ^ 4 ∧
              (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ lab.n ∧
                Nonempty (↥J ⧸ Subgroup.center ↥J ≃* projectiveSL 3 F)) ∧
              ∃ b ∈ B, ∃ hb : b ∈ Subgroup.normalizer (J : Set G),
                ¬ GGInnDiagPSL3 (2 ^ lab.n) (↥J ⧸ Subgroup.center ↥J) (ggJQAut J b hb)

@[expose] def GGNbrLSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ¬ GGLarge3RankIn2Local L → ∀ (Q : ℕ), 4 ≤ Q → 3 ∣ Q - 1 →
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = Q ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃* projectiveSL 3 F)) →
        ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (J : Set G),
          GGInnDiagPSL3 Q (↥J ⧸ Subgroup.center ↥J) (ggJQAut J b hb)

end CFSG.StandardType

end
