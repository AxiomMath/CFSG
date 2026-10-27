module

public import CFSG.Quasithin.Recognition.Stroth.Str86Crit
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RLab

import CFSG.Quasithin.Recognition.St84.Gen.S3Slice

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G : Type} [Group G] [Finite G]

structure Str86AbHyp (L1 L2 S : Subgroup G) (k m : ℕ) (F : Type) [Field F] [Finite F] :
    Prop where
  hF : F112Hyp L1 L2 S
  hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)
  hk : 2 ≤ k
  hFc : Nat.card F = (2 ^ k) ^ 2
  hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
    Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))
  hB2 : VBig L2
  hm : 2 ≤ m
  hL2 : IsL2Quot m (oTwoQuot ↥L2)
  hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)

theorem str86AbHyp_exists {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (h1 : VU3Big L1) (hB2 : VBig L2)
    (h2 : VL2 L2) (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    ∃ (k m : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Str86AbHyp L1 L2 S k m F := by
  obtain ⟨k, hk, F, hFld, hFin, hFc, hU3⟩ := h1
  obtain ⟨m, hL2⟩ := h2
  exact ⟨k, m, F, hFld, hFin, hF, hSB, hk, hFc, hU3, hB2,
    two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2, hL2, hZI⟩

theorem Str86AbHyp.critHypN {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    CritHypN (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) S (Z2 L1 L2 S) :=
  str86_critHypN hI.hF hI.hSB ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
    hI.hB2 ⟨m, hI.hL2⟩ hI.hZI

abbrev Str86Γ (L1 L2 S : Subgroup G) : Type :=
  CosetGeom (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)

@[expose] noncomputable def str86V2 (L1 L2 S : Subgroup G) (δ : Str86Γ L1 L2 S) :
    Subgroup G :=
  ⨆ (γ : Str86Γ L1 L2 S) (_ : γ ∈ nbrs δ), Vv (Z2 L1 L2 S) γ

structure Str86CritPath (L1 L2 S : Subgroup G) (lam : ℕ → Str86Γ L1 L2 S) : Prop where
  linear : vtype (lam 0) = false
  isGeo : CosetGeom.IsGeo lam (str86CritB L1 L2 S)
  critical : ¬ Vv (Z2 L1 L2 S) (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))

@[expose] def Str86OddRGeQSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (k m : ℕ) (F : Type) [Field F]
    [Finite F],
    Str86AbHyp L1 L2 S k m F → 3 ≤ str86CritB L1 L2 S → Odd (str86CritB L1 L2 S) → 2 * k ≤ m

end CFSG.Quasithin.Stroth

end
