module

import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] noncomputable def Step1623Frattini : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → IsSimpleGroup ↥L → ∀ n : ℕ, IsZ3LThreeTwo A c L n →
      Nonempty (↥L ≃* projSU 3 2 n) → omegaA A = {Subgroup.zpowers c} →
    (∀ a ∈ A, a ≠ 1 → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) = ⊥) →
    (∀ T ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2),
      T = ⊥) →
    ∀ R : Subgroup G, Minimal (fun Q => Q ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ Q ≠ ⊥) R →
      IsKleinFour R → R = ⁅R, Subgroup.zpowers c⁆ →
      Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = 9 →
      (∀ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 →
        R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) →
      ∀ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 →
      ∀ S ∈ scriptQPiStar A (lB A) (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))
          (piOf 2),
        R ≤ S → ⁅S, A ⊓ Subgroup.centralizer (R : Set G)⁆ = ⊥ →
          CFSG.Open.pCoreOf 2 (Subgroup.centralizer (S : Set G)) ⊓
              Subgroup.centralizer ({b} : Set G) ≤
            pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))

namespace Proof1623Rep

variable {G : Type} [Group G] [Finite G]

theorem commutator_pCoreOf_normalizer_ne_bot (hG : CFSG.Assembly.IsCharTwoType G)
    {S B : Subgroup G} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hB3 : IsPGroup 3 B) (hB1 : B ≠ ⊥)
    (hBS : B ≤ Subgroup.centralizer (S : Set G)) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S : Set G)), B⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (S : Set G) with hM
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMloc : IsPLocal 2 M := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hS2 hS1
  have hMchar : IsCharacteristicP 2 ↥M := CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hG hMloc
  have hBM : B ≤ M := hBS.trans (Subgroup.centralizer_le_normalizer _)
  intro h0
  have hBC : B ≤ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.commutator_comm] at h0
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
  have hBQ : B ≤ Q := by
    intro x hx
    have hxM : x ∈ M := hBM hx
    have hx' : (⟨x, hxM⟩ : ↥M) ∈ Subgroup.centralizer (CFSG.pCore 2 ↥M : Set ↥M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyQ : (y : G) ∈ Q := by
        exact ⟨y, hy, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hBC hx) (y : G) hyQ)
    have hxO := hMchar hx'
    exact ⟨_, hxO, rfl⟩
  apply hB1
  rw [eq_bot_iff]
  intro x hx
  exact Subgroup.mem_bot.mpr
    (Proof1619.eq_one_of_mem_of_mem (by norm_num : Nat.Coprime 3 2) hB3 hQ2 hx (hBQ hx))

end Proof1623Rep

open Proof1623Rep

end CFSG.RankThree.PartTwo.Sec16
