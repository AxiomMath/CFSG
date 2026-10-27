module

public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofEnd
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec16.Item16TailEnd

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] noncomputable def Step1623EndRep : Prop :=
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
      ∃ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 ∧
        ∃ S : Subgroup G, S ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ∧
          R ≤ S ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
          ⁅S, A ⊓ Subgroup.centralizer (R : Set G)⁆ ≠ ⊥

namespace Proof1623EndS

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_commutator_ne_bot {R S B : Subgroup G} (hR2 : IsPGroup 2 R)
    (hS2 : IsPGroup 2 S) (hB : Nat.Coprime 2 (Nat.card B)) (hRS : R ≤ S)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) (hBR : B ≤ Subgroup.centralizer (R : Set G))
    (hne : ⁅S, B⁆ ≠ ⊥) : ⁅S ⊓ Subgroup.centralizer (R : Set G), B⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h0
  apply hne
  have hRB : ⁅R, B⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hBR)
  refine GorensteinWalter.ThompsonPQ.thompson_p_times_q R B S hR2 hS2 hB
    (hRS.trans Subgroup.le_normalizer) hBS hRB ?_
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0

end Proof1623EndS

open Proof1623EndS

theorem step1623EndS_of (hRep : Step1623EndRep) : Step1623EndS := by
  intro G _ _ A c L h hLs n hn hU hΩ h21 hH R hRmin hR4 hRc hB9 hRb
  obtain ⟨b, hbB, hb1, S, hSb, hRS, hS2, hAS, hSB⟩ :=
    hRep G A c L h hLs n hn hU hΩ h21 hH R hRmin hR4 hRc hB9 hRb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 2) (by rw [hR4.card_four]; norm_num)
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRmin.prop.1.1.1.1.2.2
  have hAC : A ≤ Subgroup.normalizer
      ((Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) :=
    hAR.trans (Proof169.normalizer_le_normalizer_centralizer R)
  have hBco : Nat.Coprime 2 (Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G)) := by
    rw [hB9]
    norm_num
  refine ⟨b, hbB, hb1, S ⊓ Subgroup.centralizer (R : Set G), inf_le_left.trans hSb, inf_le_right,
    hS2.to_le inf_le_left, Proof169.le_normalizer_inf hAS hAC, ?_⟩
  exact inf_centralizer_commutator_ne_bot hR2 hS2 hBco hRS
    ((inf_le_left : A ⊓ Subgroup.centralizer (R : Set G) ≤ A).trans hAS) inf_le_right hSB

end CFSG.RankThree.PartTwo.Sec16
