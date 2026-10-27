module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddComm
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddInv
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddStrong
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem not_isPGroup_barO3_opp (S : SliceCore D L D₃ Y H) :
    ¬ IsPGroup 3 (F09.BarO3 (Opp 3 Y)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  have hle : CFSG.pPrimeCore 3 ↥(Opp 3 Y) ≤ CFSG.pCore 2 ↥(Opp 3 Y) :=
    le_pCore_two_of_normal S.isSimpleGroup_bar2_opp S.three_dvd_card_bar2_opp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card)
  have hker : CFSG.pPrimeCore 3 ↥(Opp 3 Y) ≤
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Opp 3 Y))).ker := by
    rwa [QuotientGroup.ker_mk']
  haveI := (h3.of_surjective (QuotientGroup.lift _ _ hker)
    (QuotientGroup.lift_surjective_of_surjective _ _
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(Opp 3 Y))) hker)).isNilpotent
  exact S.not_isSolvable_bar2_opp inferInstance

end SliceCore

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem mem_of_fixed_of_inv_opp (S : Slice D L D₃ Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {U W : Subgroup G} {r : ℕ} (hr : Odd r)
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r (Opp 3 Y) U W) (hW3 : ¬ 3 ∣ Nat.card W)
    (hWM : W ≤ D.M) (hUM : U ⊓ D.M ≤ W) {A : Subgroup G} (hAX : A ≤ Opp 3 Y)
    (hA : (Nat.card A).Prime) (hA2 : Nat.card A ≠ 2) {t : G} (htX : t ∈ Opp 3 Y)
    (htA : ∀ a ∈ A, a * t = t * a) (htinv : ∀ u ∈ U, u * (t * u * t⁻¹) ∈ W) :
    ∀ u ∈ U, (∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ W) → u ∈ W := by
  haveI : Fact (Nat.card A).Prime := ⟨hA⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWU : W ≤ U := hUW.1.le
  have hUnW : U ≤ normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWU).mp hUW.normal
  have hnW₂ := UC6S846.normalizer_le_normalizer_pCoreOf W
  have hp : ¬ Nat.card A ∣ Nat.card (pCoreOf 2 W) := by
    have h2 : IsPGroup 2 (pCoreOf 2 W) := CFSG.pCore_isPGroup.map W.subtype
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [hk]
    exact fun h => hA2 ((Nat.prime_dvd_prime_iff_eq hA Nat.prime_two).mp (hA.dvd_of_dvd_pow h))
  have hcomm : ⁅W, Opp 3 Y⁆ ≤ pCoreOf 2 W := S.comm_le_pCoreOf ⟨hWM, hW3, hUW.2.2.1⟩
  refine mem_of_fixed_of_inv hr hUW.2.2.2.2.2.1 hWU (map_subtype_le _) hUW.2.2.2.1
    (fun u hu w hw => (Subgroup.mem_normalizer_iff.mp (hnW₂ (hUnW hu)) w).mp hw)
    (IsPGroup.of_card (n := 1) (pow_one _).symm) hp
    (fun a ha w hw => (Subgroup.mem_normalizer_iff.mp (hnW₂ (hUW.2.2.1 (hAX ha))) w).mp hw)
    (fun u hu => (Subgroup.mem_normalizer_iff.mp (hUW.2.1 htX) u).mp hu) htA
    (fun w hw => by
      have h := hcomm (Subgroup.commutator_mem_commutator hw htX)
      rwa [commutatorElement_def] at h) htinv ?_
  intro n hnU hnA
  have hnC : n ∈ centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => mul_inv_eq_iff_eq_mul.mp (hnA a ha)
  exact hUM ⟨hnU, hN A (hAX.trans (opp_le 3 Y)) hA (hA.odd_of_ne_two hA2)
    (Subgroup.centralizer_le_normalizer _ hnC)⟩

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
