module

public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofU4
import CFSG.Walter.Bender1970.S3.TransitivityTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def Item2115U4Fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) →
    Nat.card A = 3 ^ 4 → Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
      (∃ P : Sylow 3 G, (P : Subgroup G) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)) ∧
      ∀ g : G, g * c * g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
        g * c * g⁻¹ ∈ Subgroup.zpowers c

@[expose] def Item2115U4Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) →
    Nat.card A = 3 ^ 4 → Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
    (∃ P : Sylow 3 G, (P : Subgroup G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)) →
    (∀ g : G, g * c * g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
      g * c * g⁻¹ ∈ Subgroup.zpowers c) →
    ∀ e ∈ E, e ≠ 1 → ∀ T : Subgroup G, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set G) →
      T ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer ({c} : Set G)

namespace Item2113Res2Proof

open Subgroup

theorem eq_one_of_mem_two_group {G : Type} [Group G] {T : Subgroup G} (hT : IsPGroup 2 T)
    {x : G} (hx : x ∈ T) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨j, hj⟩ := hT ⟨x, hx⟩
  have h2 : x ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hd : orderOf x ∣ Nat.gcd (2 ^ j) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hx3)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left j (by norm_num)), Nat.dvd_one,
    orderOf_eq_one_iff] at hd
  exact hd

theorem item2115U4Ten_of (hF : Item2115U4Fusion) (hLoc : Item2115U4Local) : Item2115U4Ten := by
  intro G _ _ A E U c L hpair hU4 h81 hS4 hW
  obtain ⟨hP, hfus⟩ := hF G A E U c L hpair hU4 h81 hS4 hW
  have hloc := hLoc G A E U c L hpair hU4 h81 hS4 hW hP hfus
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hEe := hpair.mem_E.1.1
  have hE27 : Nat.card E = 27 := hpair.mem_E.1.2.1
  have hcE : c ∈ E := hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : c ^ 3 = 1 := hEe.2 c hcE
  have hall : ∀ T : Subgroup G, IsPGroup 2 T → E ≤ normalizer (T : Set G) →
      T ≤ centralizer ({c} : Set G) := by
    intro T hT2 hET
    have hcop : ¬ 3 ∣ Nat.card T := by
      intro h3
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
      rw [hk] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have hgen := CFSG.Walter.le_iSup_inf_centralizer Nat.prime_three hEe.1
      hEe.2 (by rw [hE27]; norm_num) hET hcop
    refine hgen.trans (iSup_le fun e => iSup_le fun he => iSup_le fun he1 => ?_)
    exact hloc e he he1 T hT2 hET
  obtain ⟨hEU, hUe, hU4c⟩ := mem_fourGroups_iff.mp hpair.mem_U
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4c]; norm_num)
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hU4c
    omega
  set M := normalizer (U : Set G) with hM
  have hM2 : CFSG.Assembly.IsTwoLocal M := ⟨U, hUne, hU2, rfl⟩
  have hT2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hET : E ≤ normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) :=
    hEU.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hTc := hall _ hT2 hET
  have hcC : c ∈ centralizer (CFSG.Assembly.pCoreOf 2 M : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact (mem_centralizer_singleton_iff.mp (hTc hs))
  have hcO : c ∈ CFSG.Open.pCoreOf 2 M :=
    hpair.standing.charTwoType M hM2 ⟨hEU hcE, hcC⟩
  exact hc1 (eq_one_of_mem_two_group hT2 hcO hc3)

end Item2113Res2Proof

end CFSG.RankThree.PartTwo.Sec21
