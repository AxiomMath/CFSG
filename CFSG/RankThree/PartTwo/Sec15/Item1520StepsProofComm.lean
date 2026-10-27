module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof1520

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_three_of_isElemAbelian {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup hA

omit [Finite G] in
theorem eq_one_of_pow_eq_one_of_isPGroup {H : Type*} [Group H] {C : Subgroup H}
    (hC : IsPGroup 3 ↥C) {x : H} (hx : x ∈ C) {p : ℕ} (hp3 : Nat.Coprime 3 p)
    (hxp : x ^ p = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hC ⟨x, hx⟩
  have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (3 ^ k) p := Nat.Coprime.pow_left k hp3
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_of_pow_eq_one hxp))

theorem inf_centralizer_eq_bot (h1517 : Step1517R) (h138 : Item138N) (hK : KS1520HessCent)
    {A : Subgroup G} {c : G} {L Y : Subgroup G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) {p : ℕ} {P : Subgroup G} (hP : Data1519 A (lB A) L p P) :
    P ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
  obtain ⟨m, hm1, hisoL, h9, -, -, h9AL, -⟩ := config_of h1517 h138 h hctx hP
  have hp : p.Prime := hP.1
  have hp3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by
    have := hP.2.1
    omega)
  have hPL : P ≤ L := hP.2.2.2.2.2.1.1.2
  set E : Subgroup ↥L := A.subgroupOf L with hE
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_subgroupOf L h.toSec13Data.isElemAbelian
  have hE9 : Nat.card ↥E = 9 := by
    rw [hE, ← Subgroup.inf_subgroupOf_right, card_subgroupOf_inf, h9AL]
  have hC := hK ↥L m hm1 hisoL h9 E hEab hE9
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxP, hxA⟩ := Subgroup.mem_inf.mp hx
  have hxL : x ∈ L := hPL hxP
  have hxE : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.centralizer (E : Set ↥L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxA (e : G) he)
  have hxp : (⟨x, hxL⟩ : ↥L) ^ p = 1 := Subtype.ext (by simpa using hP.2.2.2.1.2 x hxP)
  have h1 := eq_one_of_pow_eq_one_of_isPGroup hC hxE hp3 hxp
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

end Proof1520

open Proof1520

theorem step1520Comm_of (h1517 : Step1517R) (h138 : Item138N) (hK : KS1520HessCent) :
    Step1520Comm := by
  intro G _ _ A c L h Y hctx p P hP
  have hp : p.Prime := hP.1
  have h3P : ¬ 3 ∣ Nat.card ↥P := by
    rw [hP.2.2.2.2.1]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    have := hP.2.1
    omega
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := hP.2.2.2.2.2.1.1.1.1.2.2
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three A P (isPGroup_three_of_isElemAbelian h.toSec13Data.isElemAbelian) h3P hAP
  rwa [inf_centralizer_eq_bot h1517 h138 hK h hctx hP, sup_bot_eq] at hfac

end CFSG.RankThree.PartTwo.Sec15
