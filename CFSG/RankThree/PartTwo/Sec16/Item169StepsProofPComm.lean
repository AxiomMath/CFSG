module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofTheta
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169Theta CFSG.GH74.GLS

@[expose] def KS169HessCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec4.IsoLThreePi X 2 n →
    ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8) →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      IsPGroup 3 (Subgroup.centralizer (E : Set X))

namespace ProofPComm

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_map {H : Type*} [Group H] {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian p E) (f : G →* H) :
    CFSG.Assembly.IsElemAbelian p (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {A L : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian p A) : CFSG.Assembly.IsElemAbelian p (A.subgroupOf L) :=
  CFSG.Open.IsElemAbelian.subgroupOf hA L

theorem eq_one_of_pow_eq_one_of_isPGroup {H : Type*} [Group H] {C : Subgroup H} (hC : IsPGroup 3 C)
    {x : H} (hx : x ∈ C) {p : ℕ} (hp3 : Nat.Coprime 3 p) (hxp : x ^ p = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hC ⟨x, hx⟩
  have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 := orderOf_dvd_of_pow_eq_one hk'
  have h2 := orderOf_dvd_of_pow_eq_one hxp
  have hcop : Nat.Coprime (3 ^ k) p := Nat.Coprime.pow_left k hp3
  have : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp this

theorem inf_centralizer_eq_bot {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD13 : Sec13Data G A c L) {b : G} {n p : ℕ} {P : Subgroup G}
    (hD : Data1619 A c L b n p P) (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    (h9 : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8)) (hK : KS169HessCent) :
    P ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
  obtain ⟨hn1, hiso, ⟨φ⟩⟩ := hD.isZ3
  have hp := hD.prime
  have hp3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by
    have := hD.three_lt
    omega)
  have hp2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by
    have := hD.three_lt
    omega)
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπdef
  set E := (A.subgroupOf L).map π with hEdef
  have hE : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_map (isElemAbelian_subgroupOf hD13.isElemAbelian) π
  have hE9 : Nat.card E = 9 := by
    rw [hEdef, hπdef, card_map_mk_subgroupOf hD13.isElemAbelian]
    exact card_inf_eq_nine hD13 (isPerfect_lBar hD13) φ
  have hC := hK _ n hn1 hiso h9 E hE hE9
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxA⟩
  rw [Subgroup.mem_bot]
  have hxL : x ∈ L := (hD.mem_Q.1.2 hxP).1
  have hxp : x ^ p = 1 := hD.elem.2 x hxP
  set x' : ↥L := ⟨x, hxL⟩ with hx'
  have hx'p : x' ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hxE : π x' ∈ Subgroup.centralizer (E : Set (↥L ⧸ θ)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
    have hcomm : (y : G) * x = x * (y : G) := Subgroup.mem_centralizer_iff.mp hxA _ hyA
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hcomm)
  have hπx : π x' = 1 :=
    eq_one_of_pow_eq_one_of_isPGroup hC hxE hp3 (by rw [← map_pow, hx'p, map_one])
  have hxθ' : x' ∈ θ := (QuotientGroup.eq_one_iff x').mp hπx
  have hxθ : x' ∈ CFSG.pCore 2 ↥L := by
    rw [← hθ]
    exact hxθ'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x', hxθ⟩
  have hk' : x' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 := orderOf_dvd_of_pow_eq_one hk'
  have h2 := orderOf_dvd_of_pow_eq_one hx'p
  have hord : orderOf x' = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hp2) h1 h2
  have hx1 : x' = 1 := orderOf_eq_one_iff.mp hord
  exact congrArg Subtype.val hx1

end ProofPComm

open ProofPComm

theorem step169PComm_of
    (h135 : Item135Simple) (h138 : Item138N)
    (hK : KS169HessCent) : Step169PComm := by
  intro G _ _ A c L hc b n p P hD
  have hD13 := hc.toSec13Data
  obtain ⟨hn1, hiso, hprod⟩ := hD.isZ3
  have h9 : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8) :=
    not_modNine_of_inner hc.toSec15R h138 KFacts.kSL3PiOrder3TypeC hn1 hiso hprod
  have hθ := theta_eq_pCore_two_of_item135Simple h135 hD13 (Or.inl ⟨2, n, inferInstance, hn1, hiso⟩)
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD13.card_eq]; norm_num)
  have hP3 : ¬ 3 ∣ Nat.card P := by
    rw [hD.card]
    intro h3
    have h3p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hD.prime).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    have := hD.three_lt
    omega
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := hD.mem_Q.1.1.1.2.2
  have hfac := RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
    Nat.prime_three A P hA3 hP3 hAP
  rwa [inf_centralizer_eq_bot hD13 hD hθ h9 hK, sup_bot_eq] at hfac

end CFSG.RankThree.PartTwo.Sec16
