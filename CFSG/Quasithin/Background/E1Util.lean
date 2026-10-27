module

public import CFSG.Quasithin.Background.E1Defs
public import CFSG.GroupTheory.SolvableHallNodes
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b

variable {G : Type*} [Group G]

@[expose] def PiNum (p n : ℕ) : Prop := ∀ q : ℕ, q.Prime → q ∣ n → q = 2 ∨ q = p

theorem PiNum.mul {p a b : ℕ} (ha : PiNum p a) (hb : PiNum p b) : PiNum p (a * b) := by
  intro q hq hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · exact ha q hq h
  · exact hb q hq h

theorem PiNum.of_dvd {p a b : ℕ} (hb : PiNum p b) (h : a ∣ b) : PiNum p a :=
  fun q hq hqa => hb q hq (hqa.trans h)

theorem piNum_two_pow (p n : ℕ) : PiNum p (2 ^ n) := by
  intro q hq hdvd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))

theorem piNum_prime_pow {p : ℕ} (hp : p.Prime) (n : ℕ) : PiNum p (p ^ n) := by
  intro q hq hdvd
  exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd))

theorem piNum_card_of_isPGroup {p q : ℕ} {H : Type*} [Group H] [Finite H] (hq : q.Prime)
    (hp : IsPGroup q H) (hpq : q = 2 ∨ q = p) : PiNum p (Nat.card H) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  rw [hn]
  rcases hpq with rfl | rfl
  · exact piNum_two_pow _ _
  · exact piNum_prime_pow hq _

theorem exists_relIndex_eq_prime_pow [Finite G] {p : ℕ} [Fact p.Prime] {N H : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hq : ∀ x ∈ H, ∃ k : ℕ, x ^ p ^ k ∈ N) :
    ∃ n : ℕ, N.relIndex H = p ^ n := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have hp : IsPGroup p (H ⧸ N.subgroupOf H) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨k, hk⟩ := hq d d.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  exact ⟨n, hn⟩

theorem isSolvable_of_pow_mem [Finite G] {p : ℕ} [Fact p.Prime] {N H : Subgroup G}
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hq : ∀ x ∈ H, ∃ k : ℕ, x ^ p ^ k ∈ N) [hN : Group.IsSolvable N] : Group.IsSolvable H := by
  have hnorm := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have hp : IsPGroup p (H ⧸ N.subgroupOf H) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨k, hk⟩ := hq d d.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  have h1 : Group.IsSolvable (H ⧸ N.subgroupOf H) := by
    have : Group.IsNilpotent (H ⧸ N.subgroupOf H) := hp.isNilpotent
    infer_instance
  have h2 : Group.IsSolvable (N.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNH).injective
  exact Group.isSolvable_of_subgroup_quotient (N.subgroupOf H)

theorem isSolvable_of_isPGroup_two [Finite G] {N : Subgroup G} (hN : IsPGroup 2 N) :
    Group.IsSolvable N := by
  have : Group.IsNilpotent N := hN.isNilpotent
  infer_instance

theorem mul_pow_mem_of_mem_normalizer {X : Subgroup G} {x n : G} (hx : x ∈ X)
    (hn : n ∈ Subgroup.normalizer (X : Set G)) (k : ℕ) :
    ∃ x' ∈ X, (x * n) ^ k = x' * n ^ k := by
  induction k with
  | zero => exact ⟨1, X.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨x', hx', h⟩ := ih
    have hnk : n ^ k ∈ Subgroup.normalizer (X : Set G) := Subgroup.pow_mem _ hn k
    have h1 : n ^ k * x * (n ^ k)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hnk x).mp hx
    refine ⟨x' * (n ^ k * x * (n ^ k)⁻¹), X.mul_mem hx' h1, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem exists_pow_mem_of_mem_sup {X N : Subgroup G} (hN : IsPGroup 2 N)
    (hNX : N ≤ Subgroup.normalizer (X : Set G)) {q : G} (hq : q ∈ X ⊔ N) :
    ∃ j : ℕ, q ^ 2 ^ j ∈ X := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X N hNX] at hq
  obtain ⟨x, hx, n, hn, rfl⟩ := hq
  obtain ⟨m, hm⟩ := hN ⟨n, hn⟩
  have hnm : n ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  obtain ⟨x', hx', h⟩ := mul_pow_mem_of_mem_normalizer hx (hNX hn) (2 ^ m)
  refine ⟨m, ?_⟩
  show (x * n) ^ 2 ^ m ∈ X
  rw [h, hnm, mul_one]
  exact hx'

theorem isSolvable_of_isTwoClosed [Finite G] {R : Subgroup G} (h : IsTwoClosed R) :
    Group.IsSolvable R := by
  obtain ⟨P, hP, hPn⟩ := h
  have hP2 : IsPGroup 2 (P.subgroupOf R) :=
    hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP.le).symm
  have h1 : Group.IsSolvable (P.subgroupOf R) := by
    have : Group.IsNilpotent (P.subgroupOf R) := hP2.isNilpotent
    infer_instance
  have hodd : Odd (Nat.card (R ⧸ P.subgroupOf R)) := by
    have : ¬ 2 ∣ (P.subgroupOf R).index := hP.not_dvd_relIndex
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp this)
  have h2 : Group.IsSolvable (R ⧸ P.subgroupOf R) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_subgroup_quotient (P.subgroupOf R)

theorem exists_hall_two_p [Finite G] {K T : Subgroup G} {p : ℕ} (hp : p.Prime) (hTK : T ≤ K)
    (hT : IsPGroup 2 T) (hK : Group.IsSolvable K) :
    ∃ K₀ : Subgroup G, K₀ ≤ K ∧ T ≤ K₀ ∧ PiNum p (Nat.card K₀) ∧
      ∀ q : ℕ, q.Prime → q ∣ K₀.relIndex K → q ≠ 2 ∧ q ≠ p := by
  let π' : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨p, hp⟩}
  have hT' : IsPGroup 2 (T.subgroupOf K) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  obtain ⟨H, hH, hTH⟩ := CFSG.SolvableHall.solvable_hall_containment hK π' (T.subgroupOf K) (by
    intro q hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT'
    rw [hn] at hq
    have := (Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp (q.2.dvd_of_dvd_pow hq)
    exact Or.inl (Subtype.ext this))
  refine ⟨H.map K.subtype, Subgroup.map_subtype_le H, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hTK hx⟩, hTH (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  · intro q hq hdvd
    rw [Subgroup.card_map_of_injective K.subtype_injective] at hdvd
    have := hH.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hdvd
    rcases this with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · intro q hq hdvd
    have e : (H.map K.subtype).relIndex K = H.index := by
      show ((H.map K.subtype).comap K.subtype).index = H.index
      rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    rw [e] at hdvd
    have := hH.p_in_pi_of_p_dvd_index ⟨q, hq⟩ hdvd
    refine ⟨fun h2 => this (Or.inl (Subtype.ext h2)), fun hpq => this (Or.inr (Subtype.ext hpq))⟩

end E1

end CFSG.Quasithin
