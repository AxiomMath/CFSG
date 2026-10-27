module

public import CFSG.Quasithin.H13.NQCatT513Gen
public import CFSG.GroupTheory.WielandtProductFinal
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

theorem isSolvable_sup_of_perm {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hH : Group.IsNilpotent ↥H) (hK : Group.IsNilpotent ↥K)
    (hperm : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G))
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥K)) : Group.IsSolvable ↥(H ⊔ K) := by
  have hHle : H ≤ H ⊔ K := le_sup_left
  have hKle : K ≤ H ⊔ K := le_sup_right
  refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product (H.subgroupOf (H ⊔ K))
    (K.subgroupOf (H ⊔ K)) ?_ ?_ ?_ ?_
  · exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHle).symm
  · exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKle).symm
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv]
  · rintro ⟨g, hg⟩
    have hg' : g ∈ (H : Set G) * (K : Set G) := by
      rw [← coe_sup_eq_mul H K hperm]
      exact hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hg'
    exact ⟨⟨a, hHle ha⟩, Subgroup.mem_subgroupOf.mpr ha, ⟨b, hKle hb⟩,
      Subgroup.mem_subgroupOf.mpr hb, rfl⟩

theorem card_of_isSylowTwoOf_top {X : Type} [Group X] [Finite X] {S₀ : Subgroup X}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {a m : ℕ} (hX : Nat.card X = 2 ^ a * m) (hm : ¬ 2 ∣ m) :
    Nat.card ↥S₀ = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hS₀.2.1
  have hidx := Subgroup.card_mul_index S₀
  have hodd : ¬ 2 ∣ S₀.index := by
    have e : (S₀.subgroupOf ⊤).index = S₀.index := Subgroup.relIndex_top_right _
    rw [← e]
    exact hS₀.2.2
  rw [hb, hX] at hidx
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 2)
  have hi0 : S₀.index ≠ 0 := fun h => by
    rw [h, mul_zero] at hidx
    exact (Nat.mul_ne_zero (pow_ne_zero a two_ne_zero) hm0) hidx.symm
  have h1 := congrArg (padicValNat 2) hidx
  rw [padicValNat.mul (pow_ne_zero b two_ne_zero) hi0, padicValNat.mul (pow_ne_zero a two_ne_zero)
    hm0, padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hodd,
    padicValNat.eq_zero_of_not_dvd hm] at h1
  rw [hb]
  simpa using h1

theorem exists_hall_two_p {Q : Type} [Group Q] [Finite Q] {S Z : Subgroup Q}
    (hS : IsPGroup 2 ↥S) (hSZ : S ≤ Z) (hZs : Group.IsSolvable ↥Z) {p : ℕ} (hp : p.Prime) :
    ∃ H : Subgroup Q, S ≤ H ∧ H ≤ Z ∧ ∃ k : ℕ, Nat.card ↥H * k = Nat.card ↥Z ∧ ¬ 2 ∣ k ∧
      ¬ p ∣ k ∧ ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥H → q = 2 ∨ q = p := by
  classical
  let π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨p, hp⟩}
  have hU : IsPGroup 2 ↥(S.subgroupOf Z) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSZ).symm
  have hUπ : CFSG.IsPiSubgroup π (S.subgroupOf Z) := by
    intro q hq
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU
    have h2 : q.val ∣ 2 ^ n := hn ▸ hq
    left
    exact Subtype.ext
      ((Nat.prime_dvd_prime_iff_eq q.prop Nat.prime_two).1 (q.prop.dvd_of_dvd_pow h2))
  obtain ⟨H, hH, hUH⟩ := CFSG.SolvableHall.solvable_hall_containment hZs π _ hUπ
  have hSH : S ≤ H.map Z.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hSZ]
    exact Subgroup.map_mono hUH
  have hcard : Nat.card ↥(H.map Z.subtype) = Nat.card ↥H :=
    (Nat.card_congr (H.equivMapOfInjective Z.subtype Subtype.val_injective).toEquiv).symm
  refine ⟨H.map Z.subtype, hSH, Subgroup.map_subtype_le H, H.index, ?_, ?_, ?_, ?_⟩
  · rw [hcard]
    exact Subgroup.card_mul_index H
  · exact fun h2 => hH.p_in_pi_of_p_dvd_index ⟨2, Nat.prime_two⟩ h2 (Or.inl rfl)
  · exact fun hpd => hH.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpd (Or.inr rfl)
  · intro q hq hqd
    rw [hcard] at hqd
    rcases hH.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqd with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem pPart_of_overgroups {X : Type} [Group X] [Finite X] {S₀ : Subgroup X}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {E : ℕ → Prop}
    (hidx : ∀ Z : Subgroup X, S₀ ≤ Z → ∀ m : ℕ, Nat.card ↥Z = m * Nat.card ↥S₀ →
      m = 1 ∨ 3 ∣ m ∨ E m)
    {Dc : Subgroup X} (hcyc : IsCyclic ↥Dc) (hodd : Odd (Nat.card ↥Dc))
    (hperm : (Dc : Set X) * (S₀ : Set X) = (S₀ : Set X) * (Dc : Set X)) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hpD : p ∣ Nat.card ↥Dc) : ∃ a : ℕ, E (p ^ (a + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥S₀ := hS₀.2.1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS2
  have hcop : Nat.Coprime (Nat.card ↥Dc) (Nat.card ↥S₀) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)
  have hY := card_sup_of_perm hperm hcop
  have hDn : Group.IsNilpotent ↥Dc := by
    have := hcyc
    infer_instance
  have hSn : Group.IsNilpotent ↥S₀ := hS2.isNilpotent
  have hYs := isSolvable_sup_of_perm hDn hSn hperm hcop
  obtain ⟨H, hSH, hHY, k, hk, hk2, hkp, hHq⟩ := exists_hall_two_p hS2 le_sup_right hYs hp
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hSH
  rw [mul_comm] at hm
  have hpos : 0 < Nat.card ↥S₀ := Nat.card_pos
  have hmk : m * k = Nat.card ↥Dc := by
    rw [hm, hY] at hk
    have : (m * k) * Nat.card ↥S₀ = Nat.card ↥Dc * Nat.card ↥S₀ := by rw [← hk]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hmk
    exact absurd hmk.symm Nat.card_pos.ne'
  have hmodd : ¬ 2 ∣ m := fun h2 => (Nat.not_even_iff_odd.mpr hodd)
    (even_iff_two_dvd.mpr (hmk ▸ Dvd.dvd.mul_right h2 k))
  have hmp : m = p ^ m.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hm0 fun {q} hq hqm => ?_
    rcases hHq q hq (hm ▸ Dvd.dvd.mul_right hqm _) with h | h
    · exact absurd (h ▸ hqm) hmodd
    · exact h
  have hpm : p ∣ m := by
    rw [← hmk] at hpD
    rcases hp.dvd_mul.mp hpD with h | h
    · exact h
    · exact absurd h hkp
  have hlen : m.primeFactorsList.length ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hmp
    rw [hmp] at hpm
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpm)
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hlen
  rw [ha] at hmp
  refine ⟨a, ?_⟩
  rcases hidx H hSH m hm with h | h | h
  · rw [h] at hpm
    exact absurd (Nat.dvd_one.mp hpm) hp.one_lt.ne'
  · rw [hmp] at h
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm hp3
  · rwa [← hmp]

theorem cycOddPerm_of_overgroups {X : Type} [Group X] [Finite X] {S₀ : Subgroup X}
    (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hidx : ∀ Z : Subgroup X, S₀ ≤ Z → ∀ m : ℕ, Nat.card ↥Z = m * Nat.card ↥S₀ → m = 1 ∨ 3 ∣ m) :
    CycOddPerm X fun _ => False := by
  refine cycOddPerm_of_sylow hS₀ fun Dc hcyc hodd hperm => Or.inl ?_
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqD => ?_⟩
  by_contra h3
  obtain ⟨a, ha⟩ := pPart_of_overgroups (E := fun _ => False) hS₀
    (fun Z hZ m hm => (hidx Z hZ m hm).elim Or.inl fun h => Or.inr (Or.inl h)) hcyc hodd hperm
    hq h3 hqD
  exact ha

end CFSG.Quasithin.H13.NQCat.T513P
