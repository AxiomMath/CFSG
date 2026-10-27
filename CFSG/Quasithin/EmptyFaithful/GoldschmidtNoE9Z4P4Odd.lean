module

public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S14612ED

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Odd

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem exists_mem_oTwoUpper_resBeta_eq
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {Q : Subgroup (MulAut ↥(kOf (rhoH h)))} (hQr : Q ≤ (resBeta (rhoH h)).range)
    (hQ3 : Nat.card Q = 3) {b : MulAut ↥(kOf (rhoH h))} (hb : b ∈ Q) :
    ∃ x : G, ∃ hxH : x ∈ H, x ∈ oTwoUpper (HLb (resBeta (rhoH h)) Q) ∧
      resBeta (rhoH h) ⟨x, hxH⟩ = b := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hqQ, hq1, hqz, hq3⟩ := exists_generator_of_prime_card hQ3
  obtain ⟨g, hg⟩ := hQr hqQ
  obtain ⟨k, hk⟩ := exists_odd_orderOf_pow (g : G)
  have hgR : (g : G) ∈ HLb (resBeta (rhoH h)) Q := mem_HLb_of_mem (by rw [hg]; exact hqQ)
  have hg'H : (g : G) ^ 2 ^ k ∈ H := H.pow_mem g.2 _
  have hg'R : (g : G) ^ 2 ^ k ∈ HLb (resBeta (rhoH h)) Q := (HLb (resBeta (rhoH h)) Q).pow_mem hgR _
  have hg'odd : (g : G) ^ 2 ^ k ∈ oTwoUpper (HLb (resBeta (rhoH h)) Q) :=
    mem_oTwoUpper_of_odd hg'R hk
  have hβg' : resBeta (rhoH h) ⟨(g : G) ^ 2 ^ k, hg'H⟩ = q ^ 2 ^ k := by
    have e : (⟨(g : G) ^ 2 ^ k, hg'H⟩ : ↥H) = g ^ 2 ^ k := Subtype.ext (by simp)
    rw [e, map_pow, hg]
  have hq'1 : q ^ 2 ^ k ≠ 1 := by
    intro e
    have hd : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one e
    rw [hq3] at hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hq'Q : q ^ 2 ^ k ∈ Q := Q.pow_mem hqQ _
  have hzp : Subgroup.zpowers (q ^ 2 ^ k) = Q := zpowers_eq_of_prime_card hQ3 hq'Q hq'1
  rw [← hzp] at hb
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hxH : ((g : G) ^ 2 ^ k) ^ i ∈ H := H.zpow_mem hg'H i
  refine ⟨((g : G) ^ 2 ^ k) ^ i, hxH, (oTwoUpper _).zpow_mem hg'odd i, ?_⟩
  have e : (⟨((g : G) ^ 2 ^ k) ^ i, hxH⟩ : ↥H) = ⟨(g : G) ^ 2 ^ k, hg'H⟩ ^ i :=
    Subtype.ext (by simp)
  rw [e, map_zpow, hβg', hi]

end Odd

end CFSG.Quasithin
