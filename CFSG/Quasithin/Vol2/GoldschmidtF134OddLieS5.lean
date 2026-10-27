module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Quasithin.Vol2.F134LieF4Group
import CFSG.CharacterTheory.Burnside
import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieS5Act

public section

open CFSG.ABGLocalTools CFSG.LieType.BorelTits CFSG.Quasithin.F134.LieF4

namespace CFSG.Quasithin.H13.NQCore.S5

section Containment

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_proper_overgroup_of_normal_two_subgroup (hBT : Holds Y 2) {U H V : Subgroup Y}
    (hU : IsSylowOf 2 U ⊤) (hUH : U ≤ H) (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hHV : H ≤ Subgroup.normalizer (V : Set Y)) :
    ∃ Q : Subgroup Y, Q ≠ ⊤ ∧ H ≤ Q ∧ Subgroup.normalizer (U : Set Y) ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, Q, hQ, hNQ, -, -, hSQ⟩ := hBT V hV hV2
  have hHQ : H ≤ Q := hHV.trans hNQ
  exact ⟨Q, hQ, hHQ, normalizer_le_of_isSylowOf
    (isSylowOf_of_sylow S (Subgroup.le_normalizer.trans hSQ))
    (hU.of_le (hUH.trans hHQ) le_top) hSQ⟩

omit [Finite Y] in
theorem le_normalizer_map_subtype_of_normal {H : Subgroup Y} (K : Subgroup H) [K.Normal] :
    H ≤ Subgroup.normalizer (K.map H.subtype : Set Y) := by
  have hn : ((K.map H.subtype).subgroupOf H).Normal := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le K)).1 hn

end Containment

section Main

variable {Y : Type*} [Group Y] [Finite Y]

theorem isSolvable_of_card_eq {H : Type*} [Group H] [Finite H] {p m a : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcard : Nat.card H = 2 ^ m * p ^ a) : Group.IsSolvable H := by
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2)
    (q := p) (a := m) (b := a) Nat.prime_two hp (Ne.symm hp2)
    (by rw [← Nat.card_eq_fintype_card, hcard])

theorem eq_one_of_sq_eq_one_of_pow_eq_one {G : Type*} [Group G] {p j : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : G} (h2 : x * x = 1) (hj : x ^ p ^ j = 1) : x = 1 := by
  have hcop : Nat.Coprime 2 (p ^ j) :=
    Nat.Coprime.pow_right j ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2 : x ^ 2 = 1))
    (orderOf_dvd_of_pow_eq_one hj)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

theorem exists_proper_overgroup (hBT : Holds Y 2) {U H E : Subgroup Y} (hU : IsSylowOf 2 U ⊤)
    (hUH : U ≤ H) (hEH : E ≤ H) (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE : 16 ≤ Nat.card E)
    {p m a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcard : Nat.card H = 2 ^ m * p ^ a) (ha : a ≤ 3) :
    ∃ Q : Subgroup Y, Q ≠ ⊤ ∧ H ≤ Q ∧ Subgroup.normalizer (U : Set Y) ≤ Q := by
  classical
  by_cases hV : ∃ V : Subgroup Y, V ≠ ⊥ ∧ IsPGroup 2 V ∧ H ≤ Subgroup.normalizer (V : Set Y)
  · obtain ⟨V, hV1, hV2, hHV⟩ := hV
    exact exists_proper_overgroup_of_normal_two_subgroup hBT hU hUH hV1 hV2 hHV
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hsolv : Group.IsSolvable H := isSolvable_of_card_eq hp hp2 hcard
  have hP' : CFSG.pPrimeCore p H = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hKn hKcop
    have hKd : Nat.card K ∣ 2 ^ m := by
      have h1 : Nat.card K ∣ 2 ^ m * p ^ a := hcard ▸ Subgroup.card_subgroup_dvd_card K
      exact (Nat.Coprime.pow_right a hKcop.symm).dvd_of_dvd_mul_right h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hKd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_contra hK1
    refine hV ⟨K.map H.subtype, ?_, (IsPGroup.of_card hj).map H.subtype,
      le_normalizer_map_subtype_of_normal K⟩
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective]
  have hFit : CFSG.fittingSubgroup H = CFSG.pCore p H := CFSG.Fitting_eq_pcore H p hP'
  have hWp : IsPGroup p (CFSG.pCore p H) := CFSG.pCore_isPGroup (p := p) (G := H)
  have hWc : Nat.card (CFSG.pCore p H) ∣ p ^ 3 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hWp
    have h1 : p ^ k ∣ 2 ^ m * p ^ a := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card _
    have hcop : Nat.Coprime (p ^ k) (2 ^ m) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    rw [hk]
    exact (hcop.dvd_of_dvd_mul_left h1).trans (pow_dvd_pow p ha)
  have hE'card : Nat.card (E.subgroupOf H) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  have h8 := card_le_eight_of_faithful (G := H) (W := CFSG.pCore p H) (E := E.subgroupOf H) hp2
    hWp hWc (by rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact le_top)
    (fun x hx => Subtype.ext (by simpa [sq] using hE2 x hx)) (fun x hx hcomm => ?_)
  · omega
  have hxF : x ∈ CFSG.fittingSubgroup H :=
    CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
      (by rw [hFit]; exact Subgroup.mem_centralizer_iff.2 hcomm)
  rw [hFit] at hxF
  obtain ⟨j, hj⟩ := hWp ⟨x, hxF⟩
  exact eq_one_of_sq_eq_one_of_pow_eq_one hp hp2 (Subtype.ext (by simpa [sq] using hE2 x hx))
    (by simpa using congrArg Subtype.val hj)

end Main

end CFSG.Quasithin.H13.NQCore.S5
