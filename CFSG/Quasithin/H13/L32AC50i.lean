module

public import CFSG.Quasithin.H13.L32AC50d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

section Four

variable {π : ↥H →* Equiv.Perm (Fin 7)} (hker : π.ker = CFSG.Open.pCore 2 ↥H)
  (hrange : π.range = alternatingGroup (Fin 7))

omit [Finite G] in
theorem two_elt_of_ker {h : ↥H} (hh : h ∈ π.ker) (hker : π.ker = CFSG.Open.pCore 2 ↥H) :
    ∃ n : ℕ, (h : G) ^ 2 ^ n = 1 := by
  have hp : IsPGroup 2 (CFSG.Open.pCore 2 ↥H) := by
    exact CFSG.pCore_isPGroup
  obtain ⟨n, hn⟩ := hp ⟨h, hker ▸ hh⟩
  refine ⟨n, ?_⟩
  have := congrArg (fun z : CFSG.Open.pCore 2 ↥H => ((z : ↥H) : G)) hn
  simpa using this

include hrange

omit [Finite G] in
theorem exists_preim_stab {g : Equiv.Perm (Fin 7)} (hg : g ∈ Alt7.stabSub) :
    ∃ r : G, ∃ hr : r ∈ H, r ∈ preim π Alt7.stabSub ∧ π ⟨r, hr⟩ = g := by
  have hgA : g ∈ π.range := by
    rw [hrange]
    exact mem_alternatingGroup.mpr hg.1
  obtain ⟨h, rfl⟩ := hgA
  exact ⟨h, h.2, mem_preim.mpr ⟨h.2, hg⟩, rfl⟩

omit [Finite G] in
theorem map_mem_v4 {N : Subgroup G} (hNR : N ≤ preim π Alt7.stabSub)
    (hRN : preim π Alt7.stabSub ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N)
    {n : G} (hn : n ∈ N) (hnH : n ∈ H) : π ⟨n, hnH⟩ ∈ Alt7.v4List := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hnH', hnS⟩ := mem_preim.mp (hNR hn)
  have hxs : π ⟨n, hnH⟩ ∈ Alt7.stabList := Alt7.mem_stabList hnS
  have h2e : ∀ m ∈ N, ∀ hm : m ∈ H, π ⟨m, hm⟩ ∈ Alt7.stabList → π ⟨m, hm⟩ ^ 4 = 1 := by
    intro m hm hmH hms
    obtain ⟨k, hk⟩ := hN2 ⟨m, hm⟩
    have hk' : π ⟨m, hmH⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨m, hmH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      rw [this, map_one]
    have h12 := Alt7.stab_exp _ hms
    have h1 := orderOf_dvd_of_pow_eq_one hk'
    have h2 := orderOf_dvd_of_pow_eq_one h12
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hj2 : j ≤ 2 := by
      by_contra hj3
      have : 2 ^ 3 ∣ 12 := (Nat.pow_dvd_pow 2 (by omega)).trans (hj ▸ h2)
      omega
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [hj]
    exact Nat.pow_dvd_pow 2 hj2
  by_contra hv
  obtain ⟨g, hg, hg3, hg1⟩ := Alt7.d1 _ hxs hv (h2e n hn hnH hxs)
  obtain ⟨r, hrH, hrR, hπr⟩ := exists_preim_stab hrange (Alt7.mem_stabSub_iff.mpr hg)
  have hc : n * r * n⁻¹ * r⁻¹ ∈ N := by
    have h1 : r * n⁻¹ * r⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hRN hrR) _).mp (N.inv_mem hn)
    have e : n * r * n⁻¹ * r⁻¹ = n * (r * n⁻¹ * r⁻¹) := by group
    rw [e]
    exact N.mul_mem hn h1
  have hcH : n * r * n⁻¹ * r⁻¹ ∈ H := H.mul_mem (H.mul_mem (H.mul_mem hnH hrH) (H.inv_mem hnH))
    (H.inv_mem hrH)
  have hπc : π ⟨n * r * n⁻¹ * r⁻¹, hcH⟩ = π ⟨n, hnH⟩ * g * (π ⟨n, hnH⟩)⁻¹ * g⁻¹ := by
    rw [← hπr, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hcs : π ⟨n * r * n⁻¹ * r⁻¹, hcH⟩ ∈ Alt7.stabList := Alt7.mem_stabList
    ((mem_preim.mp (hNR hc)).2)
  have h4 := h2e _ hc hcH hcs
  rw [hπc] at h4
  apply hg1
  set c := π ⟨n, hnH⟩ * g * (π ⟨n, hnH⟩)⁻¹ * g⁻¹ with hcdef
  calc c = c ^ 4 * (c ^ 3)⁻¹ := by group
    _ = 1 := by rw [h4, hg3, inv_one, one_mul]

include hker

theorem card_preim_stab : ∃ a : ℕ, Nat.card ↥(preim π Alt7.stabSub) = 2 ^ a * 72 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := preim π Alt7.stabSub with hR
  set φ : ↥R →* Equiv.Perm (Fin 7) := π.comp (Subgroup.inclusion (preim_le π _)) with hφ
  have hrg : φ.range = Alt7.stabSub := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨hx, hxs⟩ := mem_preim.mp x.2
      exact hxs
    · intro g hg
      obtain ⟨r, hrH, hrR, hπr⟩ := exists_preim_stab hrange hg
      exact ⟨⟨r, hrR⟩, hπr⟩
  have hk2 : IsPGroup 2 φ.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := two_elt_of_ker (h := Subgroup.inclusion (preim_le π _) x) hx hker
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using hn))⟩
  obtain ⟨a, ha⟩ := hk2.exists_card_eq
  refine ⟨a, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrg, Alt7.card_stabSub, ha,
    mul_comm]

theorem isSolvable_preim_stab : Group.IsSolvable ↥(preim π Alt7.stabSub) := by
  obtain ⟨a, ha⟩ := card_preim_stab hker hrange
  refine isSolvable_of_isTwoThree ⟨a + 3, 2, ?_⟩
  rw [ha]
  ring

theorem exists_three_cent {V' : Subgroup G}
    (hRV : preim π Alt7.stabSub ≤ Subgroup.normalizer (V' : Set G))
    (hAut : Nat.card (MulAut ↥V') = 168) :
    ∃ c : G, ∃ hcH : c ∈ H, c ∈ preim π Alt7.stabSub ∧
      c ∈ Subgroup.centralizer (V' : Set G) ∧ π ⟨c, hcH⟩ ^ 3 = 1 ∧ π ⟨c, hcH⟩ ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := preim π Alt7.stabSub with hR
  obtain ⟨a, ha⟩ := card_preim_stab hker hrange
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥R) := inferInstance
  obtain ⟨r, hr⟩ := P.isPGroup'.exists_card_eq
  have hPi : ¬ 3 ∣ (P : Subgroup ↥R).index := P.not_dvd_index
  have hPmul := (P : Subgroup ↥R).card_mul_index
  rw [hr, ha] at hPmul
  have hr2 : r = 2 := by
    have h1 : 3 ^ r ∣ 2 ^ a * 72 := ⟨_, hPmul.symm⟩
    have h1' : 3 ^ r ∣ 2 ^ (a + 3) * 9 := by
      have e : 2 ^ a * 72 = 2 ^ (a + 3) * 9 := by ring
      rwa [e] at h1
    have h2 : 3 ^ r ∣ 9 := Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 3 2)) h1'
    have hr2 : r ≤ 2 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at h2
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
    by_contra hne
    apply hPi
    have e : (P : Subgroup ↥R).index = 2 ^ (a + 3) * 3 ^ (2 - r) := by
      have h9 : 2 ^ a * 72 = 3 ^ r * (2 ^ (a + 3) * 3 ^ (2 - r)) := by
        have e9 : (9 : ℕ) = 3 ^ r * 3 ^ (2 - r) := by
          rw [← pow_add, show r + (2 - r) = 2 by omega]
          norm_num
        calc 2 ^ a * 72 = 2 ^ (a + 3) * 9 := by ring
          _ = _ := by rw [e9]; ring
      rw [h9] at hPmul
      exact Nat.eq_of_mul_eq_mul_left (by positivity) hPmul
    rw [e]
    exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  subst hr2
  set ρ : ↥(P : Subgroup ↥R) →* MulAut ↥V' :=
    (conjAct V').comp ((Subgroup.inclusion hRV).comp (P : Subgroup ↥R).subtype) with hρ
  have hρ3 : IsPGroup 3 ρ.range := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    obtain ⟨k, hk⟩ := P.isPGroup' x
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hk, map_one]; rfl)⟩
  obtain ⟨s, hs⟩ := hρ3.exists_card_eq
  have hs1 : s ≤ 1 := by
    have h1 : 3 ^ s ∣ 168 := hs ▸ hAut ▸ Subgroup.card_subgroup_dvd_card ρ.range
    by_contra hs2
    have : 3 ^ 2 ∣ 168 := (Nat.pow_dvd_pow 3 (by omega)).trans h1
    omega
  have hkerc : 1 < Nat.card ρ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hs, hr] at h1
    interval_cases s
    · rw [pow_zero, one_mul] at h1
      omega
    · omega
  obtain ⟨c, hc, hc1⟩ := (ρ.ker.bot_or_exists_ne_one).resolve_left
    ((Subgroup.one_lt_card_iff_ne_bot ρ.ker).mp hkerc)
  set c' : G := (((c : ↥(P : Subgroup ↥R)) : ↥R) : G) with hc'
  have hc'R : c' ∈ R := ((c : ↥(P : Subgroup ↥R)) : ↥R).2
  have hc'H : c' ∈ H := preim_le π _ hc'R
  have hcC : c' ∈ Subgroup.centralizer (V' : Set G) := by
    have := A1b.conjAct_eq_one_iff.mp (show conjAct V' ⟨c', hRV hc'R⟩ = 1 from hc)
    exact this
  obtain ⟨j, hj⟩ := P.isPGroup' c
  have hcj : c' ^ 3 ^ j = 1 := by
    have := congrArg (fun z : ↥(P : Subgroup ↥R) => ((z : ↥R) : G)) hj
    simpa using this
  have hπj : π ⟨c', hc'H⟩ ^ 3 ^ j = 1 := by
    rw [← map_pow]
    have : (⟨c', hc'H⟩ : ↥H) ^ 3 ^ j = 1 := Subtype.ext (by simpa using hcj)
    rw [this, map_one]
  have hcs : π ⟨c', hc'H⟩ ∈ Alt7.stabList := Alt7.mem_stabList (mem_preim.mp hc'R).2
  refine ⟨c', hc'H, hc'R, hcC, ?_, ?_⟩
  · have h12 := Alt7.stab_exp _ hcs
    have h1 := orderOf_dvd_of_pow_eq_one hπj
    have h2 := orderOf_dvd_of_pow_eq_one h12
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    have hi1 : i ≤ 1 := by
      by_contra hi2
      have : 3 ^ 2 ∣ 12 := (Nat.pow_dvd_pow 3 (by omega)).trans (hi ▸ h2)
      omega
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [hi]
    exact Nat.pow_dvd_pow 3 hi1
  · intro h1
    obtain ⟨n, hn⟩ := two_elt_of_ker (h := ⟨c', hc'H⟩) h1 hker
    apply hc1
    have ho : orderOf c' = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one hn)
      (orderOf_dvd_of_pow_eq_one hcj)
    have : c' = 1 := orderOf_eq_one_iff.mp ho
    exact Subtype.ext (Subtype.ext this)

end Four

end CFSG.Quasithin.H13.L32A.C
