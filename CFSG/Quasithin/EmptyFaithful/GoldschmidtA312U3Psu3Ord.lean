module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Ord

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.A38c15

theorem false_of_p_six_dvd {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) {s c d : ℕ} (hd : d ∣ 3)
    (h6 : p ^ 6 ∣ s * d)
    (hdvd : s * c ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) : False := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  have hpd : Nat.Coprime (p ^ 6) d :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right hd hcop)
  have h6s : p ^ 6 ∣ s := hpd.dvd_of_dvd_mul_right h6
  have h7 : p ^ 6 ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := (h6s.mul_right c).trans hdvd
  have h8 : p ^ 3 ∣ (p ^ 2 - 1) * (p ^ 3 + 1) := by
    have : p ^ 3 * p ^ 3 ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
      rw [← pow_add]; exact h7
    exact (Nat.mul_dvd_mul_iff_left (by positivity)).mp this
  have hp_dvd : p ∣ (p ^ 2 - 1) * (p ^ 3 + 1) := (dvd_pow_self p (by norm_num)).trans h8
  rcases hp.dvd_mul.mp hp_dvd with h | h
  · have h1 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
    have h2 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h1 h
    have h3 : p ^ 2 - (p ^ 2 - 1) = 1 := by
      have := Nat.one_le_pow 2 p hp.pos
      omega
    rw [h3] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  · have h1 : p ∣ p ^ 3 := dvd_pow_self p (by norm_num)
    have h2 : p ∣ (p ^ 3 + 1) - p ^ 3 := Nat.dvd_sub h h1
    have h3 : (p ^ 3 + 1) - p ^ 3 = 1 := by omega
    rw [h3] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

theorem eq_top_of_index_three {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {M : Subgroup G} (h : M.index = 3) : M = ⊤ := by
  classical
  have : Fintype (G ⧸ M) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ M) = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact h
  let f : G →* Equiv.Perm (G ⧸ M) := MulAction.toPermHom G (G ⧸ M)
  have hdvd : Nat.card f.range ∣ 48 := by
    have h1 : Nat.card f.range ∣ Nat.card (Equiv.Perm (G ⧸ M)) :=
      Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (Equiv.Perm (G ⧸ M)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcard]; rfl
    rw [h2] at h1
    exact h1.trans (by norm_num)
  have hsolv : Group.IsSolvable ↥f.range := hess_isSolvable_of_card_dvd hdvd
  have hperf : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have hsub : Subsingleton ↥f.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥f.range hsolv
  rw [eq_top_iff]
  intro g _
  have h1 : f g = 1 := by
    have := Subsingleton.elim (⟨f g, g, rfl⟩ : ↥f.range) 1
    exact congrArg Subtype.val this
  have h2 : g • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
    have := congrArg (fun π : Equiv.Perm (G ⧸ M) => π (QuotientGroup.mk 1)) h1
    simpa [f] using this
  have h3 : (QuotientGroup.mk g : G ⧸ M) = QuotientGroup.mk 1 := by
    simpa using h2
  have h4 := QuotientGroup.eq.mp h3
  simpa using h4

variable {p : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_top_of_card_psu3 [Fact p.Prime] (hperf : Group.IsPerfect ↥(StatedSU 3 (p ^ 1) K))
    {M : Subgroup ↥(StatedSU 3 (p ^ 1) K)} {H : Subgroup (GL (Fin 3) K)} (h : QCtx p K M H)
    {d : ℕ} (hd : d ∣ 3)
    (hS : Nat.card (H ⧸ Subgroup.center H) * d = Nat.card ↥(StatedSU 3 (p ^ 1) K)) :
    M = ⊤ := by
  obtain ⟨s, hs⟩ : ∃ s, Nat.card (H ⧸ Subgroup.center H) = s := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, Nat.card (Subgroup.center H) = c := ⟨_, rfl⟩
  rw [hs] at hS
  have hH : Nat.card H = s * c := by rw [card_eq_quotient_mul H, hs, hc]
  have hcd : c ∣ 3 := hc ▸ h.center
  have hspos : 0 < s := hs ▸ Nat.card_pos
  have hHM : Nat.card H ∣ Nat.card M := by
    have h1 : Nat.card H ∣ Nat.card (M.map (StatedSU 3 (p ^ 1) K).subtype) :=
      Subgroup.card_dvd_of_le h.le
    rwa [Subgroup.card_map_of_injective (StatedSU 3 (p ^ 1) K).subtype_injective] at h1
  rw [hH] at hHM
  have hMX : Nat.card M ∣ s * d := hS ▸ Subgroup.card_subgroup_dvd_card M
  have hcd' : c ∣ d := Nat.dvd_of_mul_dvd_mul_left hspos (hHM.trans hMX)
  have htop_of : Nat.card M = s * d → M = ⊤ := fun hMd => by
    rw [← Subgroup.card_eq_iff_eq_top, hMd, hS]
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with rfl | rfl <;>
    rcases (Nat.dvd_prime Nat.prime_three).mp hcd with rfl | rfl
  · exact htop_of (Nat.dvd_antisymm hMX hHM)
  · exfalso
    have := Nat.le_of_dvd (by norm_num) hcd'
    omega
  · obtain ⟨m, hm⟩ := hHM
    have hm' : Nat.card M = s * m := by simpa using hm
    have hm3 : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hspos (by rw [← hm']; exact hMX)
    rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with rfl | rfl
    · have hidx : M.index = 3 := by
        have h1 := Subgroup.card_mul_index M
        rw [hm', ← hS] at h1
        exact Nat.eq_of_mul_eq_mul_left hspos (by simpa using h1)
      have := hperf
      exact eq_top_of_index_three hidx
    · exact htop_of hm'
  · exact htop_of (Nat.dvd_antisymm hMX hHM)

end CFSG.Quasithin.A312U3
