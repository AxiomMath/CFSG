module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocCop

public section

namespace CFSG.Quasithin.HSRuLoc.Mod

open scoped commutatorElement

variable {H : Type} [Group H]

theorem exists_involution_pow {R : Subgroup H} (hR2 : IsPGroup 2 ↥R) {t : H} (ht : t ∈ R)
    (ht1 : t ≠ 1) : ∃ n : ℕ, orderOf (t ^ n) = 2 := by
  obtain ⟨k, hk⟩ := hR2 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ht1 (orderOf_eq_one_iff.mp (by simpa using ha))
  refine ⟨2 ^ (a - 1), ?_⟩
  have hdvd : 2 ^ (a - 1) ∣ orderOf t := ha ▸ pow_dvd_pow 2 (Nat.sub_le a 1)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, ha,
    Nat.pow_div (Nat.sub_le a 1) (by norm_num)]
  have : a - (a - 1) = 1 := by omega
  rw [this]

theorem hno_of_inv
    (hinv : ∀ t : H, orderOf t = 2 → ¬ 21 ∣ Nat.card (Subgroup.centralizer ({t} : Set H)))
    {R : Subgroup H} (hR2 : IsPGroup 2 ↥R) {u y : H} (hu : orderOf u = 7) (hy : orderOf y = 3) :
    ∀ t ∈ R, t ≠ 1 → ¬ (u * t = t * u ∧ y * t = t * y) := by
  rintro t ht ht1 ⟨hut, hyt⟩
  obtain ⟨n, hn⟩ := exists_involution_pow hR2 ht ht1
  have hdvd : ∀ {x : H}, x * t ^ n = t ^ n * x → orderOf x ∣
      Nat.card (Subgroup.centralizer ({t ^ n} : Set H)) := fun {x} hx => by
    have hx' : x ∈ Subgroup.centralizer ({t ^ n} : Set H) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hx
    have := orderOf_dvd_natCard (⟨x, hx'⟩ : Subgroup.centralizer ({t ^ n} : Set H))
    rwa [Subgroup.orderOf_mk] at this
  have h7 := hdvd (Commute.pow_right (show Commute u t from hut) n).eq
  have h3 := hdvd (Commute.pow_right (show Commute y t from hyt) n).eq
  rw [hu] at h7
  rw [hy] at h3
  exact hinv _ hn (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 3) h7 h3)

theorem le_normalizer_commutator_of {A P Q : Subgroup H}
    (hAP : A ≤ Subgroup.normalizer (P : Set H)) (hAQ : A ≤ Subgroup.normalizer (Q : Set H)) :
    A ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup H) : Set H) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAP hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAQ hh)]

variable [Finite H]

theorem hsru_comm {K R : Subgroup H} (hRK : R ≤ K) (hRn : (R.subgroupOf K).Normal)
    (hR2 : IsPGroup 2 ↥R) {u y : H} (huK : u ∈ K) (hyK : y ∈ K) (hu : orderOf u = 7)
    (hy : orderOf y = 3) (huy : y * u * y⁻¹ ∈ Subgroup.zpowers u)
    (hinv : ∀ t : H, orderOf t = 2 → ¬ 21 ∣ Nat.card (Subgroup.centralizer ({t} : Set H))) :
    ⁅R, K⁆ = R := by
  have hKN : K ≤ Subgroup.normalizer (R : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRK).mp hRn
  have hle : ⁅R, K⁆ ≤ R := by
    refine Subgroup.commutator_le.mpr fun r hr k hk => ?_
    have h1 : k * r⁻¹ * k⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hKN hk) r⁻¹).mp (R.inv_mem hr)
    have : ⁅r, k⁆ = r * (k * r⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact R.mul_mem hr h1
  have hKV : K ≤ Subgroup.normalizer ((⁅R, K⁆ : Subgroup H) : Set H) :=
    le_normalizer_commutator_of hKN Subgroup.le_normalizer
  have hRc : ∀ g ∈ K, ∀ r ∈ R, r⁻¹ * (g * r * g⁻¹) ∈ ⁅R, K⁆ := fun g hg r hr => by
    have : r⁻¹ * (g * r * g⁻¹) = ⁅r⁻¹, g⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Subgroup.commutator_mem_commutator (R.inv_mem hr) hg
  exact le_antisymm hle (hsru_le_of_fixed hle hR2 hu hy huy
    (fun w hw => (Subgroup.mem_normalizer_iff.mp (hKV huK) w).mp hw)
    (fun w hw => (Subgroup.mem_normalizer_iff.mp (hKV hyK) w).mp hw)
    (hRc u huK) (hRc y hyK) (hno_of_inv hinv hR2 hu hy))

end CFSG.Quasithin.HSRuLoc.Mod
