module

public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

namespace S152V

theorem fm_half_forms {p : ℕ} (hFM : IsFermatOrMersennePrime p) :
    ((∃ a : ℕ, (p - 1) / 2 = 2 ^ a) ∨ Odd ((p - 1) / 2)) ∧
      ((∃ a : ℕ, (p + 1) / 2 = 2 ^ a) ∨ Odd ((p + 1) / 2)) := by
  rcases hFM.2 with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  ·
    obtain ⟨m', hm'⟩ : ∃ m' : ℕ, 2 ^ k = m' + 1 := ⟨2 ^ k - 1, by have := @Nat.one_le_two_pow k; omega⟩
    rw [hm', pow_succ] at hk
    have hpos : 1 ≤ 2 ^ m' := Nat.one_le_two_pow
    refine ⟨Or.inl ⟨m', by omega⟩, ?_⟩
    rcases Nat.eq_zero_or_pos m' with h0 | h0
    · subst h0
      exact Or.inl ⟨1, by omega⟩
    · right
      have : 2 ^ m' % 2 = 0 := by
        obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
        rw [pow_succ]; omega
      rw [Nat.odd_iff]
      omega
  ·
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
    have h4 : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    refine ⟨Or.inr ?_, Or.inl ⟨j + 1, ?_⟩⟩
    · rw [Nat.odd_iff]; omega
    · rw [pow_succ]; omega

theorem fm_ne_two {p : ℕ} (hFM : IsFermatOrMersennePrime p) : p ≠ 2 := by
  rcases hFM.2 with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  · have h1 : 2 ^ 1 ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    omega
  · have h1 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

theorem not_two_mul_prime_dvd {p r : ℕ} (hFM : IsFermatOrMersennePrime p) (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ 2 * r ∣ p ∧ ¬ 2 * r ∣ (p - 1) / 2 ∧ ¬ 2 * r ∣ (p + 1) / 2 := by
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hpow : ∀ a : ℕ, ¬ 2 * r ∣ 2 ^ a := fun a h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
      (hr.dvd_of_dvd_pow ((Dvd.intro_left 2 rfl).trans h)))
  have hodd : ∀ n : ℕ, Odd n → ¬ 2 * r ∣ n := fun n hn h =>
    (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 ((Dvd.intro r rfl).trans h))
  obtain ⟨h1, h2⟩ := fm_half_forms hFM
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hp := hFM.1
    rcases (Nat.dvd_prime hp).1 h with h1 | h1
    · omega
    · have : 2 ∣ p := ⟨r, h1.symm⟩
      exact fm_ne_two hFM ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
  · rcases h1 with ⟨a, ha⟩ | ho
    · rw [ha]; exact hpow a
    · exact hodd _ ho
  · rcases h2 with ⟨a, ha⟩ | ho
    · rw [ha]; exact hpow a
    · exact hodd _ ho

theorem psl2_orderOf_ne_two_mul {K : Type} [Field K] [Finite K] {p : ℕ} (hFM : IsFermatOrMersennePrime p)
    (hK : Nat.card K = p) (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : orderOf y ≠ 2 * r := by
  intro h
  have : Fact p.Prime := ⟨hFM.1⟩
  obtain ⟨hn1, hn2, hn3⟩ := not_two_mul_prime_dvd hFM hr hr2
  have hp2 : p % 2 = 1 := (hFM.1.eq_two_or_odd).resolve_left (fm_ne_two hFM)
  have hgcd : Nat.gcd (p - 1) 2 = 2 := Nat.gcd_eq_right (by omega)
  rcases CFSG.Glauberman.Dickson.psl2_orderOf_dvd (F := K) (p := p) (f := 1) (by rw [hK, pow_one]) y with
    h1 | h1 | h1
  · exact hn1 (h ▸ h1)
  · rw [hK, hgcd] at h1
    exact hn2 (h ▸ h1)
  · rw [hK, hgcd] at h1
    exact hn3 (h ▸ h1)

theorem exists_pow_orderOf_eq {Γ : Type*} [Group Γ] {g : Γ} (hn : orderOf g ≠ 0) {r : ℕ}
    (hrn : r ∣ orderOf g) : ∃ g' : Γ, orderOf g' = r ∧ g' ∈ Subgroup.zpowers g :=
  ⟨g ^ (orderOf g / r), orderOf_pow_orderOf_div hn hrn, Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _⟩

theorem eq_one_of_commute_odd {Γ K : Type} [Group Γ] [Field K] [Finite K] {p : ℕ}
    (hFM : IsFermatOrMersennePrime p) (hK : Nat.card K = p)
    (e : Γ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) {l : Γ} (hl2 : l ^ 2 = 1) (hl1 : l ≠ 1)
    {g : Γ} (hg : g * l = l * g) (hodd : Odd (orderOf g)) : g = 1 := by
  by_contra hg1
  have hord1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.1 h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hord1
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrdvd)
  obtain ⟨g', hg'ord, hg'mem⟩ := exists_pow_orderOf_eq hodd.pos.ne' hrdvd
  have hcomm : Commute g' l := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg'mem
    exact (Commute.zpow_left (show Commute g l from hg) k)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlord : orderOf l = 2 := orderOf_eq_prime hl2 hl1
  have hco : (orderOf g').Coprime (orderOf l) := by
    rw [hg'ord, hlord]
    exact (Nat.coprime_primes hr Nat.prime_two).2 hr2
  have hprod := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco
  rw [hg'ord, hlord] at hprod
  apply psl2_orderOf_ne_two_mul hFM hK (e (g' * l)) hr hr2
  rw [MulEquiv.orderOf_eq, hprod, mul_comm]

theorem odd_order_aut_eq_one {Γ : Type} [Group Γ] [Finite Γ]
    (hZ : ∀ c : Γ, (∀ y, c * y = y * c) → c = 1) (hAut : Nat.card (MulAut Γ) ≤ 2 * Nat.card Γ) (l : Γ)
    (hP : ∀ g : Γ, g * l = l * g → Odd (orderOf g) → g = 1) (α : MulAut Γ) (hα : Odd (orderOf α))
    (hc : α * MulAut.conj l = MulAut.conj l * α) : α = 1 := by
  have hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
    rw [injective_iff_map_eq_one]
    intro c hc1
    apply hZ
    intro y
    have h := MulEquiv.ext_iff.1 hc1 y
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc c * y = (c * y * c⁻¹) * c := by group
      _ = y * c := by rw [h]
  let N : Subgroup (MulAut Γ) := (MulAut.conj : Γ →* MulAut Γ).range
  have hNcard : Nat.card N = Nat.card Γ := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : N.index ∣ 2 := by
    have h1 := Subgroup.card_mul_index N
    rw [hNcard] at h1
    have hpos : 0 < Nat.card Γ := Nat.card_pos
    have : Nat.card Γ * N.index ≤ Nat.card Γ * 2 := by rw [h1, mul_comm]; exact hAut
    have hle : N.index ≤ 2 := Nat.le_of_mul_le_mul_left this hpos
    have hne : N.index ≠ 0 := by
      intro h0
      rw [h0] at h1
      have : Nat.card (MulAut Γ) = 0 := by rw [← h1]; simp
      exact absurd this Nat.card_pos.ne'
    interval_cases h : N.index
    · exact absurd rfl hne
    · exact one_dvd _
    · exact dvd_rfl
  have hαN : α ∈ N := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · rw [Subgroup.index_eq_one.1 h1]; exact Subgroup.mem_top α
    · have hsq := Subgroup.sq_mem_of_index_two h2 α
      obtain ⟨m, hm⟩ := hα
      have : α = (α ^ 2) ^ (m + 1) := by
        have h3 : α ^ (2 * m + 2) = α := by
          have := pow_orderOf_eq_one α
          rw [hm] at this
          calc α ^ (2 * m + 2) = α ^ (2 * m + 1) * α := pow_succ _ _
            _ = α := by rw [this, one_mul]
        rw [← pow_mul]
        rw [show 2 * (m + 1) = 2 * m + 2 by ring, h3]
      rw [this]
      exact N.pow_mem hsq _
  obtain ⟨g, rfl⟩ := hαN
  have hgl : g * l = l * g := by
    apply hinj
    rw [map_mul, map_mul]
    exact hc
  have hordg : orderOf g = orderOf (MulAut.conj g) := (orderOf_injective _ hinj g).symm
  rw [hP g hgl (hordg ▸ hα)]
  exact map_one _

end S152V

end CFSG.Quasithin
