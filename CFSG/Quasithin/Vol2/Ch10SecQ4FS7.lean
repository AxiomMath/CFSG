module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem mem_of_mem_sup_of_pow_three {N O : Subgroup G}
    (hO : O ≤ Subgroup.normalizer (N : Set G)) (hO2 : IsPGroup 2 O) {x : G} (hx : x ∈ N ⊔ O)
    (hx3 : x ^ 3 = 1) : x ∈ N := by
  have hx' : x ∈ ((N ⊔ O : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N O hO] at hx'
  obtain ⟨n, hn, o, ho, rfl⟩ := Set.mem_mul.mp hx'
  have key : ∀ k : ℕ, ∃ n' ∈ N, (n * o) ^ k = n' * o ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨n', hn', e⟩ := ih
      have hc : o ^ k * n * (o ^ k)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hO (O.pow_mem ho k)) n).mp hn
      refine ⟨n' * (o ^ k * n * (o ^ k)⁻¹), N.mul_mem hn' hc, ?_⟩
      rw [pow_succ, e, pow_succ]
      group
  obtain ⟨m, hm⟩ := hO2 ⟨o, ho⟩
  have hom : o ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨n', hn', e⟩ := key (2 ^ m)
  rw [hom, mul_one] at e
  have hmod : ∀ j : ℕ, (n * o) ^ j = (n * o) ^ (j % 3) := fun j => by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hx3, one_pow, one_mul]
  have h2 : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
    have : 2 ^ m % 3 ≠ 0 := by
      intro h0
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0))
      omega
    omega
  rcases h2 with h | h
  · rw [← pow_one (n * o), ← h, ← hmod, e]
    exact hn'
  · have hsq : (n * o) ^ 2 ∈ N := by rw [← h, ← hmod, e]; exact hn'
    have e4 : n * o = ((n * o) ^ 2) ^ 2 := by
      rw [← pow_mul, hmod 4]
      simp
    rw [e4]
    exact N.pow_mem hsq 2

theorem mul_self_eq_one_of_two_elt {g : A5} {k : ℕ} (hg : g ^ 2 ^ k = 1) : g * g = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hg
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h60 : orderOf g ∣ 60 := SecB.card_alt5 ▸ orderOf_dvd_natCard g
  have hj2 : j ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := (this.trans (hjo ▸ h60))
    norm_num at this
  have h4 : g ^ 4 = 1 := by
    have : orderOf g ∣ 4 := by
      rw [hjo]
      exact (pow_dvd_pow 2 hj2).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have h2 := sq_of_pow_four (g : Equiv.Perm (Fin 5)) g.2 (by
    rw [← Subgroup.coe_pow, h4, Subgroup.coe_one])
  apply Subtype.ext
  rw [Subgroup.coe_mul, ← pow_two, h2, Subgroup.coe_one]

theorem card_sylow_A5_prod {P : Subgroup (A5 × A5)} (hP : IsSylowTwoOf P ⊤) :
    Nat.card P = 16 := by
  obtain ⟨-, hp, hodd⟩ := hP
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hcard : Nat.card (A5 × A5) = 3600 := by
    rw [Nat.card_prod, SecB.card_alt5]
  have h1 := Subgroup.relIndex_mul_card P ⊤
  rw [inf_top_eq, Subgroup.card_top, hcard, hk] at h1
  have hodd' : ¬ 2 ∣ P.relIndex ⊤ := hodd
  have hk12 : k ≤ 12 := by
    by_contra h
    have : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h0 : 0 < P.relIndex ⊤ := Nat.pos_of_ne_zero (by rintro h'; rw [h'] at h1; omega)
    have := Nat.le_mul_of_pos_left (2 ^ k) h0
    omega
  rw [hk]
  interval_cases k <;> omega

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
