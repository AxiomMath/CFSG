module

public import CFSG.Quasithin.Vol2.Ch10SecFAct
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem prime_dvd_two_pow_sub_one {p k : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hk8 : k ≤ 8)
    (h : p ∣ 2 ^ k - 1) : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 127 := by
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h17 : Nat.Prime 17 := by norm_num
  have h31 : Nat.Prime 31 := by norm_num
  have h127 : Nat.Prime 127 := by norm_num
  interval_cases k
  · norm_num at h
    exact absurd h hp.ne_one
  · exact Or.inl (hq 3 h3 (by simpa using h))
  · exact Or.inr (Or.inr (Or.inl (hq 7 h7 (by simpa using h))))
  · have h' : p ∣ 3 * 5 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
    · exact Or.inl (hq 3 h3 h1)
    · exact Or.inr (Or.inl (hq 5 h5 h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 31 h31 (by simpa using h))))))
  · have h' : p ∣ 3 * 3 * 7 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2 <;> exact Or.inl (hq 3 h3 h2)
    · exact Or.inr (Or.inr (Or.inl (hq 7 h7 h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hq 127 h127 (by simpa using h))))))
  · have h' : p ∣ 3 * 5 * 17 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact Or.inl (hq 3 h3 h2)
      · exact Or.inr (Or.inl (hq 5 h5 h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 17 h17 h1))))

variable {G : Type} [Group G] [Finite G]

theorem dvd_two_pow_sub_one_of_act {W : Subgroup G} (hW : IsPGroup 2 ↥W) {g : G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hg : orderOf g = r)
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hne : ∃ w ∈ W, g * w * g⁻¹ ≠ w) :
    ∃ k, 1 ≤ k ∧ 2 ^ k ≤ Nat.card ↥W ∧ r ∣ 2 ^ k - 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : MulAut ↥W := W.normalizerMonoidHom ⟨g, hgW⟩ with hσ
  have hσr : σ ^ r = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨g, hgW⟩ : ↥(Subgroup.normalizer (W : Set G))) ^ r = 1 := by
      apply Subtype.ext
      simp [← hg, pow_orderOf_eq_one]
    rw [this, map_one]
  have hσv : ∀ w : ↥W, ((σ w : ↥W) : G) = g * w * g⁻¹ := fun w => rfl
  have hp : IsPGroup r (Subgroup.zpowers σ) := by
    intro x
    obtain ⟨k, hk⟩ := x
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσr, one_zpow]
  have hmod := hp.card_modEq_card_fixedPoints ↥W
  set F := FixedPoints.subgroup (Subgroup.zpowers σ) ↥W with hF
  have hFc : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) ↥W) = Nat.card ↥F := rfl
  rw [hFc] at hmod
  obtain ⟨w, hw⟩ := hW.exists_card_eq
  obtain ⟨c, hc⟩ := (hW.to_subgroup F).exists_card_eq
  have hcw : c < w := by
    have hdvd : Nat.card ↥F ∣ Nat.card ↥W := Subgroup.card_subgroup_dvd_card F
    rw [hc, hw] at hdvd
    have hle : c ≤ w := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso
      obtain ⟨w₀, hw₀, hne₀⟩ := hne
      have hFtop : F = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hc, hw, heq]
      have hmem : (⟨w₀, hw₀⟩ : ↥W) ∈ F := hFtop ▸ Subgroup.mem_top _
      have h1 := (FixedPoints.mem_subgroup _ _ _).mp hmem ⟨σ, Subgroup.mem_zpowers σ⟩
      apply hne₀
      have h2 : σ ⟨w₀, hw₀⟩ = ⟨w₀, hw₀⟩ := h1
      have h3 := congrArg Subtype.val h2
      rw [hσv] at h3
      exact h3
    · exact hlt
  refine ⟨w - c, by omega, ?_, ?_⟩
  · rw [hw]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [hw, hc] at hmod
    have h1 : r ∣ 2 ^ w - 2 ^ c := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num)
      hcw.le)).mp hmod.symm
    have h2 : 2 ^ w - 2 ^ c = 2 ^ c * (2 ^ (w - c) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hcw.le]
    rw [h2] at h1
    exact ((Nat.coprime_primes hr Nat.prime_two).mpr hr2).pow_right c |>.dvd_of_dvd_mul_left h1

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
