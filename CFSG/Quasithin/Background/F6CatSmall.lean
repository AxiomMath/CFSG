module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Logic.Equiv.Fin.Rotate

public section

namespace CFSG.Quasithin

namespace F6

theorem alternating_six_pow_six : ∀ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 →
    σ ^ 6 = 1 → σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by
  decide +kernel

theorem perm_six_pow_twelve : ∀ σ : Equiv.Perm (Fin 6), σ ^ 12 = 1 → σ ^ 4 = 1 ∨ σ ^ 6 = 1 := by
  decide +kernel

theorem eq_twelve_of_dvd {k : ℕ} (h : k ∣ 12) (h4 : ¬ k ∣ 4) (h6 : ¬ k ∣ 6) : k = 12 := by
  have hk : k ≤ 12 := Nat.le_of_dvd (by norm_num) h
  interval_cases k <;> omega

theorem dvd_six_of_dvd_twelve {k : ℕ} (h : k ∣ 12) (h4 : ¬ 4 ∣ k) : k ∣ 6 := by
  have hk : k ≤ 12 := Nat.le_of_dvd (by norm_num) h
  interval_cases k <;> omega

theorem dvd_four_of_dvd_twelve {k : ℕ} (h : k ∣ 12) (h3 : ¬ 3 ∣ k) : k ∣ 4 := by
  have hk : k ≤ 12 := Nat.le_of_dvd (by norm_num) h
  interval_cases k <;> omega

theorem eq_four_of_dvd_twelve {a : ℕ} (h : a ∣ 12) (h4 : 4 ∣ a) (h7 : a ≤ 7) : a = 4 := by
  interval_cases a <;> omega

theorem eq_three_or_six_of_dvd_twelve {b : ℕ} (h : b ∣ 12) (h3 : 3 ∣ b) (h7 : b ≤ 7) :
    b = 3 ∨ b = 6 := by
  interval_cases b <;> omega

theorem alternating_seven_pow_twelve (σ : Equiv.Perm (Fin 7)) (hσ : Equiv.Perm.sign σ = 1)
    (h12 : σ ^ 12 = 1) : σ ^ 4 = 1 ∨ σ ^ 6 = 1 := by
  by_contra hne
  push Not at hne
  obtain ⟨h4, h6⟩ := hne
  have ho : orderOf σ = 12 := eq_twelve_of_dvd (orderOf_dvd_of_pow_eq_one h12)
    (fun h => h4 (orderOf_dvd_iff_pow_eq_one.mp h)) (fun h => h6 (orderOf_dvd_iff_pow_eq_one.mp h))
  set m := σ.cycleType with hm
  have hlcm : m.lcm = 12 := by rw [hm, Equiv.Perm.lcm_cycleType, ho]
  have hsum : m.sum ≤ 7 := (Equiv.Perm.sum_cycleType_le σ).trans (by simp)
  have hdvd : ∀ k ∈ m, k ∣ 12 := fun k hk => hlcm ▸ Multiset.dvd_lcm hk
  have hle : ∀ k ∈ m, k ≤ 7 := fun k hk => (Multiset.le_sum_of_mem hk).trans hsum
  have h4m : ∃ k ∈ m, 4 ∣ k := by
    by_contra hno
    push Not at hno
    have : m.lcm ∣ 6 := Multiset.lcm_dvd.mpr fun k hk =>
      dvd_six_of_dvd_twelve (hdvd k hk) (hno k hk)
    rw [hlcm] at this
    norm_num at this
  have h3m : ∃ k ∈ m, 3 ∣ k := by
    by_contra hno
    push Not at hno
    have : m.lcm ∣ 4 := Multiset.lcm_dvd.mpr fun k hk =>
      dvd_four_of_dvd_twelve (hdvd k hk) (hno k hk)
    rw [hlcm] at this
    norm_num at this
  obtain ⟨a, ha, ha4⟩ := h4m
  obtain ⟨b, hb, hb3⟩ := h3m
  have ha' : a = 4 := eq_four_of_dvd_twelve (hdvd a ha) ha4 (hle a ha)
  have hb' : b = 3 ∨ b = 6 := eq_three_or_six_of_dvd_twelve (hdvd b hb) hb3 (hle b hb)
  obtain ⟨m', hm'⟩ := Multiset.exists_cons_of_mem ha
  have hb'' : b ∈ m' := by
    rw [hm', Multiset.mem_cons] at hb
    rcases hb with hb | hb
    · omega
    · exact hb
  obtain ⟨m'', hm''⟩ := Multiset.exists_cons_of_mem hb''
  have hsum' : m.sum = a + (b + m''.sum) := by rw [hm', hm'', Multiset.sum_cons, Multiset.sum_cons]
  have hb3' : b = 3 := by omega
  have hm0 : m'' = 0 := by
    by_contra h0
    obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero h0
    have hcm : c ∈ m := by
      rw [hm', hm'']
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hc)
    have h2 : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hcm
    have h3 : c ≤ m''.sum := Multiset.le_sum_of_mem hc
    omega
  have hs := Equiv.Perm.sign_of_cycleType σ
  rw [← hm, hm', hm'', hm0, hσ, ha', hb3'] at hs
  simp at hs
  exact absurd hs (by decide)

theorem dihedral_twelve_facts' :
    (DihedralGroup.r (1 : ZMod 12)) ^ 12 = 1 ∧ (DihedralGroup.r (1 : ZMod 12)) ^ 4 ≠ 1 ∧
      (DihedralGroup.r (1 : ZMod 12)) ^ 6 ≠ 1 ∧ (DihedralGroup.r (2 : ZMod 12)) ^ 6 = 1 ∧
      (DihedralGroup.r (2 : ZMod 12)) ^ 2 ≠ 1 ∧ (DihedralGroup.r (2 : ZMod 12)) ^ 3 ≠ 1 := by
  decide +kernel

theorem z3_e4_order_six :
    (Multiplicative.ofAdd (1 : ZMod 3), Multiplicative.ofAdd (1 : ZMod 2),
        (1 : Multiplicative (ZMod 2))) ^ 6 = 1 ∧
      (Multiplicative.ofAdd (1 : ZMod 3), Multiplicative.ofAdd (1 : ZMod 2),
        (1 : Multiplicative (ZMod 2))) ^ 2 ≠ 1 ∧
      (Multiplicative.ofAdd (1 : ZMod 3), Multiplicative.ofAdd (1 : ZMod 2),
        (1 : Multiplicative (ZMod 2))) ^ 3 ≠ 1 := by
  decide +kernel

theorem s3_d8_order_twelve :
    (finRotate 3, DihedralGroup.r (1 : ZMod 4)) ^ 12 = 1 ∧
      (finRotate 3, DihedralGroup.r (1 : ZMod 4)) ^ 4 ≠ 1 ∧
      (finRotate 3, DihedralGroup.r (1 : ZMod 4)) ^ 6 ≠ 1 := by
  decide +kernel

theorem pow_facts_of_injective {X G : Type*} [Monoid X] [Monoid G] (f : X →* G)
    (hf : Function.Injective f) {x : X} {n a b : ℕ} (h : x ^ n = 1 ∧ x ^ a ≠ 1 ∧ x ^ b ≠ 1) :
    f x ^ n = 1 ∧ f x ^ a ≠ 1 ∧ f x ^ b ≠ 1 := by
  refine ⟨by rw [← map_pow, h.1, map_one], fun h' => h.2.1 (hf ?_), fun h' => h.2.2 (hf ?_)⟩
  · rw [map_pow, h', map_one]
  · rw [map_pow, h', map_one]

end F6

end CFSG.Quasithin
