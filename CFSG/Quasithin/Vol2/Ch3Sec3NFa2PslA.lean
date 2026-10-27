module

public import CFSG.Quasithin.Vol2.Ch3Sec3L2qFacts
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2L2Gen

public section

namespace CFSG.Quasithin.H13.NFa2

theorem psl_small_two_conj_zpow {X : Type} [Group X] {A : Subgroup X} {x : X}
    (hxA : x ∈ Subgroup.normalizer (A : Set X)) (j : ℤ) {b : X} (hb : b ∈ A) :
    x ^ j * b * (x ^ j)⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (A : Set X)).zpow_mem hxA j) b).mp hb

theorem psl_small_two_exists_normal_form {X : Type} [Group X] {A : Subgroup X} {x : X}
    (hxA : x ∈ Subgroup.normalizer (A : Set X)) :
    ∃ T : Subgroup X, A ≤ T ∧ x ∈ T ∧ T ≤ Subgroup.normalizer (A : Set X) ∧
      ∀ g ∈ T, ∃ a ∈ A, ∃ j : ℤ, g = a * x ^ j := by
  let T : Subgroup X :=
    { carrier := {g | ∃ a ∈ A, ∃ j : ℤ, g = a * x ^ j}
      one_mem' := ⟨1, A.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, j, rfl⟩ ⟨b, hb, k, rfl⟩
        exact ⟨a * (x ^ j * b * (x ^ j)⁻¹), A.mul_mem ha (psl_small_two_conj_zpow hxA j hb),
          j + k, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, j, rfl⟩
        exact ⟨x ^ (-j) * a⁻¹ * (x ^ (-j))⁻¹, psl_small_two_conj_zpow hxA (-j) (A.inv_mem ha),
          -j, by group⟩ }
  refine ⟨T, ?_, ⟨1, A.one_mem, 1, by simp⟩, ?_, fun g hg => hg⟩
  · intro a ha
    exact ⟨a, ha, 0, by simp⟩
  · rintro g ⟨a, ha, j, rfl⟩
    exact (Subgroup.normalizer (A : Set X)).mul_mem (Subgroup.le_normalizer ha)
      ((Subgroup.normalizer (A : Set X)).zpow_mem hxA j)

theorem psl_small_two_card_twelve {X : Type} [Group X] {A T : Subgroup X} {x : X}
    (hAT : A ≤ T) (hxT : x ∈ T) (hTN : T ≤ Subgroup.normalizer (A : Set X))
    (hform : ∀ g ∈ T, ∃ a ∈ A, ∃ j : ℤ, g = a * x ^ j)
    (hA4 : Nat.card A = 4) (hx3 : orderOf x = 3) (hxA : x ∉ A) : Nat.card T = 12 := by
  have hx3' : x ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
  haveI : (A.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAT).mpr hTN
  have hA'card : Nat.card (A.subgroupOf T) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv).trans hA4
  obtain ⟨x', hx'⟩ : ∃ x' : T, (x' : X) = x := ⟨⟨x, hxT⟩, rfl⟩
  have hmem : ∀ y : T ⧸ A.subgroupOf T,
      y ∈ Subgroup.zpowers (QuotientGroup.mk x' : T ⧸ A.subgroupOf T) := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha, j, hw⟩ := hform w.1 w.2
    have hwj : w = (⟨a, hAT ha⟩ : T) * x' ^ j := Subtype.ext (by simp [hw, hx'])
    have hone : (QuotientGroup.mk (⟨a, hAT ha⟩ : T) : T ⧸ A.subgroupOf T) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha)
    rw [hwj, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hone, one_mul]
    exact Subgroup.zpow_mem_zpowers _ j
  have hpow : (QuotientGroup.mk x' : T ⧸ A.subgroupOf T) ^ 3 = 1 := by
    have h1 : x' ^ 3 = 1 := Subtype.ext (by simpa [hx'] using hx3')
    rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  have hne : (QuotientGroup.mk x' : T ⧸ A.subgroupOf T) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    have hxA0 : (x' : X) ∈ A := Subgroup.mem_subgroupOf.mp h
    rw [hx'] at hxA0
    exact hxA hxA0
  have hord : orderOf (QuotientGroup.mk x' : T ⧸ A.subgroupOf T) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hidx : (A.subgroupOf T).index = 3 := by
    rw [Subgroup.index_eq_card, ← orderOf_eq_card_of_forall_mem_zpowers hmem, hord]
  have hcard := Subgroup.card_mul_index (A.subgroupOf T)
  rw [hA'card, hidx] at hcard
  omega

theorem psl_small_two_subgroup {X : Type} [Group X] (q : ℕ)
    (hq : q.Prime) (h24 : q % 24 = 11 ∨ q % 24 = 13)
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 q 1)
    (A : Subgroup X) (hA : IsPGroup 2 A) (x s : X) (hx3 : orderOf x = 3)
    (hxA : x ∈ Subgroup.normalizer (A : Set X)) (hsA : s ∈ Subgroup.normalizer (A : Set X))
    (hs : ∃ a ∈ A, s * x * s⁻¹ = a * x⁻¹) :
    Nat.card A ≤ 2 := by
  have hq5 : 5 ≤ q := by omega
  have h3 : q % 8 = 3 ∨ q % 8 = 5 := by omega
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFq : Nat.card (ZMod q) = q := Nat.card_zmod q
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_zmod hq hX
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  by_contra hgt
  obtain ⟨P, hAP⟩ := IsPGroup.exists_le_sylow hA
  have hPcard : Nat.card (P : Subgroup X) = 4 :=
    CFSG.Quasithin.H13.L2q.card_sylow_four e hFq hq hq5 h3 P.isPGroup' P.not_dvd_index
  have hdvd : Nat.card A ∣ 4 := by
    have := Subgroup.card_dvd_of_le hAP
    rwa [hPcard] at this
  have hA4 : Nat.card A = 4 := by
    have hle : Nat.card A ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    rcases (show Nat.card A = 3 ∨ Nat.card A = 4 by omega) with h | h
    · rw [h] at hdvd
      norm_num at hdvd
    · exact h
  have hAeq : A = (P : Subgroup X) := Subgroup.eq_of_le_of_card_ge hAP (by omega)
  have hSi : ¬ 2 ∣ A.index := by
    rw [hAeq]
    exact P.not_dvd_index
  have hxA' : x ∉ A := by
    intro h
    have h3A := orderOf_dvd_natCard (⟨x, h⟩ : A)
    rw [Subgroup.orderOf_mk, hx3, hA4] at h3A
    omega
  obtain ⟨T, hAT, hxT, hTN, hform⟩ := psl_small_two_exists_normal_form hxA
  have hTcard : Nat.card T = 12 := psl_small_two_card_twelve hAT hxT hTN hform hA4 hx3 hxA'
  obtain ⟨hNT, -⟩ :=
    CFSG.Quasithin.H13.L2q.normalizer_twelve_X e hFq hq hq5 h3 hA hSi hAT hTcard hTN
  have hsT : s ∈ T := by
    rw [← hNT]
    exact hsA
  obtain ⟨a', ha', j, rfl⟩ := hform s hsT
  obtain ⟨a, ha, hsx⟩ := hs
  have hx3' : x ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
  have hb : a' * (x * a'⁻¹ * x⁻¹) ∈ A :=
    A.mul_mem ha' ((Subgroup.mem_normalizer_iff.mp hxA a'⁻¹).mp (A.inv_mem ha'))
  have hconj : a' * x ^ j * x * (a' * x ^ j)⁻¹ = a' * (x * a'⁻¹ * x⁻¹) * x := by group
  rw [hconj] at hsx
  have e1 : a⁻¹ * (a' * (x * a'⁻¹ * x⁻¹)) = x⁻¹ * x⁻¹ := by
    calc a⁻¹ * (a' * (x * a'⁻¹ * x⁻¹)) = a⁻¹ * (a' * (x * a'⁻¹ * x⁻¹) * x) * x⁻¹ := by group
      _ = a⁻¹ * (a * x⁻¹) * x⁻¹ := by rw [hsx]
      _ = x⁻¹ * x⁻¹ := by group
  have h2 : x⁻¹ * x⁻¹ ∈ A := e1 ▸ A.mul_mem (A.inv_mem ha) hb
  have h4 : x⁻¹ * x⁻¹ * (x⁻¹ * x⁻¹) = x⁻¹ := by
    calc x⁻¹ * x⁻¹ * (x⁻¹ * x⁻¹) = (x ^ 3)⁻¹ * x⁻¹ := by group
      _ = x⁻¹ := by rw [hx3', inv_one, one_mul]
  have h5 : x⁻¹ ∈ A := h4 ▸ A.mul_mem h2 h2
  have hxA2 : x ∈ A := by simpa using A.inv_mem h5
  exact hxA' hxA2

end CFSG.Quasithin.H13.NFa2
