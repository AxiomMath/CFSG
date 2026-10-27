module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3CoverX
public import CFSG.RankThree.PartTwo.Sec8.Hering611SCover

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG.AGLEmbedding.KFactProofs.J3Sylow

theorem eq_bot_or_eq_of_invariant {J : Type} [Group J] {T R : Subgroup J} {s : J}
    (hF : J3CoverFacts T R s) (Q : Subgroup J) (hQR : Q ≤ R)
    (hQs : ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) : Q = ⊥ ∨ Q = R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR9 : Nat.card R = 9 := hF.R_card
  haveI : Finite R := Nat.finite_of_card_ne_zero (by rw [hR9]; norm_num)
  haveI : Finite Q :=
    Finite.of_injective (Subgroup.inclusion hQR) (Subgroup.inclusion_injective hQR)
  have hdvd : Nat.card Q ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hR9]
    exact Subgroup.card_dvd_of_le hQR
  obtain ⟨k, hk, hkQ⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · left
    exact Subgroup.eq_bot_of_card_eq Q (by simpa using hkQ)
  · exfalso
    have hQ3 : Nat.card Q = 3 := by simpa using hkQ
    obtain ⟨q, hqQ, hq1⟩ : ∃ q ∈ Q, q ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr hcon
      rw [hbot] at hQ3
      simp at hQ3
    have hqR : q ∈ R := hQR hqQ
    have hq3 : q ^ 3 = 1 := hF.R_elem.2 q hqR
    have hord : orderOf q = 3 := orderOf_eq_prime hq3 hq1
    have hQz : Q = Subgroup.zpowers q := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hqQ)
      rw [hQ3, Nat.card_zpowers, hord]
    have hsq : s * q * s⁻¹ ∈ Subgroup.zpowers q := hQz ▸ hQs q hqQ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hsq
    rw [← zpow_mod_orderOf, hord] at hn
    have h0 : 0 ≤ n % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h3' : n % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    generalize n % ((3 : ℕ) : ℤ) = r at hn h0 h3'
    interval_cases r
    ·
      apply hq1
      have h1 : s * q * s⁻¹ = 1 := by simpa using hn.symm
      simpa using h1
    ·
      exact hq1 (hF.R_fix q hqR (by simpa using hn.symm))
    ·
      have h1 : s * q * s⁻¹ = q ^ 2 := by simpa using hn.symm
      have hq4 : q ^ 4 = q := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hq3, one_mul, pow_one]
      set φ : MulAut J := MulAut.conj s with hφ
      have hφq : φ q = q ^ 2 := h1
      have hφ2 : φ (q ^ 2) = q := by
        rw [map_pow, hφq, ← pow_mul]
        exact hq4
      have hφφ : φ (φ q) = q := by rw [hφq, hφ2]
      have h4 : (φ ^ 4) q = q := by
        have : (φ ^ 4) q = φ (φ (φ (φ q))) := by simp [pow_succ, MulAut.mul_apply]
        rw [this, hφφ, hφφ]
      have h4' : (φ ^ 4) q = s ^ 4 * q * (s ^ 4)⁻¹ := by
        rw [hφ, ← map_pow, MulAut.conj_apply]
      have hinv := hF.R_inv q hqR
      rw [← h4', h4] at hinv
      have hq2 : q ^ 2 = 1 := by
        have : q * q = 1 := by
          calc q * q = q⁻¹ * q := by rw [← hinv]
            _ = 1 := inv_mul_cancel q
        rwa [pow_two]
      apply hq1
      calc q = q ^ 3 * (q ^ 2)⁻¹ := by group
        _ = 1 := by rw [hq3, hq2]; simp
  · right
    exact Subgroup.eq_of_le_of_card_ge hQR (by rw [hkQ, hR9]; norm_num)

private theorem conj_mem_of_mem_normalizer {J : Type} [Group J] {T R : Subgroup J} {s : J}
    (hF : J3CoverFacts T R s) {r : J} (hr : r ∈ R) : s * r * s⁻¹ ∈ R := by
  obtain ⟨hrT, hrc⟩ := (hF.mem_R r).1 hr
  refine (hF.mem_R _).2 ⟨(Subgroup.mem_normalizer_iff.1 hF.s_norm r).1 hrT, fun y hy => ?_⟩
  have hy' : s⁻¹ * y * s ∈ T := (Subgroup.mem_normalizer_iff''.1 hF.s_norm y).1 hy
  have key : s⁻¹ * y * s * r = r * (s⁻¹ * y * s) := hrc _ hy'
  calc y * (s * r * s⁻¹) = s * (s⁻¹ * y * s * r) * s⁻¹ := by group
    _ = s * (r * (s⁻¹ * y * s)) * s⁻¹ := by rw [key]
    _ = s * r * s⁻¹ * y := by group

private theorem comm_of_mk_eq {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) {T : Subgroup X} {y x' : X}
    (hy : y ∈ Subgroup.centralizer (T : Set X))
    (hxy : QuotientGroup.mk' Z x' = QuotientGroup.mk' Z y) {t : X} (ht : t ∈ T) :
    x' * t = t * x' := by
  have hz : y⁻¹ * x' ∈ Z := by
    simp only [QuotientGroup.mk'_apply] at hxy
    exact QuotientGroup.eq.1 hxy.symm
  obtain ⟨z, hzZ, rfl⟩ : ∃ z ∈ Z, x' = y * z :=
    ⟨y⁻¹ * x', hz, (mul_inv_cancel_left y x').symm⟩
  have hyt : t * y = y * t := Subgroup.mem_centralizer_iff.1 hy t ht
  have hzt : t * z = z * t := Subgroup.mem_center_iff.1 (hZc hzZ) t
  calc y * z * t = y * (z * t) := mul_assoc _ _ _
    _ = y * (t * z) := by rw [hzt]
    _ = y * t * z := (mul_assoc _ _ _).symm
    _ = t * y * z := by rw [hyt]
    _ = t * (y * z) := mul_assoc _ _ _

theorem exists_noncentral_of_facts {X : Type} [Group X] [Finite X] (hX : Group.IsPerfect X)
    {Z : Subgroup X} [Z.Normal] (hZc : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3)
    {Tb Rb : Subgroup (X ⧸ Z)} {sb : X ⧸ Z} (hF : J3CoverFacts Tb Rb sb)
    (hidx : ¬ 3 ∣ Tb.index) {e : X ⧸ Z} (he : e ∈ Rb) (he1 : e ≠ 1) {x : X}
    (hx : QuotientGroup.mk' Z x = e) :
    ∃ t : X, QuotientGroup.mk' Z t ∈ Tb ∧ x * t ≠ t * x := by
  have hπs : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  obtain ⟨s, hs⟩ := hπs sb
  obtain ⟨T, hT⟩ : ∃ T : Subgroup X, T = Tb.comap (QuotientGroup.mk' Z) := ⟨_, rfl⟩
  have hTmem : ∀ h : X, h ∈ T ↔ QuotientGroup.mk' Z h ∈ Tb := fun h => by
    rw [hT, Subgroup.mem_comap]
  have hidxT : ¬ 3 ∣ (Tb.comap (QuotientGroup.mk' Z)).index := by
    rw [Subgroup.index_comap_of_surjective Tb hπs]
    exact hidx
  have hsN : s ∈ Subgroup.normalizer (T : Set X) := by
    refine Subgroup.mem_normalizer_iff.2 fun h => ?_
    show h ∈ T ↔ s * h * s⁻¹ ∈ T
    rw [hTmem, hTmem, map_mul, map_mul, map_inv, hs]
    exact Subgroup.mem_normalizer_iff.1 hF.s_norm (QuotientGroup.mk' Z h)
  have hconj_cent : ∀ y ∈ Subgroup.centralizer (T : Set X),
      s * y * s⁻¹ ∈ Subgroup.centralizer (T : Set X) := by
    intro y hy
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    have hh' : s⁻¹ * h * s ∈ T := (Subgroup.mem_normalizer_iff''.1 hsN h).1 hh
    have hc : s⁻¹ * h * s * y = y * (s⁻¹ * h * s) := Subgroup.mem_centralizer_iff.1 hy _ hh'
    calc h * (s * y * s⁻¹) = s * (s⁻¹ * h * s * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * h * s)) * s⁻¹ := by rw [hc]
      _ = s * y * s⁻¹ * h := by group
  obtain ⟨K0, hK0⟩ : ∃ K0 : Subgroup (X ⧸ Z),
      K0 = (Subgroup.centralizer (T : Set X)).map (QuotientGroup.mk' Z) ⊓ Rb := ⟨_, rfl⟩
  have hmemK0 : ∀ q : X ⧸ Z, q ∈ K0 ↔
      (∃ y ∈ Subgroup.centralizer (T : Set X), QuotientGroup.mk' Z y = q) ∧ q ∈ Rb := by
    intro q
    rw [hK0, Subgroup.mem_inf, Subgroup.mem_map]
  have hK0R : K0 ≤ Rb := by
    intro q hq
    exact ((hmemK0 q).1 hq).2
  have hinv : ∀ q ∈ K0, sb * q * sb⁻¹ ∈ K0 := by
    intro q hq
    obtain ⟨⟨y, hy, rfl⟩, hqR⟩ := (hmemK0 q).1 hq
    refine (hmemK0 (sb * QuotientGroup.mk' Z y * sb⁻¹)).2
      ⟨⟨s * y * s⁻¹, hconj_cent y hy, ?_⟩, conj_mem_of_mem_normalizer hF hqR⟩
    simp only [map_mul, map_inv, hs]
  have hK0bot : K0 = ⊥ := by
    rcases eq_bot_or_eq_of_invariant hF K0 hK0R hinv with h | h
    · exact h
    · exfalso
      have hcent : ∀ x' ∈ Rb.comap (QuotientGroup.mk' Z), ∀ t ∈ Tb.comap (QuotientGroup.mk' Z),
          x' * t = t * x' := by
        intro x' hx' t ht
        have hxR : QuotientGroup.mk' Z x' ∈ K0 := by
          rw [h]
          exact Subgroup.mem_comap.1 hx'
        obtain ⟨⟨y, hy, hyx⟩, -⟩ := (hmemK0 _).1 hxR
        exact comm_of_mk_eq hZc hy hyx.symm ((hTmem t).2 (Subgroup.mem_comap.1 ht))
      obtain ⟨_, _, hcov⟩ := coverX_of_facts hZc hZ3 hF hcent
      exact false_of_coverX hX hcov hidxT
  have hx_notcent : x ∉ Subgroup.centralizer (T : Set X) := by
    intro hxc
    have heK : e ∈ K0 := (hmemK0 e).2 ⟨⟨x, hxc, hx⟩, he⟩
    rw [hK0bot, Subgroup.mem_bot] at heK
    exact he1 heK
  have hnc : ¬ ∀ t ∈ T, t * x = x * t := fun hall =>
    hx_notcent (Subgroup.mem_centralizer_iff.2 hall)
  push Not at hnc
  obtain ⟨t, htT, htx⟩ := hnc
  exact ⟨t, (hTmem t).1 htT, fun h => htx h.symm⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
