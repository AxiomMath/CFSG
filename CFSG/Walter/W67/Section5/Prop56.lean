module

public import CFSG.Walter.W67.Section5.Prop56A2c
public import CFSG.Walter.W67.Section5.P56K3c
public import CFSG.Walter.W67.Section5.P56N3

public section

namespace CFSG.Walter.W67

theorem prop_5_6_of
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) : S_prop_5_6 := by
  intro G _ _ s hp hR h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f5⟩ := Frame5.nonempty s
  obtain ⟨R, hR3, hRC, hP₁R, hRN, hRmax⟩ := f5.exists_R h26i hp
  have hRd : f5.RData R := ⟨hR3, hRC, hP₁R, hRN, hRmax⟩
  obtain ⟨⟨x, hxE⟩, hox⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.E) 3 h3
  rw [Subgroup.orderOf_mk] at hox
  have hn : s.f = 3 ∨ 9 ≤ s.f := by
    obtain ⟨m, hm⟩ := s.three_dvd_f h26i h3
    obtain ⟨j, hj⟩ := s.odd_f_of_p3 hp
    omega
  have hexp : ∀ Q : Subgroup G, IsPGroup 3 Q → f5.P₁ ≤ Q →
      f5.B ≤ Subgroup.normalizer (Q : Set G) → s.fr.E ≤ Subgroup.normalizer (Q : Set G) →
      s.J ∈ Subgroup.normalizer (Q : Set G) →
      Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = s.q →
      ∃ y ∈ Q, y ^ 3 ≠ 1 := by
    intro Q hQ3 hP₁Q hBQ hEQ hJQ hQx
    rcases hn with hf | h9
    · exact f5.exists_pow_three_ne_one_three h26i hJR hR hp hf hQ3 hBQ hEQ hxE hox hQx
    · exact f5.exists_pow_three_ne_one_nine h22 h26i hJR hR hp hQ3 hP₁Q hBQ hEQ hJQ hxE hox h9
        hQx
  have hcen : ∀ Q : Subgroup G, IsPGroup 3 Q → f5.P₁ ≤ Q →
      f5.P₁ ≤ Subgroup.centralizer (Q : Set G) →
      f5.B ≤ Subgroup.normalizer (Q : Set G) → s.fr.E ≤ Subgroup.normalizer (Q : Set G) →
      s.J ∈ Subgroup.normalizer (Q : Set G) →
      Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = s.q → False := by
    intro Q hQ3 hP₁Q hP₁C hBQ hEQ hJQ hQx
    rcases hn with hf | h9
    · exact f5.false_of_center_three h26i hJR hR hp hf hQ3 hP₁Q hP₁C hBQ hEQ hxE hox hQx
    · exact f5.false_of_center_nine h22 h26i hJR hR hp hQ3 hP₁Q hP₁C hBQ hEQ hJQ hxE hox h9 hQx
  have hcube : ∀ Q : Subgroup G, IsPGroup 3 Q → f5.B ≤ Subgroup.normalizer (Q : Set G) →
      s.fr.E ≤ Subgroup.normalizer (Q : Set G) → ∃ k ≤ 3, Nat.card Q = s.q ^ k ∧
        (k = 3 → Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = s.q) := by
    intro Q hQ3 hBQ hEQ
    obtain ⟨k, hk⟩ := f5.card_eq_q_pow hp hQ3 hBQ (f5.fpf_of_isPGroup h22 h26i hp hQ3 hBQ hEQ)
    have h1 := f5.card_inf_centralizer_le h26i hJR hR hp hQ3 hBQ hEQ hxE hox
    have h2 := f5.card_inf_centralizer_pow_three h22 h26i hp hQ3 hBQ hEQ hxE hox
    obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp (hQ3.to_le
      (inf_le_left : Q ⊓ Subgroup.centralizer ({x} : Set G) ≤ Q))
    rw [ht, hk, Hyp.q, hp, ← pow_mul, ← pow_mul] at h2
    rw [ht, Hyp.q, hp] at h1
    have h2' : t * 3 = s.f * k := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2
    have h1' : t ≤ s.f := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    have hf := s.f_pos
    have hk3 : k ≤ 3 := by
      by_contra h
      push Not at h
      have : s.f * 4 ≤ s.f * k := Nat.mul_le_mul_left _ h
      omega
    refine ⟨k, hk3, hk, fun hk3' => ?_⟩
    rw [hk3'] at h2'
    rw [ht, Hyp.q, hp, show t = s.f by omega]
  obtain ⟨k, hk3, hk, hkx⟩ := hcube R hR3 hRd.B_le hRd.E_le
  have hk1 : 1 ≤ k := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le hP₁R
    rw [hk, show k = 0 by omega, pow_zero, f5.card_P₁] at h1
    have := s.one_lt_q
    omega
  interval_cases k
  ·
    apply f5.false_of_card_centralizer h22 h26i hp h3
    intro Q hQ hQC
    calc Nat.card Q ≤ Nat.card R := hRmax Q hQ hQC
      _ = Nat.card f5.P₁ := by rw [hk, pow_one, f5.card_P₁]
  ·
    by_cases hRna : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a
    · exact hRd.false_of_nonabelian h22 h26i hp h3 hk hRna
    push Not at hRna
    obtain ⟨V, ⟨hV3, hRV, hJV, hBV, hEV⟩, hVmax⟩ := Set.exists_max_image
      {Q : Subgroup G | IsPGroup 3 Q ∧ R ≤ Q ∧ s.J ∈ Subgroup.normalizer (Q : Set G) ∧
        f5.B ≤ Subgroup.normalizer (Q : Set G) ∧ s.fr.E ≤ Subgroup.normalizer (Q : Set G)}
      (fun Q => Nat.card Q) (Set.toFinite _) ⟨R, hR3, le_rfl, hRd.J_le, hRd.B_le, hRd.E_le⟩
    have hmaxV : ∀ Q : Subgroup G, IsPGroup 3 Q → V ≤ Q →
        s.J ∈ Subgroup.normalizer (Q : Set G) → f5.B ≤ Subgroup.normalizer (Q : Set G) →
        s.fr.E ≤ Subgroup.normalizer (Q : Set G) → Q = V := fun Q hQ hVQ hJQ hBQ hEQ =>
      (Subgroup.eq_of_le_of_card_ge hVQ (hVmax Q ⟨hQ, hRV.trans hVQ, hJQ, hBQ, hEQ⟩)).symm
    by_cases hVR : V = R
    ·
      subst hVR
      exact hRd.false_of_abelian h22 h26i hp h3 hRna hk hmaxV
    ·
      obtain ⟨l, hl3, hl, hlx⟩ := hcube V hV3 hBV hEV
      have hlt : R < V := lt_of_le_of_ne hRV (Ne.symm hVR)
      have hl3' : l = 3 := by
        have h1 := Subgroup.card_lt_of_lt hlt
        rw [hk, hl] at h1
        have := (Nat.pow_lt_pow_iff_right s.one_lt_q).mp h1
        omega
      subst hl3'
      have hK : f5.K3Data R V :=
        ⟨hRd, hRna, hk, hV3, hRV, fun h => hVR h.symm, hl, hJV, hBV, hEV, hmaxV⟩
      exact hK.false_of_exp h22 h26i hp h3
        (hexp V hV3 (hP₁R.trans hRV) hBV hEV hJV (hlx rfl))
  ·
    exact hcen R hR3 hP₁R hRd.P₁_le_centralizer hRd.B_le hRd.E_le hRd.J_le (hkx rfl)

theorem prop_5_6 :
    S_prop_5_6 :=
  prop_5_6_of lemma_2_2 lemma_2_6_i IsJRSubgroup.nonempty_jrGroup

end CFSG.Walter.W67
