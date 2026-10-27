module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D3Loc
public import CFSG.Quasithin.Vol2.GoldschmidtF431D3NFGen

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.D4Hex
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] noncomputable def d3Q : Subgroup (MulAut D) := d4Q.map (MulAut.conj : D →* MulAut D)

@[expose] def d3O (w : MulAut D) : Prop := ∃ v : D, D4O v ∧ w = MulAut.conj v

section Data


theorem d3Q_le_d3T : d3Q ≤ d3T := Subgroup.map_mono d4Q_le_d4U

theorem card_d3Q (hs : IsSimpleGroup D) : Nat.card d3Q = 512 := by
  rw [d3Q, Subgroup.card_map_of_injective (conj_injective hs)]
  exact card_d4Q

theorem card_d3T (hs : IsSimpleGroup D) : Nat.card d3T = 4096 := by
  rw [d3T, Subgroup.card_map_of_injective (conj_injective hs)]
  exact card_d4U'

theorem d3_hTQ : ∀ x ∈ d3T, ∀ y ∈ d3T, x * y * x⁻¹ * y⁻¹ ∈ d3Q := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact ⟨x * y * x⁻¹ * y⁻¹, d4_hTQ x hx y hy, by simp⟩

theorem d3_hQcomm : ∀ x ∈ d3Q, ∀ y ∈ d3Q,
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = d3z := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have e : (MulAut.conj x : MulAut D) * MulAut.conj y * (MulAut.conj x)⁻¹ * (MulAut.conj y)⁻¹ =
      MulAut.conj (x * y * x⁻¹ * y⁻¹) := by simp
  rw [e]
  rcases d4_hQcomm x hx y hy with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]
    rfl

theorem d3_hQsq : ∀ x ∈ d3Q, x * x = 1 ∨ x * x = d3z := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul]
  rcases d4_hQsq x hx with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]
    rfl

theorem d3_hQZ (hs : IsSimpleGroup D) :
    ∀ w ∈ d3Q, (∀ q ∈ d3Q, q * w = w * q) → w = 1 ∨ w = d3z := by
  rintro _ ⟨w, hw, rfl⟩ hc
  have hc' : ∀ q ∈ d4Q, q * w = w * q := by
    intro q hq
    have h1 := hc (MulAut.conj q) ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact conj_injective hs h1
  rcases d4_hQZ w hw hc' with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]
    rfl

end Data

section Data2


theorem d3_hQn : ∀ h ∈ autStab d4H, ∀ q ∈ d3Q, h * q * h⁻¹ ∈ d3Q := by
  rintro h hh _ ⟨q, hq, rfl⟩
  rw [aut_mul_conj_inv]
  exact ⟨h q, d4Q_char hh q hq, rfl⟩

theorem d3_hOinv (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z) :
    ∀ h ∈ autStab d4H, ∀ w, d3O w → d3O (h * w * h⁻¹) := by
  rintro h hh _ ⟨v, hv, rfl⟩
  have hz : h⁻¹ d4z = d4z := by
    have h1 := fix_of_mem_autStab_H hCU hh
    calc h⁻¹ d4z = h⁻¹ (h d4z) := by rw [h1]
      _ = d4z := by simp
  refine ⟨h v, ⟨d4Q_char hh v hv.1, ?_, ?_, ?_⟩, aut_mul_conj_inv h v⟩
  · rw [← map_mul, hv.2.1, map_one]
  · intro e
    exact hv.2.2.1 (h.injective (by rw [e, map_one]))
  · intro hc
    apply hv.2.2.2
    obtain ⟨c, hc'⟩ := isConj_iff.1 hc
    have h1 := congrArg (fun x => h⁻¹ x) hc'
    simp only [map_mul, map_inv, hz] at h1
    rw [show h⁻¹ (h v) = v by simp] at h1
    exact isConj_iff.2 ⟨h⁻¹ c, h1⟩

theorem d3_hOt (hs : IsSimpleGroup D) : ∀ w, d3O w → ∃ t ∈ d3T, t * w * t⁻¹ * w⁻¹ ≠ 1 ∧
    t * w * t⁻¹ * w⁻¹ ≠ d3z := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨t0, ht0, h1, h2⟩ := D4O.exists_comm hv
  have e : (MulAut.conj t0 : MulAut D) * MulAut.conj v * (MulAut.conj t0)⁻¹ * (MulAut.conj v)⁻¹ =
      MulAut.conj (t0 * v * t0⁻¹ * v⁻¹) := by simp
  refine ⟨MulAut.conj t0, conj_mem_d3T ht0, ?_, ?_⟩ <;> rw [e]
  · exact fun h => h1 (conj_injective hs (h.trans (map_one _).symm))
  · exact fun h => h2 (conj_injective hs h)

theorem d3_pair_conj {v a b : D} (ha : a ∈ d4Q) (hb : b ∈ d4Q) (hav : a * v = v * a)
    (hbv : b * v = v * b) (hab : a * b * a⁻¹ * b⁻¹ = d4z) :
    ∃ a' ∈ d3Q, ∃ b' ∈ d3Q, a' * MulAut.conj v = MulAut.conj v * a' ∧
      b' * MulAut.conj v = MulAut.conj v * b' ∧ a' * b' * a'⁻¹ * b'⁻¹ = d3z := by
  refine ⟨MulAut.conj a, ⟨a, ha, rfl⟩, MulAut.conj b, ⟨b, hb, rfl⟩, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hav]
  · rw [← map_mul, ← map_mul, hbv]
  · have e : (MulAut.conj a : MulAut D) * MulAut.conj b * (MulAut.conj a)⁻¹ *
        (MulAut.conj b)⁻¹ = MulAut.conj (a * b * a⁻¹ * b⁻¹) := by simp
    rw [e, hab]
    rfl

end Data2

section Main


theorem d3_not_conj (hs : IsSimpleGroup D)
    (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z)
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index)
    {M : Type} [Group M] [Finite M] {b1 : ↥(autStab d4H) →* M} {b2 : ↥(autStab d4N) →* M}
    (C : F431Comp (autStab d4H) (autStab d4N) b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 d3z} : Set M) ≤ b1.range) :
    ¬ IsConj (amalgamMap b1 b2 d3z) (amalgamMap b1 b2 d3t) := by
  intro hzt
  have hinj := conj_injective hs
  have hLie := d3_F431LieI hs hCU hodd
  have hzM : d3z ∈ autStab d4H := hLie.T_le₁ d3z_mem_d3T
  have htM : d3t ∈ autStab d4H := hLie.T_le₁ d3t_mem_d3T
  rw [amalgamMap_of_mem₁ b1 b2 hzM] at hb hzt
  obtain ⟨v0, hv0, a0, ha0, b0, hb0, hav, hbv, hab⟩ := d4_hpair
  have hv0T : MulAut.conj v0 ∈ d3T := conj_mem_d3T (d4Q_le_d4U hv0.1)
  have hv0M : MulAut.conj v0 ∈ autStab d4H := hLie.T_le₁ hv0T
  have hv0o : orderOf (MulAut.conj v0) = 2 := by
    rw [orderOf_conj hinj]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hv0.2.1) hv0.2.2.1
  have hconj : IsConj d3t (MulAut.conj v0) := by
    rcases hLie.classes (MulAut.conj v0) hv0o with h | h
    · exfalso
      apply hv0.2.2.2
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      rw [d3z, aut_mul_conj_inv] at hc
      obtain ⟨c', hc'⟩ := exists_aut_d4z c
      exact isConj_iff.2 ⟨c', by rw [← hc', hinj hc]⟩
    · exact h
  have hfus := hLie.fusion_forward C d3t_mem_d3T hv0T hLie.ht hv0o hconj
  rw [amalgamMap_of_mem₁ b1 b2 hv0M, amalgamMap_of_mem₁ b1 b2 htM] at hfus
  rw [amalgamMap_of_mem₁ b1 b2 htM] at hzt
  have hQ : MulAut.conj v0 ∈ d3Q := ⟨v0, hv0.1, rfl⟩
  have hnf := nf_apply_gen (A := MulAut D) (M1 := autStab d4H) (T := d3T) (Q := d3Q) (z := d3z)
    (b1 := b1) C.inj₁ hzM (by rw [d3z, ← map_mul, d4z_sq.1, map_one])
    (fun h => d4z_sq.2 (hinj (h.trans (map_one _).symm)))
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 ((d3_cent_z hs hCU).symm ▸ hx))
    hb hLie.sylow hLie.T_le₁ d3Q_le_d3T d3_hTQ d3_hQn d3_hQcomm d3_hQsq (d3_hQZ hs)
    (card_d3Q hs) (card_d3T hs) d3O (d3_hOinv hCU) (d3_hOt hs) (v := MulAut.conj v0)
    ⟨v0, hv0, rfl⟩ hQ (fun h => hv0.2.2.2 (by rw [hinj h]))
    (d3_pair_conj ha0 hb0 hav hbv hab)
  exact hnf (hzt.trans hfus)

end Main

section LocalCent


theorem d3_localCent_comp (hs : IsSimpleGroup D)
    (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z)
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index)
    (hcard : Nat.card (MulAut D) ∣ 3 * Nat.card D)
    {M : Type} [Group M] [Finite M] {b1 : ↥(autStab d4H) →* M} {b2 : ↥(autStab d4N) →* M}
    (C : F431Comp (autStab d4H) (autStab d4N) b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 d3z} : Set M) ≤ b1.range) :
    Subgroup.centralizer ({amalgamMap b1 b2 d3t} : Set M) ≤ b2.range := by
  have : Finite (MulAut D) := Nat.finite_of_card_ne_zero (fun h0 => by
    have hD : 0 < Nat.card D := by
      have := finite_D
      exact Nat.card_pos
    rw [h0] at hcard
    exact absurd (Nat.eq_zero_of_zero_dvd hcard) (by omega))
  obtain ⟨q, hD⟩ := d3_Loc442DatumX hs hCU hodd hcard
  exact loc442X hD C hb (d3_not_conj hs hCU hodd C hb)

end LocalCent

end CFSG.Quasithin.D4Hex
