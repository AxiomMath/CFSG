module

public import CFSG.Quasithin.EmptyFaithful.S1565L8
public import CFSG.Quasithin.EmptyFaithful.S1565L4
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases1

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Matrix

theorem exists_unit_odd_order_ne_one {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m) : ∃ ω : Kˣ, ω ≠ 1 ∧ Odd (orderOf ω) := by
  obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one hm
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
    (by rw [Nat.card_units, hK]; exact hrd)
  refine ⟨ω, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at hω
    exact hr.one_lt.ne hω
  · rw [hω]
    exact hr.odd_of_ne_two hr2

section Orders

theorem le_card_of_psl2_or_sz {X : Type} [Group X] {n : ℕ}
    (hn : 3 ≤ n) (h : IsPSL 2 2 n X ∨ IsSz n X) : 504 ≤ Nat.card X := by
  rcases h with h | h
  · obtain ⟨-, hc⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two h
    rw [hc]
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h64 : 64 ≤ 2 ^ (2 * n) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h63 : 63 ≤ Vol2.Ch11.SecA.oSL2 n := by
      show 63 ≤ 2 ^ (2 * n) - 1
      omega
    calc 504 = 8 * 63 := by norm_num
      _ ≤ 2 ^ n * Vol2.Ch11.SecA.oSL2 n := Nat.mul_le_mul h8 h63
  · obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
    subst hf
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h64 : 64 ≤ (2 ^ (2 * a + 1)) ^ 2 := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h8 2
    have h7 : 7 ≤ 2 ^ (2 * a + 1) - 1 := by omega
    have h65 : 65 ≤ (2 ^ (2 * a + 1)) ^ 2 + 1 := by omega
    calc 504 ≤ 64 * 7 * 65 := by norm_num
      _ ≤ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h64 h7) h65

variable {W : Type} [CommGroup W]

theorem card_le_six_of_natural_sl2_small {L : Subgroup (MulAut W)} {U Z : Subgroup W} {n' : ℕ}
    (h : BinaryNaturalSL L U Z 2 n') (hn' : n' ≤ 1) : Nat.card ↥L ≤ 6 := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hsurj := hπ.1
  have h1 : Nat.card ↥L ≤ Nat.card ↥(StatedSL 2 K) := Nat.card_le_card_of_surjective π hsurj
  have h2 : Nat.card ↥(StatedSL 2 K) ≤ Nat.card (GL (Fin 2) K) :=
    Subgroup.card_le_card_group _
  have := Fintype.ofFinite K
  have h3 := Matrix.card_GL_field (𝔽 := K) 2
  rw [← Nat.card_eq_fintype_card] at h3
  have hq : Nat.card K ≤ 2 := by
    rw [hK]
    calc 2 ^ n' ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn'
      _ = 2 := by norm_num
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq' : Nat.card K = 1 ∨ Nat.card K = 2 := by omega
  rcases hq' with h4 | h4
  · rw [h4] at h3
    simp at h3
    omega
  · rw [h4] at h3
    simp [Fin.prod_univ_two] at h3
    omega

theorem card_le_168_of_natural_sl3 {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (h : BinaryNaturalSL L U Z 3 1) : Nat.card ↥L ≤ 168 := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hsurj := hπ.1
  have h1 : Nat.card ↥L ≤ Nat.card ↥(StatedSL 3 K) := Nat.card_le_card_of_surjective π hsurj
  have h2 : Nat.card ↥(StatedSL 3 K) ≤ Nat.card (GL (Fin 3) K) :=
    Subgroup.card_le_card_group _
  have := Fintype.ofFinite K
  have h3 := Matrix.card_GL_field (𝔽 := K) 3
  rw [← Nat.card_eq_fintype_card, hK] at h3
  simp [Fin.prod_univ_three] at h3
  omega

theorem card_le_sixty_of_alternating_five {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (h : AlternatingNatural L U Z 5) : Nat.card ↥L ≤ 60 := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 5)) :=
    Nat.card_le_card_of_surjective π hπ.1
  have h2 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  omega

end Orders

section Sum

variable {W : Type} [CommGroup W]

private theorem fixV_inv_of_normalizer {Mp : Subgroup (MulAut W)} {τ : MulAut W}
    (hτ : τ ∈ Subgroup.normalizer (Mp : Set (MulAut W))) {c : W} (hc : c ∈ fixV Mp) :
    τ c ∈ fixV Mp :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hτ hc

theorem mod_sum_good {Mp L₀ : Subgroup (MulAut W)} {τ : MulAut W}
    (hLMp : L₀ ≤ Mp) (hτMp : τ ∈ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hτ2 : ∀ g ∈ L₀, τ⁻¹ * g * τ ∈ conjAutSub τ L₀)
    (hsum : IsSumMod (fixV Mp) (commV L₀) ((commV L₀).map τ.toMonoidHom) ⊤)
    (hA : commV L₀ ≤ fixV (conjAutSub τ L₀)) {s : MulAut W} (hs : s ∈ L₀)
    (hNat : ∀ a ∈ commV L₀, s a * a⁻¹ ∈ commV L₀ ⊓ fixV Mp → a ∈ fixV Mp) :
    ∀ w : W, ((s * (τ * s * τ⁻¹)) w) * w⁻¹ ∈ fixV Mp → w ∈ fixV Mp := by
  have hmemconj : τ * s * τ⁻¹ ∈ conjAutSub τ L₀ :=
    Subgroup.mem_map.mpr ⟨s, hs, by simp [MulAut.conj_apply]⟩
  refine sum_good_element (C := fixV Mp) (A := commV L₀) (t := τ) (s := s) (s' := τ * s * τ⁻¹)
    hsum ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hNat
  · simp [mul_assoc]
  · intro a ha
    exact hA ha _ hmemconj
  · intro a ha
    have h1 : τ⁻¹ * s * τ ∈ conjAutSub τ L₀ := hτ2 s hs
    have h2 := hA ha _ h1
    have h3 : (τ * (τ⁻¹ * s * τ)) a = τ a := by
      rw [MulAut.mul_apply, h2]
    have h4 : τ * (τ⁻¹ * s * τ) = s * τ := by group
    rw [h4] at h3
    exact h3
  · intro c hc
    exact hc s (hLMp hs)
  · intro c hc
    refine hc _ ?_
    have := (Subgroup.mem_normalizer_iff.mp hτMp s).mp (hLMp hs)
    exact this
  · intro a ha
    exact (le_stabSub_commV_self L₀ hs a).mpr ha
  · intro c hc
    exact fixV_inv_of_normalizer hτMp hc
  · intro c hc
    exact fixV_inv_of_normalizer (Subgroup.inv_mem _ hτMp) hc

end Sum

end CFSG.Quasithin
