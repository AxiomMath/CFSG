module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BRows
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint
open CFSG.Quasithin.Ch1Four

section Rows

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {n : ℕ}

omit [Finite Q] in
theorem card_block (hD : BarData B n) (hO2 : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ (2 * n)) :
    Nat.card ↥B = 2 ^ (3 * n) * oSL2 n := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), hO2]
  change Nat.card (ModO2 B) * _ = _
  rw [hD.cardQ, show 3 * n = n + 2 * n by ring, pow_add]
  ring

omit [Finite Q] in
theorem block_eq (hD : BarData B n) (hO2 : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ (2 * n)) {d o : ℕ}
    (ho : Odd o) (h : Nat.card ↥B = 2 ^ d * o) : 3 * n = d ∧ oSL2 n = o := by
  have hn := hD.two_le
  exact two_pow_mul_odd_inj (odd_oSL2 (by omega)) ho ((card_block hD hO2).symm.trans h)

omit [Finite Q] in
theorem card_eq_quot_mul {V : Subgroup ↥B} [V.Normal] :
    Nat.card ↥B = Nat.card (↥B ⧸ V) * Nat.card V :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup V

theorem rows_block
    (hD : BarData B n) (hO2 : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ (2 * n)) (h : A312Case B L) :
    A312C2 B L ∨ (n = 2 ∧ (IsSporadic .M22 ↥L ∨
      IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨ IsSporadic .M23 ↥L ∨
      IsSporadic .J4 ↥L)) := by
  have hn := hD.two_le
  have hbe : ∀ {d o : ℕ}, Odd o → Nat.card ↥B = 2 ^ d * o → 3 * n = d ∧ oSL2 n = o :=
    fun ho h => block_eq hD hO2 ho h
  have hext : ∀ {PV PY : ∀ (V : Type) [Group V], Prop}, IsExt ↥B PV PY →
      ∀ {d₁ d₂ o : ℕ}, Odd o → (∀ (V : Type) [Group V], PV V → Nat.card V = 2 ^ d₂) →
        (∀ (Y : Type) [Group Y], PY Y → Nat.card Y = 2 ^ d₁ * o) →
          3 * n = d₁ + d₂ ∧ oSL2 n = o := by
    intro PV PY hB d₁ d₂ o ho hV hY
    obtain ⟨V, hVn, hPV, hPY⟩ := hB
    refine hbe ho ?_
    rw [card_eq_quot_mul (V := V), hY _ hPY, hV _ hPV, pow_add]
    ring
  have hE : ∀ k : ℕ, ∀ (V : Type) [Group V], IsE2 k V → Nat.card V = 2 ^ k :=
    fun k V _ hV => card_isE2 hV
  have hX : ∀ m : ℕ, ∀ (V : Type) [Group V], IsExtraspecial2 m V → Nat.card V = 2 ^ (1 + 2 * m) :=
    fun m V _ hV => card_isExtraspecial2 hV
  rcases h with h | ⟨f, hf, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩ | ⟨hB | hB, -⟩ | (⟨hB, -⟩ | ⟨hB, -⟩) | h |
      h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  ·
    exfalso
    apply not_three_dvd_card_of_isSz hf
    rw [hD.cardQ]
    exact dvd_mul_of_dvd_right (three_dvd_oSL2 n) _
  · exact absurd (hD.oSL2_eq' (d := 3) (by decide)
      (by rw [card_of_isPSL (by norm_num) hB]; decide)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq' (d := 6) (by decide)
      (by rw [card_of_isPSL (by norm_num) hB]; decide)) oSL2_ne_315
  ·
    have := hbe (by decide) (card_alt5 hB)
    omega
  · exact absurd (hbe (by decide) (card_L32 hB)).2 oSL2_ne_21
  · exact absurd (hbe (by decide) (card_alt6 hB)).2 oSL2_ne_45
  · exact absurd (hbe (by decide) (card_hat6 hB)).2 oSL2_ne_135
  ·
    exfalso
    rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
    · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
      rw [card_block hD hO2] at h2
      obtain ⟨rfl, rfl⟩ := eq_five_of_sl2 hp (by omega) hn (b := 3 * n + 1) (by omega)
        (by rw [← h2, pow_succ]; ring)
      norm_num at h2
    · have := hbe (by decide) (card_alt5 hB)
      omega
  ·
    exfalso
    rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · have h2 := card_of_isSL2 hp hB
      rw [card_block hD hO2] at h2
      obtain ⟨rfl, rfl⟩ := eq_five_of_sl2 hp (by omega) hn (b := 3 * n) (by omega) h2.symm
      norm_num at h2
    · exact absurd (hbe (by decide) (card_alt6 hB)).2 oSL2_ne_45
    · exact absurd (hbe (by decide) (card_hat6 hB)).2 oSL2_ne_135
  ·
    exfalso
    obtain ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ := h
    have : NeZero p := ⟨hp.ne_zero⟩
    have hcardV : Nat.card ↥V = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hodd : Odd (Nat.card ↥V) := by
      rw [hcardV]
      exact (hp.odd_of_ne_two (by omega)).pow
    have hbot := hD.odd V hV hodd
    rw [hbot, Subgroup.card_bot] at hcardV
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  · exact absurd (hbe (by decide) (card_alt6 h.1)).2 oSL2_ne_45
  ·
    rcases h with ⟨hB | hB, hL⟩ | ⟨hB | hB, hL⟩
    · have := hext hB (d₁ := 2) (d₂ := 4) (by decide) (hE 4) (fun Y _ hY => card_alt5 hY)
      exact Or.inr ⟨by omega, Or.inl hL⟩
    · exact absurd (hext hB (d₁ := 3) (d₂ := 4) (by decide) (hE 4)
        (fun Y _ hY => card_alt6 hY)).2 oSL2_ne_45
    · have := hext hB (d₁ := 2) (d₂ := 4) (by decide) (hE 4) (fun Y _ hY => card_alt5 hY)
      exact Or.inr ⟨by omega, Or.inr (Or.inl hL)⟩
    · exact absurd (hext hB (d₁ := 3) (d₂ := 4) (by decide) (hE 4)
        (fun Y _ hY => card_hat6 hY)).2 oSL2_ne_135
  ·
    rcases h with ⟨⟨⟨e⟩⟩ | hB | hB | hB | hB | hB | hB, hL⟩
    · exact (hD.false_of_M22 (k := 0) (m := 1) (one_dvd 3)
        (by rw [Nat.card_congr e.toEquiv, pow_zero, one_mul, one_mul]; rfl)).elim
    · exact absurd (hbe (by decide) (card_L34 hB)).2 oSL2_ne_315
    · exact absurd (hext hB (d₁ := 3) (d₂ := 4) (by decide) (hE 4)
        (fun Y _ hY => card_alt7 hY)).2 oSL2_ne_315
    · exact absurd (hext hB (d₁ := 3) (d₂ := 4) (by decide) (hE 4)
        (fun Y _ hY => card_L32 hY)).2 oSL2_ne_21
    · exact absurd (hext hB (d₁ := 3) (d₂ := 3) (by decide) (hE 3)
        (fun Y _ hY => card_L32 hY)).2 oSL2_ne_21
    · exact absurd (hext hB (d₁ := 3) (d₂ := 4) (by decide) (hE 4)
        (fun Y _ hY => card_alt6 hY)).2 oSL2_ne_45
    · have := hext hB (d₁ := 2) (d₂ := 4) (by decide) (hE 4) (fun Y _ hY => card_alt5 hY)
      exact Or.inr ⟨by omega, Or.inr (Or.inr (Or.inl hL))⟩
  ·
    exfalso
    rcases h with ⟨hB | hB | hB | hB, -⟩
    · exact absurd (hext hB (d₁ := 6) (d₂ := 4) (by decide) (hE 4)
        (fun Y _ hY => card_L42 hY)).2 oSL2_ne_315
    · exact absurd (hext hB (d₁ := 3) (d₂ := 6) (by decide) (hE 6)
        (fun Y _ hY => card_L32 hY)).2 oSL2_ne_21
    · exact absurd (hext hB (d₁ := 3) (d₂ := 1 + 2 * 3) (by decide) (hX 3)
        (fun Y _ hY => card_L32 hY)).2 oSL2_ne_21
    · exact absurd (hext hB (d₁ := 3) (d₂ := 6) (by decide) (hE 6)
        (fun Y _ hY => card_hat6 hY)).2 oSL2_ne_135
  · have := hbe (by decide) (card_alt5 h.1)
    omega
  ·
    have := hext h.1 (d₁ := 2) (d₂ := 1 + 2 * 2) (by decide) (hX 2) (fun Y _ hY => card_alt5 hY)
    omega
  ·
    rcases h with ⟨hL, hB | hB | hB | hB | hB | hB⟩
    · exfalso
      obtain ⟨V, hVn, hPV, hPY⟩ := hB
      have h1 := card_eq_quot_mul (V := V)
      have hM : Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 = 443520 :=
        card_of_isSporadic_M22' ⟨MulEquiv.refl _⟩
      rw [card_isExtraspecial2 hPV, card_hatM22 hPY,
        show (1330560 : ℕ) = 3 * Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 from by
          rw [hM]] at h1
      exact hD.false_of_M22 (k := 1 + 2 * 6) (m := 3) dvd_rfl (by rw [h1]; ring)
    · exfalso
      obtain ⟨V, hVn, hPV, ⟨e⟩⟩ := hB
      have h1 := card_eq_quot_mul (V := V)
      rw [card_isE2 hPV, Nat.card_congr e.toEquiv] at h1
      exact hD.false_of_M24 (k := 11) (by rw [h1, mul_comm]; rfl)
    · exact Or.inr ⟨hD.eq_two' (card_alt5 hB), Or.inr (Or.inr (Or.inr hL))⟩
    · exact absurd (hD.oSL2_eq' (by decide) (card_hat6 hB)) oSL2_ne_135
    · exact absurd (hD.oSL2_eq' (by decide) (card_L42 hB)) oSL2_ne_315
    · exact absurd (hD.oSL2_eq' (by decide) (card_L32 hB)) oSL2_ne_21
  ·
    exfalso
    rcases h with ⟨hB | hB, -⟩
    ·
      obtain ⟨V, hVn, hPV, hPY⟩ := hB
      have h1 := card_eq_quot_mul (V := V)
      obtain ⟨k, hk⟩ := (isPGroup_of_isZ4StarExtra2 hPV).exists_card_eq
      obtain ⟨Z, E, -, -, hE5, -, -, -⟩ := hPV
      have hE32 : 2 ^ 5 ≤ Nat.card ↥V := by
        rw [show (2 : ℕ) ^ 5 = 2 ^ (1 + 2 * 2) by norm_num, ← card_isExtraspecial2 hE5]
        exact Subgroup.card_le_card_group E
      rw [Vol2.Ch11.SecA.card_alt5 hPY, hk] at h1
      have h2 := hbe (d := k + 2) (o := 15) (by decide) (by rw [h1, pow_add]; ring)
      have h3 := oSL2_eq_fifteen h2.2
      rw [hk] at hE32
      have : 5 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hE32
      omega
    · exact absurd (hext hB (d₁ := 3) (d₂ := 6) (by decide)
        (fun V _ hV => card_isZ4Cubed hV) (fun Y _ hY => card_L32 hY)).2 oSL2_ne_21
  ·
    exfalso
    rcases h with ⟨hB | hB, -⟩
    · exact absurd (hext hB (d₁ := 3) (d₂ := 1 + 2 * 3) (by decide) (hX 3)
        (fun Y _ hY => card_L32 hY)).2 oSL2_ne_21
    · exact absurd (hext hB (d₁ := 3) (d₂ := 6) (by decide) (hE 6)
        (fun Y _ hY => card_hat6 hY)).2 oSL2_ne_135
  ·
    exfalso
    obtain ⟨-, h11, -⟩ := h
    rw [hO2] at h11
    have := Nat.pow_right_injective (le_refl 2) h11
    omega

omit [Finite Q] in
theorem false_of_surjective_sl2_block [Finite Q] (hD : BarData B n)
    (hO2 : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ (2 * n)) (hsimp : IsSimpleGroup (ModO2 B))
    (hcomm : ⁅CFSG.pCore 2 ↥B, ⊤⁆ = CFSG.pCore 2 ↥B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : ↥B →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hσ : Function.Surjective σ) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := hD.two_le
  set O := CFSG.pCore 2 ↥B with hO
  have hO2g : IsPGroup 2 ↥O := CFSG.pCore_isPGroup
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) :=
    card_of_isSL2 hp ⟨MulEquiv.refl _⟩
  have hp_dvd : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [hcardSL]
    exact dvd_mul_right p _
  have hkO : σ.ker ≤ O := by
    have hN : ((σ.ker).map (QuotientGroup.mk' O)).Normal :=
      (MonoidHom.normal_ker σ).map _ (QuotientGroup.mk'_surjective O)
    have := hsimp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((σ.ker).map (QuotientGroup.mk' O)) with
      hb | ht
    · intro k hk
      have : QuotientGroup.mk' O k = 1 := by
        have h1 : QuotientGroup.mk' O k ∈ (σ.ker).map (QuotientGroup.mk' O) := ⟨k, hk, rfl⟩
        rw [hb] at h1
        exact h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    · exfalso
      have htop : σ.ker ⊔ O = ⊤ := by
        rw [eq_top_iff]
        intro b _
        have h1 : QuotientGroup.mk' O b ∈ (σ.ker).map (QuotientGroup.mk' O) := by
          rw [ht]
          trivial
        obtain ⟨k, hk, hkb⟩ := h1
        have h2 : k⁻¹ * b ∈ O := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          change (QuotientGroup.mk' O k)⁻¹ * QuotientGroup.mk' O b = 1
          rw [hkb, inv_mul_cancel]
        have : b = k * (k⁻¹ * b) := by group
        rw [this]
        exact Subgroup.mul_mem_sup hk h2
      have hrange : O.map σ = ⊤ := by
        rw [← Subgroup.map_top_of_surjective σ hσ, ← htop, Subgroup.map_sup,
          (Subgroup.map_eq_bot_iff _).mpr le_rfl, bot_sup_eq]
      have h2 : IsPGroup 2 ↥(O.map σ) := hO2g.map σ
      rw [hrange] at h2
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      rw [Subgroup.card_top] at hk
      rw [hk] at hp_dvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hp_dvd))
  have hk2 : IsPGroup 2 ↥σ.ker := hO2g.to_le hkO
  obtain ⟨j, hj⟩ := hk2.exists_card_eq
  have hjle : j ≤ 2 * n := by
    have h1 : Nat.card ↥σ.ker ≤ Nat.card ↥O := Subgroup.card_le_of_le hkO
    rw [hj, hO2] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hB := Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hσ).toEquiv, hcardSL, hj,
    card_block hD hO2] at hB
  have hB' : p * (p ^ 2 - 1) = 2 ^ (3 * n - j) * oSL2 n := by
    have h1 : 2 ^ (3 * n) = 2 ^ (3 * n - j) * 2 ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [h1] at hB
    have hpos : 0 < 2 ^ j := Nat.pos_of_ne_zero (by positivity)
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [← hB]; ring)
  obtain ⟨rfl, rfl⟩ := eq_five_of_sl2 hp hp2 hn (b := 3 * n - j) (by omega) hB'
  have hj3 : j = 3 := by
    have h1 : (2 : ℕ) ^ (6 - j) = 8 := by
      have := hB'
      norm_num at this
      omega
    have h2 : 6 - j = 3 := Nat.pow_right_injective (le_refl 2) (show 2 ^ (6 - j) = 2 ^ 3 by rw [h1])
    omega
  have hO16 : Nat.card ↥O = 16 := by rw [hO2]; norm_num
  set σO := σ.comp O.subtype with hσO
  have hrng : σO.range = O.map σ := by rw [hσO, MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerO : Nat.card ↥σO.ker = 8 := by
    have e1 : σO.ker = σ.ker.subgroupOf O := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      rfl
    rw [e1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkO).toEquiv, hj, hj3]
    norm_num
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup σO.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange σO).toEquiv, hrng, hkerO, hO16] at h1
  have hcardO : Nat.card ↥(O.map σ) = 2 := by omega
  have hnorm : (O.map σ).Normal := (CFSG.pCore_normal (p := 2) (G := ↥B)).map σ hσ
  have heq2 : ∀ a ∈ O.map σ, ∀ b ∈ O.map σ, a ≠ 1 → b ≠ 1 → a = b := by
    intro a ha b hb ha1 hb1
    by_contra hab
    classical
    have : Fintype ↥(O.map σ) := Fintype.ofFinite _
    have h3 : ({⟨1, (O.map σ).one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩} : Finset ↥(O.map σ)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · exact fun h => hab (congrArg Subtype.val h)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
          fun h => hb1 (congrArg Subtype.val h).symm⟩
    have h4 := Finset.card_le_univ ({⟨1, (O.map σ).one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩} :
      Finset ↥(O.map σ))
    rw [h3, Fintype.card_eq_nat_card, hcardO] at h4
    omega
  have hle : ⁅O, ⊤⁆ ≤ σ.ker := by
    rw [Subgroup.commutator_le]
    intro o ho b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have hy : σ o ∈ O.map σ := ⟨o, ho, rfl⟩
    have hgy : σ b * σ o * (σ b)⁻¹ ∈ O.map σ := hnorm.conj_mem _ hy _
    by_cases h1 : σ o = 1
    · rw [h1, mul_one, one_mul]
    · have h2 : σ b * σ o * (σ b)⁻¹ ≠ 1 := by
        intro h
        apply h1
        have : σ o = (σ b)⁻¹ * (σ b * σ o * (σ b)⁻¹) * σ b := by group
        rw [this, h]
        group
      have h3 := heq2 _ hgy _ hy h2 h1
      have h4 : σ b * σ o = σ o * σ b := by
        calc σ b * σ o = (σ b * σ o * (σ b)⁻¹) * σ b := by group
          _ = σ o * σ b := by rw [h3]
      exact h4.symm
  rw [hcomm] at hle
  have := Subgroup.card_le_of_le hle
  rw [hO16, hj, hj3] at this
  norm_num at this

omit [Finite Q] in
theorem card_perfectCore_of_classical [Finite Q] {P : Subgroup Q} {f : ℕ} (hf : 2 ≤ f)
    (hL : (IsPSL 3 2 f ↥L ∨ IsSL3 (2 ^ f) ↥L) ∨ IsPSp4 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    ∃ a : ℕ, ((IsPSL 3 2 f ↥L ∨ IsSL3 (2 ^ f) ↥L) → a = 3) ∧ (IsPSp4 2 f ↥L → a = 4) ∧
      Nat.card (CFSG.pCore 2 ↥(perfectCore P)) = 2 ^ ((a - 1) * f) ∧
      Nat.card ↥(perfectCore P) = 2 ^ (a * f) * (2 ^ (2 * f) - 1) := by
  have hP' := isMaxParabolic2_top_subgroupOf hP
  have hPL : P ≤ L := hP.1.1
  have hcore : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPL]
  let e : ↥(perfectCore (P.subgroupOf L)) ≃* ↥(perfectCore P) :=
    ((perfectCore (P.subgroupOf L)).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hcore)
  rcases hL with hL | hL
  · obtain ⟨o, ho, hY⟩ := (Lie2Parabolic.two_part_of_type (Y := ↥L)).1 hL
    have h1 := Lie2Parabolic.card_perfectCore hf (Or.inl hL) hP' ho hY
    refine ⟨3, fun _ => rfl, fun h4 => ?_, ?_, ?_⟩
    · exfalso
      obtain ⟨o', ho', hY'⟩ := (Lie2Parabolic.two_part_of_type (Y := ↥L)).2 h4
      have := (two_pow_mul_odd_inj ho ho' (hY.symm.trans hY')).1
      omega
    · rw [A312.card_pCore_eq e]
      exact h1.1
    · rw [← Nat.card_congr e.toEquiv]
      exact h1.2
  · obtain ⟨o, ho, hY⟩ := (Lie2Parabolic.two_part_of_type (Y := ↥L)).2 hL
    have h1 := Lie2Parabolic.card_perfectCore hf (Or.inr hL) hP' ho hY
    refine ⟨4, fun h3 => ?_, fun _ => rfl, ?_, ?_⟩
    · exfalso
      obtain ⟨o', ho', hY'⟩ := (Lie2Parabolic.two_part_of_type (Y := ↥L)).1 h3
      have := (two_pow_mul_odd_inj ho ho' (hY.symm.trans hY')).1
      omega
    · rw [A312.card_pCore_eq e]
      exact h1.1
    · rw [← Nat.card_congr e.toEquiv]
      exact h1.2

theorem a312C2_block (hExcSq : FactExcParabolicO2NeSq) (hD : BarData B n)
    (hO2 : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ (2 * n)) (h : A312C2 B L) :
    (IsPSL 3 2 n ↥L ∨ IsSL3 (2 ^ n) ↥L) ∧ ∃ P, IsMaxParabolic2 L P ∧ B = perfectCore P := by
  obtain ⟨⟨m, hm⟩, hrk, P, hP, rfl⟩ := h
  obtain ⟨hm1, hcm⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two hm
  have hn := hD.two_le
  obtain ⟨rfl, -⟩ := two_pow_mul_odd_inj (odd_oSL2 hm1) (odd_oSL2 (m := n) (by omega))
    (hcm.symm.trans hD.cardQ)
  have hcB := card_block hD hO2
  have h168 : Nat.card ↥L = 168 → False := fun hL => by
    have hdvd : 2 ^ (3 * m) * oSL2 m ∣ 168 := by
      rw [← hcB, ← hL]
      exact Subgroup.card_dvd_of_le ((CFSG.Quasithin.perfectCore_le P).trans hP.1.1)
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have h64 : 64 ≤ 2 ^ (3 * m) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h15 : 15 ≤ oSL2 m := by
      have : 16 ≤ 2 ^ (2 * m) := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [oSL2]
      omega
    have := Nat.mul_le_mul h64 h15
    omega
  have hfm : ∀ {f a : ℕ}, Nat.card ↥(perfectCore P) = 2 ^ (a * f) * (2 ^ (2 * f) - 1) →
      1 ≤ f → f = m ∧ a * f = 3 * m := by
    intro f a h1 hf1
    have h2 := two_pow_mul_odd_inj (odd_oSL2 hf1) (odd_oSL2 (m := m) hm1) (h1.symm.trans hcB)
    have h3 : f = m := by
      rcases lt_trichotomy f m with hlt | heq | hgt
      · exact absurd h2.2 (oSL2_lt_oSL2 hlt).ne
      · exact heq
      · exact absurd h2.2 (oSL2_lt_oSL2 hgt).ne'
    exact ⟨h3, h2.1⟩
  rcases hrk with ⟨f, ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hf3, hL⟩⟩ | hT
  · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · exact (h168 ((card_L32 hL).trans (by norm_num))).elim
    · obtain ⟨a, ha3, -, -, hcard⟩ := card_perfectCore_of_classical hf2 (Or.inl (Or.inl hL)) hP
      obtain ⟨rfl, -⟩ := hfm hcard (by omega)
      exact ⟨Or.inl hL, P, hP, rfl⟩
  · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
      exact (h168 (by rw [Nat.card_congr e.toEquiv, card_sl3, hK]; norm_num)).elim
    · obtain ⟨a, -, -, -, hcard⟩ := card_perfectCore_of_classical hf2 (Or.inl (Or.inr hL)) hP
      obtain ⟨rfl, -⟩ := hfm hcard (by omega)
      exact ⟨Or.inr hL, P, hP, rfl⟩
  · exfalso
    obtain ⟨a, -, ha4, -, hcard⟩ := card_perfectCore_of_classical hf (Or.inr hL) hP
    obtain ⟨rfl, h2⟩ := hfm hcard (by omega)
    rw [ha4 hL] at h2
    omega
  · exact (hExcSq Q L P m (by omega) (Or.inl ⟨f, Or.inl ⟨hf, hL⟩⟩) hP hm
      (by rw [hO2]; ring)).elim
  · exact (hExcSq Q L P m (by omega) (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hL⟩)⟩) hP hm
      (by rw [hO2]; ring)).elim
  · exact (hExcSq Q L P m (by omega) (Or.inl ⟨f, Or.inr (Or.inr ⟨hf, hf3, hL⟩)⟩) hP hm
      (by rw [hO2]; ring)).elim
  · exact (hExcSq Q L P m (by omega) (Or.inr hT) hP hm (by rw [hO2]; ring)).elim

omit [Finite Q] in
theorem false_of_a312Nonquasi_of_block [Finite Q] (hD : BarData B n)
    (hO2 : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ (2 * n)) (hsimp : IsSimpleGroup (ModO2 B))
    (hcomm : ⁅CFSG.pCore 2 ↥B, ⊤⁆ = CFSG.pCore 2 ↥B) (hBL : B ≤ L) (h : A312Nonquasi B L) :
    False := by
  unfold A312Nonquasi at h
  rcases h with ⟨-, hLeq, p, hp, hp2, hSL⟩ | ⟨-, -, N, hNn, hN, hSL⟩
  · obtain ⟨e⟩ : Nonempty (↥L ⧸ CFSG.oddCore ↥L ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := hSL
    set τ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥L)) with hτ
    have hτs : Function.Surjective τ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hOL : (CFSG.oddCore ↥L).map L.subtype ≤ L := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hsup : B.subgroupOf L ⊔ CFSG.oddCore ↥L = ⊤ := by
      have h1 : (B ⊔ (CFSG.oddCore ↥L).map L.subtype).subgroupOf L = ⊤ := by
        rw [← hLeq]
        exact Subgroup.subgroupOf_self L
      rw [Subgroup.subgroupOf_sup hBL hOL] at h1
      have h2 : ((CFSG.oddCore ↥L).map L.subtype).subgroupOf L = CFSG.oddCore ↥L :=
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
      rwa [h2] at h1
    have hker : CFSG.oddCore ↥L ≤ τ.ker := fun x hx => by
      rw [MonoidHom.mem_ker, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff x).mpr hx, map_one]
    have hτB := surjective_comp_subtype_of_sup τ hτs hsup hker
    exact false_of_surjective_sl2_block hD hO2 hsimp hcomm hp hp2
      ((τ.comp (B.subgroupOf L).subtype).comp (Subgroup.subgroupOfEquivOfLe hBL).symm.toMonoidHom)
      (hτB.comp (Subgroup.subgroupOfEquivOfLe hBL).symm.surjective)
  · have := hNn
    obtain ⟨e⟩ : Nonempty (↥(B ⊔ (CFSG.oddCore ↥L).map L.subtype) ⧸ N ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := hSL
    set τ : ↥(B ⊔ (CFSG.oddCore ↥L).map L.subtype) →*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
      e.toMonoidHom.comp (QuotientGroup.mk' N) with hτ
    have hτs : Function.Surjective τ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hsup : B.subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype) ⊔ N = ⊤ := by
      rw [hN, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have hker : N ≤ τ.ker := fun x hx => by
      rw [MonoidHom.mem_ker, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff x).mpr hx, map_one]
    have hτB := surjective_comp_subtype_of_sup τ hτs hsup hker
    have hle : B ≤ B ⊔ (CFSG.oddCore ↥L).map L.subtype := le_sup_left
    exact false_of_surjective_sl2_block hD hO2 hsimp hcomm Nat.prime_five (by norm_num)
      ((τ.comp (B.subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype)).subtype).comp
        (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (hτB.comp (Subgroup.subgroupOfEquivOfLe hle).symm.surjective)

end Rows

end CFSG.Quasithin.H13
