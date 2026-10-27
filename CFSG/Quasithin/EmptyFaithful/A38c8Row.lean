module

public import CFSG.Quasithin.Background.A3Structure312Defs
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.B69Iso
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.A38c8

open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)

section Orders

variable {X : Type} [Group X]

private theorem card_of_isAlt {k : ℕ} (hk : 2 ≤ k) (h : IsAlt k X) :
    Nat.card X = Nat.factorial k / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

private theorem card_of_isHat {S : Type} [Group S] (h : IsHat X S) :
    Nat.card X = Nat.card S * 3 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, h3, Nat.card_congr e.toEquiv]

private theorem card_of_isPSL {k p e : ℕ} (hk : 0 < k) (h : IsPSL k p e X) :
    Nat.card X = ((p ^ e) ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 2 k, ((p ^ e) ^ i - 1)) /
      k.gcd (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl hk h

private theorem card_of_isSL2 {p : ℕ} (hp : p.Prime) (h : IsSL2 p X) :
    Nat.card X = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.OrderReductions.LinearOrders.card_specialLinear (ZMod p) 2 (by norm_num),
    Nat.card_zmod]
  simp

private theorem not_three_dvd_card_of_isSz {f : ℕ} (h : IsSz f X) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  have h2 : (2 ^ (2 * a + 1)) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at h2 ⊢
  intro h3
  have hq1 : 1 ≤ q := by omega
  have h1 : (((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ZMod 3)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h3
  have h2' : (q : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, h2]
    rfl
  push_cast [Nat.cast_sub hq1] at h1
  rw [h2'] at h1
  exact absurd h1 (by decide)

private theorem odd_two_pow_sub_one {e : ℕ} (he : 1 ≤ e) : Odd (2 ^ e - 1) := by
  have h2 : Even (2 ^ e) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) h2 odd_one

private theorem eleven_dvd_card_M22 : 11 ∣ Nat.card ↥NativeSporadic.M22 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg, hg11, hg1⟩ : ∃ g ∈ NativeSporadic.M22, g ^ 11 = 1 ∧ g ≠ 1 := by
    refine ⟨_, Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  have ho : orderOf (⟨g, hg⟩ : ↥NativeSporadic.M22) = 11 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hg11 hg1
  rw [← ho]
  exact orderOf_dvd_natCard _

private theorem card_isE2 {k : ℕ} (h : IsE2 k X) : Nat.card X = 2 ^ k := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin k → ZMod 2) = 2 ^ k
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem card_isZ4Cubed (h : IsZ4Cubed X) : Nat.card X = 2 ^ 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 3 → ZMod 4) = 2 ^ 6
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

private theorem card_isZ4StarExtra2 [Finite X] (h : IsZ4StarExtra2 X) :
    ∃ k, Nat.card X = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, E, hZ, -, hE, hZc, hZE, -⟩ := h
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hp : IsPGroup 2 ↥(Z ⊔ E) :=
    IsPGroup.to_sup_of_normal_left (IsPGroup.of_card (n := 2) (by rw [hZ]; norm_num))
      (IsPGroup.of_card hE.2)
  rw [hZE] at hp
  exact IsPGroup.iff_card.mp (hp.of_equiv Subgroup.topEquiv)

private theorem card_alt5 (h : IsAlt 5 X) : Nat.card X = 60 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

private theorem card_alt6 (h : IsAlt 6 X) : Nat.card X = 360 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

private theorem card_alt7 (h : IsAlt 7 X) : Nat.card X = 2520 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

private theorem card_hat6 (h : IsHat X (alternatingGroup (Fin 6))) : Nat.card X = 1080 := by
  rw [card_of_isHat h, nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem card_L32 (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

private theorem card_L42 (h : IsPSL 4 2 1 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

private theorem card_L34 (h : IsPSL 3 2 2 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

private theorem two_mul_card_of_isPSL_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSL 2 p 1 X) :
    2 * Nat.card X = p * (p ^ 2 - 1) :=
  CFSG.Open.StatedAPI.two_mul_card_of_statedClassicalModel_psl_two_prime hp hp2 h

private theorem false_of_isPSL_two_two {m : ℕ} (h : IsPSL 2 2 m X) (hc : Nat.card X = 20160) : False := by
  have hm : 1 ≤ m := h.1.2.1
  have hform := card_of_isPSL (by norm_num) h
  have hg : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hm)
  rw [hg, Nat.div_one] at hform
  simp only [pow_one, show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self,
    Finset.prod_singleton] at hform
  rw [hc] at hform
  rcases Nat.lt_or_ge m 5 with hlt | hge
  · interval_cases m <;> omega
  · have h5 : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have : 32 * 1023 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      refine Nat.mul_le_mul (by simpa using h5) ?_
      have : 32 ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left (by simpa using h5) 2
      omega
    omega

end Orders

structure L42Data {Q : Type} [Group Q] (B : Subgroup Q) : Prop where
  card : ∃ a, Nat.card ↥(CFSG.pCore 2 ↥B) = 2 ^ a ∧ Nat.card ↥B = 2 ^ a * (2 ^ 6 * 315)
  psl : IsPSL 4 2 1 (ModO2 B)
  odd : ∀ N : Subgroup ↥B, N.Normal → Odd (Nat.card ↥N) → N = ⊥

theorem l42Data_of {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q}
    (h : IsPSL 4 2 1 (ModO2 B)) : L42Data B where
  card := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
    refine ⟨a, ha, ?_⟩
    rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, card_L42 h, ha, mul_comm]
    norm_num
  psl := h
  odd := fun N hN hodd => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hs : IsSimpleGroup (ModO2 B) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 h).2
    have hNn : (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B))).Normal :=
      Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B))) with hbot | htop
    · have hle : N ≤ CFSG.pCore 2 ↥B := by
        intro x hx
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥B) x ∈
            N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B)) := ⟨x, hx, rfl⟩
        rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      obtain ⟨k, hk⟩ :=
        IsPGroup.iff_card.mp ((CFSG.pCore_isPGroup (p := 2) (G := ↥B)).to_le hle)
      rw [hk] at hodd
      have hk0 : k = 0 := by
        by_contra hk0
        exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
      rw [hk0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    · exfalso
      have h1 := Subgroup.card_map_dvd (H := N) (QuotientGroup.mk' (CFSG.pCore 2 ↥B))
      rw [htop, Subgroup.card_top, card_L42 h] at h1
      have h2 : 2 ∣ Nat.card ↥N := dvd_trans (by norm_num) h1
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

section Data

variable {Q : Type} [Group Q] {B : Subgroup Q}

theorem L42Data.le_card (hD : L42Data B) : 2 ^ 6 * 315 ≤ Nat.card ↥B := by
  obtain ⟨a, -, ha⟩ := hD.card
  rw [ha]
  exact Nat.le_mul_of_pos_left _ (by positivity)

theorem L42Data.not_prime_dvd (hD : L42Data B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp315 : ¬ p ∣ 315) : ¬ p ∣ Nat.card ↥B := by
  obtain ⟨a, -, ha⟩ := hD.card
  rw [ha, ← mul_assoc, ← pow_add]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  · exact hp315 h1

theorem L42Data.false_of_prime_dvd_card (hD : L42Data B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpB : p ∣ Nat.card ↥B) (hsmall : p = 3 ∨ p = 5 ∨ p = 7 → False) : False := by
  by_cases h315 : p ∣ 315
  · have h' : p ∣ 3 * (3 * (5 * 7)) := by norm_num; exact h315
    rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h'
    · exact hsmall (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3))
    rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h'
    · exact hsmall (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3))
    rcases (Nat.Prime.dvd_mul hp).mp h' with h5 | h7
    · exact hsmall (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5)))
    · exact hsmall (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7)))
  · exact hD.not_prime_dvd hp hp2 h315 hpB

theorem L42Data.false_of_lt (hD : L42Data B) (h : Nat.card ↥B < 2 ^ 6 * 315) : False :=
  absurd hD.le_card (not_le.mpr h)

end Data

section Ext

variable {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q}

theorem L42Data.ext (hD : L42Data B) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k) :
    ∃ (V : Subgroup ↥B) (_ : V.Normal), PY (↥B ⧸ V) ∧ V ≤ CFSG.pCore 2 ↥B ∧
      2 ^ 6 * 315 ≤ Nat.card (↥B ⧸ V) := by
  obtain ⟨V, hVn, hPV', hPY⟩ := h
  obtain ⟨k, hk⟩ := hPV _ hPV'
  have hVp : IsPGroup 2 ↥V := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card hk
  have hVO : V ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hVn, hVp⟩
  refine ⟨V, hVn, hPY, hVO, ?_⟩
  have h1 := V.card_eq_card_quotient_mul_card_subgroup
  have h2 := (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
  rw [card_L42 hD.psl] at h2
  have h3 : Nat.card ↥V ≤ Nat.card ↥(CFSG.pCore 2 ↥B) := Subgroup.card_le_of_le hVO
  have h4 : 0 < Nat.card ↥V := Nat.card_pos
  by_contra hlt
  have hlt' : Nat.card (↥B ⧸ V) < 2 ^ 6 * 315 := lt_of_not_ge hlt
  have : Nat.card (↥B ⧸ V) * Nat.card ↥V < 2 ^ 6 * 315 * Nat.card ↥(CFSG.pCore 2 ↥B) :=
    calc Nat.card (↥B ⧸ V) * Nat.card ↥V < 2 ^ 6 * 315 * Nat.card ↥V :=
          Nat.mul_lt_mul_of_pos_right hlt' h4
      _ ≤ 2 ^ 6 * 315 * Nat.card ↥(CFSG.pCore 2 ↥B) := Nat.mul_le_mul_left _ h3
  omega

theorem L42Data.false_of_ext_lt (hD : L42Data B) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k)
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y < 2 ^ 6 * 315) : False := by
  obtain ⟨V, _, hPY, -, hge⟩ := hD.ext h hPV
  exact absurd hge (not_le.mpr (hY _ hPY))

end Ext

section Rows

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

omit [Finite Q] in
theorem L42Data.false_C2_C11 (hD : L42Data B)
    (h : A312C2 B L ∨ A312C3 B L ∨ A312C4 B L ∨ A312C6 B L ∨ A312C7 B L ∨ A312C8 B L ∨
      A312C9 B L ∨ A312C10 B L ∨ A312C11 B L) : False := by
  have h3 : Nat.card (ModO2 B) = 20160 := card_L42 hD.psl
  rcases h with ⟨⟨m, hm⟩, -⟩ | ⟨f, hf, -⟩ | ⟨hB, -⟩ | ⟨hB | hB, -⟩ |
      (⟨hB, -⟩ | ⟨hB, -⟩) | (⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩) |
      (⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩) | ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ | ⟨hB, -⟩
  · exact false_of_isPSL_two_two hm h3
  · exact not_three_dvd_card_of_isSz hf (by rw [h3]; norm_num)
  · rw [card_L32 hB] at h3
    norm_num at h3
  · exact hD.false_of_lt (by rw [card_alt5 hB]; norm_num)
  · exact hD.false_of_lt (by rw [card_L32 hB]; norm_num)
  · exact hD.false_of_lt (by rw [card_alt6 hB]; norm_num)
  · exact hD.false_of_lt (by rw [card_hat6 hB]; norm_num)
  · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
    have hpB : p ∣ Nat.card ↥B := by
      have h1 : p ∣ 2 * Nat.card ↥B := h2 ▸ dvd_mul_right p _
      exact ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)).dvd_of_dvd_mul_left h1
    refine hD.false_of_prime_dvd_card hp (by omega) hpB fun hp' => ?_
    have hle := hD.le_card
    rcases hp' with rfl | rfl | rfl <;> omega
  · exact hD.false_of_lt (by rw [card_alt5 hB]; norm_num)
  · have h2 := card_of_isSL2 hp hB
    have hpB : p ∣ Nat.card ↥B := h2 ▸ dvd_mul_right p _
    refine hD.false_of_prime_dvd_card hp (by omega) hpB fun hp' => ?_
    have hle := hD.le_card
    rcases hp' with rfl | rfl | rfl <;> omega
  · exact hD.false_of_lt (by rw [card_alt6 hB]; norm_num)
  · exact hD.false_of_lt (by rw [card_hat6 hB]; norm_num)
  · have : NeZero p := ⟨hp.ne_zero⟩
    have hcard : Nat.card ↥V = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hodd : Odd (Nat.card ↥V) := by
      rw [hcard]
      exact (hp.odd_of_ne_two (by omega)).pow
    have hbot := hD.odd V hV hodd
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  · exact hD.false_of_lt (by rw [card_alt6 hB]; norm_num)

omit [Finite Q] in
theorem L42Data.false_of_psl34 (hD : L42Data B) (hB : IsPSL 3 2 2 ↥B) : False := by
  obtain ⟨a, ha1, ha2⟩ := hD.card
  have h1 : Nat.card ↥B = 20160 := card_L34 hB
  have h2 : 2 ^ a = 1 := by
    rw [h1] at ha2
    have h3 : 0 < 2 ^ a := by positivity
    omega
  have hbot : CFSG.pCore 2 ↥B = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [ha1, h2])
  have e : ↥B ≃* ModO2 B :=
    (QuotientGroup.quotientBot (G := ↥B)).symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  obtain ⟨-, K3, _, _, hK3, ⟨e3⟩⟩ := hB
  obtain ⟨-, K4, _, _, hK4, ⟨e4⟩⟩ := hD.psl
  exact B69.not_equiv_sl_four_psl_three (K := K4) (F := K3) (by rw [hK4]; norm_num)
    (by rw [hK3]; norm_num) (e.trans e4) e3

theorem L42Data.of_C12_C20 (hD : L42Data B)
    (h : A312C12 B L ∨ A312C13 B L ∨ A312C14 B L ∨ A312C15 B L ∨ A312C16 B L ∨ A312C17 B L ∨
      A312C18 B L ∨ A312C19 B L ∨ A312C20 B L) :
    (IsExt ↥B (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 4 2 1 Y') ∧ IsSporadic .M24 ↥L) ∨
      IsSporadic .J4 ↥L := by
  have hE : ∀ m, ∀ (V : Type) [Group V] [Finite V], IsE2 m V → ∃ k, Nat.card V = 2 ^ k :=
    fun m V _ _ hV => ⟨m, card_isE2 hV⟩
  have hX : ∀ (V : Type) [Group V] [Finite V], ∀ {m : ℕ}, IsExtraspecial2 m V →
      ∃ k, Nat.card V = 2 ^ k := fun V _ _ _ hV => ⟨_, hV.2⟩
  have h3 : Nat.card (ModO2 B) = 20160 := card_L42 hD.psl
  rcases h with (⟨hB | hB, -⟩ | ⟨hB | hB, -⟩) | h | h | ⟨hB, -⟩ | ⟨hB, -⟩ | h | ⟨hB | hB, -⟩ |
      ⟨hB | hB, -⟩ | ⟨hB | hB, -, -⟩
  · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt6 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_hat6 hY]; norm_num).elim
  · obtain ⟨hB | hB | hB | hB | hB | hB | hB, hL⟩ := h
    · obtain ⟨e⟩ := hB
      exact (hD.not_prime_dvd (p := 11) (by norm_num) (by norm_num) (by norm_num)
        (by rw [Nat.card_congr e.toEquiv]; exact eleven_dvd_card_M22)).elim
    · exact (hD.false_of_psl34 hB).elim
    · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt7 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 3) fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt6 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · obtain ⟨hB | hB | hB | hB, hL⟩ := h
    · exact Or.inl ⟨hB, hL⟩
    · exact (hD.false_of_ext_lt hB (hE 6) fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (fun V _ _ hV => hX V hV)
        fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 6) fun Y _ hY => by rw [card_hat6 hY]; norm_num).elim
  · exact (hD.false_of_lt (by rw [card_alt5 hB]; norm_num)).elim
  · exact (hD.false_of_ext_lt hB (fun V _ _ hV => hX V hV)
      fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · exact Or.inr h.1
  · exact (hD.false_of_ext_lt hB (fun V _ _ hV => card_isZ4StarExtra2 hV)
      fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (fun V _ _ hV => ⟨6, card_isZ4Cubed hV⟩)
      fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (fun V _ _ hV => hX V hV)
      fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (hE 6) fun Y _ hY => by rw [card_hat6 hY]; norm_num).elim
  · rw [card_alt5 hB] at h3
    norm_num at h3
  · rw [card_L32 hB] at h3
    norm_num at h3

omit [Finite Q] in
private theorem relIndex_sup_eq_of_le_normalizer {A D : Subgroup Q}
    (h : A ≤ Subgroup.normalizer (D : Set Q)) : D.relIndex (A ⊔ D) = D.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A D h).toEquiv.symm

omit [Finite Q] in
theorem L42Data.card_sup_eq (hD : L42Data B) {O : Subgroup Q}
    (hBO : B ≤ Subgroup.normalizer (O : Set Q)) (hO : Odd (Nat.card ↥O)) :
    Nat.card ↥(B ⊔ O) = Nat.card ↥B * Nat.card ↥O := by
  have hN : (O.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
    exact fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨hBO hb, Subgroup.le_normalizer hb⟩
  have hc : Nat.card ↥(O.subgroupOf B) = Nat.card ↥(O ⊓ B) := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hodd : Odd (Nat.card ↥(O.subgroupOf B)) := by
    rw [hc]
    exact hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hbot := hD.odd _ hN hodd
  have hOB : O ⊓ B = ⊥ := by
    rw [← Subgroup.subgroupOf_map_subtype, hbot, Subgroup.map_bot]
  have h2 := Subgroup.relIndex_mul_card O B
  rw [hOB, Subgroup.card_bot, mul_one] at h2
  have h3 := Subgroup.relIndex_mul_card O (B ⊔ O)
  rw [relIndex_sup_eq_of_le_normalizer hBO, h2, inf_eq_left.mpr le_sup_right] at h3
  exact h3.symm

theorem L42Data.false_of_nonquasi (hD : L42Data B) (hBL : B ≤ L) (h : A312Nonquasi B L) :
    False := by
  have hOLL : (CFSG.oddCore ↥L).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hLO :
      L ≤ Subgroup.normalizer (((CFSG.oddCore ↥L).map L.subtype : Subgroup Q) : Set Q) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOLL).mp ?_
    have he : ((CFSG.oddCore ↥L).map L.subtype).subgroupOf L = CFSG.oddCore ↥L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [he]
    infer_instance
  have hOcard : Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) = Nat.card ↥(CFSG.oddCore ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hOodd : Odd (Nat.card ↥((CFSG.oddCore ↥L).map L.subtype)) := by
    rw [hOcard]
    exact A37.odd_card_oddCore _
  have h1 := hD.card_sup_eq (hBL.trans hLO) hOodd
  have hpos : 0 < Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) := Nat.card_pos
  have hle := hD.le_card
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, hNeq, hN5⟩
  · rw [← hLB] at h1
    have h2 := (CFSG.oddCore ↥L).card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 hp hSL, ← hOcard] at h2
    have hB : Nat.card ↥B = p * (p ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    refine hD.false_of_prime_dvd_card hp hp2 (hB ▸ dvd_mul_right p _) fun hp' => ?_
    rcases hp' with rfl | rfl | rfl <;> omega
  · have h2 := N.card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 (by norm_num) hN5] at h2
    have h3 : Nat.card ↥N = Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) := by
      rw [hNeq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [h3] at h2
    have hB : Nat.card ↥B = 5 * (5 ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    omega

theorem L42Data.of_a312Case (hD : L42Data B) (h : A312Case B L) :
    IsPSL 5 2 1 ↥L ∨
      (IsExt ↥B (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 4 2 1 Y') ∧ IsSporadic .M24 ↥L) ∨
      IsSporadic .J4 ↥L := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (hD.false_C2_C11 (Or.inl h)).elim
  · exact (hD.false_C2_C11 (Or.inr (Or.inl h))).elim
  · exact (hD.false_C2_C11 (Or.inr (Or.inr (Or.inl h)))).elim
  · exact Or.inl h.2.1
  · exact (hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inl h))))).elim
  · exact (hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).elim
  · exact (hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).elim
  · exact (hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).elim
  · exact (hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))).elim
  · exact (hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))).elim
  · exact Or.inr (hD.of_C12_C20 (Or.inl h))
  · exact Or.inr (hD.of_C12_C20 (Or.inr (Or.inl h)))
  · exact Or.inr (hD.of_C12_C20 (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (hD.of_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (hD.of_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (hD.of_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (hD.of_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (hD.of_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  · exact Or.inr (hD.of_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))

end Rows

theorem row_of_a312 {Y : Type} [Group Y] [Finite Y] {B N : Subgroup Y}
    (hBN : B ≤ N) (h4 : IsPSL 4 2 1 (ModO2 B)) (h : A312Case B N ∨ A312Nonquasi B N) :
    IsPSL 5 2 1 ↥N ∨
      (IsExt ↥B (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 4 2 1 Y') ∧ IsSporadic .M24 ↥N) ∨
      IsSporadic .J4 ↥N := by
  have hD := l42Data_of h4
  rcases h with h | h
  · exact hD.of_a312Case h
  · exact (hD.false_of_nonquasi hBN h).elim

end CFSG.Quasithin.A38c8
