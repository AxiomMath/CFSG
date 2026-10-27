module

public import CFSG.Quasithin.Background.A3Structure312Defs
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.LieType.Simplicity.Classical
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Stellmacher.CD.L3YC.L32

open CFSG.Quasithin CFSG.Blueprint
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

theorem card_of_isPSL {k p e : ℕ} (hk : 0 < k) (h : IsPSL k p e X) :
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

private theorem five_dvd_card_of_isSz {f : ℕ} (h : IsSz f X) :
    5 ∣ Nat.card X := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  have h2 : ((2 ^ (2 * a + 1)) ^ 2) % 5 = 4 := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 4 * a + 2 by ring, pow_add, pow_mul, Nat.mul_mod,
      Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at h2 ⊢
  have h5 : 5 ∣ q ^ 2 + 1 := by omega
  exact Dvd.dvd.mul_left h5 _

private theorem false_of_isPSL_two_two {m : ℕ} (h : IsPSL 2 2 m X) (hc : Nat.card X = 168) :
    False := by
  have hm : 1 ≤ m := h.1.2.1
  have hform := card_of_isPSL (by norm_num) h
  have hg : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hm)
  rw [hg, Nat.div_one] at hform
  simp only [pow_one, show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self,
    Finset.prod_singleton] at hform
  rw [hc] at hform
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · interval_cases m <;> omega
  · have h5 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have : 8 * 63 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      refine Nat.mul_le_mul (by simpa using h5) ?_
      have : 8 ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left (by simpa using h5) 2
      omega
    omega

end Orders

structure L32Data {Q : Type} [Group Q] (B : Subgroup Q) : Prop where
  card : ∃ a, Nat.card ↥(CFSG.pCore 2 ↥B) = 2 ^ a ∧ Nat.card ↥B = 2 ^ a * 168
  psl : IsPSL 3 2 1 (ModO2 B)
  odd : ∀ N : Subgroup ↥B, N.Normal → Odd (Nat.card ↥N) → N = ⊥

theorem l32Data_of {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q}
    (h : IsPSL 3 2 1 (ModO2 B)) : L32Data B where
  card := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
    refine ⟨a, ha, ?_⟩
    rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, card_L32 h, ha, mul_comm]
  psl := h
  odd := fun N hN hodd => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hs : IsSimpleGroup (ModO2 B) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 h).2
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
      rw [htop, Subgroup.card_top, card_L32 h] at h1
      have h2 : 2 ∣ Nat.card ↥N := dvd_trans (by norm_num) h1
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

section Data

variable {Q : Type} [Group Q] {B : Subgroup Q}

theorem L32Data.le_card (hD : L32Data B) : 168 ≤ Nat.card ↥B := by
  obtain ⟨a, -, ha⟩ := hD.card
  rw [ha]
  exact Nat.le_mul_of_pos_left _ (by positivity)

theorem L32Data.not_prime_dvd (hD : L32Data B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp168 : ¬ p ∣ 168) : ¬ p ∣ Nat.card ↥B := by
  obtain ⟨a, -, ha⟩ := hD.card
  rw [ha]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  · exact hp168 h1

theorem L32Data.false_of_prime_dvd_card (hD : L32Data B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpB : p ∣ Nat.card ↥B) (hsmall : p = 3 ∨ p = 7 → False) : False := by
  by_cases h168 : p ∣ 168
  · have h' : p ∣ 2 * (2 * (2 * (3 * 7))) := by norm_num; exact h168
    rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h'
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
    rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h'
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
    rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h'
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
    rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h7
    · exact hsmall (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3))
    · exact hsmall (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7))
  · exact hD.not_prime_dvd hp hp2 h168 hpB

theorem L32Data.not_five_dvd (hD : L32Data B) : ¬ 5 ∣ Nat.card ↥B :=
  hD.not_prime_dvd (by norm_num) (by norm_num) (by norm_num)

theorem L32Data.not_eleven_dvd (hD : L32Data B) : ¬ 11 ∣ Nat.card ↥B :=
  hD.not_prime_dvd (by norm_num) (by norm_num) (by norm_num)

theorem card_quotient_dvd_of_isExt {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt ↥B PV PY) :
    ∃ Y : Type, ∃ _ : Group Y, PY Y ∧ Nat.card Y ∣ Nat.card ↥B := by
  obtain ⟨V, hVn, -, hPY⟩ := h
  exact ⟨_, inferInstance, hPY, V.card_quotient_dvd_card⟩

theorem L32Data.false_of_ext_prime (hD : L32Data B) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    (hY : ∀ (Y : Type) [Group Y], PY Y → p ∣ Nat.card Y) : False := by
  obtain ⟨Y, _, hPY, hdvd⟩ := card_quotient_dvd_of_isExt h
  exact hD.false_of_prime_dvd_card hp hp2 ((hY Y hPY).trans hdvd)
    fun h' => by rcases h' with h' | h' <;> omega

end Data

section Rows

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

private theorem five_dvd_alt5 {X : Type} [Group X] (h : IsAlt 5 X) : 5 ∣ Nat.card X := by
  rw [card_alt5 h]; norm_num
private theorem five_dvd_alt6 {X : Type} [Group X] (h : IsAlt 6 X) : 5 ∣ Nat.card X := by
  rw [card_alt6 h]; norm_num
private theorem five_dvd_alt7 {X : Type} [Group X] (h : IsAlt 7 X) : 5 ∣ Nat.card X := by
  rw [card_alt7 h]; norm_num
private theorem five_dvd_hat6 {X : Type} [Group X] (h : IsHat X (alternatingGroup (Fin 6))) : 5 ∣ Nat.card X := by
  rw [card_hat6 h]; norm_num
private theorem five_dvd_L42 {X : Type} [Group X] (h : IsPSL 4 2 1 X) : 5 ∣ Nat.card X := by
  rw [card_L42 h]; norm_num
private theorem five_dvd_L34 {X : Type} [Group X] (h : IsPSL 3 2 2 X) : 5 ∣ Nat.card X := by
  rw [card_L34 h]; norm_num

omit [Finite Q] in
theorem L32Data.false_of_bad (hD : L32Data B)
    (h : A312C2 B L ∨ A312C3 B L ∨ A312C5 B L ∨ A312C7 B L ∨ A312C10 B L ∨ A312C11 B L ∨
      A312C12 B L ∨ A312C15 B L ∨ A312C16 B L) : False := by
  have h3 : Nat.card (ModO2 B) = 168 := card_L32 hD.psl
  rcases h with ⟨⟨m, hm⟩, -⟩ | ⟨f, hf, -⟩ | ⟨hB, -⟩ | (⟨hB, -⟩ | ⟨hB, -⟩) |
      ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ | ⟨hB, -⟩ |
      ((⟨hB | hB, -⟩ | ⟨hB | hB, -⟩)) | ⟨hB, -⟩ | ⟨hB, -⟩
  · exact false_of_isPSL_two_two hm h3
  · have := five_dvd_card_of_isSz hf
    rw [h3] at this
    norm_num at this
  · have := card_L42 hB
    omega
  · exact hD.not_five_dvd (five_dvd_alt6 hB)
  · exact hD.not_five_dvd (five_dvd_hat6 hB)
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
  · exact hD.not_five_dvd (five_dvd_alt6 hB)
  · exact hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun Y _ hY => five_dvd_alt5 hY
  · exact hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun Y _ hY => five_dvd_alt6 hY
  · exact hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun Y _ hY => five_dvd_alt5 hY
  · exact hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun Y _ hY => five_dvd_hat6 hY
  · exact hD.not_five_dvd (five_dvd_alt5 hB)
  · exact hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun Y _ hY => five_dvd_alt5 hY

omit [Finite Q] in
theorem L32Data.of_C6 (hD : L32Data B) (h : A312C6 B L) :
    IsPSL 3 2 1 ↥B ∧ (IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7))) := by
  obtain ⟨hB | hB, hL⟩ := h
  · exact (hD.not_five_dvd (five_dvd_alt5 hB)).elim
  · exact ⟨hB, hL⟩

omit [Finite Q] in
theorem L32Data.of_C8 (hD : L32Data B) (h : A312C8 B L) : IsPSL 2 7 1 ↥B ∧ IsPSL 2 7 2 ↥L := by
  rcases h with ⟨p, hp, hp3, hB, hL⟩ | ⟨hB, -⟩
  · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
    have hpB : p ∣ Nat.card ↥B := by
      have h1 : p ∣ 2 * Nat.card ↥B := h2 ▸ dvd_mul_right p _
      exact ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)).dvd_of_dvd_mul_left h1
    have hp7 : p = 7 := by
      by_contra hne
      exact hD.false_of_prime_dvd_card hp (by omega) hpB fun hp' => by
        rcases hp' with h' | h' <;> omega
    subst hp7
    exact ⟨hB, hL⟩
  · exact (hD.not_five_dvd (five_dvd_alt5 hB)).elim

omit [Finite Q] in
theorem L32Data.of_C9 (hD : L32Data B) (h : A312C9 B L) :
    ∃ s : Bool, IsSL2 7 ↥B ∧ (IsPSLEps3 s 7 1 ↥L ∨ IsSLEps3 s 7 ↥L) := by
  rcases h with ⟨s, p, hp, hp3, hB, hL⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
  · have h2 := card_of_isSL2 hp hB
    have hpB : p ∣ Nat.card ↥B := h2 ▸ dvd_mul_right p _
    have hp7 : p = 7 := by
      by_contra hne
      exact hD.false_of_prime_dvd_card hp (by omega) hpB fun hp' => by
        rcases hp' with h' | h' <;> omega
    subst hp7
    exact ⟨s, hB, hL⟩
  · exact (hD.not_five_dvd (five_dvd_alt6 hB)).elim
  · exact (hD.not_five_dvd (five_dvd_hat6 hB)).elim

omit [Finite Q] in
theorem L32Data.of_C13 (hD : L32Data B) (h : A312C13 B L) :
    (IsExt ↥B (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 3 2 1 Y') ∨
      IsExt ↥B (fun V _ => IsE2 3 V) (fun Y' _ => IsPSL 3 2 1 Y')) ∧ IsSporadic .M23 ↥L := by
  obtain ⟨hB | hB | hB | hB | hB | hB | hB, hL⟩ := h
  · obtain ⟨e⟩ := hB
    exact (hD.not_eleven_dvd (by rw [Nat.card_congr e.toEquiv]; exact eleven_dvd_card_M22)).elim
  · exact (hD.not_five_dvd (five_dvd_L34 hB)).elim
  · exact (hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) fun Y _ hY => five_dvd_alt7 hY).elim
  · exact ⟨Or.inl hB, hL⟩
  · exact ⟨Or.inr hB, hL⟩
  · exact (hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) fun Y _ hY => five_dvd_alt6 hY).elim
  · exact (hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) fun Y _ hY => five_dvd_alt5 hY).elim

omit [Finite Q] in
theorem L32Data.of_C14 (hD : L32Data B) (h : A312C14 B L) :
    (IsExt ↥B (fun V _ => IsE2 6 V) (fun Y' _ => IsPSL 3 2 1 Y') ∨
      IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y' _ => IsPSL 3 2 1 Y')) ∧
      IsSporadic .M24 ↥L := by
  obtain ⟨hB | hB | hB | hB, hL⟩ := h
  · exact (hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) fun Y _ hY => five_dvd_L42 hY).elim
  · exact ⟨Or.inl hB, hL⟩
  · exact ⟨Or.inr hB, hL⟩
  · exact (hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) fun Y _ hY => five_dvd_hat6 hY).elim

omit [Finite Q] in
theorem L32Data.of_C17 (_hD : L32Data B) (h : A312C17 B L) : IsSporadic .J4 ↥L := h.1

omit [Finite Q] in
theorem L32Data.of_C18 (hD : L32Data B) (h : A312C18 B L) :
    IsExt ↥B (fun V _ => IsZ4Cubed V) (fun Y' _ => IsPSL 3 2 1 Y') ∧ IsSporadic .HS ↥L := by
  obtain ⟨hB | hB, hL⟩ := h
  · exact (hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) fun Y _ hY => five_dvd_alt5 hY).elim
  · exact ⟨hB, hL⟩

omit [Finite Q] in
theorem L32Data.of_C19 (hD : L32Data B) (h : A312C19 B L) :
    IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y' _ => IsPSL 3 2 1 Y') ∧
      IsSporadic .He ↥L := by
  obtain ⟨hB | hB, hL⟩ := h
  · exact ⟨hB, hL⟩
  · exact (hD.false_of_ext_prime hB (p := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) fun Y _ hY => five_dvd_hat6 hY).elim

omit [Finite Q] in
theorem L32Data.of_C20 (_hD : L32Data B) (h : A312C20 B L) :
    Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11 ∧ IsSporadic .Ru ↥L := by
  exact ⟨h.2.1, h.2.2⟩

omit [Finite Q] in
private theorem relIndex_sup_eq_of_le_normalizer {A D : Subgroup Q}
    (h : A ≤ Subgroup.normalizer (D : Set Q)) : D.relIndex (A ⊔ D) = D.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A D h).toEquiv.symm

omit [Finite Q] in
theorem L32Data.card_sup_eq (hD : L32Data B) {O : Subgroup Q}
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

theorem L32Data.of_nonquasi (hD : L32Data B) (hBL : B ≤ L) (h : A312Nonquasi B L) :
    ⁅(CFSG.oddCore ↥L).map L.subtype, L⁆ ≠ ⊥ ∧ L = B ⊔ (CFSG.oddCore ↥L).map L.subtype ∧
      IsSL2 7 (↥L ⧸ CFSG.oddCore ↥L) ∧ Nat.card ↥B = 336 := by
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
  rcases h with ⟨hne, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, hNeq, hN5⟩
  · have h2 := (CFSG.oddCore ↥L).card_eq_card_quotient_mul_card_subgroup
    rw [← hLB] at h1
    rw [card_of_isSL2 hp hSL, ← hOcard] at h2
    have hB : Nat.card ↥B = p * (p ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    have hp7 : p = 7 := by
      by_contra hne7
      exact hD.false_of_prime_dvd_card hp hp2 (hB ▸ dvd_mul_right p _) fun hp' => by
        rcases hp' with h' | h'
        · subst h'; omega
        · exact hne7 h'
    subst hp7
    exact ⟨hne, hLB, hSL, by rw [hB]; norm_num⟩
  · exfalso
    have h2 := N.card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 (by norm_num) hN5] at h2
    have h3 : Nat.card ↥N = Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) := by
      rw [hNeq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [h3] at h2
    have hB : Nat.card ↥B = 5 * (5 ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    omega

@[expose] def L32Survivor (B L : Subgroup Q) : Prop :=
  ((IsPSL 4 2 1 ↥L ∨ IsPSL 5 2 1 ↥L) ∧ ∃ P, IsParabolic2 L P ∧ B = perfectCore P) ∨
  (IsPSL 3 2 1 ↥B ∧ (IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7)))) ∨
  (IsPSL 2 7 1 ↥B ∧ IsPSL 2 7 2 ↥L) ∨
  (∃ s : Bool, IsSL2 7 ↥B ∧ (IsPSLEps3 s 7 1 ↥L ∨ IsSLEps3 s 7 ↥L)) ∨
  ((IsExt ↥B (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 3 2 1 Y') ∨
      IsExt ↥B (fun V _ => IsE2 3 V) (fun Y' _ => IsPSL 3 2 1 Y')) ∧ IsSporadic .M23 ↥L) ∨
  ((IsExt ↥B (fun V _ => IsE2 6 V) (fun Y' _ => IsPSL 3 2 1 Y') ∨
      IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y' _ => IsPSL 3 2 1 Y')) ∧
    IsSporadic .M24 ↥L) ∨
  IsSporadic .J4 ↥L ∨
  (IsExt ↥B (fun V _ => IsZ4Cubed V) (fun Y' _ => IsPSL 3 2 1 Y') ∧ IsSporadic .HS ↥L) ∨
  (IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y' _ => IsPSL 3 2 1 Y') ∧ IsSporadic .He ↥L) ∨
  (Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11 ∧ IsSporadic .Ru ↥L)

omit [Finite Q] in
theorem L32Data.of_a312Case (hD : L32Data B) (h : A312Case B L) :
    L32Survivor B L := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (hD.false_of_bad (Or.inl h)).elim
  · exact (hD.false_of_bad (Or.inr (Or.inl h))).elim
  · exact Or.inl ⟨h.2.1, h.2.2⟩
  · exact (hD.false_of_bad (Or.inr (Or.inr (Or.inl h)))).elim
  · exact Or.inr (Or.inl (hD.of_C6 h))
  · exact (hD.false_of_bad (Or.inr (Or.inr (Or.inr (Or.inl h))))).elim
  · exact Or.inr (Or.inr (Or.inl (hD.of_C8 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hD.of_C9 h))))
  · exact (hD.false_of_bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).elim
  · exact (hD.false_of_bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).elim
  · exact (hD.false_of_bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hD.of_C13 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hD.of_C14 h))))))
  · exact (hD.false_of_bad
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))).elim
  · exact (hD.false_of_bad
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hD.of_C17 h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hD.of_C18 h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hD.of_C19 h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (hD.of_C20 h)))))))))

end Rows

theorem row_of_a312_l32 {Y : Type} [Group Y] [Finite Y]
    {B N : Subgroup Y} (hBN : B ≤ N) (h3 : IsPSL 3 2 1 (ModO2 B))
    (h : A312Case B N ∨ A312Nonquasi B N) :
    L32Survivor B N ∨
      (⁅(CFSG.oddCore ↥N).map N.subtype, N⁆ ≠ ⊥ ∧
        N = B ⊔ (CFSG.oddCore ↥N).map N.subtype ∧ IsSL2 7 (↥N ⧸ CFSG.oddCore ↥N) ∧
        Nat.card ↥B = 336) := by
  have hD := l32Data_of h3
  rcases h with h | h
  · exact Or.inl (hD.of_a312Case h)
  · exact Or.inr (hD.of_nonquasi hBN h)

end CFSG.Quasithin.Stellmacher.CD.L3YC.L32
