module

public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

structure L34Data {Q : Type} [Group Q] (B : Subgroup Q) : Prop where
  card : ∃ a, Nat.card ↥B = 2 ^ a * (2 ^ 6 * 315)
  psl : IsPSL 3 2 2 (ModO2 B)
  odd : ∀ N : Subgroup ↥B, N.Normal → Odd (Nat.card ↥N) → N = ⊥

variable {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q}

theorem l34Data_of (h : IsPSL 3 2 2 (ModO2 B)) : L34Data B where
  card := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
    refine ⟨a, ?_⟩
    rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, card_L34 h, ha, mul_comm]
  psl := h
  odd := fun N hN hodd => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hs : IsSimpleGroup (ModO2 B) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 h).2
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
      rw [htop, Subgroup.card_top, card_L34 h] at h1
      have h2 : 2 ∣ Nat.card ↥N := dvd_trans (by norm_num) h1
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

omit [Finite Q] in
theorem L34Data.le_card (hD : L34Data B) : 2 ^ 6 * 315 ≤ Nat.card ↥B := by
  obtain ⟨a, ha⟩ := hD.card
  rw [ha]
  exact Nat.le_mul_of_pos_left _ (by positivity)

omit [Finite Q] in
theorem L34Data.odd_eq (hD : L34Data B) {d o : ℕ} (ho : Odd o) (h : Nat.card ↥B = 2 ^ d * o) :
    o = 315 := by
  obtain ⟨a, ha⟩ := hD.card
  have h1 : 2 ^ (a + 6) * 315 = 2 ^ d * o := by rw [← h, ha, pow_add, mul_assoc]
  have h2 := eq_of_two_pow_mul_odd (a := a + 6) (b := d) (by decide) ho h1
  rw [← h2] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm

omit [Finite Q] in
theorem L34Data.not_prime_dvd (hD : L34Data B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp315 : ¬ p ∣ 315) : ¬ p ∣ Nat.card ↥B := by
  obtain ⟨a, ha⟩ := hD.card
  rw [ha, ← mul_assoc, ← pow_add]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  · exact hp315 h1

theorem L34Data.ext (hD : L34Data B) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k) :
    ∃ (V : Subgroup ↥B) (_ : V.Normal), PY (↥B ⧸ V) ∧ V ≤ CFSG.pCore 2 ↥B ∧
      2 ^ 6 * 315 ≤ Nat.card (↥B ⧸ V) ∧
      ∀ {d o : ℕ}, Odd o → Nat.card (↥B ⧸ V) = 2 ^ d * o → o = 315 := by
  obtain ⟨V, hVn, hPV', hPY⟩ := h
  obtain ⟨k, hk⟩ := hPV _ hPV'
  have hVp : IsPGroup 2 ↥V := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card hk
  have hVO : V ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hVn, hVp⟩
  refine ⟨V, hVn, hPY, hVO, ?_, fun {d o} ho hY => ?_⟩
  · have h1 := V.card_eq_card_quotient_mul_card_subgroup
    have h2 := (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
    rw [card_L34 hD.psl] at h2
    have h3 : Nat.card ↥V ≤ Nat.card ↥(CFSG.pCore 2 ↥B) := Subgroup.card_le_of_le hVO
    have h4 : 0 < Nat.card ↥V := Nat.card_pos
    by_contra hlt
    have hlt' : Nat.card (↥B ⧸ V) < 2 ^ 6 * 315 := lt_of_not_ge hlt
    have : Nat.card (↥B ⧸ V) * Nat.card ↥V < 2 ^ 6 * 315 * Nat.card ↥(CFSG.pCore 2 ↥B) :=
      calc Nat.card (↥B ⧸ V) * Nat.card ↥V < 2 ^ 6 * 315 * Nat.card ↥V :=
            Nat.mul_lt_mul_of_pos_right hlt' h4
        _ ≤ 2 ^ 6 * 315 * Nat.card ↥(CFSG.pCore 2 ↥B) := Nat.mul_le_mul_left _ h3
    omega
  · have h1 := V.card_eq_card_quotient_mul_card_subgroup
    rw [hY, hk] at h1
    exact hD.odd_eq ho (by rw [h1, mul_comm, ← mul_assoc, ← pow_add])

end CFSG.Quasithin.Vol2.Ch11.SecS
