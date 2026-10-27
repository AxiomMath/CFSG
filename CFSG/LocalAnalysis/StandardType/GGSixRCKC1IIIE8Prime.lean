module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeConfigID
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBlockInner
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import Mathlib.Tactic.NormNum

public section

namespace CFSG.Open

theorem eq_two_or_three_or_five_or_seven_of_pow_four_dvd_ordE8_two
    {p : ℕ} (hp : p.Prime) (hd : p ^ 4 ∣ ordE8 2) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have hf : ordE8 2 = 2 ^ 120 * 3 ^ 13 * 5 ^ 5 * 7 ^ 4 * 11 ^ 2 * 13 ^ 2 * 17 ^ 2 *
      19 * 31 ^ 2 * 41 * 43 * 73 * 127 * 151 * 241 * 331 := by
    norm_num [ordE8]
  have hpd : p ∣ 2 ^ 120 * 3 ^ 13 * 5 ^ 5 * 7 ^ 4 * 11 ^ 2 * 13 ^ 2 * 17 ^ 2 *
      19 * 31 ^ 2 * 41 * 43 * 73 * 127 * 151 * 241 * 331 := by
    rw [← hf]
    exact (dvd_pow_self p (by decide : 4 ≠ 0)).trans hd
  simp only [hp.dvd_mul, or_assoc] at hpd
  have heq {q k : ℕ} (hq : q.Prime) (h : p ∣ q ^ k) : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)
  rcases hpd with h2 | h3 | h5 | h7 | h11 | h13 | h17 | h19 | h31 | h41 | h43 |
    h73 | h127 | h151 | h241 | h331
  · exact Or.inl (heq Nat.prime_two h2)
  · exact Or.inr (Or.inl (heq (by norm_num) h3))
  · exact Or.inr (Or.inr (Or.inl (heq (by norm_num) h5)))
  · exact Or.inr (Or.inr (Or.inr (heq (by norm_num) h7)))
  · have : p = 11 := heq (by norm_num) h11
    subst p
    norm_num [ordE8] at hd
  · have : p = 13 := heq (by norm_num) h13
    subst p
    norm_num [ordE8] at hd
  · have : p = 17 := heq (by norm_num) h17
    subst p
    norm_num [ordE8] at hd
  · have : p = 19 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h19
    subst p
    norm_num [ordE8] at hd
  · have : p = 31 := heq (by norm_num) h31
    subst p
    norm_num [ordE8] at hd
  · have : p = 41 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h41
    subst p
    norm_num [ordE8] at hd
  · have : p = 43 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h43
    subst p
    norm_num [ordE8] at hd
  · have : p = 73 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h73
    subst p
    norm_num [ordE8] at hd
  · have : p = 127 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h127
    subst p
    norm_num [ordE8] at hd
  · have : p = 151 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h151
    subst p
    norm_num [ordE8] at hd
  · have : p = 241 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h241
    subst p
    norm_num [ordE8] at hd
  · have : p = 331 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h331
    subst p
    norm_num [ordE8] at hd

end CFSG.Open

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType


theorem prime_eq_three_or_five_or_seven_of_e8_two_innerDiag
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A : Subgroup X}
    (hpres : GGPresentsG0 G₀ (ggU .E8 n 1).D .E8 n 1 ψ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsElemAbelian p A)
    (hAN : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hdiag : ∀ a ∈ A, GGPsiInnerDiag (ggU .E8 n 1).D ψ a)
    (hfaith : A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥)
    (h4 : p ^ 4 ≤ Nat.card A) : p = 3 ∨ p = 5 ∨ p = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : ψ.range = G₀ := hpres.2.1.1
  have hfield : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hAG : Nat.card A ∣ Nat.card G₀ :=
    CFSG.AGLEmbedding.card_dvd_of_faithful_inner hAN Subgroup.le_normalizer hfaith fun a ha => by
      obtain ⟨g, hg, hag⟩ := ggPsiDiagInner_E8 X n 1 ψ G₀ hpres a (hAN ha) (hdiag a ha)
      exact ⟨g⁻¹, G₀.inv_mem hg, by simpa only [inv_inv] using hag⟩
  have hU : Nat.card (ggU .E8 n 1).K = CFSG.Open.ordE8 2 := by
    change Nat.card ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 1)) = _
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hfield]
  have hAo : Nat.card A ∣ CFSG.Open.ordE8 2 := by
    rw [← hU]
    exact hAG.trans (hrange ▸ Subgroup.card_range_dvd ψ)
  have : Fact p.Prime := ⟨hp⟩
  have hPA : IsPGroup p A := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hA.2 a a.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPA
  have h4k : 4 ≤ k := Nat.pow_le_pow_iff_right hp.one_lt |>.mp (hk ▸ h4)
  have hd : p ^ 4 ∣ CFSG.Open.ordE8 2 := (Nat.pow_dvd_pow p h4k).trans (hk ▸ hAo)
  exact (CFSG.Open.eq_two_or_three_or_five_or_seven_of_pow_four_dvd_ordE8_two hp hd).resolve_left hp2

theorem prime_eq_three_or_five_or_seven_of_e8_two_compConfig
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (h : RCKRP.RCKCompConfig .E8 n 1 ψ p G₀ A B₁ D J L K e) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have hdiag := RCKRP.rckRPConfigInnerDiag_holds X .E8 n 1 ψ p G₀ A B₁ D J L K e h
  obtain ⟨hpres, -, hp, hp2, hA, hBA, -, -, hAN, -, -, -, hB4, -, -, hfaith, -⟩ := h
  exact prime_eq_three_or_five_or_seven_of_e8_two_innerDiag hpres hp hp2 hA hAN hdiag hfaith
    (hB4.trans (Nat.le_of_dvd (Nat.card_pos : 0 < Nat.card A) (Subgroup.card_dvd_of_le hBA)))

end CFSG.StandardType.RCKC1
