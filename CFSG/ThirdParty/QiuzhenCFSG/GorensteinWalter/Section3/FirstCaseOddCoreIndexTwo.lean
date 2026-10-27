module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd-core index two at an index-six intersection

The quotient of a finite group of order six has nontrivial odd core.  Applied
to a normal odd subgroup of index six, this forces the ambient odd core to
have index two.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem pPrimeCore_nonbot_of_card_six
    {Q : Type u} [Group Q] [Finite Q]
    (hcard : Nat.card Q = 6) :
    pPrimeCore 2 Q ≠ ⊥ := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by
    rw [hcard]
    norm_num)
  let R : Subgroup Q := Subgroup.zpowers x
  have hRcard : Nat.card R = 3 := by
    dsimp [R]
    rw [Nat.card_zpowers]
    exact hxorder
  have hRindex : R.index = 2 := by
    have hmul := R.card_mul_index
    rw [hRcard, hcard] at hmul
    omega
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 1) (by
    simpa using hRcard)
  let P : Sylow 3 Q := hRp.toSylow (by
    rw [hRindex]
    norm_num)
  have hPcoe : (P : Subgroup Q) = R := rfl
  have hPcard : Nat.card (P : Subgroup Q) = 3 := by
    simpa [hPcoe] using hRcard
  have hPindex : (P : Subgroup Q).index = 2 := by
    have hmul := (P : Subgroup Q).card_mul_index
    rw [hPcard, hcard] at hmul
    omega
  have hSylowCardDvd : Nat.card (Sylow 3 Q) ∣ 2 := by
    rw [← hPindex]
    exact Sylow.card_dvd_index P
  have hSylowCardLe : Nat.card (Sylow 3 Q) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hSylowCardDvd
  have hmod := card_sylow_modEq_one 3 Q
  have hmod' : Nat.card (Sylow 3 Q) % 3 = 1 % 3 := hmod
  have hSylowCard : Nat.card (Sylow 3 Q) = 1 := by
    have hpos : 0 < Nat.card (Sylow 3 Q) := Nat.card_pos
    omega
  let : Subsingleton (Sylow 3 Q) := by
    obtain ⟨z, hz⟩ := (Nat.card_eq_one_iff_exists.mp hSylowCard)
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩
  have hPNormal : (P : Subgroup Q).Normal := Sylow.normal_of_subsingleton P
  have hPcop : Nat.Coprime 2 (Nat.card (P : Subgroup Q)) := by
    rw [hPcard]
    norm_num
  have hPle : (P : Subgroup Q) ≤ pPrimeCore 2 Q := by
    exact le_sSup ⟨hPNormal, (by simpa [Nat.coprime_comm] using hPcop)⟩
  intro hbot
  have hPbot : (P : Subgroup Q) = ⊥ := le_bot_iff.mp (hbot ▸ hPle)
  have hPcard1 : Nat.card (P : Subgroup Q) = 1 := by
    rw [hPbot]
    simp
  omega

public theorem pPrimeCore_index_two_of_normal_odd_index_six
    {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) (hNnormal : N.Normal)
    (hNodd : Nat.Coprime 2 (Nat.card N))
    (hindex : N.index = 6) :
    (pPrimeCore 2 H).index = 2 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup H := pPrimeCore 2 H
  have hNleO : N ≤ O := by
    exact le_sSup ⟨hNnormal, hNodd⟩
  have hOdvd : O.index ∣ N.index := Subgroup.index_dvd_of_le hNleO
  have hOdvd6 : O.index ∣ 6 := by simpa [hindex] using hOdvd
  have hHcard : 2 ∣ Nat.card H := by
    have hmul := N.card_mul_index
    rw [hindex] at hmul
    exact ⟨Nat.card N * 3, by omega⟩
  have hOcardOdd : Nat.Coprime 2 (Nat.card O) :=
    pPrimeCore_coprime_card (p := 2) (G := H)
  have hOeven : 2 ∣ O.index := by
    have hmul := O.card_mul_index
    have hdiv : 2 ∣ Nat.card O * O.index := by simpa [hmul] using hHcard
    rcases (Nat.prime_two.dvd_mul).mp hdiv with h | h
    · exact ((Nat.prime_two.coprime_iff_not_dvd).mp hOcardOdd h).elim
    · exact h
  have hOindexle : O.index ≤ 6 := Nat.le_of_dvd (by norm_num) hOdvd6
  have hOindex_cases : O.index = 2 ∨ O.index = 6 := by
    interval_cases h : O.index <;> omega
  rcases hOindex_cases with h2 | h6
  · exact h2
  · exfalso
    have hQcard : Nat.card (H ⧸ O) = 6 := by
      rw [← O.index_eq_card, h6]
    have hQcore : pPrimeCore 2 (H ⧸ O) ≠ ⊥ :=
      pPrimeCore_nonbot_of_card_six hQcard
    have hQbot : pPrimeCore 2 (H ⧸ O) = ⊥ := by
      simpa [O] using pPrimeCore_quotient_pPrimeCore_eq_bot (G := H) 2
    exact hQcore hQbot

end CFSG.GorensteinWalter
