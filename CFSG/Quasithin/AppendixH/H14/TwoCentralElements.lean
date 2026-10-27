module

public import Mathlib
public import CFSG.Milestones.ASVolI.H13
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Sporadic.Schreier

variable {X : Type*} [Group X]

private lemma factorization_two_card_le_of_le [Finite X] {H K : Subgroup X} (h : H ≤ K) :
    (Nat.card H).factorization 2 ≤ (Nat.card K).factorization 2 :=
  (Nat.factorization_le_iff_dvd (Nat.card_pos (α := H)).ne'
    (Nat.card_pos (α := K)).ne').2 (Subgroup.card_dvd_of_le h) 2

theorem isTwoCentralElt_of_dvd_card [Finite X] {M : Subgroup X} {a : X}
    (h : 2 ^ (Nat.card M).factorization 2 ∣ Nat.card (centralizerIn M a)) :
    IsTwoCentralElt M a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSC, -⟩ :=
    exists_isSylowIn_ge 2 (H := centralizerIn M a) (P := ⊥) bot_le IsPGroup.of_bot
  have hSM : S ≤ M := hSC.le.trans inf_le_left
  have hle : (Nat.card M).factorization 2 ≤
      (Nat.card (centralizerIn M a)).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos (α := centralizerIn M a)).ne').1 h
  have hge : (Nat.card (centralizerIn M a)).factorization 2 ≤
      (Nat.card M).factorization 2 := factorization_two_card_le_of_le inf_le_left
  refine ⟨S, isSylowIn_of_card_eq hSM ?_,
    fun s hs => (mem_centralizerIn.mp (hSC.le hs)).2⟩
  rw [IsSylowIn.card_eq hSC, le_antisymm hge hle]

theorem not_isTwoCentralElt_of_not_dvd_card [Finite X] {M : Subgroup X} {a : X}
    (h : ¬ 2 ^ (Nat.card M).factorization 2 ∣ Nat.card (centralizerIn M a)) :
    ¬ IsTwoCentralElt M a := by
  rintro ⟨S, hSyl, hcomm⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC : S ≤ centralizerIn M a :=
    fun s hs => mem_centralizerIn.2 ⟨hSyl.le hs, hcomm s hs⟩
  have hdvd : Nat.card S ∣ Nat.card (centralizerIn M a) := Subgroup.card_dvd_of_le hSC
  rw [IsSylowIn.card_eq hSyl] at hdvd
  exact h hdvd

theorem isTwoCentralElt_iff_dvd_card [Finite X] {M : Subgroup X} {a : X} :
    IsTwoCentralElt M a ↔ 2 ^ (Nat.card M).factorization 2 ∣ Nat.card (centralizerIn M a) :=
  ⟨fun h => by_contra fun h' => not_isTwoCentralElt_of_not_dvd_card h' h,
    isTwoCentralElt_of_dvd_card⟩

theorem card_centralizerIn_conj (H : Subgroup X) {c : X} (hc : c ∈ H) (u : X) :
    Nat.card (centralizerIn H (c * u * c⁻¹)) = Nat.card (centralizerIn H u) := by
  rw [centralizerIn_conj H hc u, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem isTwoCentralElt_conj [Finite X] {M : Subgroup X} {a c : X} (hc : c ∈ M) :
    IsTwoCentralElt M (c * a * c⁻¹) ↔ IsTwoCentralElt M a := by
  rw [isTwoCentralElt_iff_dvd_card, isTwoCentralElt_iff_dvd_card, card_centralizerIn_conj M hc]

end CFSG.Quasithin.AppendixH.H14
