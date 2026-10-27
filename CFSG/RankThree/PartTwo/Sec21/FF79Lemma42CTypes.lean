module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CTypesJ
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CTypesN
import CFSG.GF2Type.Smith1979.CaseIIExclL52

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.GroupTheory.GL52

variable {G : Type} [Group G]

theorem e9_types [Finite G] (J R : Subgroup G) (hJ : IsLnq 5 2 1 J) (hRJ : R ≤ J)
    (hR : IsElemAb 3 2 R) :
    (∀ x ∈ R, x ≠ 1 → (IsLnq 2 2 2 (Lay (J ⊓ Cen x)) ∨ IsLnq 3 2 1 (Lay (J ⊓ Cen x)))) ∧
    (∀ x : G, ¬ (IsLnq 2 2 2 (Lay (J ⊓ Cen x)) ∧ IsLnq 3 2 1 (Lay (J ⊓ Cen x)))) ∧
    Nat.card {x : G // x ∈ R ∧ x ≠ 1 ∧ IsLnq 2 2 2 (Lay (J ⊓ Cen x))} = 4 ∧
    Nat.card {x : G // x ∈ R ∧ x ≠ 1 ∧ IsLnq 3 2 1 (Lay (J ⊓ Cen x))} = 4 ∧
    (∀ x ∈ R, x ≠ 1 → ∃ e ∈ R ⊓ Lay (J ⊓ Cen x), e ≠ 1) ∧
    (∀ x ∈ R, x ≠ 1 → ∀ e ∈ R ⊓ Lay (J ⊓ Cen x), e ≠ 1 →
      e ∉ Subgroup.zpowers x ∧
      ((IsLnq 2 2 2 (Lay (J ⊓ Cen e)) ↔ IsLnq 2 2 2 (Lay (J ⊓ Cen x))) ∧
       (IsLnq 3 2 1 (Lay (J ⊓ Cen e)) ↔ IsLnq 3 2 1 (Lay (J ⊓ Cen x))))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two (X := ↥J) (n := 5) hJ
  haveI := hR.1
  have hcube : ∀ r ∈ R, r ^ 3 = 1 := fun r hr => elemPow_eq_one_of_isElementaryAbelian r hr
  have hord : ∀ r ∈ R, r ≠ 1 → orderOf r = 3 := fun r hr h1 =>
    orderOf_eq_prime (hcube r hr) h1
  have hdata := fun x (hx : x ∈ R) (h1 : x ≠ 1) => lay_cen_data e (hRJ hx) (hord x hx h1)
  have hA : ∀ x ∈ R, x ≠ 1 → (IsLnq 2 2 2 (Lay (J ⊓ Cen x)) ↔
      ∃ hx : x ∈ J, Matrix.trace ((e ⟨x, hx⟩ : G52) : M5) = 1) := by
    intro x hxR h1
    rcases (hdata x hxR h1).1 with ⟨ht, hA, hB⟩ | ⟨ht, hB, hA⟩
    · exact ⟨fun _ => ⟨hRJ hxR, ht⟩, fun _ => hA⟩
    · exact ⟨fun h => absurd h hA, fun ⟨hx, h⟩ => absurd (ht.symm.trans h) (by decide)⟩
  have hB : ∀ x ∈ R, x ≠ 1 → (IsLnq 3 2 1 (Lay (J ⊓ Cen x)) ↔
      ∃ hx : x ∈ J, Matrix.trace ((e ⟨x, hx⟩ : G52) : M5) = 0) := by
    intro x hxR h1
    rcases (hdata x hxR h1).1 with ⟨ht, hA, hB⟩ | ⟨ht, hB, hA⟩
    · exact ⟨fun h => absurd h hB, fun ⟨hx, h⟩ => absurd (ht.symm.trans h) (by decide)⟩
    · exact ⟨fun _ => ⟨hRJ hxR, ht⟩, fun _ => hB⟩
  refine ⟨?_, fun x => not_isLnq_both _, ?_, ?_, ?_, ?_⟩
  · intro x hx h1
    rcases (hdata x hx h1).1 with ⟨-, h, -⟩ | ⟨-, h, -⟩
    exacts [Or.inl h, Or.inr h]
  · refine Eq.trans (Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_))
      (card_trace e hRJ hR.2 1)
    exact and_congr_right fun hxR => and_congr_right fun h1 => hA x hxR h1
  · refine Eq.trans (Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_))
      (card_trace e hRJ hR.2 0)
    exact and_congr_right fun hxR => and_congr_right fun h1 => hB x hxR h1
  · intro x hxR h1
    obtain ⟨-, -, hdec, -⟩ := hdata x hxR h1
    have hnot : ¬ R ≤ Subgroup.zpowers x := fun hle => by
      have := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hord x hxR h1, hR.2] at this
      omega
    obtain ⟨r, hr, hrx⟩ := Set.not_subset.mp hnot
    have hrJ := hRJ hr
    have hcomm : r * x = x * r := Subtype.ext_iff.mp
      (hR.1.is_comm.comm (⟨r, hr⟩ : ↥R) ⟨x, hxR⟩)
    obtain ⟨i, l, hl, hrl⟩ := hdec r ⟨hrJ, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    refine ⟨l, ⟨?_, hl⟩, fun hl1 => hrx ?_⟩
    · have : l = (x ^ i)⁻¹ * r := by rw [hrl]; group
      rw [this]
      exact R.mul_mem (R.inv_mem (R.zpow_mem hxR i)) hr
    · rw [hrl, hl1, mul_one]
      exact Subgroup.zpow_mem_zpowers x i
  · intro x hxR h1 e' he' he'1
    obtain ⟨he'R, he'L⟩ := he'
    obtain ⟨-, hdtr, -, hdint⟩ := hdata x hxR h1
    have hzp : e' ∉ Subgroup.zpowers x := fun h => he'1 (hdint e' he'L h)
    refine ⟨hzp, ?_⟩
    obtain ⟨hz, htr⟩ := hdtr e' he'L (hord e' he'R he'1)
    have hiff : (∃ hx : e' ∈ J, Matrix.trace ((e ⟨e', hx⟩ : G52) : M5) = 1) ↔
        ∃ hx : x ∈ J, Matrix.trace ((e ⟨x, hx⟩ : G52) : M5) = 1 :=
      ⟨fun ⟨_, h⟩ => ⟨hRJ hxR, htr ▸ h⟩, fun ⟨_, h⟩ => ⟨hz, htr.trans h⟩⟩
    have hiff0 : (∃ hx : e' ∈ J, Matrix.trace ((e ⟨e', hx⟩ : G52) : M5) = 0) ↔
        ∃ hx : x ∈ J, Matrix.trace ((e ⟨x, hx⟩ : G52) : M5) = 0 :=
      ⟨fun ⟨_, h⟩ => ⟨hRJ hxR, htr ▸ h⟩, fun ⟨_, h⟩ => ⟨hz, htr.trans h⟩⟩
    exact ⟨(hA e' he'R he'1).trans (hiff.trans (hA x hxR h1).symm),
      (hB e' he'R he'1).trans (hiff0.trans (hB x hxR h1).symm)⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
