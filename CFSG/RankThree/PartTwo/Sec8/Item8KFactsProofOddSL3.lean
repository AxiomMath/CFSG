module

public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofDefs
import CFSG.RankThree.PartTwo.Sec4.Item47CasesOdd
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Item8KFactsProof

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_field_of_natural {x : G} {p e : ℕ} (hp : p.Prime) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hx3 : x ^ 3 = 1) :
    (∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ e →
        ¬ KFacts.InducesKindPSL 3 K L x .field ∧ ¬ KFacts.InducesKindSL 3 K L x .field) ∧
      (∀ (K : Type) [Field K] (hK : UnitaryFieldData p e K) (hq : 2 < p ^ e),
        ¬ KFacts.InducesKindPSU3 hK L x .field ∧ ¬ KFacts.InducesKindSU3 hK L hq x .field) := by
  have h3 : ∀ m : ℕ, 3 ∣ m → m = e ∨ m = 2 * e → False := by
    intro m hm hme
    rcases hme with rfl | rfl <;> omega
  refine ⟨fun K _ _ hK => ⟨?_, ?_⟩, fun K _ hK hq => ⟨?_, ?_⟩⟩
  · rintro ⟨E, hE⟩
    have := Sec4.three_dvd_card_of_inducesKind_field (ψ := LinearFlag.fieldAut 3 K) rfl hE hx3
    rw [Sec4.card_ringAut_eq hp he1 hK] at this
    exact h3 e this (Or.inl rfl)
  · rintro ⟨E, hxN, hf⟩
    have := Sec4.three_dvd_card_of_isField (ψ := LinearFlag.fieldAut 3 K) rfl hf
      (Sec4.descendAut_inducedAutHom_pow_three hxN hx3)
    rw [Sec4.card_ringAut_eq hp he1 hK] at this
    exact h3 e this (Or.inl rfl)
  · rintro ⟨E, hE⟩
    have : Finite (K ≃+* K) := Sec4.finite_ringAut hp hK.card
    have := Sec4.three_dvd_card_of_inducesKind_field (ψ := KFacts.psuField hK) rfl hE hx3
    rw [Sec4.card_ringAut_eq hp (by omega) hK.card] at this
    exact h3 (2 * e) this (Or.inr rfl)
  · rintro ⟨E, hxN, hf⟩
    have : Finite (K ≃+* K) := Sec4.finite_ringAut hp hK.card
    have h3' : MulAut.congr (KFacts.suCenterEquiv hK hq)
        (KFacts.centerDescend _ (KFacts.inducedAutHom L E ⟨x, hxN⟩)) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, KFacts.inducedAutHom_pow_eq_one L E hxN hx3, map_one, map_one]
    have := Sec4.three_dvd_card_of_isField (ψ := KFacts.psuField hK) rfl hf h3'
    rw [Sec4.card_ringAut_eq hp (by omega) hK.card] at this
    exact h3 (2 * e) this (Or.inr rfl)

theorem not_graphField_of_natural {x : G} {p e : ℕ} (hx3 : x ^ 3 = 1) :
    (∀ (K : Type) [Field K] [Finite K],
        ¬ KFacts.InducesKindPSL 3 K L x .graphField ∧
          ¬ KFacts.InducesKindSL 3 K L x .graphField) ∧
      (∀ (K : Type) [Field K] (hK : UnitaryFieldData p e K) (hq : 2 < p ^ e),
        ¬ KFacts.InducesKindPSU3 hK L x .graphField ∧
          ¬ KFacts.InducesKindSU3 hK L hq x .graphField) := by
  refine ⟨fun K _ _ => ⟨?_, ?_⟩, fun K _ hK hq => ⟨?_, ?_⟩⟩
  · rintro ⟨E, hxN, hk⟩
    have hτ3 : KFacts.inducedAutHom L E ⟨x, hxN⟩ ^ 3 = 1 :=
      KFacts.inducedAutHom_pow_eq_one L E hxN hx3
    have hsep := KFacts.stdPinnedPSL_separated (K := K) (n := 3) le_rfl
    have hD := hsep.not_mem_inndiag_of_hasKind hk (by decide) (by decide)
    exact hsep.not_isGraphField_of_isField (KFacts.isField_of_pow_three_eq_one le_rfl hτ3 hD)
      ((KFacts.stdPinnedPSL 3 K).hasKind_graphField.mp hk)
  · rintro ⟨E, hxN, hk⟩
    have hτ3 := Sec4.descendAut_inducedAutHom_pow_three hxN hx3 (e := E)
    have hsep := KFacts.stdPinnedPSL_separated (K := K) (n := 3) le_rfl
    have hD := hsep.not_mem_inndiag_of_hasKind hk (by decide) (by decide)
    exact hsep.not_isGraphField_of_isField (KFacts.isField_of_pow_three_eq_one le_rfl hτ3 hD)
      ((KFacts.stdPinnedPSL 3 K).hasKind_graphField.mp hk)
  · rintro ⟨E, hN, γ, hγ, -⟩
    exact hγ
  · rintro ⟨E, hxN, γ, hγ, -⟩
    exact hγ

end Item8KFactsProof


@[expose] def KF82OddSL3Model : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (p e : ℕ) [Fact p.Prime]
    (k : KFacts.AutKind), 3 < p → 1 ≤ e → e ≤ 2 →
    (Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
      Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) →
    KFacts.InducesStdKind L x k →
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ e ∧
        (KFacts.InducesKindPSL 3 K L x k ∨ KFacts.InducesKindSL 3 K L x k)) ∨
      (∃ (K : Type) (_ : Field K) (hK : UnitaryFieldData p e K) (hq : 2 < p ^ e),
        KFacts.InducesKindPSU3 hK L x k ∨ KFacts.InducesKindSU3 hK L hq x k)


open Item8KFactsProof

theorem kF82OddSLThree_of (hM : KF82OddSL3Model) : KF82OddSLThree := by
  intro G _ _ L x p e _ hp3 he1 he2 hX hx3
  have hp : p.Prime := Fact.out
  obtain ⟨hFn, hFu⟩ := not_field_of_natural (L := L) hp he1 he2 hx3
  obtain ⟨hGn, hGu⟩ := not_graphField_of_natural (L := L) (p := p) (e := e) hx3
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rcases hM G L x p e .field hp3 he1 he2 hX hk with ⟨K, _, _, hK, h | h⟩ |
      ⟨K, _, hK, hq, h | h⟩
    · exact (hFn K hK).1 h
    · exact (hFn K hK).2 h
    · exact (hFu K hK hq).1 h
    · exact (hFu K hK hq).2 h
  · rcases hM G L x p e .graphField hp3 he1 he2 hX hk with ⟨K, _, _, hK, h | h⟩ |
      ⟨K, _, hK, hq, h | h⟩
    · exact (hGn K).1 h
    · exact (hGn K).2 h
    · exact (hGu K hK hq).1 h
    · exact (hGu K hK hq).2 h

end CFSG.RankThree.PartTwo.Sec8
