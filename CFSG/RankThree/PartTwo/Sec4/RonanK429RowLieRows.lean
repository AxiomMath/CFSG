module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem cfgS429_pow_three {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)}
    {σ : MulAut S} {K : Subgroup S} (hc : CfgS429 S A σ K) : σ ^ 3 = 1 :=
  hc.isE27.1.2 σ hc.mem

section Rows


theorem rowS429_seven_SL3 (n : ℕ) (hn : 1 ≤ n) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* projSL 3 (GaloisField 2 n)) → RowS429 S := by
  intro S _ _ hs hna ⟨eS⟩ A σ K hc
  haveI := hc.isPerfect
  obtain ⟨hO2, m, hm, rfl, hK, hS, τ, hfield⟩ := rowLie_SL3 hs hna hn eS
    (cfgS429_pow_three hc) hc.ne_one (C := Sec4.autFix σ) (fun x => Sec4.mem_autFix)
    hc.le_autFix hc.isSubnormal hc.isType
  exact ⟨hO2, Or.inr ⟨m, hm, hK, hS, Or.inl ⟨GaloisField 2 (3 * m), inferInstance, inferInstance,
    τ, hfield⟩⟩⟩

theorem rowS429_seven_SU3 (n : ℕ) (hn : 1 ≤ n) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* projSU 3 2 n) → RowS429 S := by
  intro S _ _ hs hna ⟨eS⟩ A σ K hc
  haveI := hc.isPerfect
  obtain ⟨hO2, m, hm, rfl, hK, hS, h, τ, hfield⟩ := rowLie_SU3 hs hna hn eS
    (cfgS429_pow_three hc) hc.ne_one (C := Sec4.autFix σ) (fun x => Sec4.mem_autFix)
    hc.le_autFix hc.isSubnormal hc.isType
  have hq2 : 2 < 2 ^ (3 * m) := by
    have h8 : 2 ^ 3 ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact ⟨hO2, Or.inr ⟨m, hm, hK, hS, Or.inr ⟨2, 3 * m, GaloisField 2 (2 * (3 * m)),
    inferInstance, h, hq2, τ, hfield⟩⟩⟩

end Rows

section D4


theorem rowS429NoL3_seven_D4 (hG2 : G2Excl429) (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p = 2) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) → RowS429NoL3 S := by
  intro S _ _ hs hna ⟨e⟩ A σ K hc
  have hm : Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hq hq2 (by decide) e⟩
  rw [hq2] at hm
  haveI := hc.isPerfect
  obtain ⟨hO2, hf1, hK, hout⟩ := rowLie_D4 hG2 hs hna hm (cfgS429_pow_three hc) hc.ne_one
    hc.le_autFix hc.isSubnormal hc.isType
  exact ⟨hO2, Or.inr ⟨q.exponent, hf1, hK, hm, hout⟩⟩

end D4

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
