module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33Inj
import CFSG.GroupTheory.PRankBound
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankCl
import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankGapE6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open TauCeti
open CFSG.Blueprint (AdjointQuotient)
open CFSG.Blueprint.Chevalley (Tag)
open CFSG.TauCetiBridge (fieldOf card_fieldOf)
open CFSG.TauCetiBridge.Even (UntwistedBridgeAll chevalleyBridgesAll)
open CFSG.LieType.Chevalley (four_le_pRank_three_adjointQuotient_any)
open CFSG.HardMathSupport.Cooperstein.Coordinator (reeTitsModel_reeF4_of_lie)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (twistedChevalleyModel_of_bridge)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (untwistedChevalleyModel_of_bridge)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3 (three_le_pRank_of_equiv
  three_le_pRank_of_glbCore_eq_top)

private theorem k33exc_three_le_pRank
    {τ : Tag} {c : PrimePower → LieTypeIndex} (hB : UntwistedBridgeAll τ c)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (q : PrimePower) (hv : (c q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have hF := card_fieldOf q Nat.one_pos
  rw [pow_one] at hF
  obtain ⟨φ⟩ := hB q hv (fieldOf q 1) hF
  have e' := e.trans φ.symm
  have : Finite (AdjointQuotient τ (fieldOf q 1)) := Finite.of_equiv L e'.toEquiv
  exact three_le_pRank_of_equiv e'
    ((by norm_num : 3 ≤ 4).trans (four_le_pRank_three_adjointQuotient_any hτ))

section Chevalley


theorem k33Models_E6 {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.E6 q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  exfalso
  have := k33exc_three_le_pRank chevalleyBridgesAll.e6 (Or.inr (Or.inl rfl)) q hv e
  omega

theorem k33Models_E7 {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.E7 q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  exfalso
  have := k33exc_three_le_pRank chevalleyBridgesAll.e7 (Or.inr (Or.inr (Or.inl rfl))) q hv e
  omega

theorem k33Models_E8 {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.E8 q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  exfalso
  have := k33exc_three_le_pRank chevalleyBridgesAll.e8 (Or.inr (Or.inr (Or.inr rfl))) q hv e
  omega

theorem k33Models_F4 {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.F4 q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  exfalso
  have := k33exc_three_le_pRank chevalleyBridgesAll.f4 (Or.inl rfl) q hv e
  omega

theorem k33Models_G2 {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    K33Models L := by
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
  exact K33Models.of_g2 (p := q.p) (f := q.exponent)
    (Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
      untwistedChevalleyModel_of_bridge chevalleyBridgesAll.g2 e⟩))

theorem k33Models_trialityD4 {q : PrimePower} (hv : (LieTypeIndex.trialityD4 q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    K33Models L :=
  K33Models.of_trialityD4 (p := q.p) (f := q.exponent)
    (Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      twistedChevalleyModel_of_bridge (t := .D4) chevalleyBridgesAll.trialityD4 e⟩))

end Chevalley

theorem k33Models_twistedE6
    {q : PrimePower} (hv : (LieTypeIndex.twistedE6 q).Valid)
    {L : Type} [Group L] [Finite L] (hs : IsSimpleGroup L) (hna : ∃ a b : L, a * b ≠ b * a)
    (e : L ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  exfalso
  by_cases hp3 : q.p = 3
  · have hd : CFSG.AGLEmbedding.IsExceptionalIndex ⟨.twistedE6 q, hv⟩ :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))))
    have := hs.toNontrivial
    obtain ⟨T⟩ : Nonempty (Sylow 3 L) := inferInstance
    have hcore := CFSG.AGLEmbedding.charPGen3At_exceptional L hs hna ⟨.twistedE6 q, hv⟩ hd ⟨e⟩ 3
      Nat.prime_three (by norm_num) (by simp [hp3])
      (by rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> cases h) T
    have := three_le_pRank_of_glbCore_eq_top (L := L) Nat.prime_three hcore
    omega
  · have : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩) :=
      Finite.of_equiv L e.toEquiv
    obtain ⟨-, E, hE, hc⟩ := CFSG.LieType.SeitzGeneration.exists_isElemAbelian_card_of_not_rankLE2
      Nat.prime_three
      (CFSG.LieType.SeitzGeneration.not_rankLE2_cat_twistedE6_three q hv (Ne.symm hp3))
    have := three_le_pRank_of_equiv e (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc)
    omega

theorem k33Models_suzuki
    {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  exfalso
  have hc : Nat.Coprime 3 (Nat.card L) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.LieType.SeitzGeneration.card_cat_suzuki_coprime_three hv
  have h3 : ¬ 3 ^ (0 + 1) ∣ Nat.card (⊤ : Subgroup L) := by
    rw [Subgroup.card_top, zero_add, pow_one]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc
  have := CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := ⊤) Nat.prime_three h3
  omega

theorem k33Models_reeG2
    {m : ℕ} (hv : (LieTypeIndex.reeG2 m).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.reeG2 m, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  exfalso
  obtain ⟨-, h3, hr⟩ := CFSG.SectionRank.smallReeModel_rank
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩)
  omega

section ReeTits


theorem k33Models_reeF4 {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩) :
    K33Models L :=
  K33Models.of_twistedF4 (f := 2 * m + 1)
    (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, reeTitsModel_reeF4_of_lie hv e⟩)))

theorem k33Models_tits (hv : LieTypeIndex.tits.Valid) {L : Type} [Group L] [Finite L]
    (e : L ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩) : K33Models L :=
  K33Models.of_tits
    (Or.inr (Or.inr (Or.inl ⟨rfl, by decide,
      CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩⟩)))

end ReeTits

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
