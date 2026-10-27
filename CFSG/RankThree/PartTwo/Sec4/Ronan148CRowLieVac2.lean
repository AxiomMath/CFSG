module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankTwo
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRow

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.RankThreeEven (projSp)

theorem rowSOf148_seven_Sp4_of (n : ℕ) (hn : 1 ≤ n) (h3n : ¬ 3 ∣ n) :
    RowSOf148 (projSp 2 (GaloisField 2 n)) := by
  refine rowSOf148_of_autNoE27 fun S _ _ hs hna ⟨eS⟩ => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hF
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  set τ : S ≃* StatedProj (StatedSp 2 F) :=
    eS.trans (CFSG.PGLModel.projSpEquivStatedProj 2 F) with hτ
  have hnaP : ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨τ a, τ b, fun h => hab (τ.injective (by rw [map_mul, map_mul, h]))⟩
  have hsP : IsSimpleGroup (StatedProj (StatedSp 2 F)) := τ.symm.isSimpleGroup
  have hZ : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ :=
    center_eq_bot_of_isSimpleGroup hsP hnaP
  have h3F : ¬ 3 ∣ Nat.card F := by
    rw [hFcard]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hinn : ∀ α : MulAut (StatedProj (StatedSp 2 F)), α ^ 3 = 1 →
      α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ := by
    intro α hα3
    by_cases hD : α ∈ (conjAut 2 F).range
    · obtain ⟨H, rfl⟩ := hD
      exact conjAut_mem_inner_of_charTwo H
    · exfalso
      obtain ⟨φ, hφ, -⟩ := sp4_even_order_three_field_descent α hα3 hD
      exact h3n (eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two hn hFcard hφ).1
  exact (autNoE27_of_forall_inner hinn hZ (fun D hD =>
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.noE27_projSp_two h3F
      ⟨D, hD.1, hD.2⟩)).of_mulEquiv τ

section G2


theorem rowSOf148_seven_G2_of : ∀ q : TauCeti.PrimePower, q.p = 2 → ¬ 3 ∣ q.exponent →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
      RowSOf148 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro q hq2 h3n hq
  refine rowSOf148_of_autNoE27 fun S _ _ hs hna ⟨e⟩ => ?_
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hq).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  obtain ⟨F, _, _, hF, ⟨eA⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hq hq2 e
  rw [hq2] at hF h3
  have hn : 2 ≤ q.exponent := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have eC : AdjointQuotient .G2 F ≃* adjointGroup .G2 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .G2) (K := F))).trans
      QuotientGroup.quotientBot
  set τ : S ≃* adjointGroup .G2 F := eA.trans eC with hτ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar F = 2 := by
    have := Fintype.ofFinite F
    have hp : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card, hF])
    exact ringChar.eq F 2
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hn
  have h3F : ¬ 3 ∣ Nat.card F := by
    rw [hF]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hZ : Subgroup.center (adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  have hinn : ∀ α : MulAut (adjointGroup .G2 F), α ^ 3 = 1 →
      α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ := by
    intro α hα3
    by_contra hin
    have hchar3 : ringChar F ≠ 3 := by rw [hchar]; norm_num
    obtain ⟨φ, hφ, -⟩ := g2_order_three_field_descent hchar3 h4 hα3 hin
    exact h3n (eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF hφ).1
  exact (autNoE27_of_forall_inner hinn hZ (fun D hD =>
    CFSG.HardMathSupport.Dickson.Sec6.I1431.noE27_adjointG2 F h3F ⟨D, hD.1, hD.2⟩)).of_mulEquiv τ

end G2

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
