module

public import CFSG.Sporadic.ON
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.TwoCoverCensusResidual
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped Pointwise

theorem factorization_three_card_onan : (460815505920 : ℕ).factorization 3 = 4 := by
  rw [show (460815505920 : ℕ) = 3 ^ 4 * 5689080320 by norm_num,
    Nat.factorization_mul (show (3 : ℕ) ^ 4 ≠ 0 by norm_num)
      (show (5689080320 : ℕ) ≠ 0 by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 5689080320 by norm_num), add_zero]

theorem sylow_three_comm_of_ON
    {S : Type} [Group S] [Finite S] (e : S ≃* Spor .ONan) :
    ∀ P : Sylow 3 S, ∀ a b : S, a ∈ (P : Subgroup S) → b ∈ (P : Subgroup S) → a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have hS : Nat.card S = 460815505920 :=
    (Nat.card_congr (e.toEquiv.trans β.toEquiv.symm)).trans CFSG.Sporadic.ON.card_ON
  have hfac : (Nat.card S).factorization 3 = 4 := by
    rw [hS]
    exact factorization_three_card_onan
  have hrank : CFSG.pRank 3 S = CFSG.pRank 3 (Spor .ONan) := CFSG.pRank_congr_of_mulEquiv e 3
  have h3 : 3 < CFSG.pRank 3 S := by
    rw [hrank]
    exact Census.SporadicTwoCover.three_lt_pRank_onan
  obtain ⟨E, hE, hEc⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434Spor.exists_elemAbelian_sylow_of_three_lt_pRank h3 hfac
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  let Q : Sylow 3 S := Sylow.ofCard E hEc
  have hQ : (Q : Subgroup S) = E := rfl
  haveI : Finite (Sylow 3 S) := Sylow.finite_of_finiteIndex Q
  intro P a b ha hb
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q P
  have hPg : (P : Subgroup S) = MulAut.conj g • E := by
    rw [← hg, Sylow.coe_subgroup_smul, hQ]
  have key : ∀ m ∈ (P : Subgroup S), ∃ x ∈ E, m = g * x * g⁻¹ := by
    intro m hm
    rw [hPg] at hm
    obtain ⟨x, hx, hxm⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hm
    exact ⟨x, hx, by rw [← hxm]; rfl⟩
  obtain ⟨x, hx, rfl⟩ := key a ha
  obtain ⟨y, hy, rfl⟩ := key b hb
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [hEcomm x hx y hy]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
