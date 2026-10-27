module

public import CFSG.RankThree.PartOne.SEITZ2.Narrow
public import CFSG.RankThree.PartOne.SEITZ2.G2F2Main
public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Small
public import CFSG.RankThree.PartOne.SEITZ7.D4Wire
public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.RankThree.PartOne.SEITZ8.D4TwoMain
public import CFSG.RankThree.PartOne.SEITZ10.U5Field
public import CFSG.RankThree.PartOne.SEITZ10.SzMain
public import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
public import CFSG.RankThree.PartOne.SEITZU49.Main
public import CFSG.RankThree.PartOne.SEITZU49.FourMain
public import CFSG.RankThree.PartOne.SEITZ3.D4Assembly
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxDone

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.RankThree.PartOne.CTP

@[expose] def Exc2F4NonsplitPhi4 : Prop :=
  ∀ m : ℕ, ExtSeitzAtInnerFor (.reeF4 m) fun p => p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1

@[expose] def Exc2F4NonsplitPhi2 : Prop :=
  ∀ m : ℕ, ExtSeitzAtInnerFor (.reeF4 m) fun p => p ∣ 2 ^ (2 * m + 1) + 1

section Planes2F4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag TauCeti CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.SEITZ3
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem exc2F4Nonsplit_of_phi4_phi2 (h4 : Exc2F4NonsplitPhi4) (h2 : Exc2F4NonsplitPhi2) :
    Exc2F4Nonsplit := by
  intro m K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hinner
  have : Fact p.Prime := ⟨hp⟩
  by_cases h3 : p ∣ 2 ^ (2 * m + 1) + 1
  · exact h2 m K hnab hiso p hp hp5 hpd h3 E hE hcard hinner
  by_cases h4' : p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1
  · exact h4 m K hnab hiso p hp hp5 hpd h4' E hE hcard hinner
  left
  exfalso
  have hinj := conj_injective_of_simple hnab
  obtain ⟨hE₁, hmap⟩ := inner_preimage_data (p := p) hinj E hinner
  set E₁ := E.comap (MulAut.conj : K →* MulAut K) with hE₁def
  have hcard₁ : Nat.card E₁ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hcard
  obtain ⟨X, _, _, _, -, hX, ⟨e⟩⟩ := CFSG.RankThree.PartOne.SEITZX.exists_reeGamma_model hiso
  have : Finite (ModGL F4.tag X) := finite_modGL
  have : Finite (F4.reeGamma X m) := Subtype.finite
  have hdvd : p ∣ Nat.card (F4.reeGamma X m) := by
    have h0 := Subgroup.card_subgroup_dvd_card E₁
    rw [hcard₁, Nat.card_congr e.toEquiv] at h0
    exact (dvd_pow_self p two_ne_zero).trans h0
  have h5 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt E₁ hE₁ hcard₁
  have h6 := CFSG.RankThree.PartOne.pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e
  rcases (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    m X hX).2 p hp (by omega) hdvd with h7 | h7 | h7 | h7 | h7
  · exact hP h7
  · exact h3 h7
  · exact h4' h7
  · have := CFSG.RankThree.PartOne.K128.pRank_le_one_ree_phi6 hX hp hp5 h7
    omega
  · have := CFSG.RankThree.PartOne.K128.pRank_le_one_ree_phi12 hX hp hp5 h7
    omega

end Planes2F4

section

@[expose] def SeitzExceptionalFineOdd : Prop :=
  SEITZ3.Exc3D4NonsplitPhi3Phi6 ∧ Exc2F4NonsplitPhi4 ∧ Exc2F4NonsplitPhi2

@[expose] def SeitzFieldAutFineOdd : Prop :=
  SubfieldPairReeF4

@[expose] def SeitzResidualFinePairOdd : Prop :=
  SeitzFieldAutFineOdd ∧ SeitzExceptionalFineOdd

end

section

theorem seitzFieldAutFineNarrow_of_odd (h : SeitzFieldAutFineOdd) : SeitzFieldAutFineNarrow :=
  ⟨subfieldPairOmega8mSmall, subfieldPairG2_of_f2 subfieldPairG2F2,
    SEITZ8.subfieldPairD4_of_two SEITZ8.subfieldPairD4Two_holds, SEITZ10.subfieldPairSz_holds, h⟩

theorem seitzExceptionalFine_of_odd (h : SeitzExceptionalFineOdd) : SeitzExceptionalFine :=
  ⟨SEITZ11.excG2Nonsplit_qplus (SEITZ6.maxSL2SL2G2_of_top CFSG.Goldschmidt.topStatement),
    SEITZ3.exc3D4Nonsplit_of_narrow ⟨SEITZ7.max3D4A1A1Big_of_certificates, h.1⟩,
    exc2F4Nonsplit_of_phi4_phi2 h.2.1 h.2.2⟩

theorem seitzResidual_of_fine_pair_odd
    (h : SeitzResidualFinePairOdd) : SeitzResidual :=
  seitzResidual_of_fine ⟨seitzFieldAutFine_of_narrow (seitzFieldAutFineNarrow_of_odd h.1),
    SEITZ10.seitzUnitaryFiveFine_of_diag49 (SEITZU49.psu5DiagPlane49_of_four
        SEITZU49.gen49Four_holds),
    seitzExceptionalFine_of_odd h.2⟩

end

end CFSG.RankThree.PartOne.SEITZ2
