module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusStructure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjointSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaPlus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem not_isL2_and_isL2Square_of_b_eq {b n : ℕ} (hn : 1 ≤ n) (hb : 1 ≤ b)
    (h : 2 ^ b * (2 ^ (2 * b) - 1) = 2 ^ (2 * n) * (2 ^ (2 * n) - 1) ^ 2) : False := by
  have hodd1 : Odd (2 ^ (2 * b) - 1) :=
    CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have hodd2 : Odd ((2 ^ (2 * n) - 1) ^ 2) :=
    (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)).pow
  have hb2n : b = 2 * n :=
    CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hodd1 hodd2 h
  have heq2 : 2 ^ (2 * b) - 1 = (2 ^ (2 * n) - 1) ^ 2 := by
    rw [hb2n] at h ⊢
    exact Nat.mul_left_cancel (n := 2 ^ (2 * n)) (by positivity) h
  have hb4n : 2 * b = 4 * n := by omega
  rw [hb4n,
    show 2 ^ (4 * n) = (2 ^ (2 * n)) ^ 2 by rw [← pow_mul]; congr 1; omega] at heq2
  have hq : 4 ≤ 2 ^ (2 * n) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 : 1 ≤ (2 ^ (2 * n)) ^ 2 := by
    have : 0 < (2 ^ (2 * n)) ^ 2 := by positivity
    omega
  have hq2 : 1 ≤ 2 ^ (2 * n) := by
    have : 0 < 2 ^ (2 * n) := by positivity
    omega
  have heqZ : ((2 : ℤ) ^ (2 * n)) ^ 2 - 1 = ((2 : ℤ) ^ (2 * n) - 1) ^ 2 := by
    have h' := congrArg (fun x : ℕ => (x : ℤ)) heq2
    simpa only [Nat.cast_sub hq1, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one,
      Nat.cast_ofNat] using h'
  have hqZ : (4 : ℤ) ≤ (2 : ℤ) ^ (2 * n) := by exact_mod_cast hq
  nlinarith [heqZ, hqZ]

theorem not_isL2_and_isL2Square' {X : Type} [Group X] [Finite X] {b n : ℕ} (hn : 1 ≤ n)
    (hL2 : IsL2 X b) (hSq : IsL2Square X n) : False :=
  not_isL2_and_isL2Square_of_b_eq hn hL2.admissible.2.1
    ((S17.card_of_isL2 hL2).symm.trans (S17.card_of_isL2Square_eq hSq))

theorem not_isOmegaMinus_of_isOmegaPlus {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hP : IsOmegaPlus X 4 n) (hM : IsOmegaMinus X 4 n) : False := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  exact not_isL2_and_isL2Square' hn1 (isL2_two_mul_of_isOmegaMinus_four hn1 hM)
    (isL2Square_of_isOmegaPlus hn hP)

theorem mem_calB1_of_mem_calB {T M L B : Subgroup G} (hB : B ∈ calB T M L) :
    B ∈ calB1 T M L := by
  have hB0 := hB
  obtain ⟨hBL, hBcyc, -, hBodd, hBperm, hBinv⟩ := hB
  haveI : IsCyclic ↥B := hBcyc
  refine ⟨hBL, IsCyclic.isMulCommutative, B, ⊥, hB0, ?_, ?_, ?_, ?_, hBperm, hBinv, ?_⟩
  · exact IsMulCommutative.of_comm fun _ _ => Subsingleton.elim _ _
  · simpa using hBodd
  · intro p hp hdvd
    rw [Subgroup.card_bot] at hdvd
    exact (hp.not_dvd_one hdvd).elim
  · exact (sup_bot_eq B).symm
  · intro p hp hdvd
    rw [Subgroup.card_bot] at hdvd
    exact (hp.not_dvd_one hdvd).elim

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem n_eq_of_isOmegaPlus (c : Ctx23L D Ch) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h52 : S23_5_2 D Ch) (h1930 : H1930 D)
    (hP : IsOmegaPlus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) :
    c.n = CFSG.Open.pRank 2 D.Z ∧ 3 ≤ CFSG.Open.pRank 2 D.Z := by
  have hn3c : 3 ≤ c.n := uc22p20g_hn3_of hE D Ch h207 h1930 c.toCtx23.toCtx21
  rcases h52 h1930 c with h | ⟨-, hOm, hn2⟩
  · exact ⟨h, h ▸ hn3c⟩
  · have hn : 2 ≤ CFSG.Open.pRank 2 D.Z := by omega
    exact (not_isOmegaMinus_of_isOmegaPlus hn hP hOm).elim

private theorem omegaPlus_of_isNaturalClassicalModule (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural) (hS : KSchurL2) (hS3 : KSchurSL3)
    (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch) (hN3 : S23_9_NotLarge D Ch)
    (h1930 : H1930 D) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hP : IsOmegaPlus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) :
    IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) := by
  have hnat0 := hnat
  have hn1 : 1 ≤ CFSG.Open.pRank 2 D.Z := le_trans (by norm_num) hn3
  have hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z := le_trans (by norm_num) hn3
  have hbotH : CFSG.pCore 2 (c.H hV) = ⊥ := hK.1 hnat
  have hsq : IsL2Square (Bar2 c.L) (CFSG.Open.pRank 2 D.Z) :=
    isL2Square_of_isOmegaPlus hn2 hP
  have h1 := hN1 h1930 c hn3 hV
  have h2' := hN2 h1930 c hn3 hV
  have h3' := hN3 h1930 c hn3 hV
  rcases hnat with ⟨hL2, -⟩ | ⟨hMinus4, -⟩ | ⟨hPlus4, hNatPlus4⟩ | ⟨hSp4, hNatSp4⟩ |
    ⟨hSL3, -⟩ | ⟨a, ha, hSU4, hNatSU4⟩ | ⟨hOm6, hNatOm6⟩ | ⟨hSL4, hBin4⟩ |
    ⟨hOp6, hNatOp6⟩ | ⟨hSp6, hNatSp6⟩ | ⟨hO8, hNatO8⟩
  · have hshape : IsL2 (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV))
        (CFSG.Open.pRank 2 D.Z) := isL2_quotientPCore_of_isL2 hL2 hbotH
    obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv hV hK hnat0 hS (Or.inl hshape)
    exact (not_isL2_and_isL2Square' hn1
      (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2) hsq).elim
  · obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv hV hK hnat0 hS
      (Or.inl (isL2_quotientPCore_of_isL2
        (isL2_two_mul_of_isOmegaMinus_four hn1 hMinus4) hbotH))
    exact (not_isOmegaMinus_of_isOmegaPlus hn2 hP
      (IsOmegaMinus.of_mulEquiv e.symm hMinus4)).elim
  · exact ⟨hPlus4, hNatPlus4⟩
  · exact (h1 (Or.inl ⟨hSp4, hNatSp4⟩)).elim
  · obtain ⟨e⟩ := nonempty_bar2_mulEquiv_H_of_isSLn c hV hK hnat0 hS3 hSL3 hn3
    exact (not_isL2Square_of_isSLn_three hSL3 (IsL2Square.of_mulEquiv e hsq)).elim
  · exact (h1 (Or.inr (Or.inl ⟨a, ha, hSU4, hNatSU4⟩))).elim
  · exact (h1 (Or.inr (Or.inr ⟨hOm6, hNatOm6⟩))).elim
  · exact (h3' (Or.inl ⟨hSL4, hBin4⟩)).elim
  · exact (h2' ⟨hOp6, hNatOp6⟩).elim
  · exact (h3' (Or.inr (Or.inl ⟨hSp6, hNatSp6⟩))).elim
  · exact (h3' (Or.inr (Or.inr ⟨hO8, hNatO8⟩))).elim

theorem exists_natOmegaPlus (c : Ctx23L D Ch) (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch)
    (h4 : S23_4 D Ch) (hK : KOrdNatural) (hS : KSchurL2) (hS3 : KSchurSL3)
    (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch) (hN3 : S23_9_NotLarge D Ch)
    (h1930 : H1930 D) (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hP : IsOmegaPlus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) :
    ∃ hV : IsElemAbelian 2 c.V,
      IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaPlus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) := by
  obtain ⟨hV, hnat⟩ := Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
  exact ⟨hV, omegaPlus_of_isNaturalClassicalModule c hV hK hS hS3 hN1 hN2 hN3 h1930 hn3
    hnat hP⟩

theorem ker_phiL_of_omegaPlus (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    (hS : KSchurL2) (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hP : IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z)) :
    (c.phiL hV).ker = CFSG.pCore 2 ↥c.L := by
  have hsq : IsL2Square ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) :=
    (isOmegaPlus_four_iff_isL2Square hn2).mp hP
  have hshape : IsL2Square (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV))
      (CFSG.Open.pRank 2 D.Z) :=
    isL2Square_quotientPCore_of_isL2Square hsq (hK.1 hnat)
  exact (comap_pCore_eq_of_pCore_eq_bot (c.phiL hV) (c.phiL_surjective hV)
    (c.commutator_L_eq_top) (c.phiL_ker_commutator_mem_pCore hV hK hnat) hS
    (Or.inr hshape) (hK.1 hnat)).1

theorem inf_centralizer_V_le_pCoreOf (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) (hS : KSchurL2) (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hP : IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z)) :
    c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L := by
  change c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ (CFSG.pCore 2 ↥c.L).map c.L.subtype
  rw [← c.ker_phiL_of_omegaPlus hV hK hS hn2 hnat hP]
  intro x hx
  exact Subgroup.mem_map.mpr
    ⟨⟨x, hx.1⟩, (c.phiL_eq_one_iff hV ⟨x, hx.1⟩).2 hx.2, rfl⟩

@[expose] noncomputable def e₀ (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    (hS : KSchurL2) (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hP : IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z)) :
    Bar2 c.L ≃* ↥(c.H hV) :=
  (QuotientGroup.quotientMulEquivOfEq
    (c.ker_phiL_of_omegaPlus hV hK hS hn2 hnat hP).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (c.phiL hV) (c.phiL_surjective hV))

theorem e₀_mk (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural)
    (hS : KSchurL2) (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hP : IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z)) (x : ↥c.L) :
    c.e₀ hV hK hS hn2 hnat hP (QuotientGroup.mk x) = c.phiL hV x :=
  rfl

theorem omegaPlusFrame_of (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hA : KTab23a)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hP : IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z))
    (hNat : NatOmegaPlus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) :
    OmegaPlusFrame (c.H hV) (CFSG.Open.pRank 2 D.Z) (c.sylowStar hV) (c.Tstar hV) := by
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) :=
    Or.inr (Or.inr (Or.inl ⟨hP, hNat⟩))
  refine ⟨hn2, hNat, c.Tstar_le_normalizer hV, c.isPGroup_Tstar hV,
    c.sylowStar_le_Tstar hV, ?_⟩
  intro t ht w hw
  have hwZ : w ∈ c.Ztil hV := by
    have hfix := c.fixV_sylowStar_eq_Ztil hV hA hnat h4 h1930
    rw [hfix] at hw
    exact hw
  obtain ⟨t', rfl⟩ := (c.mem_Tstar_iff hV t).1 ht
  rw [Ctx23L.Ztil, mem_imgTil] at hwZ
  obtain ⟨v, hvZ, rfl⟩ := hwZ
  rw [show c.phiT hV t' =
      actTil (⊥ : Subgroup G) c.V hV ⟨t', c.T_le_stabTil t'.2⟩ from rfl,
    actTil_mk, mkTil_eq_iff, Subgroup.mem_bot, actStab_apply_val]
  have hcent : (t' : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_omegaOneCenterIn D.T t'.2
  have hcomm : (t' : G) * v.val * (t' : G)⁻¹ = v.val := by
    have hc := (Subgroup.mem_centralizer_iff.mp hcent) v.val hvZ
    calc (t' : G) * v.val * (t' : G)⁻¹ = v.val * (t' : G) * (t' : G)⁻¹ := by rw [← hc]
      _ = v.val := by group
  rw [hcomm, mul_inv_cancel]

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
