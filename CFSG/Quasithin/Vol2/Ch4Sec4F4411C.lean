module

public import CFSG.Quasithin.Vol2.Ch4Sec4F4411B
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.Quasithin.H13.Ch4.E443.F4411

open Subgroup
open scoped MatrixGroups

theorem perfCentral_of_isPSL_two {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    {n : ℕ} (h : IsPSL 2 2 n K) : PerfCentral (K ⧸ center K) := by
  have hn : 2 ≤ n := by
    obtain ⟨⟨-, hn1, -, h22, -⟩, -⟩ := h
    by_contra hlt
    obtain rfl : n = 1 := by omega
    exact h22 rfl
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField K 2 2 n h
  have : Finite PSL(2, GaloisField 2 n) := Finite.of_equiv K e.toEquiv
  have : IsSimpleGroup PSL(2, GaloisField 2 n) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  exact perfCentral_quot_of_mulEquiv hK e
    (perfCentral_of_fusionBenderBorel (CFSG.Open.bender_psl2_borel_full n hn))

theorem perfCentral_of_isSz {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    {n : ℕ} (h : IsSz n K) : PerfCentral (K ⧸ center K) := by
  obtain ⟨a, ha, ⟨e⟩⟩ :=
    CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel h
  have hSz : CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a = CFSG.Open.Sz a :=
    (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a).symm.trans (by
      simp only [CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators, CFSG.Open.Sz,
        CFSG.Open.SzGenerators])
  have : IsSimpleGroup (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
    (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 a ha).1
  have : Finite (CFSG.Open.Sz a) :=
    Finite.of_equiv K (e.trans (MulEquiv.subgroupCongr hSz)).toEquiv
  exact perfCentral_quot_of_mulEquiv hK e (perfCentral_of_mulEquiv (MulEquiv.subgroupCongr hSz)
    (perfCentral_of_fusionBenderBorel (CFSG.Open.bender_suzuki_borel_full a ha)))

theorem perfCentral_of_isSU3 {K : Type} [Group K] [Finite K] (h : IsSU3 8 K) :
    PerfCentral (K ⧸ center K) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have hF' : Nat.card F = (2 ^ 3) ^ 2 := by rw [hF]; norm_num
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 6) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  obtain ⟨-, hc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
    (f := 3) (n := 3) hF' le_rfl (by decide)
  obtain ⟨e'⟩ :=
    CFSG.RankTwoShapes.nonempty_statedProj_statedSU_equiv_PSU3Model F 3 (by norm_num) hF'
  have hPSU : CFSG.Theory.Comparator.PSU3Model 3 = CFSG.Open.PSU3 2 3 := by
    simp only [CFSG.Open.PSU3, CFSG.Theory.Comparator.PSU3Model]
  let eK : K ⧸ center K ≃* CFSG.Open.PSU3 2 3 :=
    ((QuotientGroup.congr (center K) _ e (Subgroup.map_center_eq e)).trans
      (QuotientGroup.quotientMulEquivOfEq hc)).trans (e'.trans (MulEquiv.subgroupCongr hPSU))
  have : Finite (CFSG.Open.PSU3 2 3) := Finite.of_equiv _ eK.toEquiv
  exact perfCentral_of_mulEquiv eK
    (perfCentral_of_fusionBenderBorel (CFSG.Open.bender_psu3_borel_full 3 (by norm_num)))

end CFSG.Quasithin.H13.Ch4.E443.F4411
