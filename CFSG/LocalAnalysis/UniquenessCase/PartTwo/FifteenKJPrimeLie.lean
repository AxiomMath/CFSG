module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
import CFSG.Adapters.StatedSLPerfect
import CFSG.Open.StatedZModTwo
import CFSG.LieType.ChevTwo.OrthogonalBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyOddTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem s15k_jp_projEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (hK : Nat.card K = 2) (H : Subgroup (GL ι K)) : Nonempty (StatedProj H ≃* H) := by
  have hbot : (StatedScalars ι K).subgroupOf H = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK ι, Subgroup.bot_subgroupOf]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot⟩

theorem s15k_jp_sl_three_le {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    {n : ℕ} (hn : 3 ≤ n) (h : BinaryNaturalSL J R ⊥ n 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  obtain ⟨K, hF, hfin, hcard, hreal⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  obtain ⟨hidx, ⟨e⟩, hreal'⟩ :=
    s15k_jp_nat_perfect (CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hn K) hreal
  obtain ⟨f⟩ := s15k_jp_projEquiv hK2 (StatedSL n K)
  refine ⟨hidx.le.trans (by norm_num), Or.inl (Or.inl ⟨n, hn, ?_, K, hF, hfin, hcard, hreal'⟩)⟩
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by omega,
    fun h => absurd (congrArg Prod.fst h) (by omega),
    fun h => absurd (congrArg Prod.fst h) (by omega)⟩,
    K, hF, hfin, hcard, ⟨e.trans f.symm⟩⟩

theorem s15k_jp_sp_six_le {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    {n : ℕ} (hn : 6 ≤ n) (h : NatSpn J R ⊥ n 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  obtain ⟨hev, K, hF, hfin, hcard, hreal⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have hperf : Group.IsPerfect ↥(StatedSp (n / 2) K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp (n / 2) K
      (Or.inr (Or.inr ⟨hK2, by omega⟩))
  obtain ⟨hidx, ⟨e⟩, hreal'⟩ := s15k_jp_nat_perfect hperf hreal
  exact ⟨hidx.le.trans (by norm_num), Or.inl (Or.inr (Or.inl ⟨n, hn, ⟨hev, K, hF, hfin, hcard,
    ⟨e⟩⟩, hev, K, hF, hfin, hcard, hreal'⟩))⟩


theorem s15k_jp_isometryCore_quadPlus_equiv {K : Type} [Field K] [Finite K] (n : ℕ)
    (hK : Nat.card K = 2) :
    Nonempty (↥(CFSG.MatrixModel.isometryCore (StatedQuadPlus n K)) ≃*
      ↥(CFSG.MatrixModel.isometryCore (StatedQuadPlus n (ZMod 2)))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hmap := CFSG.ClassicalInvolution.Upgrade.map_closure_preserving
    (QK := StatedQuadPlus n K) (QL := StatedQuadPlus n (ZMod 2)) e
    (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp e v)
  exact ⟨((CFSG.Adapters.RankTwoModelTransports.glCongr e).subgroupMap _).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem s15k_jp_commutator_index_plus {m : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    (commutator ↥(CFSG.MatrixModel.isometryCore (StatedQuadPlus m K))).index = 2 := by
  obtain ⟨e⟩ := s15k_jp_isometryCore_quadPlus_equiv m hK
  rw [s15k_jp_commutator_index_congr e]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 := (CFSG.LieType.ChevTwo.goodQ_plus (n := k) (by omega)).relIndex_eq
  rw [CFSG.LieType.ChevTwo.statedOmega_eq_commutator,
    CFSG.LieType.ChevTwo.isoGrp_eq_isometryCore] at h1
  rw [← s15k_jp_subgroupOf_commutator]
  exact h1

theorem s15k_jp_commutator_index_minus {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K]
    {b c : K} (hK : Nat.card K = 2) (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (commutator ↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c))).index = 2 := by
  obtain ⟨e⟩ := s16c167_isometryCore_quadMinus_equiv m hK hpoly
  rw [s15k_jp_commutator_index_congr e]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 := (CFSG.LieType.ChevTwo.goodQ_minus (n := k) (by omega)).relIndex_eq
  rw [CFSG.LieType.ChevTwo.statedOmega_eq_commutator,
    CFSG.LieType.ChevTwo.isoGrp_eq_isometryCore] at h1
  rw [← s15k_jp_subgroupOf_commutator]
  exact h1

theorem s15k_jp_orth_plus {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    {n : ℕ} (hn : 6 ≤ n) (h : NatOrthPlus J R ⊥ n 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  obtain ⟨hev, K, hF, hfin, hcard, hreal⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  obtain ⟨hidx, ⟨e⟩, hreal'⟩ := s15k_jp_nat_derived hreal
  obtain ⟨f⟩ := s15k_jp_projEquiv hK2 (StatedOmega (StatedQuadPlus (n / 2) K))
  refine ⟨?_, Or.inl (Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨hev, K, hF, hfin, hcard,
    ⟨e.trans f.symm⟩⟩, hev, K, hF, hfin, hcard, hreal'⟩)))⟩
  rw [hidx, s15k_jp_commutator_index_plus (by omega) hK2]

theorem s15k_jp_orth_minus {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    {n : ℕ} (hn : 6 ≤ n) (h : NatOrthMinus J R ⊥ n 1) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  obtain ⟨hev, K, hF, hfin, hb, hc, hcard, hpoly, hreal⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  obtain ⟨hidx, ⟨e⟩, hreal'⟩ := s15k_jp_nat_derived hreal
  obtain ⟨f⟩ := s15k_jp_projEquiv hK2 (StatedOmega (StatedQuadMinus (n / 2) K hb hc))
  refine ⟨?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨hev, K, hF, hfin, hb, hc, hcard,
    hpoly, ⟨e.trans f.symm⟩⟩, hev, K, hF, hfin, hb, hc, hcard, hpoly, hreal'⟩))))⟩
  rw [hidx, s15k_jp_commutator_index_minus (by omega) hK2 hpoly]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
