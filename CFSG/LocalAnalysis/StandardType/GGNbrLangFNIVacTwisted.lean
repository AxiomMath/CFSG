module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacDefs
import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGFieldExc
import CFSG.LocalAnalysis.StandardType.MarkingSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwB2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsSympA6
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
import CFSG.LieType.Simplicity.TitsModel
import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec4.Item426A6
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec8.Steps
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import CFSG.Walter.W67.Statements

public section

namespace CFSG.StandardType

open CFSG.Assembly


open CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.Quasithin.G2U

private theorem l02qf3_recTwF4_deg {a j : ℕ} (hj : j = 2 * a + 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeTwF4 a Q) : LargeEvenRecipeTwF4 a (DegCont j Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun f hf => ?_⟩
  have hK' : Nat.card K = 2 ^ j := hK.trans (by rw [hj])
  have h1 := chevField_orderOf_dvd LargeEvenCartanF4 K (LargeEvenTwF4H a K)
    (fun σ h hh => CFSG.LocalAnalysis.GLTheoremA.YS09Field.twF4H_map_mem K a σ h hh) f hf
  rwa [natCard_ringEquiv_of_card hK'] at h1

private theorem l02qf3_alt6_nonabelian :
    ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    fun h => ?_⟩
  have := congrArg (fun σ : alternatingGroup (Fin 6) => (σ : Equiv.Perm (Fin 6)) 0) h
  revert this
  decide

private theorem l02qf3_twistedH_simple (t : CFSG.Blueprint.Chevalley.TwistTag) (n : ℕ) (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ t.order) (σ : K ≃+* K)
    (hσ : ∀ c : K, σ c = c ^ 2 ^ n) :
    IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n)) ∧
      ∃ a b : LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n),
        a * b ≠ b * a := by
  obtain ⟨hperf, -, hHG, -, -⟩ :=
    CFSG.LieType.Chevalley.finite_fixed_root_group_perfect t Nat.prime_two hn K hK
      σ.toRingHom hσ
  obtain ⟨hsimpleG, hnaG⟩ :=
    CFSG.LieType.Chevalley.isSimpleGroup_graphFixedRootGroup_of_perfect t K σ hperf
  haveI : IsSimpleGroup (CFSG.LieType.Chevalley.graphFixedRootGroup t K σ.toRingHom) := hsimpleG
  have hcenterG : Subgroup.center (CFSG.LieType.Chevalley.graphFixedRootGroup t K σ.toRingHom) = ⊥ :=
    CFSG.ComponentClassification.ExcSelector.center_eq_bot_of_isSimpleGroup' hnaG
  have eSub : ↥⁅CFSG.Blueprint.twistedFixedGroup t K σ.toRingHom,
      CFSG.Blueprint.twistedFixedGroup t K σ.toRingHom⁆ ≃*
      ↥(CFSG.LieType.Chevalley.graphFixedRootGroup t K σ.toRingHom) :=
    MulEquiv.subgroupCongr hHG
  have eD : CFSG.Blueprint.DerivedCentralQuotient
      (CFSG.Blueprint.twistedFixedGroup t K σ.toRingHom) ≃*
      ↥(CFSG.LieType.Chevalley.graphFixedRootGroup t K σ.toRingHom) :=
    (QuotientGroup.congr _ _ eSub (Subgroup.map_center_eq eSub)).trans
      ((QuotientGroup.quotientMulEquivOfEq hcenterG).trans QuotientGroup.quotientBot)
  obtain ⟨eR⟩ := centerQuot_twistedH_equiv (K := K) t n σ.toRingHom hσ
  let e := eR.trans eD
  exact ⟨e.isSimpleGroup, nonabelian_of_mulEquiv e.symm hnaG⟩

private theorem l02qf3_twE6_simple (n : ℕ) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) ∧
      ∃ a b : LargeEvenCenterQuot
        (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n), a * b ≠ b * a := by
  have hK' : Nat.card K = 2 ^ (n * 2) := by rw [hK, pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK'
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c : K, σ c = c ^ 2 ^ n := fun c => by
    simp only [σ, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  exact l02qf3_twistedH_simple CFSG.Blueprint.Chevalley.TwistTag.E6 n hn (K := K) hK σ hσ

private theorem l02qf3_triD4_simple (n : ℕ) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) :
    IsSimpleGroup
        (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) ∧
      ∃ a b : LargeEvenCenterQuot
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n), a * b ≠ b * a := by
  have hK' : Nat.card K = 2 ^ (n * 3) := by rw [hK, pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK'
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c : K, σ c = c ^ 2 ^ n := fun c => by
    simp only [σ, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  exact l02qf3_twistedH_simple CFSG.Blueprint.Chevalley.TwistTag.D4 n hn (K := K) hK σ hσ

private theorem l02qf3_g2der_simple {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) ∧
      ∃ a b : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), a * b ≠ b * a := by
  obtain ⟨e⟩ := CFSG.StandardType.TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
  have hs : IsSimpleGroup (CFSG.Open.StatedSU 3 3 F9) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1
      (CFSG.LinearGroups.UnitaryThreeOverNine.classicalModel_statedSU card_F9)).2
  have hnab : ∃ a b : CFSG.Open.StatedSU 3 3 F9, a * b ≠ b * a :=
    ⟨⟨CFSG.StandardType.TableBExcSmallRest.su3X,
        CFSG.StandardType.TableBExcSmallRest.su3X_mem⟩,
      ⟨CFSG.StandardType.TableBExcSmallRest.su3Y,
        CFSG.StandardType.TableBExcSmallRest.su3Y_mem⟩,
      fun h => CFSG.StandardType.TableBExcSmallRest.su3X_mul_su3Y_ne (congrArg Subtype.val h)⟩
  exact ⟨e.isSimpleGroup, nonabelian_of_mulEquiv e.symm hnab⟩

private theorem l02qf3_tits_simple {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) ∧
      ∃ a b : LargeEvenCenterQuot (LargeEvenTwF4H 0 K), a * b ≠ b * a := by
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨e⟩ := nonempty_titsQuot_equiv hK
  have hq := (CFSG.LieType.Simplicity.titsData K hK).isQuasisimple hK
  have hcenter : Subgroup.center
      ↥(commutator ↥(CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)) = ⊥ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.center_commutator_reeFixed_tits_eq_bot hK
  have eQ : (↥(commutator ↥(CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)) ⧸
      Subgroup.center ↥(commutator ↥(CFSG.LieType.Ree.reeFixed
        CFSG.LieType.Ree.ReeTag.F4 K 0))) ≃*
      ↥(commutator ↥(CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  haveI hsimpleQ : IsSimpleGroup
      (↥(commutator ↥(CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)) ⧸
        Subgroup.center ↥(commutator ↥(CFSG.LieType.Ree.reeFixed
          CFSG.LieType.Ree.ReeTag.F4 K 0))) := hq.2.1
  haveI hsimpleG : IsSimpleGroup
      ↥(commutator ↥(CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)) :=
    eQ.symm.isSimpleGroup
  exact ⟨e.isSimpleGroup, nonabelian_of_mulEquiv e.symm (nonabelian_of_mulEquiv eQ hq.2.2)⟩

theorem kgfni_fieldExponent_twisted : KGFNIFieldExponentOn KGFNITwistedLabel := by
  intro lab hlab hS
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ', hdvd⟩ :=
      recTwisted_deg (LargeEvenCartanE 6) LargeEvenRhoE6 2 n Q hQ
    exact ⟨K, hF, hfin, hK, hQ', fun f hf => orderOf_dvd_iff_pow_eq_one.mp (hdvd f hf)⟩
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ', hdvd⟩ :=
      recTwisted_deg LargeEvenCartanD4 LargeEvenRhoD4 3 n Q hQ
    exact ⟨K, hF, hfin, hK, hQ', fun f hf => orderOf_dvd_iff_pow_eq_one.mp (hdvd f hf)⟩
  ·
    obtain ⟨-, hodd, hn3⟩ := hlab.2
    have hj : n = 2 * ((n - 1) / 2) + 1 := by
      obtain ⟨k, rfl⟩ := hodd
      omega
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ', hdvd⟩ := recSuzuki_deg Q hj hQ
    refine ⟨K, hF, hfin, hK, hQ', fun f hf => ?_⟩
    simpa [kgfniFieldDegree] using orderOf_dvd_iff_pow_eq_one.mp (hdvd f hf)
  ·
    obtain ⟨-, hodd, hn3⟩ := hlab.2
    have hj : n = 2 * ((n - 1) / 2) + 1 := by
      obtain ⟨k, rfl⟩ := hodd
      omega
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ', hdvd⟩ := l02qf3_recTwF4_deg hj hQ
    refine ⟨K, hF, hfin, hK, hQ', fun f hf => ?_⟩
    simpa [kgfniFieldDegree] using orderOf_dvd_iff_pow_eq_one.mp (hdvd f hf)
  ·
    obtain ⟨-, hn1⟩ := hlab.2
    subst hn1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ', hdvd⟩ :=
      recSymplectic_deg (m := 2) (j := 1) (q := 2) rfl true Q hQ
    exact ⟨K, hF, hfin, hK, hQ', fun f hf => orderOf_dvd_iff_pow_eq_one.mp (hdvd f hf)⟩
  ·
    obtain ⟨-, hn1⟩ := hlab.2
    subst hn1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ', hdvd⟩ :=
      recChevalley_deg LargeEvenCartanG2 (j := 1) true Q hQ
    exact ⟨K, hF, hfin, hK, hQ', fun f hf => orderOf_dvd_iff_pow_eq_one.mp (hdvd f hf)⟩
  ·
    obtain ⟨-, hn1⟩ := hlab.2
    subst hn1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ', hdvd⟩ := l02qf3_recTwF4_deg (by norm_num : 1 = 2 * 0 + 1) hQ
    exact ⟨K, hF, hfin, hK, hQ', fun f hf => orderOf_dvd_iff_pow_eq_one.mp (hdvd f hf)⟩

theorem kgfni_rawSimple_twisted : KGFNIRawSimpleOn KGFNITwistedLabel := by
  intro lab hlab hS
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hF, hfin, hK, hQ', l02qf3_twE6_simple n hn hK⟩
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hF, hfin, hK, hQ', l02qf3_triD4_simple n hn hK⟩
  ·
    obtain ⟨-, hodd, hn3⟩ := hlab.2
    have hn3' : 3 ≤ n := by simpa using hn3
    have ha : 1 ≤ (n - 1) / 2 := by
      rw [Nat.one_le_div_iff (by norm_num : 0 < 2)]
      omega
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hF, hfin, hK, hQ', CFSG.LocalAnalysis.GLTheoremA.Y10GField.szQuot_simple ha hK⟩
  ·
    obtain ⟨-, hodd, hn3⟩ := hlab.2
    have hn3' : 3 ≤ n := by simpa using hn3
    have ha : 1 ≤ (n - 1) / 2 := by
      rw [Nat.one_le_div_iff (by norm_num : 0 < 2)]
      omega
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
    exact ⟨K, hF, hfin, hK, hQ',
      CFSG.LocalAnalysis.GLTheoremA.Y10GField.twF4Quot_simple ha hK⟩
  ·
    obtain ⟨-, hn1⟩ := hlab.2
    subst hn1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hF, hfin, hK, hQ', ?_⟩
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have hSbot := CFSG.LocalAnalysis.GLTheoremA.Y10GField.largeEvenScalars_two_subgroupOf_eq_bot
      hK ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆
    obtain ⟨c⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GField.zmod_two_ringEquiv hK
    let e1 : LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ ≃*
        ↥⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :=
      (QuotientGroup.quotientMulEquivOfEq hSbot).trans QuotientGroup.quotientBot
    let e2 : ↥(alternatingGroup (Fin 6)) ≃* ↥⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :=
      MulEquiv.ofBijective (CFSG.ASVolI.burnsideI23x_a6ι c)
        (CFSG.ASVolI.burnsideI23x_a6ι_bijective c)
    let eR : LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ ≃*
        ↥(alternatingGroup (Fin 6)) := e1.trans e2.symm
    exact ⟨eR.isSimpleGroup, nonabelian_of_mulEquiv eR.symm l02qf3_alt6_nonabelian⟩
  ·
    obtain ⟨-, hn1⟩ := hlab.2
    subst hn1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hF, hfin, hK, hQ', l02qf3_g2der_simple hK⟩
  ·
    obtain ⟨-, hn1⟩ := hlab.2
    subst hn1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    exact ⟨K, hF, hfin, hK, hQ', l02qf3_tits_simple hK⟩

end CFSG.StandardType
