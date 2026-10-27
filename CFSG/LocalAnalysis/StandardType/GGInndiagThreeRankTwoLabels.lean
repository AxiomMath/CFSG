module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
import CFSG.Assembly.GL83StatedBridge
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Vac
import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
import CFSG.Milestones.CL_LIT_SQTK_simple_list
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.B4Statement
import CFSG.Quasithin.Background.B5Statement
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import Certificates.Certificate10
import Certificates.Certificate100
import Certificates.Certificate101
import Certificates.Certificate102
import Certificates.Certificate103
import Certificates.Certificate104
import Certificates.Certificate105
import Certificates.Certificate106
import Certificates.Certificate107
import Certificates.Certificate108
import Certificates.Certificate109
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate8026Base
import Certificates.Certificate8046
import Certificates.Certificate8049
import Certificates.Certificate8052
import Certificates.Certificate9
import Certificates.Certificate96
import Certificates.Certificate97
import Certificates.Certificate98
import Certificates.Certificate99

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGInndiagThreeRankTwo : LargeEvenRawCont :=
  fun R _ I _ => ∀ B : Subgroup (MulAut R), CFSG.Open.IsElemAbelian 3 B →
    B ≤ Subgroup.closure I → Nat.card B ≤ 9

section KOT3


theorem largeEvenLabelAll_threeRankTwo_triD4 {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .triD4) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagThreeRankTwo) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun _ _ B hB hBI => ?_⟩
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  obtain ⟨-, -, -, -, -, -, hZC, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have := Finite.of_equiv _ e.symm.toEquiv
  have hBinn := hBI.trans
    ((Subgroup.closure_le _).mpr (TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK))
  have h27 : Nat.card B < 3 ^ 3 :=
    TableBExcSmallRest.card_lt_of_subset_inn (TableBExcSmallRest.center_eq_bot_of_mulEquiv e hZC)
      (fun A hA => TableBExcSmallRest.card_lt_of_mulEquiv e
        (fun E hE => TableBExcSmallRanks.card_lt_of_isElemAbelian_triD4 hn K hK σ hσ hE) hA)
      (fun φ hφ => by obtain ⟨r, hr⟩ := hBinn hφ; exact ⟨r, hr⟩) hB
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hB).exists_card_eq
  rw [hk] at h27 ⊢
  have hk2 : k ≤ 2 := Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h27)
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

end KOT3

section KOLU

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

private theorem isQuasisimple_and_center_eq_bot_of_simple {R : Type} [Group R]
    (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple R ∧ Subgroup.center R = ⊥ := by
  haveI := hs
  obtain ⟨a, b, hab⟩ := hna
  have hZ : Subgroup.center R = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R)).resolve_right fun h =>
      hab (Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a)
  refine ⟨⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator R)).resolve_left fun h => hab ?_,
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩, hZ⟩
  rw [← commutatorElement_eq_one_iff_mul_comm, ← Subgroup.mem_bot, ← h, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

theorem largeEvenLabelAll_threeRankTwo_A2 {lab : LargeEvenLabel} (ht : lab.tag = .A)
    (hr : lab.rank = 2) (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagThreeRankTwo) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hr h3
  subst ht hr
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun hs hna B hB _ => ?_⟩
  obtain ⟨hqs, hZ⟩ := isQuasisimple_and_center_eq_bot_of_simple hs hna
  have hF : Nat.card K % 3 = 2 := by
    rw [hK]
    omega
  have key : ∀ H : Subgroup (GL (Fin 3) K), H = CFSG.Open.StatedSL 3 K →
      Nonempty (LargeEvenProj H ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) := by
    rintro H rfl
    exact ⟨MulEquiv.refl _⟩
  obtain ⟨e⟩ := key _ (largeEvenSLGroup_eq_statedSL 3)
  have : Finite (LargeEvenSLGroup (Fin 3) K) := Subtype.finite
  have : Finite (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact CFSG.HardMathSupport.Solomon.Coordinator.VacAut.card_le_nine_linear hqs hF
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e) B hB

private theorem card_le_nine_of_le_primeFormD_one {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) (h3 : 3 ∣ Nat.card Kˣ)
    {D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))}
    (hD : CFSG.Open.IsElemAbelian 3 D)
    (hDle : D ≤ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    Nat.card D ≤ 9 := by
  haveI : Finite K := h.finite
  have hker : ∀ A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      primeFormConjHom h _ A = 1 ↔ (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    intro A
    constructor
    · intro hA
      have h1 : primeFormPsi h (isPrimeFormGram_one (K := K) (n := 3)) ⟨A, 1⟩ = 1 := by
        rw [primeFormPsi_apply, map_one, mul_one]
        exact hA
      obtain ⟨-, z, -, hz⟩ :=
        (primeFormPsi_eq_one_iff h (isPrimeFormGram_one (K := K) (n := 3)) le_rfl _).1 h1
      have hz' : (A : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) z := hz
      rw [hz']
      exact Subgroup.mem_center_iff.2 fun g =>
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar z g).eq
    · intro hA
      ext x
      induction x using QuotientGroup.induction_on with
      | H g =>
        rw [primeFormConjHom_mk, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        change (A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹ = g
        rw [(Subgroup.mem_center_iff.1 hA g).symm, mul_inv_cancel_right]
  have := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel Nat.prime_three
    (by norm_num) h3 (by norm_num) (primeFormUnitary h _) (primeFormConjHom h _) hker D hDle hD
  simpa using this

private theorem threeRankTwo_recipeUnitary_three {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGInndiagThreeRankTwo (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))) := by
  intro B hB hBI
  have h := unitaryFieldData_of_card hn hK
  have hd : 1 ≤ 3 := by norm_num
  rw [← RecipeFieldSU.coe_recIU h hK hd, Subgroup.closure_eq] at hBI
  have h3 : 3 ∣ Nat.card Kˣ := by
    have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [Nat.card_units, hK, h4]
    exact Nat.sub_one_dvd_pow_sub_one 4 n
  set ψ := (MulAut.congr (InndiagSU.projEquiv h hd)).toMonoidHom with hψ
  have hψi : Function.Injective ψ := (MulAut.congr (InndiagSU.projEquiv h hd)).injective
  have hle := card_le_nine_of_le_primeFormD_one h h3 (CFSG.Open.IsElemAbelian.map hB ψ)
    (Subgroup.map_le_iff_le_comap.mpr hBI)
  rwa [Subgroup.card_map_of_injective hψi] at hle

theorem largeEvenLabelAll_threeRankTwo_twA2 {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twA) (hr : lab.rank = 2) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagThreeRankTwo) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht hr hn
  subst ht hr
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeUnitary_and (fun K _ _ hK _ _ => threeRankTwo_recipeUnitary_three hn K hK) hQ

end KOLU

end CFSG.StandardType.SCFourCover
