module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallD4LongTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallD4Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.Quasithin.Background.B1Basic
import CFSG.Quasithin.Background.SmithB45D4
import CFSG.Quasithin.Background.SmithB42D4Main
import CFSG.Quasithin.Background.SmithB42D4Pure
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Quasithin.B42Disp CFSG.Quasithin.B45Disp CFSG.Quasithin.B42D4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Setup.X6 CFSG.Timmesfeld
open CFSG.Blueprint (LieModel)

theorem k14_5SmallFor_3d4 :
    K14_5SmallFor fun L _ e => Is3D4 L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  exfalso
  have : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  have hI' : ∀ v : I, v * v = 1 := fun v => by rw [← pow_two]; exact hI v
  have hn3 : n ≤ 3 * e := by
    rcases nParam_eq_of_is3D4_parabolic hq hS hPL hpar hinf hN with rfl | rfl <;> omega
  have hX := LieModel.chevalleyExceptionalModel hS (by decide)
  obtain ⟨he1, K, hKf, hKfin, σ, hK, hσ, ⟨φ⟩⟩ := exists_mulEquiv_triality_model hX
  let : Field K := hKf
  have : Finite K := hKfin
  have : CharP K 2 := charP_two_of_card he1 hK
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have hZL : Subgroup.center ↥L = ⊥ := center_eq_bot_of_is3D4 hS
  let e₀ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot).trans φ
  have hproj : ∀ l : ↥L, modelProj L e₀ l = φ l := fun l => rfl
  have hprojinj : Function.Injective (modelProj L e₀) := fun a b h =>
    φ.injective (by rw [← hproj, ← hproj, h])
  have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hevL : Even (Nat.card ↥L) := by
    rw [card_chevalleyExceptionalModel_two hX, ordTrialityD4]
    refine even_iff_two_dvd.2 (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _) _)
    exact (dvd_pow_self 2 (by omega : e ≠ 0)).trans (dvd_pow_self _ (by norm_num))
  have hev : Even (Nat.card ↥X) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hevL).trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨t, htX, ht2, htm⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam X hev
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; exact absurd ht2 (by norm_num)
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  suffices hbig : 2 ^ (3 * e + 2) ≤ (fixV (Subgroup.zpowers t)).index by
    rw [B1.index_eq_two_pow hI, htm] at hbig
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 hbig
    omega
  set x : ↥(normalizer (L : Set (MulAut I))) := ⟨t, hXN htX⟩ with hxdef
  have hx2 : (x : MulAut I) * x = 1 := htt
  by_cases hinn : modelAct L e₀ x ∈
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* MulAut _).range
  ·
    obtain ⟨m, hm'⟩ := hinn
    obtain ⟨l, hl⟩ := exists_lift L e₀ m
    have hconj : ∀ l' : ↥L, t * l' * t⁻¹ = (l : MulAut I) * l' * (l : MulAut I)⁻¹ := by
      intro l'
      have h1 : modelProj L e₀ (CFSG.QuasithinUnique.Setup.X5.conjOn L x l') =
          modelProj L e₀ (l * l' * l⁻¹) := by
        rw [modelProj_apply, ← modelAct_apply_mk, ← hm', MulAut.conj_apply, ← hl,
          modelProj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          map_mul, map_mul, map_inv]
      exact congrArg Subtype.val (hprojinj h1)
    set u : MulAut I := (l : MulAut I)⁻¹ * t with hudef
    have hucomm : ∀ h ∈ L, u * h = h * u := by
      intro h hh
      have h1 := hconj ⟨h, hh⟩
      calc u * h = (l : MulAut I)⁻¹ * (t * h * t⁻¹) * t := by rw [hudef]; group
        _ = (l : MulAut I)⁻¹ * ((l : MulAut I) * h * (l : MulAut I)⁻¹) * t := by rw [h1]
        _ = h * u := by rw [hudef]; group
    have hu2 : u ^ 2 = ((l⁻¹ * l⁻¹ : ↥L) : MulAut I) := by
      have h1 := hconj l⁻¹
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      rw [hti, Subgroup.coe_inv] at h1
      rw [sq, hudef, Subgroup.coe_mul, Subgroup.coe_inv]
      calc (l : MulAut I)⁻¹ * t * ((l : MulAut I)⁻¹ * t) =
          (l : MulAut I)⁻¹ * (t * (l : MulAut I)⁻¹ * t) * (t * t) := by
            rw [htt]; group
        _ = (l : MulAut I)⁻¹ * (l : MulAut I)⁻¹ := by rw [h1, htt]; group
    clear_value u
    have hcen : (l⁻¹ * l⁻¹ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : MulAut I) * ((l⁻¹ * l⁻¹ : ↥L) : MulAut I) = ((l⁻¹ * l⁻¹ : ↥L) : MulAut I) * g
      rw [← hu2, sq, ← mul_assoc, ← hucomm g g.2, mul_assoc, ← hucomm g g.2, mul_assoc]
    rw [hZL, Subgroup.mem_bot] at hcen
    have hu1 : u = 1 := eq_one_of_commute_of_isIrrOn hI hirr
      (by rw [hu2, hcen, Subgroup.coe_one]) hucomm
    have htl : t = (l : MulAut I) := by
      have h1 : (l : MulAut I)⁻¹ * t = 1 := by rw [← hudef]; exact hu1
      exact (inv_mul_eq_one.1 h1).symm
    have hll : l * l = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← htl, htt, Subgroup.coe_one])
    have hl1 : l ≠ 1 := fun h => ht1 (by rw [htl, h, Subgroup.coe_one])
    have hξ : φ l * φ l = 1 := by rw [← map_mul, hll, map_one]
    have hξ1 : φ l ≠ 1 := fun h => hl1 (φ.injective (by rw [h, map_one]))
    rcases involution_conj σ hσ3 (φ l) hξ hξ1 with hlong | hB
    · have h := two_pow_six_mul_le_index_long_of_one_le hK σ hσ he1 hI φ hlong
      rw [← htl] at h
      exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h
    · have h := B45Tor.two_pow_le_index_classB he1 hK σ hσ hI' L hZL e₀ (x := l)
        (by rw [hproj]; exact hB)
      rw [← htl] at h
      exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h
  ·
    have hα : modelAct L e₀ x * modelAct L e₀ x = 1 := by
      rw [← map_mul, show x * x = 1 from Subtype.ext hx2, map_one]
    obtain ⟨-, hD⟩ := B45D4.dispAtOut_outer he1 hK σ hσ _ hα hinn
    have h := sq_lt_index_of_dispAtOut L hperf hZL e₀ (Q := B45D4.outerPrimes e)
      (B45Tor.doubleDispOut_trialityD4 he1 hK σ hσ hI' L hZL e₀) x hx2 hD
    calc 2 ^ (3 * e + 2) ≤ (2 ^ (2 * e + 1)) ^ 2 := by
          rw [← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := h.le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
