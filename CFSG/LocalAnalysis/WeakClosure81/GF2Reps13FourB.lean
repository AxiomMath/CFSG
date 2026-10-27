module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CLie
public import CFSG.Models.Blueprint
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3M
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFORankLift
public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeAux
public import CFSG.LargeExtraspecial.S45QLin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem w16f_isL3_of_surj (hGA : GriessAllModelsStatement)
    {Y K : Subgroup (MulAut W)} (hY : ∀ P : Subgroup (MulAut W), P ≤ Y →
      (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hK : IsComponentOf K Y)
    (f : ↥K →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) (hf : Function.Surjective f) :
    UC22.IsL3 ↥K 1 := by
  classical
  have hqs : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  haveI : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two (n := 3) (by norm_num)
  have hproper : f.ker ≠ ⊤ := by
    intro htop
    have hf1 : f = 1 := MonoidHom.ker_eq_top_iff.mp htop
    obtain ⟨g, hg⟩ := exists_ne (1 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))
    obtain ⟨k, hk⟩ := hf g
    rw [hf1] at hk
    exact hg (by simpa using hk.symm)
  have hker_le_center : f.ker ≤ Subgroup.center ↥K :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hqs f.ker hproper
  haveI : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  have hcenterGL3 : Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  have hcenter_le_ker : Subgroup.center ↥K ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzmap : f z ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
      Subgroup.map_center_le_center (f := f) hf ⟨z, hz, rfl⟩
    rwa [hcenterGL3, Subgroup.mem_bot] at hzmap
  have hker : f.ker = Subgroup.center ↥K := le_antisymm hker_le_center hcenter_le_ker
  have hcoreY : CFSG.Open.pCoreOf 2 Y = ⊥ := by
    refine hY (CFSG.Open.pCoreOf 2 Y) (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    have heq : (CFSG.Open.pCoreOf 2 Y).subgroupOf Y = CFSG.pCore 2 ↥Y := by
      rw [CFSG.Open.pCoreOf]
      exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective (CFSG.pCore 2 ↥Y)
    rw [heq]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  have hcoreY' : CFSG.pCore 2 ↥Y = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥Y) Y.subtype_injective).mp
      (show (CFSG.pCore 2 ↥Y).map Y.subtype = ⊥ from hcoreY)
  have hKtop : CFSG.Open.IsComponentOf (K.subgroupOf Y) (⊤ : Subgroup ↥Y) :=
    ⟨le_top,
      CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
        (CFSG.AGLEmbedding.NoXBlock.isSubnormal_subgroupOf_of_open hK.2.1),
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe hK.1) hK.2.2⟩
  have hodd_sub : Odd (Nat.card (Subgroup.center ↥(K.subgroupOf Y))) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.RankCore.odd_card_center_of_component
      hcoreY' hKtop
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hK.1)).toEquiv]
    exact hodd_sub
  have hGAgl3 : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) = 2 := by
    obtain ⟨-, ⟨eM⟩⟩ := hGA (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) .PSL 3 2 1
      (CFSG.Models.LieModel.of_blueprint (by decide)
        CFSG.OddStandard.HigherRank.YamadaG23.y7c_lieModel_gl3)
    rw [Nat.card_congr eM.toEquiv,
      CFSG.ComponentClassification.HarrisLit.T1.P54.card_generic_prod_exceptional]
    decide
  let e : (↥K ⧸ Subgroup.center ↥K) ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := f) hf)
  have hdvdg : Nat.card (Subgroup.center ↥K) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) :=
    CFSG.ClassicalInvolution.Q3.TL4.E3S3M.natCard_center_dvd
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hK.2.2) e
  have hdvd : Nat.card (Subgroup.center ↥K) ∣ 2 := by
    rw [← hGAgl3]
    exact hdvdg
  have hcenterbot : Subgroup.center ↥K = ⊥ := by
    have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥K)) 2 :=
      (Nat.coprime_two_left.mpr hodd).symm
    exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hkerbot : f.ker = ⊥ := by rw [hker, hcenterbot]
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hkerbot
  let e2 : ↥K ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective f ⟨hinj, hf⟩
  exact CFSG.Blueprint.LieModel.of_mulEquiv e2.symm
    CFSG.OddStandard.HigherRank.YamadaG23.y7c_lieModel_gl3

end CFSG.LocalAnalysis.WeakClosure81
