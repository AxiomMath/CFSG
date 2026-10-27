module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFComp
public import CFSG.Open.Defs
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenHyp139N3Layer
public import CFSG.GroupTheory.ComponentFStarProd
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.Quasithin.Background.B15P4Comp
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting
public import CFSG.RankThree.GF2n.Stroth80.Sl2Commuting
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.InnerCentralizerProjection
public import CFSG.RankThree.PartTwo.KFacts.KS116LinRep
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenOmega4TransvectionUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Vol2.Ch9H11Norm
public import CFSG.GroupTheory.CosetActionPerm
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2Hyp139LowAll
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.C1PackNat
public import CFSG.Quasithin.Background.C1PackSolvBasic
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RepresentationTheory.PerfectWeightStabilizerModule
public import CFSG.Sporadic.Schreier.M11

public section

noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Matrix

theorem tensorNat_two_faithful (K : Type) [Field K] [CharP K 2] :
    (FFModel.tensorNat 2 K).Faithful := by
  intro γ hγ
  have hfix : ∀ X : Multiplicative (Matrix (Fin 2) (Fin 2) K), tensorAct 2 K γ X = X := by
    intro X
    have h1 : tensorAct 2 K γ X * X⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hγ X (Subgroup.mem_top X))
    exact mul_inv_eq_one.mp h1
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  let γ' : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K :=
    (e.symm γ.1, e.symm γ.2)
  have hcoe1 : ((γ'.1 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (((γ.1 : ↥(StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by
    have h1 : e (e.symm γ.1) = γ.1 := e.apply_symm_apply γ.1
    have h2 := congrArg (fun z : ↥(StatedSL 2 K) =>
      ((z : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h1
    rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe] at h2
    simpa [γ'] using h2
  have hcoe2 : ((γ'.2 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (((γ.2 : ↥(StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by
    have h1 : e (e.symm γ.2) = γ.2 := e.apply_symm_apply γ.2
    have h2 := congrArg (fun z : ↥(StatedSL 2 K) =>
      ((z : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h1
    rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe] at h2
    simpa [γ'] using h2
  have hfix' : ∀ x : Matrix (Fin 2) (Fin 2) K,
      ((γ'.1 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x *
        (((γ'.2 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))ᵀ = x := by
    intro x
    have hx := congrArg Multiplicative.toAdd (hfix (Multiplicative.ofAdd x))
    have hx' : (((γ.1 : ↥(StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) * x *
        ((((γ.2 : ↥(StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K))ᵀ = x := by
      simpa [tensorAct] using hx
    rw [hcoe1, hcoe2]
    exact hx'
  have hρ : CFSG.Quasithin.H13.H11P.rho γ' = 1 := by
    have hmap : CFSG.Quasithin.H13.H11P.rho γ' = CFSG.Quasithin.H13.H11P.rho 1 := by
      apply MulEquiv.ext
      intro X
      apply Multiplicative.toAdd.injective
      obtain ⟨x, rfl⟩ : ∃ x : Matrix (Fin 2) (Fin 2) K, Multiplicative.ofAdd x = X :=
        ⟨Multiplicative.toAdd X, rfl⟩
      rw [map_one, MulAut.one_apply, toAdd_ofAdd]
      change Multiplicative.toAdd
          (CFSG.Quasithin.H13.H11P.rho γ' (Multiplicative.ofAdd x)) = x
      rw [← CFSG.Quasithin.H13.H11P.addMap_apply, CFSG.Quasithin.H13.H11P.addMap_rho]
      exact hfix' x
    simpa using hmap
  have hγ' : γ' = 1 := CFSG.Quasithin.H13.H11P.rho_injective (hρ.trans (map_one _).symm)
  have h1 : γ.1 = 1 := by
    have := congrArg
      (fun p : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K =>
        e p.1) hγ'
    simpa [γ'] using this
  have h2 : γ.2 = 1 := by
    have := congrArg
      (fun p : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K =>
        e p.2) hγ'
    simpa [γ'] using this
  exact Prod.ext h1 h2

theorem eq_one_of_fix_of_natTensor {W : Type} [CommGroup W] [Finite W]
    {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hNat : NatTensor Y U ⊥ 2 2) {y : MulAut W} (hy : y ∈ Y)
    (hfix : ∀ u ∈ U, y u = u) : y = 1 := by
  classical
  obtain ⟨K, hKfield, hKfinite, hKcard, hR⟩ := hNat
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hKcard])
  obtain ⟨π, hπ⟩ := hR
  exact CFSG.Quasithin.G64.RealizesVia.eq_one_of_trivial (tensorNat_two_faithful K) hπ hy
    (fun u hu => by simpa [hfix u hu])

end CFSG.LocalAnalysis.WeakClosure81

end

end
