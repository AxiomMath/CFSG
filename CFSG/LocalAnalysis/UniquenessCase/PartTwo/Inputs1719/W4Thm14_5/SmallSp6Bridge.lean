module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeEndField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeSmith
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeBinary
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin.SmithCurtis Module Representation Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.Theory.Representation
open scoped TensorProduct MatrixGroups MonoidAlgebra

namespace Sp6Bridge

variable {K k : Type} [Field K] [Finite K] [CharP K 2] [Field k]

theorem factorsFinrankLe_endField_all_roots
    [Fintype K] [CharP k 2] [IsAlgClosed k] {e : ℕ}
    (hK : Fintype.card K = 2 ^ e) (he : 1 ≤ e)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (StatedSp 3 K) W) [ρ.IsIrreducible]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule) k]
    [Algebra (ZMod 2) k]
    [IsScalarTower (ZMod 2)
      (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule) k]
    {y : StatedSp 3 K} (hy : y * y = 1) (hy1 : y ≠ 1)
    (hsmall : finrank (ZMod 2) (LinearMap.range (ρ y - 1)) < 3 * e)
    (hρ : Function.Injective ρ) (i : Fin 3) :
    FactorsFinrankLe ((extendScalars k (CFSG.endFieldRep ρ)).comp
      ((spCurtisDatum 3 K).X i ⊔ (spCurtisDatum 3 K).Y i).subtype) 2 := by
  exact factorsFinrankLe_endField_extension_comp ρ k _
    (factorsFinrankLe_binary_all_roots hK he ρ hy hy1 hsmall hρ i)

end Sp6Bridge

theorem finrank_fixSub_Us_le_two {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ℕ}
    (hK : Fintype.card K = 2 ^ e) (he : 3 ≤ e)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (StatedSp 3 K) W) [ρ.IsIrreducible]
    {y : StatedSp 3 K} (hy : y * y = 1) (hy1 : y ≠ 1)
    (hsmall : finrank (ZMod 2) (LinearMap.range (ρ y - 1)) < 3 * e) (i : Fin 3) :
    finrank (AlgebraicClosure (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule))
      (fixSub (CFSG.Theory.Representation.extendScalars
          (AlgebraicClosure (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule))
          (CFSG.endFieldRep ρ)) ((spCurtisDatum 3 K).Us i)) ≤ 2 := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule
  let k := AlgebraicClosure E
  have : CharP E 2 := CFSG.HardMathSupport.GuralnickMalle.endField_charP ρ 2
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  let : Algebra K k :=
    (CFSG.HardMathSupport.GuralnickMalle.nonempty_ringHom_algebraicClosure
      (K := E) (F₀ := K) (p := 2)).some.toAlgebra
  let : Algebra (ZMod 2) k := (algebraMap (ZMod 2) k).toAlgebra
  let V := k ⊗[E] ρ.asModule
  have : Module.Finite E ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  have : Module.Finite k V := inferInstance
  let σ : Representation k (StatedSp 3 K) V := extendScalars k (CFSG.endFieldRep ρ)
  have hsimp : IsSimpleRep σ := isSimpleRep_extendScalars_endFieldRep ρ k
  have hsplit : SplitOver k (spCurtisDatum 3 K).H := spCurtisDatum_splitOver (n := 3) (K := K) k
  have h4 : 4 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : IsSimpleGroup (StatedSp 3 K) :=
    CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le h4 (by norm_num)
  let π : StatedSp 3 K →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := repLinEquiv ρ
      map_one' := repLinEquiv_one ρ
      map_mul' := repLinEquiv_mul ρ }
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hker | hker
  · have hπ := (MonoidHom.ker_eq_bot_iff π).mp hker
    have hρ : Function.Injective ρ := by
      intro a b hab
      apply hπ
      ext w
      exact congrArg (fun f : W →ₗ[ZMod 2] W => f w) hab
    have hfac := Sp6Bridge.factorsFinrankLe_endField_all_roots (k := k)
      hK (by omega) ρ hy hy1 hsmall hρ i
    exact Sp6Bridge.finrank_fixSub_Us_le_of_factors σ hsimp hsplit i hfac
  · have htriv : ∀ g, ρ g = 1 := by
      intro g
      have hg : π g = 1 := (MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g))
      ext w
      exact congrArg (fun f : W ≃ₗ[ZMod 2] W => f w) hg
    have hdim : finrank (ZMod 2) W = 1 :=
      CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.finrank_eq_one_of_trivial
        (ρ := ρ) inferInstance htriv
    have hV : finrank k V ≤ 1 := by
      have hdimE := finrank_mul_finrank (ZMod 2) E ρ.asModule
      have hρW := ρ.asModuleEquiv.finrank_eq
      have hEpos : 0 < finrank (ZMod 2) E := finrank_pos
      have hprod : finrank (ZMod 2) E * finrank E ρ.asModule = 1 :=
        hdimE.trans (hρW.trans hdim)
      have hdimEnd : finrank E ρ.asModule ≤ 1 := by
        have h := Nat.mul_le_mul_right (finrank E ρ.asModule) (show 1 ≤ finrank (ZMod 2) E from hEpos)
        rw [one_mul, hprod] at h
        exact h
      rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
      exact hdimEnd
    exact (Submodule.finrank_le (fixSub σ ((spCurtisDatum 3 K).Us i))).trans (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
