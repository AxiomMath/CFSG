module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Kernel
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Lang
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Trace
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
import CFSG.Quasithin.H13.NQCatJ4FrattiniGen
import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType.SmallExc.F4Two

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433


theorem isSolvable_centralizer_of_trace_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {x : adjointGroup .F4 K} (hx : orderOf x = 3)
    (htrx : LinearMap.trace K (RootModule Tag.F4 K)
      ((x : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)) = 0) :
    Group.IsSolvable (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))) := by
  classical
  haveI : Finite (adjointGroup Tag.F4 K) := by
    have : Finite (Module.End K (RootModule Tag.F4 K)) := Module.finite_of_finite K
    infer_instance
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨S, a, ι, g, hSq, hT, hap, h1, hinj, hrange, hda, hconj, hTame⟩ :=
    exists_langSetup_F4_conj (by rw [hK]; norm_num) (by rw [hK]; norm_num) x hx
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ := exists_omega_param hap
  have hk0 : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    refine h1 ?_
    rw [show a = 1 from funext fun i => by rw [hak i, h i, pow_zero, Pi.one_apply],
      CFSG.LieType.Chevalley.rootDiagUnit_one]
  have htr : LinearMap.trace (AlgebraicClosure K) (RootModule Tag.F4 (AlgebraicClosure K))
      ((rootDiagUnit Tag.F4 a : ModGL Tag.F4 (AlgebraicClosure K)) :
        Module.End (AlgebraicClosure K) (RootModule Tag.F4 (AlgebraicClosure K))) = 0 := by
    have h := ChevQ.E8NonToral.trace_conj g⁻¹
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K))
    rw [inv_inv] at h
    rw [hda, h, CFSG.RankThree.Chevalley.trace_baseChangeGL, htrx, map_zero]
  have hsol := CFSG.HardMathSupport.Dickson.Bal207.FamF42.isSolvable_rationalComponent_of_a2a2 S
    hT hap hω3 hω1 hk3 hk0 hak (kernelA2A2_of_trace_eq_zero hω3 hω1 hak hk3 hk0 htr) (hSq.trans hK)
  have hbot : GLALayer (fixSubgroup (MulAut.conj x)) = ⊥ := by
    unfold GLALayer
    rw [eq_bot_iff]
    refine sSup_le fun Q hQ => ?_
    obtain ⟨i, hi, -⟩ := LieComp.components_of_langSetup S Nat.prime_three ι hinj hrange
      (MulAut.conj x) hconj hT hap h1 hTame hQ
    exact absurd (hsol i) (not_isSolvable_of_isQuasisimple hi)
  have hlayer := LieSemisimple.perfectInLayer_of_langSetup_of_prime S Nat.prime_three ι hinj
    hrange (MulAut.conj x) hconj hT hap h1 hTame
  have hfix : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) =
      fixSubgroup (MulAut.conj x) := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, mem_fixSubgroup, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul, eq_comm]
  refine CFSG.Quasithin.H13.NQCat.isSolvable_of_forall_isPerfect fun Q hQ => ?_
  have hPP := hlayer _ ((Subgroup.map_subtype_le Q).trans hfix.le)
    (by rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hQ])
  rw [hbot, le_bot_iff] at hPP
  exact (Subgroup.map_eq_bot_iff_of_injective Q (Subgroup.subtype_injective _)).1 hPP

theorem ggF4TwoThreeCSolv {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    GGF4TwoThreeCSolv K := by
  have hv3 : vecDelta ^ 3 = 1 := by decide +kernel
  have hv1 : vecDelta ≠ 1 := fun h => absurd (congrFun h 0) (by decide +kernel)
  have hδ3 : orderOf (TableBF4Two.torus3 K vecDelta) = 3 :=
    orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) (by rw [← map_pow, hv3, map_one])
      fun h => hv1 (TableBF4Two.torus3_injective (h.trans (map_one _).symm))
  show Group.IsSolvable (Subgroup.centralizer
    ({TableBF4Two.torus3 K vecDelta} : Set (adjointGroup .F4 K)))
  exact isSolvable_centralizer_of_trace_eq_zero hK hδ3 trace_torus3_vecDelta

theorem ggF4TwoThreeCSolvInput : GGF4TwoThreeCSolvInput :=
  fun _ _ _ _ hK => ggF4TwoThreeCSolv hK

theorem ggF4TwoNormSmallInput : GGF4TwoNormSmallInput :=
  ggF4TwoNormSmallInput_of_threeC ggF4TwoThreeCSolvInput

end CFSG.StandardType.SmallExc.F4Two

end
