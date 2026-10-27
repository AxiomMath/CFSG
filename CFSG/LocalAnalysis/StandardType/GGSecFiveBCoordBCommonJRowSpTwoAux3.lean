module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneDefs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.A6Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockZ
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticFixed
import CFSG.CGT.PushingUpLit.CGT6.SixFourE9
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlock
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusLocalize
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitary
import CFSG.LocalAnalysis.StandardType.GGTBJFrameCorank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpSelected
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoUnitary
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagUnitary
import CFSG.LocalAnalysis.StandardType.GGTorCPlane
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.SUFour
import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentSpBlocks
import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.XbarGen
import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KDichotomy
import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KEngine2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelInvolutionFusion

public section

namespace CFSG.StandardType.CommonJSpTwo

open CFSG.Assembly
open CFSG.Open (StatedSp)
open CFSG.RankThree.Classical CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.StandardType.SpJoin
open Matrix
open Polynomial
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
open CFSG.StandardType.ClassicalPosition

private lemma planeMat_mulVec_coord {K : Type} [Field K] {r : ℕ}
    (M : Fin r → Matrix (Fin 2) (Fin 2) K) (v : Fin r ⊕ Fin r → K) (i : Fin r) (b : Fin 2) :
    (WitSpNs.planeMat M *ᵥ v) (WitSpNs.coord b i) =
      ∑ a : Fin 2, M i b a * v (WitSpNs.coord a i) := by
  change (∑ j : Fin r ⊕ Fin r,
    WitSpNs.planeMat M (WitSpNs.coord b i) j * v j) = _
  rw [Fintype.sum_sum_type,
    Finset.sum_eq_single i (fun p _ hp => by
      rw [WitSpNs.planeMat_apply,
        if_neg (by simp only [WitSpNs.plane_coord, WitSpNs.plane_inl]; exact fun h => hp h.symm),
        zero_mul]) (fun h => absurd (Finset.mem_univ i) h),
    Finset.sum_eq_single i (fun p _ hp => by
      rw [WitSpNs.planeMat_apply,
        if_neg (by simp only [WitSpNs.plane_coord, WitSpNs.plane_inr]; exact fun h => hp h.symm),
        zero_mul]) (fun h => absurd (Finset.mem_univ i) h),
    Fin.sum_univ_two, ← CFSG.StandardType.SympMinus.sympMinusZ_coord_zero,
    ← CFSG.StandardType.SympMinus.sympMinusZ_coord_one, WitSpNs.planeMat_coord,
    WitSpNs.planeMat_coord]

private lemma spEnd_spPlaneTorus_coord {K : Type} [Field K] {r : ℕ}
    (ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (f : Fin r → Multiplicative (ZMod 3)) (v : Fin r ⊕ Fin r → K) (i : Fin r) (b : Fin 2) :
    spEnd (spPlaneTorus r ζ f) v (WitSpNs.coord b i) =
      ∑ a : Fin 2, (((ζ (f i) : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) b a) * v (WitSpNs.coord a i) := by
  rw [CFSG.RankThree.Classical.spEnd_apply, CFSG.StandardType.TorC.coe_spPlaneTorus,
    planeMat_mulVec_coord]

private lemma spPlaneTorus_fixed_coord_eq_zero {K : Type} [Field K] [CharP K 2] {r : ℕ}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {f : Fin r → Multiplicative (ZMod 3)}
    {v : Fin r ⊕ Fin r → K} (hv : spEnd (spPlaneTorus r ζ f) v = v)
    {i : Fin r} (hi : f i ≠ 1) (b : Fin 2) :
    v (WitSpNs.coord b i) = 0 := by
  have h3 : (f i) ^ 3 = 1 := by
    simpa using pow_card_eq_one' (x := f i)
  have h3' : (ζ (f i)) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have h1 : ζ (f i) ≠ 1 := fun h => hi (hζ (h.trans (map_one ζ).symm))
  have hfix : ((ζ (f i) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ (fun a : Fin 2 => v (WitSpNs.coord a i)) =
      (fun a : Fin 2 => v (WitSpNs.coord a i)) := by
    funext b'
    change (∑ a : Fin 2, (((ζ (f i) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) b' a) * v (WitSpNs.coord a i)) = v (WitSpNs.coord b' i)
    rw [← spEnd_spPlaneTorus_coord ζ f v i b', hv]
  have h0 := CFSG.CGT.PushingUpLit.CGT6.fixed_vec_eq_zero_of_order_three h3' h1
    (fun a : Fin 2 => v (WitSpNs.coord a i)) hfix
  exact congrFun h0 b

theorem spFixedDim_spPlaneTorus {K : Type} [Field K] [CharP K 2] {r : ℕ}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (f : Fin r → Multiplicative (ZMod 3)) :
    spFixedDim (spPlaneTorus r ζ f) = 2 * Fintype.card {i : Fin r // f i = 1} := by
  classical
  set e : {i : Fin r // f i = 1} × Fin 2 → (Fin r ⊕ Fin r → K) :=
    fun p => (Pi.single (WitSpNs.coord p.2 (p.1 : Fin r)) (1 : K) :
      Fin r ⊕ Fin r → K) with he
  set U : Submodule K (Fin r ⊕ Fin r → K) := Submodule.span K (Set.range e) with hU
  have hUle : U ≤ LinearMap.ker (spEnd (spPlaneTorus r ζ f) - 1) := by
    rw [hU]
    refine Submodule.span_le.mpr ?_
    rintro - ⟨⟨⟨i, hi⟩, a⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact CFSG.StandardType.SympMinus.sympMinusZ_basis_fixed ζ f i hi a
  have hle : LinearMap.ker (spEnd (spPlaneTorus r ζ f) - 1) ≤ U := by
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
    have h1 : v = ∑ j : Fin r ⊕ Fin r,
        v j • (Pi.single j (1 : K) : Fin r ⊕ Fin r → K) := by
      conv_lhs => rw [← (Pi.basisFun K (Fin r ⊕ Fin r)).sum_repr v]
      simp [Pi.basisFun_apply, Pi.basisFun_repr]
    have hsplit : v = ∑ i : Fin r, ∑ a : Fin 2,
        v (WitSpNs.coord a i) • (Pi.single (WitSpNs.coord a i) (1 : K) :
          Fin r ⊕ Fin r → K) := by
      calc v = ∑ j : Fin r ⊕ Fin r,
            v j • (Pi.single j (1 : K) : Fin r ⊕ Fin r → K) := h1
        _ = (∑ j : Fin r, v (Sum.inl j) • (Pi.single (Sum.inl j) (1 : K) :
              Fin r ⊕ Fin r → K)) +
            (∑ j : Fin r, v (Sum.inr j) • (Pi.single (Sum.inr j) (1 : K) :
              Fin r ⊕ Fin r → K)) := Fintype.sum_sum_type _
        _ = ∑ i : Fin r, (v (Sum.inl i) • (Pi.single (Sum.inl i) (1 : K) :
              Fin r ⊕ Fin r → K) +
            v (Sum.inr i) • (Pi.single (Sum.inr i) (1 : K) : Fin r ⊕ Fin r → K)) := by
            rw [Finset.sum_add_distrib]
        _ = ∑ i : Fin r, ∑ a : Fin 2,
            v (WitSpNs.coord a i) • (Pi.single (WitSpNs.coord a i) (1 : K) :
              Fin r ⊕ Fin r → K) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Fin.sum_univ_two, ← CFSG.StandardType.SympMinus.sympMinusZ_coord_zero,
              ← CFSG.StandardType.SympMinus.sympMinusZ_coord_one]
    rw [hsplit, hU]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : f i = 1
    · refine Submodule.sum_mem _ fun a _ => ?_
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨i, hi⟩, a), rfl⟩)
    · have h0 := spPlaneTorus_fixed_coord_eq_zero hζ hv hi
      rw [Fin.sum_univ_two, h0 0, h0 1]
      simp
  have hker : CFSG.RankThree.PartOne.KCPrimary.primaryComponent
      (spEnd (spPlaneTorus r ζ f)) (X - 1) =
      LinearMap.ker (spEnd (spPlaneTorus r ζ f) - 1) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.primaryComponent_X_sub_one_eq_ker _
  have hinj : Function.Injective fun p : {i : Fin r // f i = 1} × Fin 2 =>
      WitSpNs.coord p.2 (p.1 : Fin r) := by
    rintro ⟨⟨i, hi⟩, a⟩ ⟨⟨j, hj⟩, b⟩ hpq
    have h1 : WitSpNs.plane (WitSpNs.coord a i) = WitSpNs.plane (WitSpNs.coord b j) :=
      congrArg WitSpNs.plane hpq
    rw [WitSpNs.plane_coord, WitSpNs.plane_coord] at h1
    have h2 : WitSpNs.side (WitSpNs.coord a i) = WitSpNs.side (WitSpNs.coord b j) :=
      congrArg WitSpNs.side hpq
    rw [WitSpNs.side_coord, WitSpNs.side_coord] at h2
    exact Prod.ext (Subtype.ext h1) h2
  have hlin : LinearIndependent K e := by
    have h := (Pi.basisFun K (Fin r ⊕ Fin r)).linearIndependent.comp
      (fun p : {i : Fin r // f i = 1} × Fin 2 => WitSpNs.coord p.2 (p.1 : Fin r)) hinj
    simpa [he, Pi.basisFun_apply, Function.comp_def] using h
  have hfin : Module.finrank K U = 2 * Fintype.card {i : Fin r // f i = 1} := by
    rw [hU, he, finrank_span_eq_card hlin, Fintype.card_prod, Fintype.card_fin, mul_comm]
  rw [CFSG.RankThree.PartOne.spFixedDim, hker, le_antisymm hle hUle, hfin]

private lemma spFixedDim_spPlaneTorus_eq_zero {K : Type} [Field K] [CharP K 2] {r : ℕ}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {f : Fin r → Multiplicative (ZMod 3)}
    (hdense : GGCoordDense f) :
    spFixedDim (spPlaneTorus r ζ f) = 0 := by
  rw [spFixedDim_spPlaneTorus hζ f]
  have hcard : Fintype.card {i : Fin r // f i = 1} = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun i => (hdense i.1).1 i.2⟩
  rw [hcard, mul_zero]

private lemma sq_add_self_add_one_eq_zero {K : Type} [Field K] [CharP K 2] {r : ℕ}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {f : Fin r → Multiplicative (ZMod 3)}
    (hdense : GGCoordDense f) :
    ((spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ^ 2 +
      ((spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + 1 = 0 := by
  classical
  set b : StatedSp r K := spPlaneTorus r ζ f with hb
  have hdim : spFixedDim b = 0 := spFixedDim_spPlaneTorus_eq_zero hζ hdense
  have hker : LinearMap.ker (spEnd b - (1 : Module.End K (Fin r ⊕ Fin r → K))) = ⊥ := by
    rw [← CFSG.HardMathSupport.Timmesfeld.CrossChar.primaryComponent_X_sub_one_eq_ker]
    exact Submodule.finrank_eq_zero.mp hdim
  have hinj : Function.Injective ⇑(spEnd b - (1 : Module.End K (Fin r ⊕ Fin r → K))) :=
    LinearMap.ker_eq_bot.mp hker
  have hb3 : b ^ 3 = 1 := CFSG.StandardType.SympMinus.sympMinusZ_spPlaneTorus_pow (p := 3) ζ f
  have hsp3 : spEnd b ^ 3 = 1 := spEnd_pow hb3
  have hrel : (spEnd b - (1 : Module.End K (Fin r ⊕ Fin r → K))) *
      (spEnd b ^ 2 + spEnd b + (1 : Module.End K (Fin r ⊕ Fin r → K))) = 0 := by
    have hquad : (spEnd b - (1 : Module.End K (Fin r ⊕ Fin r → K))) *
        (spEnd b ^ 2 + spEnd b + (1 : Module.End K (Fin r ⊕ Fin r → K))) =
        spEnd b ^ 3 - 1 := by
      calc (spEnd b - 1) * (spEnd b ^ 2 + spEnd b + 1)
          = spEnd b * (spEnd b ^ 2 + spEnd b + 1) -
              1 * (spEnd b ^ 2 + spEnd b + 1) := sub_mul _ _ _
        _ = (spEnd b * spEnd b ^ 2 + spEnd b * spEnd b + spEnd b * 1) -
              (1 * (spEnd b ^ 2 + spEnd b + 1)) := by rw [mul_add, mul_add, mul_one]
        _ = (spEnd b ^ 3 + spEnd b ^ 2 + spEnd b) -
              (spEnd b ^ 2 + spEnd b + 1) := by
            rw [one_mul, mul_one, show spEnd b * spEnd b = spEnd b ^ 2 by rw [pow_two],
              show spEnd b * spEnd b ^ 2 = spEnd b ^ 3 by
                rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_one, pow_two,
                  mul_assoc]]
        _ = spEnd b ^ 3 - 1 := by abel
    rw [hquad, hsp3, sub_self]
  have hzero : spEnd b ^ 2 + spEnd b + (1 : Module.End K (Fin r ⊕ Fin r → K)) = 0 := by
    apply LinearMap.ext
    intro v
    have h : (spEnd b - (1 : Module.End K (Fin r ⊕ Fin r → K)))
        ((spEnd b ^ 2 + spEnd b + (1 : Module.End K (Fin r ⊕ Fin r → K))) v) = 0 := by
      rw [← Module.End.mul_apply, hrel]
      simp
    exact hinj (by simpa using h)
  have hsp : (Matrix.toLinAlgEquiv' ((b : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) : Module.End K (Fin r ⊕ Fin r → K)) =
      spEnd b := by
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLinAlgEquiv'_apply, spEnd_apply]
  have hmat : Matrix.toLinAlgEquiv' (((b : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ^ 2 +
      ((b : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + 1) = 0 := by
    simpa [hsp] using hzero
  exact Matrix.toLinAlgEquiv'.injective (by simpa using hmat)

private lemma spPlaneTorus_adjoin_algEquiv {K : Type} [Field K] [CharP K 2] [Finite K] {r : ℕ}
    (hK : Nat.card K = 2) (hr : 0 < r)
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {f : Fin r → Multiplicative (ZMod 3)}
    (hdense : GGCoordDense f) :
    Nonempty (AdjoinRoot (X ^ 2 + X + 1 : K[X]) ≃ₐ[K]
      Algebra.adjoin K {((spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)}) := by
  classical
  let p : K[X] := X ^ 2 + X + 1
  let b : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  let A : Subalgebra K (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := Algebra.adjoin K {b}
  have hb : b ^ 2 + b + 1 = 0 := by
    simpa [b] using sq_add_self_add_one_eq_zero hζ hdense
  have hb' : Polynomial.aeval b p = 0 := by
    simpa [p, Polynomial.aeval_def] using hb
  have hcommP : ({b} : Set (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).Pairwise Commute := by
    intro x hx y hy _
    rw [Set.mem_singleton_iff] at hx hy
    subst hx
    subst hy
    exact Commute.refl _
  letI : CommRing A := Algebra.adjoinCommRingOfComm K hcommP
  have hbA : b ∈ A := Algebra.subset_adjoin (by simp)
  let x : A := ⟨b, hbA⟩
  have hx' : Polynomial.aeval x p = 0 := by
    apply Subtype.ext
    simpa [x] using hb'
  let φ : AdjoinRoot p →ₐ[K] A :=
    AdjoinRoot.liftAlgHom (S := K) p (Algebra.ofId K A) x (by
      simpa [Polynomial.aeval_def] using hx')
  have hPirr : Irreducible p := by
    simpa [p] using
      CFSG.HardMathSupport.Curtis.Coordinator.irreducible_X_sq_add_X_add_one_of_card_eq_two hK
  haveI : Fact (Irreducible p) := ⟨hPirr⟩
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  haveI : Nontrivial A := by
    refine ⟨⟨1, 0, ?_⟩⟩
    intro h
    exact one_ne_zero (α := Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      (congrArg Subtype.val h)
  have hφinj : Function.Injective φ := RingHom.injective φ.toRingHom
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ∈
        (Polynomial.aeval (R := K) b : Polynomial K →ₐ[K]
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact y.2
    obtain ⟨q, hq⟩ := hy
    refine ⟨(AdjoinRoot.mk p) q, ?_⟩
    apply Subtype.ext
    rw [AdjoinRoot.liftAlgHom_mk]
    change (Subalgebra.val A) (Polynomial.aeval (R := K) x q) =
      (y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    have h1 : (Polynomial.aeval (R := K) b) q =
        (Subalgebra.val A) (Polynomial.aeval (R := K) x q) := by
      have h := congrArg (fun f : Polynomial K →ₐ[K]
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K => f q)
        (Polynomial.aeval_algHom (Subalgebra.val A) x)
      simpa using h
    rw [← h1]
    exact hq
  exact ⟨AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩⟩

private lemma spPlaneTorus_adjoin_finrank {K : Type} [Field K] [CharP K 2] [Finite K] {r : ℕ}
    (hK : Nat.card K = 2) (hr : 0 < r)
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {f : Fin r → Multiplicative (ZMod 3)}
    (hdense : GGCoordDense f) :
    Module.finrank K (Algebra.adjoin K {((spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)}) = 2 := by
  obtain ⟨e⟩ := spPlaneTorus_adjoin_algEquiv hK hr hζ hdense
  have hPirr : Irreducible (X ^ 2 + X + 1 : K[X]) :=
    CFSG.HardMathSupport.Curtis.Coordinator.irreducible_X_sq_add_X_add_one_of_card_eq_two hK
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨hPirr⟩
  have hpne : (X ^ 2 + X + 1 : K[X]) ≠ 0 := hPirr.ne_zero
  have hdim : Module.finrank K (AdjoinRoot (X ^ 2 + X + 1 : K[X])) = 2 := by
    rw [(AdjoinRoot.powerBasis hpne).finrank, AdjoinRoot.powerBasis_dim hpne,
      CFSG.AGLEmbedding.ToralCensus.natDegree_X_sq_add_X_add_one]
  rw [← e.toLinearEquiv.finrank_eq]
  exact hdim

private lemma idem_eq_zero_or_one {K : Type} [Field K] [CharP K 2] [Finite K] {r : ℕ}
    (hK : Nat.card K = 2) (hr : 0 < r)
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {f : Fin r → Multiplicative (ZMod 3)}
    (hdense : GGCoordDense f) {e : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (heA : e ∈ Algebra.adjoin K {((spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)})
    (hidem : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  obtain ⟨φ⟩ := spPlaneTorus_adjoin_algEquiv hK hr hζ hdense
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) :=
    ⟨CFSG.HardMathSupport.Curtis.Coordinator.irreducible_X_sq_add_X_add_one_of_card_eq_two hK⟩
  have hidemA : IsIdempotentElem
      (⟨e, heA⟩ : Algebra.adjoin K {((spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)}) := Subtype.ext hidem
  have hidem' : IsIdempotentElem (φ.symm ⟨e, heA⟩) := hidemA.map φ.symm
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem' with h0 | h1
  · left
    have h : (⟨e, heA⟩ : Algebra.adjoin K {((spPlaneTorus r ζ f : GL
        (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)}) = 0 := by
      simpa using congrArg φ h0
    exact Subtype.ext_iff.mp h
  · right
    have h : (⟨e, heA⟩ : Algebra.adjoin K {((spPlaneTorus r ζ f : GL
        (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)}) = 1 := by
      simpa using congrArg φ h1
    exact Subtype.ext_iff.mp h

private lemma blockDegree_one_eq_two {K : Type} [Field K] [CharP K 2] [Finite K] {r : ℕ}
    (hK : Nat.card K = 2) (hr : 0 < r)
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {f : Fin r → Multiplicative (ZMod 3)}
    (hdense : GGCoordDense f) :
    blockDegree (Algebra.adjoin K (Units.val ''
      ({(spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K)} : Set (GL (Fin r ⊕ Fin r) K)))) 1 = 2 := by
  have himg : Units.val '' ({(spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K)} :
      Set (GL (Fin r ⊕ Fin r) K)) =
      {((spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)} := by
    simp
  rw [himg, blockDegree, LinearMap.mulRight_one, Submodule.map_id,
    Subalgebra.finrank_toSubmodule]
  exact spPlaneTorus_adjoin_finrank hK hr hζ hdense

theorem ggCommonJSpTwo_label_dense {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {r : ℕ} (hr : 4 ≤ r)
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    {f : Fin r → Multiplicative (ZMod 3)} {J : Subgroup (StatedSp r K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({spPlaneTorus r ζ f} : Set (StatedSp r K))))
    (hdense : GGCoordDense f) {S : Finset (Fin r)} {s : Fin r → ZMod 3}
    (hs : ∀ i, s i * s i = 1) (hS : S.card = r)
    (hAut : FrameBs.sectionFrameAut (spPlaneTorus r ζ) J =
      TypeBDatum.twistedPermAut r 3 S s hs) :
    LargeEvenInLambda2 ⟨.twA, r - 1, 1⟩ ∧
      GGHasLabel ⟨.twA, r - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J) ∧
      ((⟨.twA, r - 1, 1⟩ : LargeEvenLabel) = ⟨.twA, 3, 1⟩ → Subgroup.center ↥J = ⊥) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by simpa using hK)
  have hKf : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hr0 : 0 < r := by omega
  haveI : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set b : StatedSp r K := spPlaneTorus r ζ f with hb
  have hb3 : b ^ 3 = 1 := CFSG.StandardType.SympMinus.sympMinusZ_spPlaneTorus_pow (p := 3) ζ f
  have hf1 : f ≠ 1 := by
    intro hf
    exact (hdense ⟨0, hr0⟩).1 (by simp [hf])
  have hbne : b ≠ 1 := by
    rw [hb]
    exact CFSG.StandardType.SympMinus.sympMinusZ_spPlaneTorus_ne_one ζ hζ f hf1
  have hbneGL : ((b : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ≠ 1 := by
    intro h
    exact hbne (Subtype.ext (Units.ext h))
  have hoddB : Odd (orderOf b) := by
    have h3 : orderOf b = 3 := orderOf_eq_prime hb3 hbne
    rw [h3]
    norm_num
  have hodd : Odd (orderOf (b : GL (Fin r ⊕ Fin r) K)) := by
    rw [← Subgroup.orderOf_mk (b : GL (Fin r ⊕ Fin r) K) b.2]
    exact hoddB
  obtain ⟨ε, hε, hJε⟩ :=
    CFSG.StandardType.ClassicalBlocks.exists_isPrimAdjIdemIn_isComponentOf_glBlockCentralizer_Sp
      b hoddB J hJ
  have hεA : ε ∈ Algebra.adjoin K {((spPlaneTorus r ζ f : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)} := by
    simpa [Set.image_singleton, hb] using hε.1
  have hεeq : ε = 1 := by
    rcases idem_eq_zero_or_one hK hr0 hζ hdense hεA hε.2.1 with h0 | h1
    · exact absurd h0 hε.2.2.1
    · exact h1
  subst hεeq
  let F : Subgroup (StatedSp r K) :=
    glBlockCentralizer (StatedSp r K).subtype
      ({(b : GL (Fin r ⊕ Fin r) K)} : Set (GL (Fin r ⊕ Fin r) K)) 1
  have hJεF : CFSG.Assembly.IsComponentOf J F := hJε
  have hprim1 : IsPrimIdemIn (Algebra.adjoin K (Units.val ''
      ({(b : GL (Fin r ⊕ Fin r) K)} : Set (GL (Fin r ⊕ Fin r) K)))) 1 := by
    refine ⟨Subalgebra.one_mem _, IsIdempotentElem.one, one_ne_zero, ?_⟩
    intro e' he' hidem' _
    exact idem_eq_zero_or_one hK hr0 hζ hdense
      (by simpa [Set.image_singleton, hb] using he') hidem'
  have hbd : blockDegree (Algebra.adjoin K (Units.val ''
      ({(b : GL (Fin r ⊕ Fin r) K)} : Set (GL (Fin r ⊕ Fin r) K)))) 1 = 2 :=
    blockDegree_one_eq_two hK hr0 hζ hdense
  obtain ⟨d, m, E, hEfield, hEfin, hd1, hEcard, hbdim, hbdeg, ⟨eGU⟩⟩ :=
    CFSG.StandardType.ClassicalBlocks.blockGroup_iso_Sp_unitary
      (b : GL (Fin r ⊕ Fin r) K) b.2 hodd hε hprim1 (by simpa using hbneGL)
  have hd : d = 1 := by
    have h2 : 2 * d = 2 := by rw [← hbdeg, hbd]
    omega
  subst hd
  letI : Field E := hEfield
  letI : Fintype E := hEfin
  letI : Finite E := Fintype.finite hEfin
  have hEcard4 : Fintype.card E = 2 ^ 2 := by
    rw [hEcard, hKf]
    norm_num
  letI : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hEcard4
  have hE4 : Nat.card E = (Fintype.card K ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hEcard
  obtain ⟨f', hf'1, hQf', hlab⟩ :=
    CFSG.StandardType.exists_unitary_label_of_isComponentOf_iso_unitaryFull
      (H := StatedSp r K) (F := F) (m := m) (Q := Fintype.card K ^ 1) (E := E)
      hE4 eGU hJεF
  have hQ2 : Fintype.card K ^ 1 = 2 := by
    rw [pow_one]
    exact hKf
  have hf' : f' = 1 := by
    have h : 2 ^ f' = 2 ^ 1 := by
      rw [← hQf', hQ2]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  have hdim : Module.finrank K (LinearMap.range
      (Matrix.toLin' (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) = 2 * r := by
    rw [Matrix.toLin'_one, LinearMap.range_id, finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hmr : m = r := by
    have h := hbdim
    rw [hdim] at h
    omega
  rw [hmr] at eGU
  rw [hQ2] at eGU
  rw [hQ2] at hE4
  rw [hmr, hf'] at hlab
  have hΛ : LargeEvenInLambda2 ⟨.twA, r - 1, 1⟩ := by
    rcases hlab with ⟨hm2, -⟩ | ⟨hm3, hΛ, hGlab⟩
    · omega
    · exact hΛ
  have hGlab : GGHasLabel ⟨.twA, r - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
    rcases hlab with ⟨hm2, -⟩ | ⟨hm3, hΛ, hGlab⟩
    · omega
    · exact hGlab
  refine ⟨hΛ, hGlab, ?_⟩
  intro hlab_eq
  have hr4 : r = 4 := by
    have h1 : r - 1 = 3 := congrArg LargeEvenLabel.rank hlab_eq
    omega
  let φ : ↥F →* GL (Fin r) E :=
    (CFSG.StandardType.ClassicalBlocks.GUFull r 2 E).subtype.comp eGU.toMonoidHom
  have hinj : Function.Injective φ :=
    (CFSG.StandardType.ClassicalBlocks.GUFull r 2 E).subtype_injective.comp eGU.injective
  have hcomp : CFSG.IsComponent (J.subgroupOf F) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJεF.1).1 hJεF
  have hmapped : CFSG.IsComponent ((J.subgroupOf F).map eGU.toMonoidHom) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent eGU hcomp
  have htop : CFSG.Assembly.IsComponentOf ((J.subgroupOf F).map eGU.toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native _).2 hmapped
  have hmap : CFSG.Assembly.IsComponentOf (((J.subgroupOf F).map eGU.toMonoidHom).map
      (CFSG.StandardType.ClassicalBlocks.GUFull r 2 E).subtype)
      ((⊤ : Subgroup ↥(CFSG.StandardType.ClassicalBlocks.GUFull r 2 E)).map
        (CFSG.StandardType.ClassicalBlocks.GUFull r 2 E).subtype) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := (CFSG.StandardType.ClassicalBlocks.GUFull r 2 E).subtype)
      (CFSG.StandardType.ClassicalBlocks.GUFull r 2 E).subtype_injective).2 htop
  have hCφ : CFSG.Assembly.IsComponentOf ((J.subgroupOf F).map φ)
      (CFSG.StandardType.ClassicalBlocks.GUFull r 2 E) := by
    simpa only [Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype, φ] using hmap
  have hEqSU := CFSG.StandardType.eq_statedSU_of_isComponentOf_unitaryFull
    (m := r) (Q := 2) (E := E) hE4 hCφ
  let ec : ↥J ≃* ↥(CFSG.Open.StatedSU r (2 ^ 1) E) :=
    (Subgroup.subgroupOfEquivOfLe hJεF.1).symm.trans
      (((J.subgroupOf F).equivMapOfInjective φ hinj).trans
        (MulEquiv.subgroupCongr hEqSU))
  have hcenterSu : Subgroup.center (CFSG.ClassicalInvolution.Phan.Su E 2 1 4) = ⊥ :=
    CFSG.ClassicalInvolution.PhanDn.QTwo.center_Su_four_eq_bot (by rw [hE4]; norm_num)
  have hEqSUid : CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution E 2 1) 4 =
      CFSG.Open.StatedSU 4 (2 ^ 1) E :=
    CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 1)
      (by simpa using hE4) 4
  have hmapCenter := Subgroup.map_center_eq (MulEquiv.subgroupCongr hEqSUid)
  rw [hcenterSu] at hmapCenter
  have hcenterStated : Subgroup.center (CFSG.Open.StatedSU 4 (2 ^ 1) E) = ⊥ := by
    simpa using hmapCenter.symm
  have hcenterStated' : Subgroup.center (CFSG.Open.StatedSU r (2 ^ 1) E) = ⊥ := by
    rw [hr4]
    exact hcenterStated
  have hcenterJ : Subgroup.center ↥J = ⊥ := by
    have hmap2 := Subgroup.map_center_eq ec
    rw [hcenterStated'] at hmap2
    rw [eq_bot_iff]
    intro z hz
    have hmem : ec z ∈ (Subgroup.center ↥J).map (↑ec) := ⟨z, hz, rfl⟩
    rw [hmap2] at hmem
    rw [Subgroup.mem_bot] at hmem ⊢
    exact ec.injective (hmem.trans (map_one ec).symm)
  exact hcenterJ

private lemma exists_spFixedFactor_equiv_statedSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    {f : Fin r → Multiplicative (ZMod 3)}
    (blocks : SpPrimaryBlocks 2 1 3 (spPlaneTorus r ζ f)
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K (spPlaneTorus r ζ f)))
    (hpos : 0 < spFixedDim (spPlaneTorus r ζ f)) :
    ∃ s : ℕ, spFixedDim (spPlaneTorus r ζ f) = 2 * s ∧
      Nonempty (↥(spFixedFactor (spPlaneTorus r ζ f)) ≃* StatedSp s K) := by
  have hmem : (X - 1 : K[X]) ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors
      (spEnd (spPlaneTorus r ζ f)) :=
    CFSG.RankThree.PartOne.X_sub_one_mem_primaryFactors _ hpos
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hBalt : ((spForm r K).restrict
      (CFSG.RankThree.PartOne.KCPrimary.primaryComponent (spEnd (spPlaneTorus r ζ f))
        (X - 1))).IsAlt := fun v => spForm_isAlt v.1
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hBalt
      blocks.fixed_nondegenerate
  exact ⟨s, hs, ⟨φ.trans e⟩⟩

theorem ggCommonJSpTwo_label_sparse {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {r : ℕ} (hr : 3 ≤ r)
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    {f : Fin r → Multiplicative (ZMod 3)} {J : Subgroup (StatedSp r K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({spPlaneTorus r ζ f} : Set (StatedSp r K))))
    (hsparse : GGCoordSparse f) {S : Finset (Fin r)} (hS : S.card = r - 1)
    (hAut : FrameBs.sectionFrameAut (spPlaneTorus r ζ) J =
      TypeBDatum.signedSupportedAut r 3 S) :
    (4 ≤ r ∧ LargeEvenInLambda2 ⟨.C, r - 1, 1⟩ ∧
        GGHasLabel ⟨.C, r - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      (r = 3 ∧ LargeEvenInLambda2 ⟨.B2der, 0, 1⟩ ∧
        GGHasLabel ⟨.B2der, 0, 1⟩ (↥J ⧸ Subgroup.center ↥J)) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by simpa using hK)
  classical
  have hf1 : f ≠ 1 := by
    intro hf
    have hx1 : spPlaneTorus r ζ f = 1 := by rw [hf, map_one]
    have hcent : Subgroup.centralizer ({spPlaneTorus r ζ f} : Set (StatedSp r K)) = ⊤ := by
      rw [hx1]
      ext g
      simp [Subgroup.mem_centralizer_iff]
    have hJtop : J = ⊤ := by
      have hm : 1 ≤ r := by omega
      have h1 : ¬(r = 1 ∧ Nat.card K = 2) := by rintro ⟨h, -⟩; omega
      have h2 : ¬(r = 2 ∧ Nat.card K = 2) := by rintro ⟨h, -⟩; omega
      have hQ : CFSG.Assembly.IsQuasisimple (⊤ : Subgroup (StatedSp r K)) :=
        CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv
          (Sp.isQuasisimple_statedSp_of_not_small (K := K) hm h1 h2)
      refine CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hQ ?_
      rwa [hcent] at hJ
    have haut : TypeBDatum.signedAut r 3 = TypeBDatum.signedSupportedAut r 3 S := by
      rw [← hAut, hJtop]
      exact (CFSG.StandardType.SympMinus.sympMinus_frameAut_top (p := 3) (m := r)
        Nat.prime_three (by norm_num) hζ hζW).symm
    have hSne : S ≠ Finset.univ := by
      intro h
      rw [h, Finset.card_univ, Fintype.card_fin] at hS
      omega
    obtain ⟨i, hiS⟩ : ∃ i, i ∉ S := by
      by_contra h
      exact hSne (Finset.eq_univ_of_forall fun i => by_contra fun hi => h ⟨i, hi⟩)
    have hfixS : ∀ j ∈ S, (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)) :
        Fin r → Multiplicative (ZMod 3)) j = 1 := by
      intro j hj
      have hji : j ≠ i := by
        rintro rfl
        exact hiS hj
      change Function.update (1 : Fin r → Multiplicative (ZMod 3)) i
        (Multiplicative.ofAdd (1 : ZMod 3)) j = 1
      rw [Function.update_of_ne hji]
      simp
    have hmem : SpCoord.sgnAut (p := 3) i ∈ TypeBDatum.signedSupportedAut r 3 S := by
      rw [← haut]
      change SpCoord.sgnAut (p := 3) i ∈ TypeBDatum.signedSupportedAut r 3 Finset.univ
      exact Subgroup.subset_closure (Set.mem_union_left _ ⟨i, Finset.mem_univ i, rfl⟩)
    have hgfix : SpCoord.sgnAut (p := 3) i
        (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)) :
          Fin r → Multiplicative (ZMod 3)) =
        Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)) :=
      FrameBs.signedSupportedAut_fix hfixS _ hmem
    rw [SpCoord.sgnAut_mulSingle_self] at hgfix
    have hcc : (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ = Multiplicative.ofAdd 1 := by
      have := congrFun hgfix i
      simpa using this
    exact absurd hcc (by decide)
  obtain ⟨i₀, hi₀⟩ := hsparse
  have hi₀' : f i₀ ≠ 1 := by
    intro h
    apply hf1
    funext j
    by_cases hj : j = i₀
    · rw [hj, h, Pi.one_apply]
    · rw [hi₀ j hj, Pi.one_apply]
  have hZeq : (Finset.univ.filter fun i : Fin r => f i = 1) = Finset.univ.erase i₀ := by
    ext j
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨-, hj⟩
      exact ⟨fun hji => hi₀' (hji.symm ▸ hj), Finset.mem_univ j⟩
    · rintro ⟨hji, -⟩
      exact ⟨Finset.mem_univ j, hi₀ j hji⟩
  have hZcard : (Finset.univ.filter fun i : Fin r => f i = 1).card = r - 1 := by
    rw [hZeq, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
      Fintype.card_fin]
  have hdim : spFixedDim (spPlaneTorus r ζ f) = 2 * (r - 1) := by
    rw [spFixedDim_spPlaneTorus hζ f, Fintype.card_subtype, hZcard]
  obtain ⟨f', hf'1, hKf', blocks⟩ :=
    CFSG.StandardType.SympMinus.sympMinusZ_blocks (p := 3) (m := r) Nat.prime_three
      (by norm_num) ζ hζ f hf1
  have hf' : f' = 1 := by
    have h : 2 ^ f' = 2 ^ 1 := by rw [← hKf', hK, pow_one]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  subst hf'
  have hle : J ≤ spFixedFactor (spPlaneTorus r ζ f) := by
    rcases CFSG.StandardType.SympMinus.sympMinus_component_localize (p := 3) (m := r)
      Nat.prime_three (by norm_num) (by rw [hK]) hζ hζW f hJ with h | ⟨c, hc, h⟩
    · exact CFSG.StandardType.SympMinus.sympMinusZ_le_spFixedFactor ζ f hJ h
    · exfalso
      have hsub : (Finset.univ.filter fun i : Fin r => f i = c ∨ f i = c⁻¹) ⊆ {i₀} := by
        intro i hi
        rw [Finset.mem_filter] at hi
        obtain ⟨-, hci⟩ := hi
        rw [Finset.mem_singleton]
        by_contra hne
        have hfi : f i = 1 := hi₀ i hne
        rcases hci with h1 | h1
        · exact hc (h1.symm.trans hfi)
        · exact hc (inv_eq_one.mp (h1.symm.trans hfi))
      have hcard : (Finset.univ.filter fun i : Fin r => f i = c ∨ f i = c⁻¹).card ≤ 1 := by
        calc _ ≤ ({i₀} : Finset (Fin r)).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton i₀
      have hge := (CFSG.StandardType.SympMinus.sympMinus_block_unitary (hq := Or.inr hK)
        (p := 3) (m := r) Nat.prime_three (by norm_num) (by rw [hK]) hζ hζW f hc
        hJ h).1
      omega
  rcases Nat.lt_or_ge r 4 with hr4 | hr4
  ·
    have hr3 : r = 3 := by omega
    have hdim4 : spFixedDim (spPlaneTorus r ζ f) = 4 := by
      rw [hdim]; omega
    have hJe : J = ⁅spFixedFactor (spPlaneTorus r ζ f),
        spFixedFactor (spPlaneTorus r ζ f)⁆ :=
      CFSG.StandardType.SympMinus.sympMinusZ_d4_a6 (p := 3) (m := r) Nat.prime_three
        (by norm_num) ζ f (f := 1) (by norm_num) hK hf1 blocks hdim4 hJ hle
    refine Or.inr ⟨hr3, by simp [LargeEvenInLambda2], ?_⟩
    obtain ⟨eA⟩ := (CFSG.RankThree.PartOne.spFixed_four_two_alt hK blocks hdim4).1
    let e6 : ↥J ≃* alternatingGroup (Fin 6) := (MulEquiv.subgroupCongr hJe).trans eA
    let eZ : ↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6) :=
      (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center (alternatingGroup (Fin 6)))
        e6 (Subgroup.map_center_eq e6)).trans
        ((QuotientGroup.quotientMulEquivOfEq
          CFSG.EvenSporadicStandard.M22Std.center_alternatingGroup_six).trans
          QuotientGroup.quotientBot)
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_b2der eZ
  ·
    have hne : (Finset.univ.filter fun i : Fin r => f i = 1).Nonempty :=
      Finset.card_pos.mp (by rw [hZcard]; omega)
    obtain ⟨hFq, hFc⟩ :=
      CFSG.StandardType.SympMinus.sympMinusZ_fixedFactor_isComponent (p := 3) (m := r)
        Nat.prime_three (by norm_num) ζ f (Or.inr ⟨hK, by rw [hdim]; omega⟩) (f := 1)
        (by norm_num) (by simpa using hK) hf1 blocks hne
    have hFq' : CFSG.Assembly.IsQuasisimple ↥(spFixedFactor (spPlaneTorus r ζ f)) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hFq
    have hJeq : J = spFixedFactor (spPlaneTorus r ζ f) :=
      CFSG.StandardType.SympMinus.sympMinusZ_eq_fixedFactor ζ f hle hJ hFq' hFc
    obtain ⟨s, hs, ⟨e⟩⟩ := exists_spFixedFactor_equiv_statedSp blocks (by rw [hdim]; omega)
    have hsr : s = r - 1 := by omega
    subst hsr
    let eJ : ↥J ≃* StatedSp (r - 1) K := (MulEquiv.subgroupCongr hJeq).trans e
    have hZsp : Subgroup.center (StatedSp (r - 1) K) = ⊥ :=
      CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := r - 1)
        (by omega)
    have hZ : Subgroup.center ↥J = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hez : eJ z ∈ Subgroup.center (StatedSp (r - 1) K) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := eJ.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
      rw [hZsp, Subgroup.mem_bot] at hez
      rw [Subgroup.mem_bot]
      exact eJ.injective (hez.trans (map_one eJ).symm)
    haveI : NeZero (r - 1) := ⟨by omega⟩
    have hrec : GGHasLabel ⟨.C, r - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
      change ∃ (K' : Type) (_ : Field K') (_ : Finite K'),
        Nat.card K' = 2 ^ 1 ∧ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃*
          LargeEvenProj (LargeEvenSpGroup K' (r - 1)))
      exact ⟨K, inferInstance, inferInstance, hK,
        ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
          (eJ.trans (TableBSymp.spProjEquivSp (K := K) (m := r - 1)).symm)⟩⟩
    refine Or.inl ⟨hr4, ?_, hrec⟩
    simp only [LargeEvenInLambda2]
    exact ⟨le_refl 1, by omega, fun h2 => by omega⟩

theorem ggCommonJSpTwo_label_a6 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {r : ℕ} (hr : r = 3) {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    {f : Fin r → Multiplicative (ZMod 3)} {J : Subgroup (StatedSp r K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({spPlaneTorus r ζ f} : Set (StatedSp r K))))
    (hsparse : GGCoordSparse f)
    (hA6 : ∃ f₀ : ℕ, SpPrimaryBlocks 2 f₀ 3 (spPlaneTorus r ζ f)
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K (spPlaneTorus r ζ f)) ∧
      spFixedDim (spPlaneTorus r ζ f) = 4 ∧
      J = ⁅spFixedFactor (spPlaneTorus r ζ f), spFixedFactor (spPlaneTorus r ζ f)⁆) :
    LargeEvenInLambda2 ⟨.B2der, 0, 1⟩ ∧
      GGHasLabel ⟨.B2der, 0, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨f₀, hblocks, hdim4, hJeq⟩ := hA6
  have hΛ : LargeEvenInLambda2 ⟨.B2der, 0, 1⟩ := by
    simp [LargeEvenInLambda2]
  refine ⟨hΛ, ?_⟩
  obtain ⟨eA⟩ := (CFSG.RankThree.PartOne.spFixed_four_two_alt hK hblocks hdim4).1
  let e : ↥J ≃* alternatingGroup (Fin 6) := (MulEquiv.subgroupCongr hJeq).trans eA
  let eZ : ↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center (alternatingGroup (Fin 6)))
      e (Subgroup.map_center_eq e)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        CFSG.EvenSporadicStandard.M22Std.center_alternatingGroup_six).trans
        QuotientGroup.quotientBot)
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_b2der eZ

end CFSG.StandardType.CommonJSpTwo

end
