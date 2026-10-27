module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModelBasic
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.OddTranspositions.PartFour.LinePolar
public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.RankThree.PartOne.AUTSL.TraceAS
import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.OddTranspositions.PartThree.Twelve.NineSp
import CFSG.OddTranspositions.PartThree.Twelve.TenModel
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpArith
import CFSG.RankThree.PartOne.AUTSL.TraceASApply
import CFSG.ClassicalGroups.Orthogonal.Transitive
import CFSG.GroupTheory.CentralizerSingletonEquiv
import CFSG.LieType.SeitzGeneration.SpSubEmb
public import CFSG.OddTranspositions.PartFour.LineStabilizer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open QuadraticMap
open CFSG.Timmesfeld.Bridge CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
open CFSG.Open CFSG.OddTranspositions.PartFour CFSG.RankThree.PartOne.AUTSL
open CFSG.ClassicalGroups.Orthogonal
open CFSG.GroupTheory CFSG.GroupTheory.WeirSylow CFSG.LieType.SeitzGeneration

variable {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
  (hQ₀ : ∀ a b, QuadraticMap.polar Q₀ a b = spForm k F a b)

omit [DecidableEq F] in
private theorem fst_mLift_sq (x : Fin k ⊕ Fin k → F) :
    (mLift Q₀ x).1.1 ^ 2 = 1 + Q₀ x := by
  simpa [mLift] using frobeniusEquiv_symm_pow_p F 2 (1 + Q₀ x)

omit [Fintype F] [DecidableEq F] in
private theorem polar_linMulLin_self {l : (Fin k ⊕ Fin k → F) →ₗ[F] F}
    (a b : Fin k ⊕ Fin k → F) : polar (QuadraticMap.linMulLin l l) a b = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h : polar (QuadraticMap.linMulLin l l) a b = 2 * (l a * l b) := by
    simp only [polar, QuadraticMap.linMulLin_apply, map_add]
    ring
  rw [h, h2, zero_mul]

private noncomputable def chartLin (g : ↥(Subgroup.centralizer {mRefl Q₀ mU})) :
    (Fin k ⊕ Fin k → F) →ₗ[F] (Fin k ⊕ Fin k → F) :=
  (LinearMap.snd F (F × F) (Fin k ⊕ Fin k → F)).comp
    ((((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) : MSpace k F →ₗ[F] MSpace k F).comp
      (LinearMap.prod (0 : (Fin k ⊕ Fin k → F) →ₗ[F] (F × F)) LinearMap.id))

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem chartLin_apply (g : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    (x : Fin k ⊕ Fin k → F) :
    chartLin g x = (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2 :=
  rfl

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem chartLin_fst_snd (g : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    (x : Fin k ⊕ Fin k → F) :
    (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).1.2 = 0 := by
  have hgU : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU = mU :=
    (mem_centralizer_mRefl_mU_iff (hQ₀ := hQ₀) (g : MGroup Q₀)).mp g.2
  have h1 : polar (mForm Q₀) mU (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)) =
      polar (mForm Q₀) (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU)
        (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)) := by rw [hgU]
  have h2 : polar (mForm Q₀) mU
      (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)) = 0 := by
    rw [h1, polar_map_of_mem (g : MGroup Q₀).2, polar_mU_eq_snd]
  rwa [polar_mU_eq_snd] at h2

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem chartLin_eq_zero (g : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    {x : Fin k ⊕ Fin k → F} (hx : chartLin g x = 0) : x = 0 := by
  have hgU : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU = mU :=
    (mem_centralizer_mRefl_mU_iff (hQ₀ := hQ₀) (g : MGroup Q₀)).mp g.2
  have hZb : (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).1.2 = 0 :=
    chartLin_fst_snd (hQ₀ := hQ₀) g x
  have hZ2 : (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2 = 0 := by
    rw [← chartLin_apply]
    exact hx
  have hZeq : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x) =
      ((((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).1.1) • mU := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp [mU]
    · simp [mU, hZb]
    · simp [mU, hZ2]
  have hV : ((0, 0), x) =
      ((((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).1.1) • mU := by
    apply ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F).injective
    calc ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)
        = ((((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).1.1) • mU := hZeq
      _ = ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F)
            (((((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).1.1) • mU) := by
          rw [map_smul, hgU]
  have hx0 : x = 0 := by
    have h1 := congrArg (fun z : MSpace k F => z.2) hV
    simpa [mU] using h1
  exact hx0

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem chartLin_injective (g : ↥(Subgroup.centralizer {mRefl Q₀ mU})) :
    Function.Injective (chartLin g) := by
  intro x y hxy
  have h : x - y = 0 := chartLin_eq_zero (hQ₀ := hQ₀) g (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp h

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem chartLin_spForm (g : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    (x y : Fin k ⊕ Fin k → F) :
    spForm k F (chartLin g x) (chartLin g y) = spForm k F x y := by
  have hZb : ∀ z : Fin k ⊕ Fin k → F,
      (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), z)).1.2 = 0 :=
    fun z => chartLin_fst_snd (hQ₀ := hQ₀) g z
  have h1 : polar (mForm Q₀) (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x))
      (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), y)) =
      polar (mForm Q₀) ((0, 0), x) ((0, 0), y) :=
    polar_map_of_mem (g : MGroup Q₀).2 ((0, 0), x) ((0, 0), y)
  rw [polar_mForm (hQ₀ := hQ₀), polar_mForm (hQ₀ := hQ₀), hZb x, hZb y] at h1
  simp only [mul_zero, add_zero] at h1
  rw [chartLin_apply g x, chartLin_apply g y]
  simpa using h1

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem chartLin_mul (g h : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    (x : Fin k ⊕ Fin k → F) :
    chartLin (g * h) x = chartLin g (chartLin h x) := by
  have hgU : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU = mU :=
    (mem_centralizer_mRefl_mU_iff (hQ₀ := hQ₀) (g : MGroup Q₀)).mp g.2
  have hsplit : ((h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x) =
      ((0, 0), (((h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2) +
        ((((h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).1.1) • mU := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp [mU]
    · simp [mU, chartLin_fst_snd (hQ₀ := hQ₀) h x]
    · simp [mU]
  have hgvec : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F)
        (((h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)) =
      ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F)
          ((0, 0), (((h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2) +
        ((((h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).1.1) •
          (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU) := by
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul]
  rw [hgU] at hgvec
  have h2 := congrArg (fun z : MSpace k F => z.2) hgvec
  simp only [Prod.snd_add, Prod.smul_snd, mU, smul_zero, add_zero] at h2
  have hA : chartLin (g * h) x =
      (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F)
        (((h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x))).2 := rfl
  have hB : chartLin g (chartLin h x) =
      (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F)
        ((0, 0), (((h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2)).2 := rfl
  rw [hA, hB]
  exact h2

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem chartLin_one :
    chartLin (1 : ↥(Subgroup.centralizer {mRefl Q₀ mU})) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [chartLin_apply]
  rfl

include hQ₀ in
private noncomputable def chartUnit (g : ↥(Subgroup.centralizer {mRefl Q₀ mU})) :
    ↥(CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup (spForm k F)) :=
  ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv
      (LinearEquiv.ofInjectiveEndo (chartLin g) (chartLin_injective (hQ₀ := hQ₀) g)),
    (CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup).mpr
      (fun x y => chartLin_spForm (hQ₀ := hQ₀) g x y)⟩

private noncomputable def chartHom (hQ : ∀ a b, polar Q₀ a b = spForm k F a b) :
    ↥(Subgroup.centralizer {mRefl Q₀ mU}) →*
      ↥(CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup (spForm k F)) where
  toFun g := chartUnit (hQ₀ := hQ) g
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : (Fin k ⊕ Fin k → F) →ₗ[F] (Fin k ⊕ Fin k → F) => f x)
      (chartLin_one (Q₀ := Q₀))
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    exact chartLin_mul (hQ₀ := hQ) g h x

omit [DecidableEq F] in
theorem mRefl_mLift_mem_centralizer (x : Fin k ⊕ Fin k → F) :
    mRefl Q₀ (mLift Q₀ x) ∈ Subgroup.centralizer {mRefl Q₀ mU} :=
  mRefl_mem_centralizer_of_polar_eq_zero (by rw [polar_comm]; exact polar_mU_mLift x)

omit hQ₀ [DecidableEq F] in
private theorem chartLin_mRefl_mLift (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (x : Fin k ⊕ Fin k → F) :
    chartLin (⟨mRefl Q₀ (mLift Q₀ x), mRefl_mLift_mem_centralizer x⟩ :
      ↥(Subgroup.centralizer {mRefl Q₀ mU})) = spEnd (spTransvection x 1) := by
  apply LinearMap.ext
  intro z
  rw [chartLin_apply, spEnd_spTransvection]
  have hL : mForm Q₀ (mLift Q₀ x) = 1 := mForm_mLift x
  have hL0 : mForm Q₀ (mLift Q₀ x) ≠ 0 := by rw [hL]; exact one_ne_zero
  have hcoe : ((⟨mRefl Q₀ (mLift Q₀ x), mRefl_mLift_mem_centralizer x⟩ :
      ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = mRefl Q₀ (mLift Q₀ x) := rfl
  rw [hcoe, show ((mRefl Q₀ (mLift Q₀ x) : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) =
    reflect (mForm Q₀) (mLift Q₀ x) from rfl, reflect_apply hL0]
  have hp : polar (mForm Q₀) (mLift Q₀ x) ((0, 0), z) = spForm k F x z := by
    rw [polar_mForm (hQ₀ := hQ₀)]
    simp [mLift]
  rw [hp, hL, div_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hneg : ((0, 0), z) - spForm k F x z • mLift Q₀ x =
      ((0, 0), z) + spForm k F x z • mLift Q₀ x := by
    rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  rw [hneg]
  have hsp : spForm k F z x = spForm k F x z := by rw [← hQ₀, ← hQ₀, polar_comm]
  rw [hsp]
  simp [mLift]

private noncomputable def chartSigma (hQ : ∀ a b, polar Q₀ a b = spForm k F a b) :
    ↥(Subgroup.centralizer {mRefl Q₀ mU}) →* ↥(StatedSp k F) :=
  (spLinEquiv k F).symm.toMonoidHom.comp (chartHom (Q₀ := Q₀) hQ)

omit [DecidableEq F] in
private theorem chartSigma_mRefl_mLift (hQ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (x : Fin k ⊕ Fin k → F) :
    chartSigma (Q₀ := Q₀) hQ ⟨mRefl Q₀ (mLift Q₀ x), mRefl_mLift_mem_centralizer x⟩ =
      spTransvection x 1 := by
  apply spLin_injective
  change spLin k F ((spLinEquiv k F).symm (chartHom (Q₀ := Q₀) hQ
    ⟨mRefl Q₀ (mLift Q₀ x), mRefl_mLift_mem_centralizer x⟩)) =
    spLin k F (spTransvection x 1)
  rw [spLin_spLinEquiv_symm (r := k) (K := F)]
  apply Units.ext
  apply LinearMap.ext
  intro z
  exact congrArg (fun f : (Fin k ⊕ Fin k → F) →ₗ[F] (Fin k ⊕ Fin k → F) => f z)
    (chartLin_mRefl_mLift (hQ₀ := hQ) x)

omit [DecidableEq F] in
private theorem chartSigma_surjective (hQ : ∀ a b, polar Q₀ a b = spForm k F a b) :
    Function.Surjective (chartSigma (Q₀ := Q₀) hQ) := by
  have htop : (chartSigma (Q₀ := Q₀) hQ).range = ⊤ := by
    rw [eq_top_iff]
    rw [← CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.closure_spTransvections_eq_top]
    rw [Subgroup.closure_le]
    rintro g ⟨v, t, rfl⟩
    set c : F := (frobeniusEquiv F 2).symm t with hcdef
    set w : Fin k ⊕ Fin k → F := c • v with hw
    have hc2 : c ^ 2 = t := by
      rw [hcdef]
      exact frobeniusEquiv_symm_pow_p F 2 t
    have hT : spTransvection v t = spTransvection w 1 := by
      rw [← hc2, hw]
      simpa [_root_.sq] using
        (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.spTransvection_smul_eq c v 1).symm
    rw [hT]
    exact ⟨⟨mRefl Q₀ (mLift Q₀ w), mRefl_mLift_mem_centralizer w⟩,
      chartSigma_mRefl_mLift (Q₀ := Q₀) hQ w⟩
  intro y
  have hy : y ∈ (chartSigma (Q₀ := Q₀) hQ).range := htop ▸ Subgroup.mem_top y
  rwa [MonoidHom.mem_range] at hy

omit [Fintype F] [DecidableEq F] in
private theorem chartLin_mRefl_mU :
    chartLin (⟨mRefl Q₀ mU, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      ↥(Subgroup.centralizer {mRefl Q₀ mU})) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [chartLin_apply]
  have hL0 : mForm Q₀ mU ≠ 0 := by
    rw [mForm_mU (Q₀ := Q₀)]
    exact one_ne_zero
  change ((reflect (mForm Q₀) mU) ((0, 0), x)).2 = x
  rw [reflect_apply hL0]
  have hp : polar (mForm Q₀) mU ((0, 0), x) = 0 := by
    rw [polar_mU_eq_snd]
  rw [hp, mForm_mU, div_one, zero_smul, sub_zero]

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem eq_smul_mU_of_forall_polar (X : MSpace k F)
    (h : ∀ W : MSpace k F, W.1.2 = 0 → polar (mForm Q₀) X W = 0) : X = X.1.1 • mU := by
  have h1 : X.1.2 = 0 := by
    have hzero := h mU (by simp [mU])
    rw [polar_mForm (hQ₀ := hQ₀)] at hzero
    simpa [mU] using hzero
  have h2 : X.2 = 0 := by
    refine spForm_nondegenerate.1 X.2 (fun y => ?_)
    have hzero := h ((0, 0), y) rfl
    rw [polar_mForm (hQ₀ := hQ₀)] at hzero
    simpa using hzero
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simp [mU]
  · simp [mU, h1]
  · simp [mU, h2]

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem fix_mLift_of_chartLin_eq_one (g : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    (hlin : chartLin g = LinearMap.id) (y : Fin k ⊕ Fin k → F) :
    ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), y) = ((0, 0), y) := by
  have hb : (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), y)).1.2 = 0 :=
    chartLin_fst_snd (hQ₀ := hQ₀) g y
  have hW : (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), y)).2 = y := by
    have h2 : chartLin g y = y := by rw [hlin]; rfl
    rwa [chartLin_apply] at h2
  have hQ := map_of_mem (g : MGroup Q₀).2 ((0, 0), y)
  rw [mForm_apply, mForm_apply, hb, hW] at hQ
  simp only [mul_zero, add_zero] at hQ
  have ha : (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), y)).1.1 = 0 :=
    sq_eq_zero_iff.mp (by linear_combination hQ)
  exact Prod.ext (Prod.ext ha hb) hW

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem fix_orth_of_chartLin_eq_one (g : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    (hgU : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU = mU)
    (hlin : chartLin g = LinearMap.id) {W : MSpace k F} (hW : W.1.2 = 0) :
    ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) W = W := by
  have hdec : W = W.1.1 • mU + ((0, 0), W.2) := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp [mU]
    · simp [mU, hW]
    · simp [mU]
  calc ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) W
      = ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) (W.1.1 • mU + ((0, 0), W.2)) := by
        conv_lhs => rw [hdec]
    _ = W.1.1 • (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU) +
          ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), W.2) := by
        rw [map_add, map_smul]
    _ = W.1.1 • mU + ((0, 0), W.2) := by
        rw [hgU, fix_mLift_of_chartLin_eq_one (hQ₀ := hQ₀) g hlin W.2]
    _ = W := hdec.symm

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem apply_eq_add_smul_mU_of_chartLin_eq_one
    (g : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    (hgU : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU = mU)
    (hlin : chartLin g = LinearMap.id) (Y : MSpace k F) :
    ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) Y =
      Y + (Y.1.2 * (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0)).1.1) • mU := by
  have hZmem : ∀ W : MSpace k F, W.1.2 = 0 →
      polar (mForm Q₀) (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0) -
        ((0, 1), 0)) W = 0 := by
    intro W hW
    have hWfix := fix_orth_of_chartLin_eq_one (hQ₀ := hQ₀) g hgU hlin hW
    rw [polar_sub_left]
    have h1 : polar (mForm Q₀) (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0)) W =
        polar (mForm Q₀) (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0))
          (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) W) := by rw [hWfix]
    rw [h1, polar_map_of_mem (g : MGroup Q₀).2, sub_self]
  have hZ : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0) =
      ((0, 1), 0) +
        ((((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0)).1.1) • mU := by
    have h := eq_smul_mU_of_forall_polar (hQ₀ := hQ₀)
      (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0) - ((0, 1), 0)) hZmem
    have hsub : ((((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0) -
        ((0, 1), 0))).1.1 = (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0)).1.1 := by
      simp [mU]
    rw [hsub, sub_eq_iff_eq_add, add_comm] at h
    exact h
  have hdec : Y = ((Y.1.1, 0), Y.2) + Y.1.2 • ((0, 1), 0) := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp
  have horth : (((Y.1.1, 0), Y.2) : MSpace k F).1.2 = 0 := rfl
  conv_lhs => rw [hdec]
  have ht : (((((0 : F), (1 : F)), (0 : Fin k ⊕ Fin k → F)) +
      ((((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) (((0 : F), (1 : F)),
        (0 : Fin k ⊕ Fin k → F))).1.1) • mU)).1.1 =
      (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) (((0 : F), (1 : F)),
        (0 : Fin k ⊕ Fin k → F))).1.1 := by simp [mU]
  rw [map_add, map_smul, hZ,
    fix_orth_of_chartLin_eq_one (hQ₀ := hQ₀) g hgU hlin horth, smul_add, smul_smul, ht,
    ← add_assoc]
  conv_lhs => rw [← hdec]

private noncomputable def chartZ : ↥(Subgroup.centralizer {mRefl Q₀ mU}) :=
  ⟨mRefl Q₀ mU, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem eq_one_or_eq_chartZ_of_chartLin_eq_one
    (g : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    (hgU : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU = mU)
    (hlin : chartLin g = LinearMap.id) :
    ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) = 1 ∨
      ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) =
        ((mRefl Q₀ mU : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) := by
  set t : F := (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0)).1.1 with ht_def
  have hform := apply_eq_add_smul_mU_of_chartLin_eq_one (hQ₀ := hQ₀) g hgU hlin
  have hZt : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 1), 0) =
      ((0, 1), 0) + t • mU := by
    have h := hform ((0, 1), 0)
    rw [ht_def]
    simpa using h
  have hcoord : (((0 : F), (1 : F)), (0 : Fin k ⊕ Fin k → F)) + t • mU =
      ((t, 1), (0 : Fin k ⊕ Fin k → F)) := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [mU]
  have ht : t ^ 2 + t = 0 := by
    have hQZ := map_of_mem (g : MGroup Q₀).2 ((0, 1), 0)
    rw [hZt, hcoord, mForm_apply, mForm_apply] at hQZ
    simpa using hQZ
  have hidem : IsIdempotentElem t := by
    rw [IsIdempotentElem]
    rw [pow_two] at ht
    exact CharTwo.add_eq_zero.mp ht
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with ht0 | ht1
  · rw [ht_def] at ht0
    left
    apply LinearEquiv.ext
    intro Y
    rw [apply_eq_add_smul_mU_of_chartLin_eq_one (hQ₀ := hQ₀) g hgU hlin Y, ht0, mul_zero,
      zero_smul, add_zero]
    rfl
  · rw [ht_def] at ht1
    right
    apply LinearEquiv.ext
    intro Y
    rw [apply_eq_add_smul_mU_of_chartLin_eq_one (hQ₀ := hQ₀) g hgU hlin Y, ht1, mul_one]
    rw [show ((mRefl Q₀ mU : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) =
      reflect (mForm Q₀) mU from rfl, reflect_apply (by rw [mForm_mU]; exact one_ne_zero),
      polar_mU_eq_snd, mForm_mU, div_one, sub_eq_add_neg, ← neg_smul,
      CharTwo.neg_eq]

omit [Fintype F] [DecidableEq F] in
private theorem chartSigma_chartZ (hQ : ∀ a b, polar Q₀ a b = spForm k F a b) :
    chartSigma (Q₀ := Q₀) hQ chartZ = 1 := by
  have hchart : chartHom (Q₀ := Q₀) hQ chartZ = 1 := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : (Fin k ⊕ Fin k → F) →ₗ[F] (Fin k ⊕ Fin k → F) => f x)
      (chartLin_mRefl_mU)
  show (spLinEquiv k F).symm (chartHom (Q₀ := Q₀) hQ chartZ) = 1
  rw [hchart, map_one]

omit [Fintype F] [DecidableEq F] in
private theorem chartSigma_ker (hQ : ∀ a b, polar Q₀ a b = spForm k F a b) :
    (chartSigma (Q₀ := Q₀) hQ).ker = Subgroup.zpowers (chartZ (k := k) (F := F) (Q₀ := Q₀)) := by
  apply le_antisymm
  · intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hchart : chartHom (Q₀ := Q₀) hQ g = 1 := by
      have h2 := congrArg (⇑(spLinEquiv k F)) hg
      rw [show (spLinEquiv k F) ((chartSigma (Q₀ := Q₀) hQ) g) =
        chartHom (Q₀ := Q₀) hQ g from (spLinEquiv k F).apply_symm_apply _,
        map_one] at h2
      exact h2
    have hlin : chartLin g = LinearMap.id := by
      have h1 : (chartUnit (hQ₀ := hQ) g : LinearMap.GeneralLinearGroup F
          (Fin k ⊕ Fin k → F)) = 1 := congrArg Subtype.val hchart
      have h2 : ((chartUnit (hQ₀ := hQ) g : LinearMap.GeneralLinearGroup F
          (Fin k ⊕ Fin k → F)) : Module.End F (Fin k ⊕ Fin k → F)) = 1 :=
        congrArg Units.val h1
      exact h2
    have hgU : ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) mU = mU :=
      (mem_centralizer_mRefl_mU_iff (hQ₀ := hQ) (g : MGroup Q₀)).mp g.2
    rcases eq_one_or_eq_chartZ_of_chartLin_eq_one (hQ₀ := hQ) g hgU hlin with h | h
    · have h1 : g = 1 := Subtype.ext (by simpa using h)
      rw [h1]
      exact Subgroup.one_mem _
    · have h1 : g = chartZ := Subtype.ext (by simpa [chartZ] using h)
      rw [h1]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one _⟩
  · intro g hg
    rw [Subgroup.mem_zpowers_iff] at hg
    obtain ⟨n, rfl⟩ := hg
    rw [MonoidHom.mem_ker, map_zpow, chartSigma_chartZ, one_zpow]

@[expose] def IsModelChart (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F))
    (e : ↥(Subgroup.centralizer {mRefl Q₀ mU}) ≃*
      (↥(StatedSp k F) × Multiplicative (ZMod 2))) : Prop :=
  (∀ (g : ↥(Subgroup.centralizer {mRefl Q₀ mU})) (x : Fin k ⊕ Fin k → F),
      spEnd (e g).1 x =
        (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2) ∧
    (∀ h : mRefl Q₀ mU ∈ Subgroup.centralizer {mRefl Q₀ mU},
      e ⟨mRefl Q₀ mU, h⟩ = (1, Multiplicative.ofAdd 1)) ∧
    (∀ (x : Fin k ⊕ Fin k → F), x ≠ 0 →
      ∀ h : mRefl Q₀ (mLift Q₀ x) ∈ Subgroup.centralizer {mRefl Q₀ mU},
        e ⟨mRefl Q₀ (mLift Q₀ x), h⟩ = (spTransvection x 1, Multiplicative.ofAdd 1))

omit [Fintype F] [DecidableEq F] in
private theorem spEnd_chartSigma (hQ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (g : ↥(Subgroup.centralizer {mRefl Q₀ mU})) :
    spEnd (chartSigma (Q₀ := Q₀) hQ g) = chartLin g := by
  change ((spLin k F (chartSigma (Q₀ := Q₀) hQ g) : LinearMap.GeneralLinearGroup F
    (Fin k ⊕ Fin k → F)) : Module.End F (Fin k ⊕ Fin k → F)) = chartLin g
  show spLin k F ((spLinEquiv k F).symm (chartHom (Q₀ := Q₀) hQ g)) = chartLin g
  rw [spLin_spLinEquiv_symm (r := k) (K := F)]
  rfl

private noncomputable def chartChi (hQ : ∀ a b, polar Q₀ a b = spForm k F a b) :
    ↥(Subgroup.centralizer {mRefl Q₀ mU}) →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd
    (Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace
      (((g : MGroup Q₀)) : MSpace k F ≃ₗ[F] MSpace k F)) : ZMod 2)
  map_one' := by
    rw [show (((1 : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) :
        MSpace k F ≃ₗ[F] MSpace k F) = 1 from rfl,
      CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_one,
      ofAdd_zero]
  map_mul' g h := by
    rw [show (((g * h : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) :
        MSpace k F ≃ₗ[F] MSpace k F) =
        ((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) *
          ((h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) from rfl,
      CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul
        (Q := mForm Q₀) (nondegenerate_polarBilin_mForm (hQ₀ := hQ))
        (g : MGroup Q₀).2 (h : MGroup Q₀).2,
      ofAdd_add]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem chartChi_apply (hQ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (g : ↥(Subgroup.centralizer {mRefl Q₀ mU})) :
    chartChi (Q₀ := Q₀) hQ g = Multiplicative.ofAdd
      (Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace
        (((g : MGroup Q₀)) : MSpace k F ≃ₗ[F] MSpace k F)) : ZMod 2) := rfl

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem chartChi_chartZ (hQ : ∀ a b, polar Q₀ a b = spForm k F a b) :
    chartChi (Q₀ := Q₀) hQ (chartZ (Q₀ := Q₀)) = Multiplicative.ofAdd 1 := by
  have hQnd : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ)
  have : Invertible (mForm Q₀ mU) := by rw [mForm_mU]; exact invertibleOne
  have h := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection
    (Q := mForm Q₀) hQnd mU
  rw [← reflect_eq_reflection (Q := mForm Q₀) (v := mU)] at h
  rw [chartChi_apply]
  rw [show ((chartZ (Q₀ := Q₀) : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) =
    reflect (mForm Q₀) mU from rfl, h, Nat.cast_one]

omit [DecidableEq F] in
private theorem chartChi_mRefl_mLift (hQ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (x : Fin k ⊕ Fin k → F) :
    chartChi (Q₀ := Q₀) hQ
        ⟨mRefl Q₀ (mLift Q₀ x), mRefl_mLift_mem_centralizer x⟩ =
      Multiplicative.ofAdd 1 := by
  have hQnd : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ)
  have : Invertible (mForm Q₀ (mLift Q₀ x)) := by rw [mForm_mLift]; exact invertibleOne
  have h := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection
    (Q := mForm Q₀) hQnd (mLift Q₀ x)
  rw [← reflect_eq_reflection (Q := mForm Q₀) (v := mLift Q₀ x)] at h
  rw [chartChi_apply]
  rw [show (((⟨mRefl Q₀ (mLift Q₀ x),
      mRefl_mLift_mem_centralizer x⟩ :
      ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) :
      MSpace k F ≃ₗ[F] MSpace k F) = reflect (mForm Q₀) (mLift Q₀ x) from rfl, h, Nat.cast_one]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem chartZ_sq : (chartZ (k := k) (F := F) (Q₀ := Q₀)) ^ 2 = 1 := by
  have h : ((chartZ (Q₀ := Q₀) : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ^ 2 = 1 := by
    rw [pow_two]
    change reflect (mForm Q₀) mU * reflect (mForm Q₀) mU = 1
    exact reflect_mul_self (Q := mForm Q₀) mU
  apply Subtype.ext
  apply Subtype.ext
  simpa using h

include hQ₀ in
omit [DecidableEq F] in
theorem exists_isModelChart :
    ∃ e : ↥(Subgroup.centralizer {mRefl Q₀ mU}) ≃*
        (↥(StatedSp k F) × Multiplicative (ZMod 2)),
      IsModelChart Q₀ e := by
  let e : ↥(Subgroup.centralizer {mRefl Q₀ mU}) ≃*
      (↥(StatedSp k F) × Multiplicative (ZMod 2)) :=
    MulEquiv.ofBijective ((chartSigma (Q₀ := Q₀) hQ₀).prod (chartChi (Q₀ := Q₀) hQ₀))
      (bijective_prod_of_ker_eq_zpowers (chartSigma (Q₀ := Q₀) hQ₀) (chartChi (Q₀ := Q₀) hQ₀)
        (chartSigma_surjective hQ₀) (chartSigma_ker hQ₀)
        (chartZ_sq (k := k) (F := F) (Q₀ := Q₀)) (chartChi_chartZ hQ₀))
  refine ⟨e, ?_, ?_, ?_⟩
  · intro g x
    change spEnd (chartSigma (Q₀ := Q₀) hQ₀ g) x = _
    rw [spEnd_chartSigma hQ₀ g, chartLin_apply]
  · intro h
    refine Prod.ext ?_ ?_
    · change chartSigma (Q₀ := Q₀) hQ₀
        (⟨mRefl Q₀ mU, h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU})) = 1
      rw [show (⟨mRefl Q₀ mU, h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
        chartZ (Q₀ := Q₀) from Subtype.ext rfl]
      exact chartSigma_chartZ hQ₀
    · change chartChi (Q₀ := Q₀) hQ₀
        (⟨mRefl Q₀ mU, h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU})) = Multiplicative.ofAdd 1
      rw [show (⟨mRefl Q₀ mU, h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
        chartZ (Q₀ := Q₀) from Subtype.ext rfl]
      exact chartChi_chartZ hQ₀
  · intro x hx h
    refine Prod.ext ?_ ?_
    · change chartSigma (Q₀ := Q₀) hQ₀
        (⟨mRefl Q₀ (mLift Q₀ x), h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
          spTransvection x 1
      rw [show (⟨mRefl Q₀ (mLift Q₀ x), h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
        ⟨mRefl Q₀ (mLift Q₀ x), mRefl_mLift_mem_centralizer x⟩ from
          Subtype.ext rfl]
      exact chartSigma_mRefl_mLift (Q₀ := Q₀) hQ₀ x
    · change chartChi (Q₀ := Q₀) hQ₀
        (⟨mRefl Q₀ (mLift Q₀ x), h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
          Multiplicative.ofAdd 1
      rw [show (⟨mRefl Q₀ (mLift Q₀ x), h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
        ⟨mRefl Q₀ (mLift Q₀ x), mRefl_mLift_mem_centralizer x⟩ from
          Subtype.ext rfl]
      exact chartChi_mRefl_mLift hQ₀ x

include hQ₀ in
omit [DecidableEq F] in
theorem mem_commSet_mRefl_mU_iff {g : MGroup Q₀} :
    g ∈ commSet (mClass Q₀) (mRefl Q₀ mU) ↔
      ∃ x : Fin k ⊕ Fin k → F, x ≠ 0 ∧ g = mRefl Q₀ (mLift Q₀ x) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hQnd : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)
  constructor
  · rintro ⟨hclass, hcomm, hne⟩
    obtain ⟨X, hX, rfl⟩ := hclass
    have hc : Commute (reflect (mForm Q₀) X) (reflect (mForm Q₀) mU) := by
      rw [commute_iff_eq]
      simpa only [mRefl, Subgroup.coe_mul] using congrArg Subtype.val hcomm
    have hXU : polar (mForm Q₀) X mU = 0 :=
      (commute_reflect_iff hX mForm_mU).mp hc
    obtain ⟨⟨a, b⟩, y⟩ := X
    have hb : b = 0 := by
      rw [polar_mForm (hQ₀ := hQ₀)] at hXU
      simpa [mU] using hXU
    have ha2 : a ^ 2 = 1 + Q₀ y := by
      rw [mForm_apply] at hX
      rw [hb, mul_zero, add_zero] at hX
      linear_combination hX - Q₀ y * h2
    have ha : a = (mLift Q₀ y).1.1 := by
      apply (frobeniusEquiv F 2).injective
      rw [frobeniusEquiv_def, frobeniusEquiv_def, fst_mLift_sq, ha2]
    have hXeq : ((a, b), y) = mLift Q₀ y := by
      rw [hb, ha]
      rfl
    have hy : y ≠ 0 := by
      rintro rfl
      apply hne
      rw [hXeq, mLift_zero]
    exact ⟨y, hy, by rw [hXeq]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨mLift Q₀ x, mForm_mLift x, rfl⟩, ?_, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mp (mRefl_mLift_mem_centralizer x)
    · intro h
      have h1 : mLift Q₀ x = mU :=
        (reflect_eq_reflect_iff hQnd (mForm_mLift x) mForm_mU).mp
          (by simpa only [mRefl] using congrArg Subtype.val h)
      exact hx (by simpa [mLift, mU] using congrArg (fun z : MSpace k F => z.2) h1)

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
theorem polar_mU_eq_of_conj {Y Y' : MSpace k F} {g : MGroup Q₀} (hY : mForm Q₀ Y = 1)
    (hY' : mForm Q₀ Y' = 1) (hg : g ∈ Subgroup.centralizer {mRefl Q₀ mU})
    (h : g * mRefl Q₀ Y * g⁻¹ = mRefl Q₀ Y') : Y.1.2 = Y'.1.2 := by
  have hgU : (g : MSpace k F ≃ₗ[F] MSpace k F) mU = mU :=
    (mem_centralizer_mRefl_mU_iff (hQ₀ := hQ₀) g).mp hg
  have hconj : (g : MSpace k F ≃ₗ[F] MSpace k F) * reflect (mForm Q₀) Y *
      (g : MSpace k F ≃ₗ[F] MSpace k F)⁻¹ = reflect (mForm Q₀) Y' :=
    by simpa only [mRefl, Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val h
  rw [reflect_conj g.2 Y] at hconj
  have hgY : (g : MSpace k F ≃ₗ[F] MSpace k F) Y = Y' :=
    (reflect_eq_reflect_iff (nondegenerate_polarBilin_mForm (hQ₀ := hQ₀))
      (by rw [map_of_mem g.2, hY]) hY').mp hconj
  have hpY : polar (mForm Q₀) mU Y = Y.1.2 := polar_mU_eq_snd Y
  have hpY' : polar (mForm Q₀) mU Y' = Y'.1.2 := polar_mU_eq_snd Y'
  exact (calc Y'.1.2 = polar (mForm Q₀) mU Y' := hpY'.symm
    _ = polar (mForm Q₀) ((g : MSpace k F ≃ₗ[F] MSpace k F) mU)
          ((g : MSpace k F ≃ₗ[F] MSpace k F) Y) := by rw [hgU, hgY]
    _ = polar (mForm Q₀) mU Y := polar_map_of_mem g.2 mU Y
    _ = Y.1.2 := hpY).symm

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem commute_mRefl_iff (X Y : MSpace k F) :
    Commute (mRefl Q₀ X) (mRefl Q₀ Y) ↔
      Commute (reflect (mForm Q₀) X) (reflect (mForm Q₀) Y) := by
  have hf : Function.Injective (Subgroup.subtype
      (TauCeti.QuadraticMap.orthogonalGroup (mForm Q₀))) :=
    Subgroup.subtype_injective _
  simpa only [mRefl, Subgroup.subtype_apply] using
    (_root_.commute_map_iff hf).symm

include hQ₀ in
omit [DecidableEq F] in
private theorem polar_mLift_eq_zero_iff_mStabForm_eq_one {Y : MSpace k F}
    (hβ : Y.1.2 ≠ 0) (x : Fin k ⊕ Fin k → F) :
    polar (mForm Q₀) (mLift Q₀ x) Y = 0 ↔ mStabForm Q₀ Y x = 1 := by
  have hmF : polar (mForm Q₀) (mLift Q₀ x) Y =
      (mLift Q₀ x).1.1 * Y.1.2 + spForm k F x Y.2 := by
    rw [polar_mForm (hQ₀ := hQ₀)]
    simp [mLift]
  have hstab : mStabForm Q₀ Y x = Q₀ x + ((Y.1.2)⁻¹ * spForm k F x Y.2) ^ 2 := by
    rw [mStabForm_apply (hQ₀ := hQ₀), LinearMap.BilinForm.smul_left, ← hQ₀,
      polar_comm (⇑Q₀), hQ₀]
  rw [hmF, hstab]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsb : ((mLift Q₀ x).1.1 * Y.1.2) ^ 2 = (1 + Q₀ x) * Y.1.2 ^ 2 := by
    rw [mul_pow, fst_mLift_sq]
  constructor
  · intro hzero
    have h1 : (mLift Q₀ x).1.1 * Y.1.2 = spForm k F x Y.2 := by
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hzero
      exact hzero
    have h2' : (1 + Q₀ x) * Y.1.2 ^ 2 = (spForm k F x Y.2) ^ 2 := by
      rw [← hsb, h1]
    have h3 : 1 + Q₀ x = ((Y.1.2)⁻¹ * spForm k F x Y.2) ^ 2 := by
      rw [show ((Y.1.2)⁻¹ * spForm k F x Y.2) ^ 2
        = (Y.1.2 ^ 2)⁻¹ * (spForm k F x Y.2) ^ 2 by rw [mul_pow, inv_pow]]
      rw [eq_comm, ← h2', eq_comm]
      field_simp [hβ]
    linear_combination -h3 + Q₀ x * h2
  · intro h
    have h3 : ((Y.1.2)⁻¹ * spForm k F x Y.2) ^ 2 = 1 + Q₀ x := by
      linear_combination h - Q₀ x * h2
    have h2' : ((mLift Q₀ x).1.1 * Y.1.2) ^ 2 = (spForm k F x Y.2) ^ 2 := by
      rw [hsb, ← h3, mul_pow, inv_pow]
      field_simp [hβ]
    have hEq : (mLift Q₀ x).1.1 * Y.1.2 = spForm k F x Y.2 := by
      apply (frobeniusEquiv F 2).injective
      rwa [frobeniusEquiv_def, frobeniusEquiv_def]
    rw [hEq]
    exact CharTwo.add_self_eq_zero _

include hQ₀ in
omit [DecidableEq F] in
theorem commute_mLift_iff {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0)
    (x : Fin k ⊕ Fin k → F) :
    Commute (mRefl Q₀ (mLift Q₀ x)) (mRefl Q₀ Y) ↔ mStabForm Q₀ Y x = 1 := by
  rw [commute_mRefl_iff, commute_reflect_iff (mForm_mLift x) hY,
    polar_mLift_eq_zero_iff_mStabForm_eq_one (hQ₀ := hQ₀) hβ x]

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
theorem polar_mStabForm (Y : MSpace k F) (a b : Fin k ⊕ Fin k → F) :
    polar (mStabForm Q₀ Y) a b = spForm k F a b := by
  rw [mStabForm]
  change polar (⇑Q₀ + ⇑(QuadraticMap.linMulLin (polarBilin Q₀ (Y.1.2⁻¹ • Y.2))
    (polarBilin Q₀ (Y.1.2⁻¹ • Y.2))) : (Fin k ⊕ Fin k → F) → F) a b = spForm k F a b
  rw [QuadraticMap.polar_add, hQ₀, polar_linMulLin_self, add_zero]

include hQ₀ in
omit [DecidableEq F] in
theorem isPlusType_mStabForm_iff {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0) :
    IsPlusType (mStabForm Q₀ Y) ↔
      (IsPlusType Q₀ ↔ (Y.1.2)⁻¹ ∈ (artinSchreierHom (K := F)).range) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hpolar : ∀ x, mStabForm Q₀ Y x = Q₀ x + polar Q₀ ((Y.1.2)⁻¹ • Y.2) x ^ 2 := by
    intro x
    rw [mStabForm_apply (hQ₀ := hQ₀), ← hQ₀]
  have hQ0nd : (polarBilin Q₀).Nondegenerate := by
    rw [show polarBilin Q₀ = spForm k F from
      LinearMap.ext₂ fun a b => by rw [polarBilin_apply_apply, hQ₀]]
    exact spForm_nondegenerate
  rw [isPlusType_add_sq_polar_iff hQ0nd ((Y.1.2)⁻¹ • Y.2) hpolar]
  have hsq : ∀ t : F, t ^ 2 + t ∈ (artinSchreierHom (K := F)).range :=
    fun t => ⟨t, by rw [artinSchreierHom_apply, pow_two]⟩
  have hmem : Q₀ ((Y.1.2)⁻¹ • Y.2) ∈ (artinSchreierHom (K := F)).range ↔
      (Y.1.2)⁻¹ ∈ (artinSchreierHom (K := F)).range := by
    have hQy : Q₀ Y.2 = 1 + Y.1.1 ^ 2 + Y.1.1 * Y.1.2 := by
      rw [mForm_apply] at hY
      linear_combination hY - (Y.1.1 ^ 2 + Y.1.1 * Y.1.2) * h2
    have hdiff : Q₀ ((Y.1.2)⁻¹ • Y.2) + ((Y.1.2)⁻¹) ^ 2 =
        (Y.1.1 * (Y.1.2)⁻¹) ^ 2 + Y.1.1 * (Y.1.2)⁻¹ := by
      rw [QuadraticMap.map_smul, smul_eq_mul, hQy]
      field_simp [hβ]
      linear_combination h2
    have hRdiff : Q₀ ((Y.1.2)⁻¹ • Y.2) + ((Y.1.2)⁻¹) ^ 2 ∈
        (artinSchreierHom (K := F)).range := by
      rw [hdiff]
      exact hsq _
    constructor
    · intro h
      have h1 := AddSubgroup.add_mem _ hRdiff h
      rw [show Q₀ ((Y.1.2)⁻¹ • Y.2) + ((Y.1.2)⁻¹) ^ 2 + Q₀ ((Y.1.2)⁻¹ • Y.2) =
        ((Y.1.2)⁻¹) ^ 2 by linear_combination (Q₀ ((Y.1.2)⁻¹ • Y.2)) * h2] at h1
      exact (sq_mem_range_artinSchreier_iff _).mp h1
    · intro h
      have hb2 : ((Y.1.2)⁻¹) ^ 2 ∈ (artinSchreierHom (K := F)).range :=
        (sq_mem_range_artinSchreier_iff _).mpr h
      have h1 := AddSubgroup.add_mem _ hb2 hRdiff
      rwa [show ((Y.1.2)⁻¹) ^ 2 + (Q₀ ((Y.1.2)⁻¹ • Y.2) + ((Y.1.2)⁻¹) ^ 2) =
        Q₀ ((Y.1.2)⁻¹ • Y.2) by linear_combination ((Y.1.2)⁻¹ ^ 2) * h2] at h1
  rw [hmem]

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private theorem exists_mem_centralizer_map_family {n : ℕ} {u u' : Fin n → MSpace k F}
    (hu : LinearIndependent F u) (hu' : LinearIndependent F u') {i₀ : Fin n}
    (h0 : u i₀ = mU) (h0' : u' i₀ = mU)
    (hval : ∀ i, mForm Q₀ (u' i) = mForm Q₀ (u i))
    (hpol : ∀ i j, polar (mForm Q₀) (u' i) (u' j) = polar (mForm Q₀) (u i) (u j)) :
    ∃ g : MGroup Q₀, g ∈ Subgroup.centralizer {mRefl Q₀ mU} ∧
      ∀ i, (g : MSpace k F ≃ₗ[F] MSpace k F) (u i) = u' i := by
  obtain ⟨g, hgO, hg⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    (Q := mForm Q₀) (nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)) u u' hu hu' hval hpol
  have hgU : g mU = mU := by
    have h1 : g (u i₀) = u' i₀ := hg i₀
    rwa [h0, h0'] at h1
  exact ⟨⟨g, hgO⟩, (mem_centralizer_mRefl_mU_iff (hQ₀ := hQ₀) ⟨g, hgO⟩).mpr hgU, hg⟩

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem linearIndependent_cons_two {Y : MSpace k F} (hβ : Y.1.2 ≠ 0) :
    LinearIndependent F (Fin.cons mU (Fin.cons Y Fin.elim0)) := by
  have hU0 : (mU : MSpace k F) ≠ 0 := by simp [mU]
  have hY0 : Y ≠ 0 := fun h => hβ (by simp [h])
  have hbY : ∀ a : F, a • Y ≠ mU := by
    intro a ha
    have h1 : a * Y.1.2 = 0 := by simpa [mU] using congrArg (fun z : MSpace k F => z.1.2) ha
    have ha0 : a = 0 := (mul_eq_zero.mp h1).resolve_right hβ
    rw [ha0, zero_smul] at ha
    exact hU0 ha.symm
  let u : Fin 2 → MSpace k F := Fin.cons mU (Fin.cons Y Fin.elim0)
  change LinearIndependent F u
  rw [linearIndependent_fin2]
  exact ⟨hY0, hbY⟩

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem mForm_cons_two {Y Y' : MSpace k F} (hY : mForm Q₀ Y = 1)
    (hY' : mForm Q₀ Y' = 1) :
    ∀ i : Fin 2,
      mForm Q₀ (((Fin.cons mU (Fin.cons Y' Fin.elim0)) : Fin 2 → MSpace k F) i) =
        mForm Q₀ (((Fin.cons mU (Fin.cons Y Fin.elim0)) : Fin 2 → MSpace k F) i) := by
  intro i
  fin_cases i
  · change mForm Q₀ mU = mForm Q₀ mU
    rw [mForm_mU (Q₀ := Q₀)]
  · change mForm Q₀ Y' = mForm Q₀ Y
    rw [hY', hY]

omit [Fintype F] [DecidableEq F] in
private theorem polar_cons_two {Y Y' : MSpace k F} (hY : mForm Q₀ Y = 1)
    (hY' : mForm Q₀ Y' = 1) (h : Y.1.2 = Y'.1.2) :
    ∀ i j : Fin 2,
      polar (mForm Q₀) (((Fin.cons mU (Fin.cons Y' Fin.elim0)) : Fin 2 → MSpace k F) i)
        (((Fin.cons mU (Fin.cons Y' Fin.elim0)) : Fin 2 → MSpace k F) j) =
      polar (mForm Q₀) (((Fin.cons mU (Fin.cons Y Fin.elim0)) : Fin 2 → MSpace k F) i)
        (((Fin.cons mU (Fin.cons Y Fin.elim0)) : Fin 2 → MSpace k F) j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change polar (mForm Q₀) mU mU = polar (mForm Q₀) mU mU
    rfl
  · change polar (mForm Q₀) mU Y' = polar (mForm Q₀) mU Y
    rw [show polar (mForm Q₀) mU Y' = Y'.1.2 from polar_mU_eq_snd Y',
      show polar (mForm Q₀) mU Y = Y.1.2 from polar_mU_eq_snd Y]
    exact h.symm
  · change polar (mForm Q₀) Y' mU = polar (mForm Q₀) Y mU
    rw [show polar (mForm Q₀) Y' mU = Y'.1.2 from by
          rw [polar_comm (⇑(mForm Q₀))]
          exact polar_mU_eq_snd Y',
        show polar (mForm Q₀) Y mU = Y.1.2 from by
          rw [polar_comm (⇑(mForm Q₀))]
          exact polar_mU_eq_snd Y]
    exact h.symm
  · change polar (mForm Q₀) Y' Y' = polar (mForm Q₀) Y Y
    rw [polar_self_eq_two_mul (mForm Q₀) Y', polar_self_eq_two_mul (mForm Q₀) Y, hY', hY]

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
theorem mStabForm_apply_eq_of_mem_centralizer {Y : MSpace k F} (hβ : Y.1.2 ≠ 0) {g : MGroup Q₀}
    (hg : g ∈ Subgroup.centralizer {mRefl Q₀ mU}) (x : Fin k ⊕ Fin k → F) :
    mStabForm Q₀ ((g : MSpace k F ≃ₗ[F] MSpace k F) Y)
        ((g : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2 = mStabForm Q₀ Y x := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hgU : (g : MSpace k F ≃ₗ[F] MSpace k F) mU = mU :=
    (mem_centralizer_mRefl_mU_iff (hQ₀ := hQ₀) g).mp hg
  set Y' : MSpace k F := (g : MSpace k F ≃ₗ[F] MSpace k F) Y with hY'def
  set V : MSpace k F := ((0, 0), x) with hVdef
  set V' : MSpace k F := (g : MSpace k F ≃ₗ[F] MSpace k F) V with hV'def
  have hY'b : Y'.1.2 = Y.1.2 := by
    rw [← polar_mU_eq_snd Y', hY'def, ← hgU, polar_map_of_mem g.2,
      polar_mU_eq_snd]
  have hV'b : V'.1.2 = 0 := by
    rw [← polar_mU_eq_snd V', hV'def, ← hgU, hVdef, polar_map_of_mem g.2,
      polar_mU_eq_snd]
  have hQn : Q₀ V'.2 = Q₀ x + V'.1.1 ^ 2 := by
    have h := map_of_mem g.2 V
    rw [← hV'def, hVdef] at h
    rw [mForm_apply, mForm_apply, hV'b] at h
    simp only [mul_zero, add_zero] at h
    linear_combination h - V'.1.1 ^ 2 * h2
  have hα : V'.1.1 * Y.1.2 + spForm k F Y'.2 V'.2 = spForm k F Y.2 x := by
    have h := polar_map_of_mem g.2 Y V
    rw [← hY'def, ← hV'def] at h
    rw [polar_mForm (hQ₀ := hQ₀), polar_mForm (hQ₀ := hQ₀), hV'b, hY'b, hVdef] at h
    simpa using h
  rw [mStabForm_apply (hQ₀ := hQ₀) Y' V'.2, mStabForm_apply (hQ₀ := hQ₀) Y x, hY'b, hQn]
  rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  have hc : V'.1.1 = (Y.1.2)⁻¹ * (spForm k F Y.2 x + spForm k F Y'.2 V'.2) := by
    have h1 : V'.1.1 * Y.1.2 = spForm k F Y.2 x + spForm k F Y'.2 V'.2 := by
      linear_combination hα - spForm k F Y'.2 V'.2 * h2
    rw [← h1, mul_comm V'.1.1 (Y.1.2), ← mul_assoc, inv_mul_cancel₀ hβ, one_mul]
  rw [hc]
  field_simp
  linear_combination (spForm k F Y.2 x * spForm k F Y'.2 V'.2 +
    (spForm k F Y'.2 V'.2) ^ 2) * h2

@[expose] def IsModelChartAt (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)) (V₀ : MSpace k F)
    (γ : MSpace k F ≃ₗ[F] MSpace k F)
    (e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃*
      (↥(StatedSp k F) × Multiplicative (ZMod 2))) : Prop :=
  (∀ X : MSpace k F, mForm Q₀ (γ X) = mForm Q₀ X) ∧ γ mU = V₀ ∧
    (∀ h : mRefl Q₀ V₀ ∈ Subgroup.centralizer {mRefl Q₀ V₀},
      e ⟨mRefl Q₀ V₀, h⟩ = (1, Multiplicative.ofAdd 1)) ∧
    (∀ (x : Fin k ⊕ Fin k → F), x ≠ 0 →
      ∀ h : mRefl Q₀ (γ (mLift Q₀ x)) ∈ Subgroup.centralizer {mRefl Q₀ V₀},
        e ⟨mRefl Q₀ (γ (mLift Q₀ x)), h⟩ =
          (spTransvection x 1, Multiplicative.ofAdd 1))

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem mRefl_mul_conj {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)} {g : MGroup Q₀}
    {Y : MSpace k F} :
    g * mRefl Q₀ Y * g⁻¹ = mRefl Q₀ ((g : MSpace k F ≃ₗ[F] MSpace k F) Y) := by
  refine Subtype.ext ?_
  show ((g * mRefl Q₀ Y * g⁻¹ : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) =
    reflect (mForm Q₀) ((g : MSpace k F ≃ₗ[F] MSpace k F) Y)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact reflect_conj g.2 Y

include hQ₀ in
omit [DecidableEq F] in
private theorem exists_isModelChartAt_of_isometry {V₀ : MSpace k F}
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    (hγ : γ ∈ TauCeti.QuadraticMap.orthogonalGroup (mForm Q₀)) (hγU : γ mU = V₀) :
    ∃ e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃*
        (↥(StatedSp k F) × Multiplicative (ZMod 2)),
      IsModelChartAt Q₀ V₀ γ e := by
  obtain ⟨eU, heU⟩ := exists_isModelChart (hQ₀ := hQ₀)
  let a : MGroup Q₀ := ⟨γ, hγ⟩
  have hconj : MulAut.conj a (mRefl Q₀ mU) = mRefl Q₀ V₀ := by
    rw [MulAut.conj_apply, mRefl_mul_conj, hγU]
  let c := centralizerSingletonMulEquiv (MulAut.conj a) hconj
  let e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃*
      (↥(StatedSp k F) × Multiplicative (ZMod 2)) :=
    c.symm.trans eU
  refine ⟨e, fun X => map_of_mem hγ X, hγU, ?_, ?_⟩
  · intro h
    have h1 : c.symm (⟨mRefl Q₀ V₀, h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ V₀})) =
        chartZ (Q₀ := Q₀) := by
      apply c.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      change (mRefl Q₀ V₀) = (c (chartZ (Q₀ := Q₀)) : MGroup Q₀)
      rw [coe_centralizerSingletonMulEquiv_apply, MulAut.conj_apply]
      exact hconj.symm
    change eU (c.symm ⟨mRefl Q₀ V₀, h⟩) = (1, Multiplicative.ofAdd 1)
    rw [h1]
    exact heU.2.1 (chartZ (Q₀ := Q₀)).2
  · intro x hx h
    have h2 : c.symm
        (⟨mRefl Q₀ (γ (mLift Q₀ x)), h⟩ : ↥(Subgroup.centralizer {mRefl Q₀ V₀})) =
        ⟨mRefl Q₀ (mLift Q₀ x), mRefl_mLift_mem_centralizer x⟩ := by
      apply c.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      change mRefl Q₀ (γ (mLift Q₀ x)) =
        (c ⟨mRefl Q₀ (mLift Q₀ x), mRefl_mLift_mem_centralizer x⟩ : MGroup Q₀)
      rw [coe_centralizerSingletonMulEquiv_apply, MulAut.conj_apply]
      exact (mRefl_mul_conj (Q₀ := Q₀) (g := a) (Y := mLift Q₀ x)).symm
    change eU (c.symm
      ⟨mRefl Q₀ (γ (mLift Q₀ x)), h⟩) = (spTransvection x 1, Multiplicative.ofAdd 1)
    rw [h2]
    exact heU.2.2 x hx (mRefl_mLift_mem_centralizer x)

include hQ₀ in
omit [DecidableEq F] in
theorem exists_isModelChartAt (V₀ : MSpace k F) (hV₀ : mForm Q₀ V₀ = 1) :
    ∃ (γ : MSpace k F ≃ₗ[F] MSpace k F)
      (e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃*
        (↥(StatedSp k F) × Multiplicative (ZMod 2))),
      IsModelChartAt Q₀ V₀ γ e := by
  obtain ⟨⟨γ, hγ⟩, hγU⟩ := exists_mem_mGroup_apply_eq_of_map_eq
    (nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)) mForm_mU hV₀
  obtain ⟨e, he⟩ := exists_isModelChartAt_of_isometry (hQ₀ := hQ₀) (γ := γ) hγ hγU
  exact ⟨γ, e, he⟩

omit hQ₀ [DecidableEq F] in
theorem mLift_add_smul (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {x₁ x₂ : Fin k ⊕ Fin k → F}
    (h : spForm k F x₁ x₂ = 0) (t : F) :
    (1 - t) • mLift Q₀ x₁ + t • mLift Q₀ x₂ = mLift Q₀ ((1 - t) • x₁ + t • x₂) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hQ : Q₀ ((1 - t) • x₁ + t • x₂) = (1 - t) ^ 2 * Q₀ x₁ + t ^ 2 * Q₀ x₂ := by
    rw [QuadraticMap.map_add Q₀ ((1 - t) • x₁) (t • x₂),
      QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hQ₀, h]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  have hsum : (1 - t) ^ 2 + t ^ 2 = 1 := by
    have h1 : (1 - t) ^ 2 = 1 + t ^ 2 := by linear_combination (-t) * h2
    rw [h1]
    linear_combination (t ^ 2) * h2
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · apply (frobeniusEquiv F 2).injective
    simp only [mLift, map_add, map_mul, RingEquiv.apply_symm_apply, frobeniusEquiv_def, hQ,
      Prod.smul_fst, smul_eq_mul, Prod.fst_add]
    linear_combination hsum
  · simp [mLift]
  · simp [mLift]

omit [Fintype F] [DecidableEq F] in
private theorem isSpQuadForm_mStabForm (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (Y : MSpace k F) :
    IsSpQuadForm (mStabForm Q₀ Y) := by
  refine ⟨fun c x => ?_, fun x y => ?_⟩
  · rw [QuadraticMap.map_smul, smul_eq_mul]
    ring
  · rw [QuadraticMap.map_add (mStabForm Q₀ Y) x y, polar_mStabForm (hQ₀ := hQ₀)]

omit [Fintype F] [DecidableEq F] in
theorem mStabForm_spEnd_spTransvection (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {Y : MSpace k F}
    {y : Fin k ⊕ Fin k → F} (c : F)
    (hy : mStabForm Q₀ Y y = 1) (x : Fin k ⊕ Fin k → F) :
    mStabForm Q₀ Y (spEnd (spTransvection y c) x) =
      mStabForm Q₀ Y x + (c ^ 2 + c) * spForm k F x y ^ 2 := by
  have h := (isSpQuadForm_mStabForm (hQ₀ := hQ₀) Y).Q_spTransvection y c x
  rw [hy] at h
  rw [h, mul_one]
  ring

omit [DecidableEq F] in
private theorem linearIndependent_cons_mLift {x : Fin k ⊕ Fin k → F} (hx : x ≠ 0) :
    LinearIndependent F (Fin.cons mU (Fin.cons (mLift Q₀ x) Fin.elim0)) := by
  have hU0 : (mU : MSpace k F) ≠ 0 := by simp [mU]
  have hL0 : mLift Q₀ x ≠ 0 := by
    intro h0
    exact hx (by simpa [mLift] using congrArg (fun z : MSpace k F => z.2) h0)
  have hbL : ∀ a : F, a • mLift Q₀ x ≠ mU := by
    intro a ha
    have h1 : a • x = 0 := by
      simpa [mLift, mU] using congrArg (fun z : MSpace k F => z.2) ha
    have ha0 : a = 0 := by
      rcases smul_eq_zero.mp h1 with h0 | h0
      · exact h0
      · exact absurd h0 hx
    rw [ha0, zero_smul] at ha
    exact hU0 ha.symm
  let u : Fin 2 → MSpace k F := Fin.cons mU (Fin.cons (mLift Q₀ x) Fin.elim0)
  change LinearIndependent F u
  rw [linearIndependent_fin2]
  exact ⟨hL0, hbL⟩

include hQ₀ in
omit [DecidableEq F] in
theorem exists_conj_mRefl_mLift_eq {x x' : Fin k ⊕ Fin k → F} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ∃ g ∈ Subgroup.centralizer {mRefl Q₀ mU},
      g * mRefl Q₀ (mLift Q₀ x) * g⁻¹ = mRefl Q₀ (mLift Q₀ x') := by
  have hβ : (mLift Q₀ x).1.2 = (mLift Q₀ x').1.2 := by simp [mLift]
  let u : Fin 2 → MSpace k F := Fin.cons mU (Fin.cons (mLift Q₀ x) Fin.elim0)
  let u' : Fin 2 → MSpace k F := Fin.cons mU (Fin.cons (mLift Q₀ x') Fin.elim0)
  have hu : LinearIndependent F u := linearIndependent_cons_mLift hx
  have hu' : LinearIndependent F u' := linearIndependent_cons_mLift hx'
  have hval : ∀ i : Fin 2, mForm Q₀ (u' i) = mForm Q₀ (u i) :=
    mForm_cons_two (mForm_mLift x) (mForm_mLift x')
  have hpol : ∀ i j : Fin 2, polar (mForm Q₀) (u' i) (u' j) =
      polar (mForm Q₀) (u i) (u j) :=
    polar_cons_two (mForm_mLift x) (mForm_mLift x') hβ
  obtain ⟨g, hg, hgmap⟩ := exists_mem_centralizer_map_family (hQ₀ := hQ₀) hu hu'
    (i₀ := 0) (by rfl) (by rfl) hval hpol
  refine ⟨g, hg, ?_⟩
  have hgY : (g : MSpace k F ≃ₗ[F] MSpace k F) (mLift Q₀ x) = mLift Q₀ x' := by
    have h1 := hgmap 1
    rwa [show u 1 = mLift Q₀ x from rfl, show u' 1 = mLift Q₀ x' from rfl] at h1
  have hconj : (g : MSpace k F ≃ₗ[F] MSpace k F) * reflect (mForm Q₀) (mLift Q₀ x) *
      (g : MSpace k F ≃ₗ[F] MSpace k F)⁻¹ = reflect (mForm Q₀) (mLift Q₀ x') := by
    rw [reflect_conj g.2 (mLift Q₀ x), hgY]
  exact Subtype.ext (by simpa only [mRefl, Subgroup.coe_mul, Subgroup.coe_inv] using hconj)

omit [DecidableEq F] in
private theorem polar_mLift_eq_zero_of_commute {x : Fin k ⊕ Fin k → F} {Y : MSpace k F}
    (hY : mForm Q₀ Y = 1) (hxY : Commute (mRefl Q₀ (mLift Q₀ x)) (mRefl Q₀ Y)) :
    polar (mForm Q₀) (mLift Q₀ x) Y = 0 := by
  have hc : Commute (reflect (mForm Q₀) (mLift Q₀ x)) (reflect (mForm Q₀) Y) := by
    rw [commute_iff_eq]
    simpa only [mRefl, Subgroup.coe_mul] using congrArg Subtype.val hxY
  exact (commute_reflect_iff (mForm_mLift x) hY).mp hc

omit [DecidableEq F] in
private theorem ne_zero_of_commute_mLift {x : Fin k ⊕ Fin k → F} {Y : MSpace k F}
    (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0)
    (hxY : Commute (mRefl Q₀ (mLift Q₀ x)) (mRefl Q₀ Y)) : x ≠ 0 := by
  rintro rfl
  have hp := polar_mLift_eq_zero_of_commute hY hxY
  rw [mLift_zero, polar_mU_eq_snd] at hp
  exact hβ hp

omit [DecidableEq F] in
private theorem mLift_notMem_span_pair {x : Fin k ⊕ Fin k → F} {Y : MSpace k F}
    (hβ : Y.1.2 ≠ 0) (hx : x ≠ 0) :
    mLift Q₀ x ∉ Submodule.span F ({mU, Y} : Set (MSpace k F)) := by
  intro hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have hb0 : b = 0 := by
    have h1 : b * Y.1.2 = 0 := by
      simpa [mU, mLift] using congrArg (fun z : MSpace k F => z.1.2) hab
    exact (mul_eq_zero.mp h1).resolve_right hβ
  have hx0 : x = 0 := by
    have h1 := congrArg (fun z : MSpace k F => z.2) hab
    rw [hb0, zero_smul, add_zero] at h1
    simpa [mLift, mU] using h1.symm
  exact hx hx0

omit [DecidableEq F] in
private theorem linearIndependent_cons_three {x : Fin k ⊕ Fin k → F} {Y : MSpace k F}
    (hβ : Y.1.2 ≠ 0) (hx : x ≠ 0) :
    LinearIndependent F (Fin.cons mU (Fin.cons Y (Fin.cons (mLift Q₀ x) Fin.elim0))) := by
  let u : Fin 3 → MSpace k F := Fin.cons mU (Fin.cons Y (Fin.cons (mLift Q₀ x) Fin.elim0))
  have hu2 : u 2 = mLift Q₀ x := rfl
  change LinearIndependent F u
  rw [linearIndependent_finSucc']
  constructor
  · have hinit : Fin.init u = Fin.cons mU (Fin.cons Y Fin.elim0) := by
      funext i
      fin_cases i <;> rfl
    rw [hinit]
    exact linearIndependent_cons_two hβ
  · change u 2 ∉ Submodule.span F (Set.range (Fin.init u))
    have hrange : Set.range (Fin.init u) = ({mU, Y} : Set (MSpace k F)) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hrange, hu2]
    exact mLift_notMem_span_pair hβ hx

omit [DecidableEq F] in
private theorem mForm_cons_three {x : Fin k ⊕ Fin k → F} {Y Y' : MSpace k F}
    (hY : mForm Q₀ Y = 1) (hY' : mForm Q₀ Y' = 1) :
    ∀ i : Fin 3,
      mForm Q₀ (((Fin.cons mU (Fin.cons Y' (Fin.cons (mLift Q₀ x) Fin.elim0))) :
          Fin 3 → MSpace k F) i) =
        mForm Q₀ (((Fin.cons mU (Fin.cons Y (Fin.cons (mLift Q₀ x) Fin.elim0))) :
          Fin 3 → MSpace k F) i) := by
  intro i
  fin_cases i
  · change mForm Q₀ mU = mForm Q₀ mU
    rw [mForm_mU (Q₀ := Q₀)]
  · change mForm Q₀ Y' = mForm Q₀ Y
    rw [hY', hY]
  · change mForm Q₀ (mLift Q₀ x) = mForm Q₀ (mLift Q₀ x)
    rw [mForm_mLift]

omit [DecidableEq F] in
private theorem polar_cons_three {x : Fin k ⊕ Fin k → F} {Y Y' : MSpace k F}
    (hY : mForm Q₀ Y = 1) (hY' : mForm Q₀ Y' = 1) (h : Y.1.2 = Y'.1.2)
    (hpLY : polar (mForm Q₀) (mLift Q₀ x) Y = 0)
    (hpLY' : polar (mForm Q₀) (mLift Q₀ x) Y' = 0) :
    ∀ i j : Fin 3,
      polar (mForm Q₀) (((Fin.cons mU (Fin.cons Y' (Fin.cons (mLift Q₀ x) Fin.elim0))) :
          Fin 3 → MSpace k F) i)
        (((Fin.cons mU (Fin.cons Y' (Fin.cons (mLift Q₀ x) Fin.elim0))) :
          Fin 3 → MSpace k F) j) =
      polar (mForm Q₀) (((Fin.cons mU (Fin.cons Y (Fin.cons (mLift Q₀ x) Fin.elim0))) :
          Fin 3 → MSpace k F) i)
        (((Fin.cons mU (Fin.cons Y (Fin.cons (mLift Q₀ x) Fin.elim0))) :
          Fin 3 → MSpace k F) j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change polar (mForm Q₀) mU mU = polar (mForm Q₀) mU mU
    rfl
  · change polar (mForm Q₀) mU Y' = polar (mForm Q₀) mU Y
    rw [show polar (mForm Q₀) mU Y' = Y'.1.2 from polar_mU_eq_snd Y',
      show polar (mForm Q₀) mU Y = Y.1.2 from polar_mU_eq_snd Y]
    exact h.symm
  · change polar (mForm Q₀) mU (mLift Q₀ x) = polar (mForm Q₀) mU (mLift Q₀ x)
    rfl
  · change polar (mForm Q₀) Y' mU = polar (mForm Q₀) Y mU
    rw [show polar (mForm Q₀) Y' mU = Y'.1.2 from by
          rw [polar_comm (⇑(mForm Q₀))]
          exact polar_mU_eq_snd Y',
        show polar (mForm Q₀) Y mU = Y.1.2 from by
          rw [polar_comm (⇑(mForm Q₀))]
          exact polar_mU_eq_snd Y]
    exact h.symm
  · change polar (mForm Q₀) Y' Y' = polar (mForm Q₀) Y Y
    rw [polar_self_eq_two_mul (mForm Q₀) Y', polar_self_eq_two_mul (mForm Q₀) Y, hY', hY]
  · change polar (mForm Q₀) Y' (mLift Q₀ x) = polar (mForm Q₀) Y (mLift Q₀ x)
    rw [show polar (mForm Q₀) Y' (mLift Q₀ x) = 0 from by
          rw [polar_comm (⇑(mForm Q₀))]
          exact hpLY',
        show polar (mForm Q₀) Y (mLift Q₀ x) = 0 from by
          rw [polar_comm (⇑(mForm Q₀))]
          exact hpLY]
  · change polar (mForm Q₀) (mLift Q₀ x) mU = polar (mForm Q₀) (mLift Q₀ x) mU
    rfl
  · change polar (mForm Q₀) (mLift Q₀ x) Y' = polar (mForm Q₀) (mLift Q₀ x) Y
    rw [hpLY', hpLY]
  · change polar (mForm Q₀) (mLift Q₀ x) (mLift Q₀ x) =
      polar (mForm Q₀) (mLift Q₀ x) (mLift Q₀ x)
    rfl

include hQ₀ in
omit [DecidableEq F] in
theorem exists_conj_eq_of_polar_mU_eq_of_commute {x : Fin k ⊕ Fin k → F} {Y Y' : MSpace k F}
    (hY : mForm Q₀ Y = 1) (hY' : mForm Q₀ Y' = 1) (hβ : Y.1.2 ≠ 0) (h : Y.1.2 = Y'.1.2)
    (hxY : Commute (mRefl Q₀ (mLift Q₀ x)) (mRefl Q₀ Y))
    (hxY' : Commute (mRefl Q₀ (mLift Q₀ x)) (mRefl Q₀ Y')) :
    ∃ g ∈ Subgroup.centralizer {mRefl Q₀ mU} ⊓ Subgroup.centralizer {mRefl Q₀ (mLift Q₀ x)},
      g * mRefl Q₀ Y * g⁻¹ = mRefl Q₀ Y' := by
  have hpLY : polar (mForm Q₀) (mLift Q₀ x) Y = 0 :=
    polar_mLift_eq_zero_of_commute hY hxY
  have hpLY' : polar (mForm Q₀) (mLift Q₀ x) Y' = 0 :=
    polar_mLift_eq_zero_of_commute hY' hxY'
  have hx : x ≠ 0 := ne_zero_of_commute_mLift hY hβ hxY
  have hβ' : Y'.1.2 ≠ 0 := by rw [← h]; exact hβ
  let u : Fin 3 → MSpace k F := Fin.cons mU (Fin.cons Y (Fin.cons (mLift Q₀ x) Fin.elim0))
  let u' : Fin 3 → MSpace k F := Fin.cons mU (Fin.cons Y' (Fin.cons (mLift Q₀ x) Fin.elim0))
  have hu : LinearIndependent F u := linearIndependent_cons_three hβ hx
  have hu' : LinearIndependent F u' := linearIndependent_cons_three hβ' hx
  have hval : ∀ i : Fin 3, mForm Q₀ (u' i) = mForm Q₀ (u i) :=
    mForm_cons_three hY hY'
  have hpol : ∀ i j : Fin 3, polar (mForm Q₀) (u' i) (u' j) =
      polar (mForm Q₀) (u i) (u j) :=
    polar_cons_three hY hY' h hpLY hpLY'
  have hu0 : u 0 = mU := rfl
  have hu1 : u 1 = Y := rfl
  have hu2 : u 2 = mLift Q₀ x := rfl
  have hu'0 : u' 0 = mU := rfl
  have hu'1 : u' 1 = Y' := rfl
  have hu'2 : u' 2 = mLift Q₀ x := rfl
  obtain ⟨g, hg, hgmap⟩ := exists_mem_centralizer_map_family (hQ₀ := hQ₀) hu hu'
    (i₀ := 0) hu0 hu'0 hval hpol
  have hgU : (g : MSpace k F ≃ₗ[F] MSpace k F) mU = mU := by
    have h0 := hgmap 0
    rwa [hu0, hu'0] at h0
  have hgY : (g : MSpace k F ≃ₗ[F] MSpace k F) Y = Y' := by
    have h1 := hgmap 1
    rwa [hu1, hu'1] at h1
  have hgL : (g : MSpace k F ≃ₗ[F] MSpace k F) (mLift Q₀ x) = mLift Q₀ x := by
    have h2 := hgmap 2
    rwa [hu2, hu'2] at h2
  refine ⟨g, ⟨(mem_centralizer_mRefl_mU_iff (hQ₀ := hQ₀) g).mpr hgU,
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((commute_reflect_iff_apply_eq (nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)) g
        (by rw [mForm_mLift x]; exact one_ne_zero)).mpr hgL)⟩, ?_⟩
  have hconj : (g : MSpace k F ≃ₗ[F] MSpace k F) * reflect (mForm Q₀) Y *
      (g : MSpace k F ≃ₗ[F] MSpace k F)⁻¹ = reflect (mForm Q₀) Y' := by
    rw [reflect_conj g.2 Y, hgY]
  exact Subtype.ext (by simpa only [mRefl, Subgroup.coe_mul, Subgroup.coe_inv] using hconj)

end CFSG.OddTranspositions.PartThree.ElevenSp

end
