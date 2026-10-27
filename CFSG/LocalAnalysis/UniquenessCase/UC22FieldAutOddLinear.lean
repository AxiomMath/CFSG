module

public import CFSG.GroupTheory.AutomorphismFixedSubgroupSimple
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneInner
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem fieldAutOdd_projectiveSL {K : Type} [Field K] [Finite K] {n p f r : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (hr : r.Prime) (hr2 : r ≠ 2) (hcop : ¬ r ∣ Nat.gcd n (Nat.card K - 1))
    (θ : MulAut (projectiveSL n K)) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) :
    r ∣ f ∧ ∃ Y : Subgroup (projectiveSL n K), Y ≤ signalizerFixedSubgroup θ ∧
      IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hθr : θ ^ r = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hθE : θ ∈ semilinearAutGroup n K :=
    mem_semilinearAutGroup_of_pow_odd hn (hr.odd_of_ne_two hr2) hθr
  have hθD : θ ∉ linearAutGroup n K := fun hD =>
    hout (KCLinPlane.inner_of_mem_linearAut_of_pow_eq_one hn
      ((Nat.Prime.coprime_iff_not_dvd hr).2 hcop) hD hθr)
  obtain ⟨hrf, σ, hσ, ⟨δ, -, hδ⟩, hcard⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.linear_prime_descent_char hp hf hn hK hr
      hθE hθD hθ
  let k := semilinearFixedSubfield σ
  have hf0 : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hrf) hr.pos
  have : IsSimpleGroup (projectiveSL n k) := KCLinearSubfield.isSimpleGroup_projectiveSL hn
  let ι : projectiveSL n k →* projectiveSL n K :=
    δ.toMonoidHom.comp (linearSubfieldInclusion n k)
  have hι : Function.Injective ι :=
    δ.injective.comp (linearSubfieldInclusion_injective (by omega) k)
  have hfix : ∀ y, θ (ι y) = ι y := by
    intro y
    change θ (δ (linearSubfieldInclusion n k y)) = δ (linearSubfieldInclusion n k y)
    simp only [hδ, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    exact congrArg δ (fieldAut_linearSubfieldInclusion (k := k) (σ := σ) (fun c hc => by
      change σ c = c at hc
      exact hc) y)
  have hrank : 2 ≤ CFSG.pRank p (projectiveSL n k) := by
    let e : projectiveSL n k ≃* StatedProj (StatedSL n k) :=
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).symm.trans
        (projectiveSpecialLinearGroupEquivStatedProj n k)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := n) (a := 1) (b := 2)
      (by norm_num) (by omega) hcard
    omega
  exact ⟨hrf, CFSG.exists_simple_subgroup_le_fixed_of_injective ι hι θ hfix hrank⟩

theorem fieldAutOdd_psl {X : Type} [Group X] [Finite X] {n p f r : ℕ}
    (hp : p.Prime) (hadm : StatedLieAdmissible .PSL n p f) (hX : LieModel X .PSL n p f)
    (hA1 : ¬ (StatedLieTag.PSL = .PSL ∧ n = 2)) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrg : ¬ r ∣ (CFSG.Blueprint.Multiplier.genericOrders .PSL n p f).1)
    (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup Y ∧
      2 ≤ CFSG.pRank p Y := by
  have hn : 3 ≤ n := by
    have hn2 := hadm.2.2.1
    have hnne : n ≠ 2 := fun h => hA1 ⟨rfl, h⟩
    omega
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have hθ' : orderOf (MulAut.congr e θ) = r := by
    exact (orderOf_injective (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext g
    have h := congrArg (fun α : MulAut (projectiveSL n K) => e.symm (α (e g))) hx
    simpa [MulAut.congr_apply, MulAut.conj_apply] using h
  have hcop : ¬ r ∣ Nat.gcd n (Nat.card K - 1) := by
    rw [hK]
    exact hrg
  obtain ⟨hrf, Y, hY, hs, hrank⟩ :=
    fieldAutOdd_projectiveSL hp hadm.2.1 hK hn hr (by omega) hcop
      (MulAut.congr e θ) hθ' hout'
  have : IsSimpleGroup Y := hs
  let ι : Y →* X := e.symm.toMonoidHom.comp Y.subtype
  have hι : Function.Injective ι := e.symm.injective.comp Y.subtype_injective
  have hfix : ∀ y, θ (ι y) = ι y := by
    intro y
    apply e.injective
    have hy : (MulAut.congr e θ) y = y := hY y.2
    simpa [ι, MulAut.congr_apply] using hy
  exact ⟨hrf, CFSG.exists_simple_subgroup_le_fixed_of_injective ι hι θ hfix hrank⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
