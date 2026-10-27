module

public import CFSG.GroupTheory.AutomorphismFixedSubgroupSimple
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Symplectic
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem fieldAutOdd_statedSp {K : Type} [Field K] [Finite K] {n p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 2 ≤ n)
    (hr : r.Prime) (hr2 : r ≠ 2) (θ : MulAut (StatedProj (StatedSp n K)))
    (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : StatedProj (StatedSp n K) →*
      MulAut (StatedProj (StatedSp n K))).range) :
    r ∣ f ∧ ∃ Y : Subgroup (StatedProj (StatedSp n K)), Y ≤ signalizerFixedSubgroup θ ∧
      IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  have : NeZero n := ⟨by omega⟩
  have : Fact p.Prime := ⟨hp⟩
  have := inner_normal (StatedProj (StatedSp n K))
  have O := spOuter hp hf hn hK
  have hθr : θ ^ r = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hθE : θ ∈ spSemilinearAutGroup n K :=
    mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd (hθ ▸ hr.odd_of_ne_two hr2)
  have hθD : θ ∉ spLinearAutGroup n K := fun hD =>
    hout (mem_of_pow_eq_one_of_relIndex_dvd_two
      (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hr hr2 hD hθr)
  obtain ⟨hrf, σ, hσ, δ, -, hδ⟩ := O.descent r hr θ hθE hθD hθ
  let k := descentField σ
  have hcard : Nat.card k = p ^ (f / r) := (card_semilinearFixedSubfield hp hf hK hσ).2
  have hf0 : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hrf) hr.pos
  have hpk : 3 ≤ Nat.card k := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    rw [hcard]
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have : IsSimpleGroup (StatedProj (StatedSp n k)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k n (by omega) (by
      by_cases h4 : 4 ≤ Nat.card k
      · exact Or.inl (Or.inr h4)
      · exact Or.inr (Or.inl ⟨by omega, hn⟩))
  let ι : StatedProj (StatedSp n k) →* StatedProj (StatedSp n K) :=
    δ.toMonoidHom.comp (subfieldInj (r := n) σ)
  have hι : Function.Injective ι := δ.injective.comp (subfieldInj_injective σ)
  have hfix : ∀ y, θ (ι y) = ι y := by
    intro y
    change θ (δ (subfieldInj σ y)) = δ (subfieldInj σ y)
    simp only [hδ, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    apply congrArg δ
    obtain ⟨g, rfl⟩ := proj_surjective y
    rw [subfieldInj_proj]
    exact fieldAut_subfieldProj σ g
  have hrank : 2 ≤ CFSG.pRank p (StatedProj (StatedSp n k)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    have h := CFSG.SectionRank.ClassicalOdd.le_pRank_Sp hn hcard
    nlinarith
  exact ⟨hrf, CFSG.exists_simple_subgroup_le_fixed_of_injective ι hι θ hfix hrank⟩

theorem fieldAutOdd_psp {X : Type} [Group X] [Finite X] {n p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : LieModel X .PSp n p f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup Y ∧
      2 ≤ CFSG.pRank p Y := by
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : StatedProj (StatedSp n K) →* MulAut (StatedProj (StatedSp n K))).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext g
    have h := congrArg (fun α : MulAut (StatedProj (StatedSp n K)) => e.symm (α (e g))) hx
    simpa [MulAut.congr_apply, MulAut.conj_apply] using h
  obtain ⟨hrf, Y, hY, hs, hrank⟩ :=
    fieldAutOdd_statedSp hp hp2 hf hK hn hr (by omega) (MulAut.congr e θ) hθ' hout'
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
