module

public import CFSG.RankThree.PartOne.S11b.Sec109Setup
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)

namespace Sec109

theorem card_outer_projectiveSL_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {n : ℕ} (hn : 3 ≤ n) : Nat.card (Outer (projectiveSL n K)) ≤ 2 := by
  classical
  have hunit : ∀ u : Kˣ, u = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have h1 : Nat.card Kˣ = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    have := (Nat.card_eq_one_iff_unique.mp h1).1
    exact fun u => Subsingleton.elim u 1
  have hσ : ∀ σ : K ≃+* K, σ = 1 := by
    have h := (card_ringAut_and_isCyclic Nat.prime_two K (by simpa using hK : Nat.card K = 2 ^ 1)).1
    have := (Nat.card_eq_one_iff_unique.mp h).1
    exact fun σ => Subsingleton.elim σ 1
  have hc : ∀ A : GL (Fin n) K, conjAut n K A ∈ inner (projectiveSL n K) := by
    intro A
    obtain ⟨g, hg⟩ : A ∈ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hunit _
    rw [← hg, conjAut_toGL]
    exact ⟨_, rfl⟩
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hn
  have hsurj : Function.Surjective (fun ε : Fin 2 =>
      (QuotientGroup.mk (dualAut n K ^ (ε : ℕ)) : Outer (projectiveSL n K))) := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
    refine ⟨⟨ε, by omega⟩, ?_⟩
    simp only
    rw [hσ σ, map_one, mul_one, QuotientGroup.eq]
    have h := Subgroup.Normal.conj_mem inferInstance (conjAut n K A) (hc A)
      ((dualAut n K ^ ε)⁻¹)
    simpa [mul_assoc] using h
  exact (Nat.card_le_card_of_surjective _ hsurj).trans (by simp)

theorem lnTwoOuter : LnTwoOuter := by
  intro L _ _ n hmodel
  obtain ⟨⟨-, -, hn, h22, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hn3 : 3 ≤ n := by
    by_contra h
    have h2 : n = 2 := by omega
    subst h2
    exact h22 (by simp)
  have hK2 : Nat.card K = 2 := by simpa using hK
  let e' : L ≃* projectiveSL n K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  refine ⟨?_, ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz' : e' z ∈ Subgroup.center (projectiveSL n K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨w, rfl⟩ := e'.surjective y
      rw [← map_mul, ← map_mul, hz w]
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn3,
      Subgroup.mem_bot] at hz'
    exact e'.injective (by rw [hz', map_one])
  · rw [Nat.card_congr (equivalence e').toEquiv]
    exact card_outer_projectiveSL_two hK2 hn3

end Sec109

end CFSG.RankThree.PartOne
