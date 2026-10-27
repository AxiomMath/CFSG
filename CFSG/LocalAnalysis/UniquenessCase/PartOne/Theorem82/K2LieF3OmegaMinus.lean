module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieDefs
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL7
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.SL2Pair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (ActionProperties)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)
open CFSG.RankThree.Classical.SteinbergBY
  (OrthogonalGates orthogonal_large_prime_semilinear_field_and_diagonal_gates)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  (SubfieldSetup fieldAutT fieldPair fieldPair_right orderOf_fieldAutT rootFree_of_odd_degree
    subfieldSetup_minus)
open CFSG.Blueprint.EvenSource (nonempty_statedOmegaMinus_equiv)
open CFSG.RankThree.PartTwo.Sec19 (exists_fixedSubfield_of_orderOf_three)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
  (finrank_fixedField_eq_three)

private theorem exists3_pomega8m_congr_not_inner {G H : Type*} [Group G] [Group H]
    (θ : G ≃* H) {α : MulAut G}
    (h : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G) :
    MulAut.congr θ α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner H := by
  intro hc
  apply h
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr θ, Subgroup.mem_map] at hc
  obtain ⟨a, ha, haeq⟩ := hc
  have : a = α := (MulAut.congr θ).injective haeq
  rwa [this] at ha

private theorem exists3_pomega8m_fieldPart {K : Type} [Field K] [Finite K] {d f : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hgates : OrthogonalGates Q f)
    (htop : matrixProjectiveImage Q = ⊤) {β : MulAut (matrixProjectiveDerived Q)}
    (hβout : β ∉ innAut (matrixProjectiveDerived Q)) (hβpow : ∃ m : ℕ, β ^ (3 ^ m) = 1) :
    ∃ σ : K ≃+* K, orderOf σ = 3 := by
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, m, hrel⟩, -⟩ := hgates
  have hβmem : β ∈ matrixProjectiveImage Q := by rw [htop]; exact Subgroup.mem_top β
  let τ : K ≃+* K := ψ ⟨β, hβmem⟩
  have hτpow : ∃ m : ℕ, τ ^ (3 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := hβpow
    refine ⟨m, ?_⟩
    have hm' : (⟨β, hβmem⟩ : matrixProjectiveImage Q) ^ (3 ^ m) = 1 := by
      apply Subtype.ext
      simpa using hm
    change ψ ⟨β, hβmem⟩ ^ (3 ^ m) = 1
    rw [← map_pow, hm', map_one]
  have hτ1 : τ ≠ 1 := by
    intro hτ
    have hker : (⟨β, hβmem⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]; exact hτ
    have hβD : β ∈ (linearConjugationHom Q).range := by
      rw [hψker] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    obtain ⟨s, hs⟩ := hβpow
    exact hβout
      (mem_of_pow_three_pow_mem_of_relIndex_two_pow hrel hβD (by rw [hs]; exact one_mem _))
  obtain ⟨k, hk⟩ := hτpow
  obtain ⟨σ, hσ3, hσ1⟩ := exists_pow_three_eq_one_of_pow_three_pow_eq_one hτ1 hk
  exact ⟨σ, orderOf_eq_prime hσ3 hσ1⟩

private theorem exists3_pomega8m_fieldAut_cube {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : ActionProperties Q (projectivePointAction Q)) (hσ3 : orderOf σ = 3) :
    (fieldAutT Q σ hQσ) ^ 3 = 1 := by
  have h3 : orderOf (fieldAutT Q σ hQσ) = 3 := by
    rw [orderOf_fieldAutT Q σ hQσ hnd hT hAP, hσ3]
  rw [← h3]
  exact pow_orderOf_eq_one _

private theorem exists3_pomega8m_fieldAut_not_inner {K : Type} [Field K] {d f : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hgates : OrthogonalGates Q f) (σ : K ≃+* K)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (hσ1 : σ ≠ 1) :
    fieldAutT Q σ hQσ ∉ innAut (matrixProjectiveDerived Q) := by
  obtain ⟨-, ⟨ψ, hψspec, hψker, -⟩, ⟨hInnD, -⟩, -⟩ := hgates
  intro hin
  have hD : fieldAutT Q σ hQσ ∈ (linearConjugationHom Q).range := hInnD hin
  have hmem : fieldAutT Q σ hQσ ∈ matrixProjectiveImage Q := ⟨fieldPair Q σ hQσ, rfl⟩
  have h2 : ψ ⟨fieldAutT Q σ hQσ, hmem⟩ = σ := by
    have hEq : (⟨fieldAutT Q σ hQσ, hmem⟩ : matrixProjectiveImage Q) =
        ⟨matrixProjectiveConjugationHom Q (fieldPair Q σ hQσ), ⟨fieldPair Q σ hQσ, rfl⟩⟩ :=
      Subtype.ext rfl
    rw [hEq, hψspec (fieldPair Q σ hQσ), fieldPair_right]
  have h3 : ψ ⟨fieldAutT Q σ hQσ, hmem⟩ = 1 := by
    have hx : (⟨fieldAutT Q σ hQσ, hmem⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [hψker]; exact Subgroup.mem_subgroupOf.mpr hD
    rwa [MonoidHom.mem_ker] at hx
  rw [h2] at h3
  exact hσ1 h3

private theorem exists3_pomega8m_fixed {X : Type} [Group X] [Finite X] {r f : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus 4 r f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = r ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c)))
    (σ : K ≃+* K) (hσ3 : orderOf σ = 3) : Exists3 X := by
  have hn4 : 1 ≤ 4 := by norm_num
  obtain ⟨k₀, hk₀, -, -⟩ := exists_fixedSubfield_of_orderOf_three hσ3
  have hdeg : Module.finrank k₀ K = 3 := finrank_fixedField_eq_three hσ3 hk₀
  obtain ⟨b', c', hirr'⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic k₀
  have hroot : ∀ s : K, s ^ 2 + (b' : K) * s + (c' : K) ≠ 0 :=
    rootFree_of_odd_degree k₀ (by norm_num) (by norm_num) hdeg b' c' hirr'
  let Q' : QuadraticForm K (Fin (2 * 4) → K) := coordinateQuadMinus 4 K hn4 (b' : K) (c' : K)
  have hsub : SubfieldSetup k₀ (coordinateQuadMinus 4 k₀ hn4 b' c') Q' σ 3 :=
    subfieldSetup_minus k₀ hk₀ (by norm_num) (by norm_num) hσ3 le_rfl hdeg b' c' hirr'
  have hgates' : OrthogonalGates Q' f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates
      (StatedProj (StatedOmega (StatedQuadMinus 4 K (b' : K) (c' : K)))) .POmegaMinus
      (Or.inr (Or.inr rfl)) 4 r f
      ⟨hadm, K, inferInstance, inferInstance, hK, b', c', hroot, ⟨MulEquiv.refl _⟩⟩
      hn4 K hK b' c' hroot (MulEquiv.refl _)
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [← orderOf_eq_one_iff, hσ3] at h
    norm_num at h
  have ha'3 : (fieldAutT Q' σ hsub.hQσ) ^ 3 = 1 :=
    exists3_pomega8m_fieldAut_cube Q' σ hsub.hQσ hsub.hnd hsub.hT hsub.hAP hσ3
  have ha'out : fieldAutT Q' σ hsub.hQσ ∉ innAut (matrixProjectiveDerived Q') :=
    exists3_pomega8m_fieldAut_not_inner Q' hgates' σ hsub.hQσ hσ1
  have hExists3 : Exists3 (matrixProjectiveDerived Q') := fun _ => ⟨_, ha'3, ha'out⟩
  have hι : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus 4 K (b' : K) (c' : K))) :=
    (nonempty_statedOmegaMinus_equiv hn4 hirr hroot).some
  exact exists3_of_mulEquiv
    ((e.trans hι).trans (coordinateMinusWitnessEquiv K hn4 b' c' (MulEquiv.refl _))) hExists3

private theorem exists3_pomega8m_aux {X : Type} [Group X] [Finite X] {r f : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus 4 r f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = r ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) : Exists3 X := by
  intro hφ
  obtain ⟨φ, hφout, hφpow⟩ := hφ
  have hn4 : 1 ≤ 4 := by norm_num
  let θ : X ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K hn4 b c) :=
    coordinateMinusWitnessEquiv K hn4 b c e
  let Q : QuadraticForm K (Fin (2 * 4) → K) := coordinateQuadMinus 4 K hn4 b c
  have hC : StatedClassicalModel X .POmegaMinus 4 r f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr, ⟨e⟩⟩
  have hgates : OrthogonalGates Q f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates X .POmegaMinus
      (Or.inr (Or.inr rfl)) 4 r f hC hn4 K hK b c hirr e
  have htop : matrixProjectiveImage Q = ⊤ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K 4 le_rfl b c hirr
  have hβout : MulAut.congr θ φ ∉ innAut (matrixProjectiveDerived Q) :=
    exists3_pomega8m_congr_not_inner θ hφout
  have hβpow : ∃ m : ℕ, (MulAut.congr θ φ) ^ (3 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := hφpow
    exact ⟨m, by rw [← map_pow (MulAut.congr θ) φ (3 ^ m), hm, map_one]⟩
  obtain ⟨σ, hσ3⟩ := exists3_pomega8m_fieldPart Q hgates htop hβout hβpow
  exact exists3_pomega8m_fixed hadm K hK b c hirr e σ hσ3 ⟨φ, hφout, hφpow⟩

theorem exists3_pomega8m {X : Type} [Group X] [Finite X] {r f : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (h : LieModel X .POmegaMinus 4 r f) : Exists3 X := by
  have hC : StatedClassicalModel X .POmegaMinus 4 r f :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨hadm, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
  exact exists3_pomega8m_aux hadm K hK b c hirr e

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
