module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.RankThree.PartOne.KCSpFull

open CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram)
open scoped Matrix

section Transvections

variable {r : ℕ} {K : Type} [Field K]

theorem spTransvection_conj (s : StatedSp r K) (v : Fin r ⊕ Fin r → K) (t : K) :
    s * spTransvection v t * s⁻¹ = spTransvection (spEnd s v) t :=
  CFSG.RankThree.PartOne.CTP.spTransvection_conj s v t

theorem exists_spEnd_eq {u v : Fin r ⊕ Fin r → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ s : StatedSp r K, spEnd s u = v := by
  obtain ⟨l, -, hl⟩ :=
    (CFSG.ClassicalGroups.Alternating.alternating_transvection_vector_transitivity
      (spForm_isAlt (r := r) (K := K)) spForm_nondegenerate).1 u v hu hv
  refine ⟨(l.map fun p => spTransvection p.1 p.2).prod, ?_⟩
  have hlin : spLin r K (l.map fun p => spTransvection p.1 p.2).prod =
      (l.map fun p => CFSG.ClassicalGroups.Alternating.symplecticTransvection (spForm r K)
        spForm_isAlt p.1 p.2).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    exact spLin_spTransvection p.1 p.2
  change ((spLin r K (l.map fun p => spTransvection p.1 p.2).prod :
    LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) u = v
  rw [hlin]
  exact hl

end Transvections

section RootAxis

variable {K : Type} [Field K]

theorem spForm_single_inl_zero (y : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K y (Pi.single (Sum.inl 0) 1) = - y (Sum.inr 0) := by
  rw [spForm_apply]
  simp [dotProduct, Matrix.mulVec, gram, Fintype.sum_sum_type, Fin.sum_univ_two,
    Pi.single_apply]

variable [CharP K 2]

theorem antiSpEquiv_uElt (c : K) :
    antiSpEquiv K (uElt 0 0 c 0) =
      spTransvection (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (antiSpEquiv K (uElt 0 0 c 0)) y = spEnd (spTransvection _ c) y
  rw [spEnd_spTransvection, spForm_single_inl_zero]
  have hM := spMat_antiSpEquiv (K := K) (uElt 0 0 c 0)
  show spMat (antiSpEquiv K (uElt 0 0 c 0)) *ᵥ y = _
  rw [hM, glMat_uElt]
  funext i
  rcases i with i | i <;> fin_cases i
  all_goals simp [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, uMat, antiIdx_inl_zero, antiIdx_inl_one, antiIdx_inr_zero,
    antiIdx_inr_one]
  linear_combination (c * y (Sum.inr 0)) * h2

end RootAxis

section Main

variable {K : Type} [Field K] [CharP K 2]

theorem antiProjEquiv_uElt (c : K) :
    antiProjEquiv K (uElt 0 0 c 0) =
      proj 2 K (spTransvection (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) c) := by
  change projSpEquiv K (antiSpEquiv K (uElt 0 0 c 0)) = _
  rw [antiSpEquiv_uElt]
  rfl

theorem antiProjEquiv_autCongr_symm_apply (β : MulAut (StatedProj (StatedSp 2 K))) (g : antiSp K) :
    antiProjEquiv K ((autCongr K).symm β g) = β (antiProjEquiv K g) := by
  have h2 : (MulAut.congr (antiProjEquiv K)) ((autCongr K).symm β) (antiProjEquiv K g) =
      antiProjEquiv K ((autCongr K).symm β g) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
  have h3 : (MulAut.congr (antiProjEquiv K)) ((autCongr K).symm β) = β :=
    (autCongr K).apply_symm_apply β
  rw [← h2, h3]

end Main

theorem even_symplectic_rank_two_inner_of_fixes_transvections {f : ℕ} (hf : 2 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (u : Fin 2 ⊕ Fin 2 → K) (hu : u ≠ 0)
    (α : MulAut (StatedProj (StatedSp 2 K)))
    (hα : ∀ t : K, α (proj 2 K (spTransvection u t)) = proj 2 K (spTransvection u t)) :
    α ∈ inner (StatedProj (StatedSp 2 K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have hv₀ : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp at this
  obtain ⟨s, hs⟩ := exists_spEnd_eq hv₀ hu
  have hsi : spEnd s⁻¹ u = Pi.single (Sum.inl 0) 1 := by
    rw [← hs, ← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one]
    rfl
  let β : MulAut (StatedProj (StatedSp 2 K)) :=
    MulAut.conj (proj 2 K s)⁻¹ * α * MulAut.conj (proj 2 K s)
  have hβ : ∀ c : K, β (proj 2 K (spTransvection (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) c)) =
      proj 2 K (spTransvection (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) c) := by
    intro c
    have h1 : MulAut.conj (proj 2 K s) (proj 2 K (spTransvection
        (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) c)) = proj 2 K (spTransvection u c) := by
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, spTransvection_conj, hs]
    have h2 : MulAut.conj (proj 2 K s)⁻¹ (proj 2 K (spTransvection u c)) =
        proj 2 K (spTransvection (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) c) := by
      have := spTransvection_conj s⁻¹ u c
      rw [hsi] at this
      rw [MulAut.conj_apply, ← map_inv, ← map_inv, ← map_mul, ← map_mul, this]
    show MulAut.conj (proj 2 K s)⁻¹ (α (MulAut.conj (proj 2 K s) _)) = _
    rw [h1, hα c, h2]
  let β' : MulAut (antiSp K) := (autCongr K).symm β
  have hβ' : ∀ g ∈ CFSG.RankThree.PartOne.KCRootAxis.rootU K
      CFSG.RankThree.PartOne.KCRootAxis.Axis.two, β' g = g := by
    rintro g ⟨c, rfl⟩
    apply (antiProjEquiv K).injective
    rw [antiProjEquiv_autCongr_symm_apply, antiProjEquiv_uElt, hβ c]
  obtain ⟨g, -, hg⟩ := ((CFSG.RankThree.PartOne.KCRootAxis.autNormalizerFacts_axis hf hK
    CFSG.RankThree.PartOne.KCRootAxis.Axis.two).centralizer β').mp hβ'
  have hβc : β = MulAut.conj (antiProjEquiv K g) := by
    have h1 : autCongr K β' = β := (autCongr K).apply_symm_apply β
    rw [← h1, hg]
    exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj (antiProjEquiv K) g
  refine ⟨proj 2 K s * antiProjEquiv K g * (proj 2 K s)⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hβc]
  show MulAut.conj (proj 2 K s) * (MulAut.conj (proj 2 K s)⁻¹ * α * MulAut.conj (proj 2 K s)) *
    (MulAut.conj (proj 2 K s))⁻¹ = α
  rw [map_inv]
  group

end CFSG.RankThree.PartOne.KCSpFull
