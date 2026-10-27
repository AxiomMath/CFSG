module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelAbelianization

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem orthDerived_le_omegaGroup [CharP K 2] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) : orthDerived Q ≤ omegaGroup Q hQ := by
  rw [orthDerived, Subgroup.commutator_le]
  intro g hg h hh
  have hk : (⟨⁅g, h⁆, Subgroup.commutator_le_self _
      (Subgroup.commutator_mem_commutator hg hh)⟩ :
      TauCeti.QuadraticMap.orthogonalGroup Q) ∈ (dicksonHom Q hQ).ker := by
    rw [MonoidHom.mem_ker]
    have : (⟨⁅g, h⁆, Subgroup.commutator_le_self _
        (Subgroup.commutator_mem_commutator hg hh)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Q) =
        ⁅(⟨g, hg⟩ : TauCeti.QuadraticMap.orthogonalGroup Q), ⟨h, hh⟩⁆ := rfl
    rw [this, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at hk
  exact hk

theorem omegaGroup_le_orthDerived [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    omegaGroup Q hQ ≤ orthDerived Q := by
  classical
  obtain ⟨hΩE, hgen⟩ := CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT
  obtain ⟨P, r, hr, hP, -, -⟩ := CFSG.RankThree.Classical.exists_hypPair_tail_decomposition hQ hT
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨-, hcard⟩ := CFSG.LocalAnalysis.ComponentInitial.char_two_orthogonal_abelianization_bound
    h2 hQ (hP 0 1 (by omega) (by omega) (by omega)) hΩE.ge hgen
  have : Nontrivial V := by
    obtain ⟨T, hT3, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hT3 ▸ Submodule.finrank_le T))
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hΩO : omegaGroup Q hQ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := omegaGroup_le Q hQ
  have hNΩ : orthDerived Q ≤ omegaGroup Q hQ := orthDerived_le_omegaGroup hQ
  have hmul := Subgroup.relIndex_mul_relIndex (orthDerived Q) (omegaGroup Q hQ)
    (TauCeti.QuadraticMap.orthogonalGroup Q) hNΩ hΩO
  rw [relIndex_omegaGroup Q hQ] at hmul
  have hsub : (orthDerived Q).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q) =
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [orthDerived, ← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hNO : (orthDerived Q).relIndex (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ 2 := by
    rw [Subgroup.relIndex, hsub]
    exact hcard
  have hne : (orthDerived Q).relIndex (omegaGroup Q hQ) ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_eq_one.mp (by omega)

end CFSG.RankThree.PartOne.FieldFix
