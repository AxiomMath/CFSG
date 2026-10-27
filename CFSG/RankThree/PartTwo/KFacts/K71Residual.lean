module

public import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial
open Matrix
open scoped MatrixGroups

section Residual

variable {A : Type*} [Group A]

theorem le_inSubgroup_perfectResidual [Finite A] {P X : Subgroup A} (hP : Group.IsPerfect P)
    (hPX : P ≤ X) : P ≤ inSubgroup perfectResidual X := by
  have hP' : Group.IsPerfect (P.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPX).symm.surjective
  have h := Subgroup.map_mono (f := X.subtype)
    ((CFSG.perfect_residual_transport (MonoidHom.id X)).2.2 _ hP')
  rwa [Subgroup.map_subgroupOf_eq_of_le hPX] at h

theorem inSubgroup_perfectResidual_le {B : Type*} [Group B] {X P : Subgroup A} (ψ : X →* B)
    (hψ : ∀ x y, ψ x * ψ y = ψ y * ψ x) (hker : ∀ x : X, ψ x = 1 → (x : A) ∈ P) :
    inSubgroup perfectResidual X ≤ P := by
  rintro _ ⟨x, hx, rfl⟩
  apply hker
  have h1 : perfectResidual X ≤ derivedSeries X 1 := iInf_le _ 1
  have h2 : derivedSeries X 1 ≤ ψ.ker := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hψ g₁ g₂
  exact h2 (h1 hx)

end Residual

open CFSG.Assembly.RankThreeEven (projSL) in
theorem nonempty_sl2_mulEquiv_projSL {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) : Nonempty (SL(2, F) ≃* projSL 2 (GaloisField 2 f)) := by
  have hf : f ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    rw [hF, pow_zero] at this
    exact lt_irrefl _ this
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField 2 f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, GaloisField.card 2 f hf]
  exact ⟨(CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
    (FiniteField.ringEquivOfCardEq hcard)).trans
    ((LinearCover.projectiveSLTwoEquivSL _).symm.trans
      ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 _).symm.trans
        (projSLEquivPSL _).symm))⟩

section Hom

theorem map_inSubgroup_perfectResidual_hom {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (π : A →* B) (X : Subgroup A) :
    (inSubgroup perfectResidual X).map π = inSubgroup perfectResidual (X.map π) := by
  have hrange : (π.comp X.subtype).range = X.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [inSubgroup, Subgroup.map_map, (CFSG.perfect_residual_transport (π.comp X.subtype)).1]
  exact inSubgroup_perfectResidual_congr hrange

end Hom

theorem nontrivial_sl2 (F : Type*) [Field F] : Nontrivial SL(2, F) := by
  refine ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, 1, fun h => ?_⟩⟩
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp at this

end CFSG.RankThree.PartTwo.KFacts
