module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
import CFSG.RankThree.PartTwo.Sec11.Item1116Proof
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1117Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)

variable {G : Type} [Group G] [Finite G]

theorem facts_of_isZ3PGLThreePi {e : G} {Y' A : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 e) (hAC : A ≤ Subgroup.centralizer ({e} : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y' : Set G)) (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hP : Sec8.IsZ3PGLThreePi (sec11YA e Y' A)) :
    Subgroup.center (Y' ⧸ aschbacherSolvableCore 3 Y') = ⊥ ∧
      ∃ E : Subgroup G, E ≤ Y' ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hP
  obtain ⟨ψ₀⟩ := Item1116Proof.nonempty_thetaQuot_equiv_commutator hY' hAC hAY hAc φ
  have hns : ¬ Group.IsSolvable (_root_.commutator (projImage (glPi π 3 (p ^ f) K))) := by
    intro hsol
    have hq' := Sec6.isQuasisimple_of_mem_thetaComponentsAt hY'
    have : Group.IsSolvable (Y' ⧸ aschbacherSolvableCore 3 Y') :=
      Group.isSolvable_of_isSolvable_injective (f := ψ₀.toMonoidHom) ψ₀.injective
    have : Group.IsPerfect (Y' ⧸ aschbacherSolvableCore 3 Y') := hq'.1
    have : Nontrivial (Y' ⧸ aschbacherSolvableCore 3 Y') := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      obtain ⟨u, w, huw⟩ := hq'.2.2
      exact huw (Subsingleton.elim _ _)
    exact Group.IsPerfect.not_isSolvable _ ‹_›
  have hq2 : 2 < p ^ f := by
    by_contra hle
    have h2 : p ^ f = 2 := by
      have hf : f ≠ 0 := by have := hK.one_le; omega
      have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
      omega
    cases π
    · have : Group.IsSolvable (projImage (glPi false 3 (p ^ f) K)) :=
        Sec13.isSolvable_projImage_glPi_two hK h2
      exact hns (subgroup_solvable_of_solvable _)
    · change p ^ f % 3 = 1 at hq
      omega
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := fun h => by
    subst h
    exact hK.unitary
  have hSP : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have ψ : Y' ⧸ aschbacherSolvableCore 3 Y' ≃* projImage (slPi π 3 (p ^ f) K) :=
    ψ₀.trans ((MulEquiv.subgroupCongr (Sec13.commutator_projImage_glPi hK hq2)).trans
      (Subgroup.subgroupOfEquivOfLe hSP))
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    have h1 : ψ z ∈ Subgroup.center (projImage (slPi π 3 (p ^ f) K)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro m
      obtain ⟨y, rfl⟩ := ψ.surjective m
      rw [← map_mul, ← map_mul, hz y]
    rw [Sec13.center_projImage_slPi hK hq hq2, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact ψ.injective (h1.trans ψ.map_one.symm)
  · obtain ⟨D, hD, hD9⟩ := Sec13.exists_elemAbelian_nine_projImage_slPi hK hq
    have hDb := Sec13.isElemAbelian_map hD ψ.symm.toMonoidHom
    have hDb9 : Nat.card (D.map ψ.symm.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective ψ.symm.injective, hD9]
    obtain ⟨S, -, hS, hS9, -⟩ := Sec13.exists_elemAbelian_map_eq (H := Y') (M := ⊤) hDb
      (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
    refine ⟨S.map Y'.subtype, ?_, Sec13.isElemAbelian_map hS _, ?_⟩
    · rintro _ ⟨s, -, rfl⟩
      exact s.2
    · rw [Subgroup.card_map_of_injective Y'.subtype_injective, hS9, hDb9]

end CFSG.RankThree.PartTwo.Sec11.Item1117Res7Proof
