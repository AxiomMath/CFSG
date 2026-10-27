module

import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec12.Hering129KE1
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Open (StatedScalars)
open Matrix (ProjGenLinGroup)


namespace Hering129KH3

variable {P : Type} [Group P] [Finite P] {Yh Bh : Subgroup P} {xh bh ch : P}
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem conj_compat [Yh.Normal] (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) {g : P}
    {y : GL (Fin 3) K} (hy : Sec4.IsPGLAtP e g y) {l : P} (hl : l ∈ Yh) :
    ((e ⟨g * l * g⁻¹, Subgroup.Normal.conj_mem ‹_› l hl g⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) =
    ProjGenLinGroup.mk y *
      ((e ⟨l, hl⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
      (ProjGenLinGroup.mk y)⁻¹ := by
  have h := hy.2 (e ⟨l, hl⟩)
  rw [Sec4.coe_slAct_eqP] at h
  simpa using h

theorem hess_actions [Yh.Normal] (hD : HessData Yh Bh xh bh ch) (hK : Sec4.PiField π p f K)
    (hq : Sec4.ModThree π (p ^ f)) (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) :
    ∀ g ∈ Yh ⊔ Bh, ∃ y, Sec4.IsPGLAtP e g y := by
  have hq2 : 2 < p ^ f := by
    have h2le : 2 ≤ p ^ f :=
      le_trans hK.prime.two_le (Nat.le_self_pow (by have := hK.one_le; omega) p)
    by_contra hcon
    have h2 : p ^ f = 2 := by omega
    cases π with
    | true =>
      have hq1 : p ^ f % 3 = 1 := hq
      omega
    | false =>
      haveI : Group.IsSolvable (projImage (Sec4.slPi false 3 (p ^ f) K)) :=
        Sec13.isSolvable_projImage_slPi_two hK h2
      haveI : Group.IsSolvable ↥Yh :=
        Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      obtain ⟨Xh, hXY, -, hperfX, -, -, p', n, hp', h4, φ', hφ'⟩ := hD.comp
      haveI : Group.IsSolvable ↥Xh :=
        Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hXY).toMonoidHom)
          (MulEquiv.surjective _)
      have hsub : Subsingleton ↥Xh := by
        by_contra hns
        rw [not_subsingleton_iff_nontrivial] at hns
        exact Group.IsPerfect.not_isSolvable ↥Xh inferInstance
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at h4
      have hsimpl := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 2) (GaloisField p' n)
        le_rfl (Or.inr (by rw [GaloisField.card p' n hn0]; omega))
        (Or.inr (by rw [GaloisField.card p' n hn0]; omega))
      have hsubP : Subsingleton (projSL 2 (GaloisField p' n)) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hφ' a
        obtain ⟨y, rfl⟩ := hφ' b
        rw [Subsingleton.elim x y]
      exact (not_nontrivial_iff_subsingleton.mpr hsubP) inferInstance
  haveI : IsSimpleGroup (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hMq : CFSG.IsQuasisimple (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect
        (Sec13.isPerfect_projImage_slPi hK hq2))).1
  have hθ := Sec4.aschbacherSolvableCore_eq_bot_proj hK hq (CFSG.IsQuasisimple.of_mulEquiv e hMq) e
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hY : ∀ l ∈ Yh, ∃ y, Sec4.IsPGLAtP e l y := by
    intro l hl
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
    exact ⟨s, Sec4.isPGLAtP_of_mem e hπ hl hs hse.symm⟩
  have hB : ∀ β ∈ Bh, ∃ y, Sec4.IsPGLAtP e β y := by
    intro β hβ
    have hx3 : (⟨β, Sec4.mem_normalizer_of_normal β⟩ :
        Subgroup.normalizer (Yh : Set P)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hD.elem.2 β hβ)
    rcases Sec4.pslAct_pgl_or_field hK hq2 hθ e _ hx3 with ⟨y, hy, hyall⟩ | ⟨hfield, -⟩
    · exact ⟨y, hy, hyall⟩
    · exact absurd hfield (hD.inner β hβ).1
  intro g hg
  obtain ⟨l, hl, β, hβ, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  obtain ⟨y, hy⟩ := hY l hl
  obtain ⟨z, hz⟩ := hB β hβ
  exact ⟨y * z, Sec4.isPGLAtP_mul e hy hz⟩

end Hering129KH3

end CFSG.RankThree.PartTwo.Sec12
