module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL
import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

variable {G : Type} [Group G] {X : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def actSL (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) :
    Subgroup.normalizer (X : Set G) →* MulAut (Matrix.SpecialLinearGroup (Fin 3) K) :=
  (MulAut.congr ι).toMonoidHom.comp X.normalizerMonoidHom

theorem actSL_apply (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (a : Subgroup.normalizer (X : Set G)) (x : X) :
    actSL ι a (ι x) = ι (X.normalizerMonoidHom a x) := by
  simp [actSL, MulAut.congr_apply]

theorem actSL_apply_eq (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (a : Subgroup.normalizer (X : Set G)) {x y : X} (h : (y : G) = a * x * (a : G)⁻¹) :
    actSL ι a (ι x) = ι y := by
  rw [actSL_apply]
  congr 1
  exact Subtype.ext h.symm

theorem actSL_eq_one_iff (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (a : Subgroup.normalizer (X : Set G)) :
    actSL ι a = 1 ↔ ∀ x ∈ X, (a : G) * x = x * a := by
  constructor
  · intro h x hx
    have h1 := congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 3) K) => φ (ι ⟨x, hx⟩)) h
    simp only [actSL_apply, MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val (ι.injective h1)
    change (a : G) * x * (a : G)⁻¹ = x at h2
    calc (a : G) * x = (a : G) * x * (a : G)⁻¹ * a := by group
      _ = x * a := by rw [h2]
  · intro h
    ext y : 1
    obtain ⟨x, rfl⟩ := ι.surjective y
    rw [actSL_apply, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    change (a : G) * x * (a : G)⁻¹ = x
    rw [h x x.2, mul_inv_cancel_right]

theorem exists_actSL_eq_slConjugation [Finite G] [Finite K]
    (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) (hθ : aschbacherSolvableCore 3 X = ⊥) {a : G}
    (ha : a ∈ Subgroup.normalizer (X : Set G)) (ha3 : a ^ 3 = 1)
    (hnf : ¬ KFacts.InducesKindSL 3 K X a .field) :
    ∃ g : GL (Fin 3) K, actSL ι ⟨a, ha⟩ = slConjugation 3 K g := by
  have hmk : Function.Bijective (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) := by
    refine ⟨?_, QuotientGroup.mk'_surjective _⟩
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hθ
  set q : X ≃* X ⧸ aschbacherSolvableCore 3 X := MulEquiv.ofBijective _ hmk with hq
  set e : X ⧸ aschbacherSolvableCore 3 X ≃* Matrix.SpecialLinearGroup (Fin 3) K := q.symm.trans ι
    with he
  have hqx : ∀ x : X, q x = (x : X ⧸ aschbacherSolvableCore 3 X) := fun x => rfl
  have hτ : KFacts.inducedAutHom X e ⟨a, ha⟩ = actSL ι ⟨a, ha⟩ := by
    ext y : 1
    obtain ⟨x, rfl⟩ := ι.surjective y
    rw [actSL_apply, KFacts.inducedAutHom_apply, MulAut.congr_apply]
    have h1 : e.symm (ι x) = (x : X ⧸ aschbacherSolvableCore 3 X) := by
      rw [he, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply, hqx]
    change e (Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨a, ha⟩) (e.symm (ι x))) = _
    rw [h1, Sec4.thetaQuotMulAut_mk, ← hqx, he, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have hmem : descendAut 3 K (KFacts.inducedAutHom X e ⟨a, ha⟩) ∈ linearAutGroup 3 K := by
    rcases KFacts.inducesKindSL_inner_or_diagonal_or_field X (n := 3) (K := K) le_rfl ha ha3 e
      with h | h | h
    · exact (KFacts.stdPinnedPSL 3 K).inn_le h
    · exact h.1
    · exact absurd ⟨e, ha, h⟩ hnf
  obtain ⟨g, hg⟩ := mem_linearAutGroup_iff.mp hmem
  refine ⟨g, ?_⟩
  rw [← hτ]
  set τ := KFacts.inducedAutHom X e ⟨a, ha⟩ with hτdef
  have hg' : descendAut 3 K (slConjugation 3 K g) = descendAut 3 K τ := hg
  have hρ : descendAut 3 K ((slConjugation 3 K g)⁻¹ * τ) = 1 := by
    rw [map_mul, map_inv, hg', inv_mul_cancel]
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) (n := 3)
    le_rfl
  have h1 : (slConjugation 3 K g)⁻¹ * τ = 1 := by
    apply KFacts.eq_one_of_forall_mul_inv_mem_center
    intro s
    have h2 := congrArg (fun φ : MulAut (projectiveSL 3 K) => φ (proj 3 K s)) hρ
    simp only [descendAut_proj, MulAut.one_apply] at h2
    exact scalars_le_center 3 K (proj_eq_proj_iff.mp h2.symm)
  calc τ = slConjugation 3 K g * ((slConjugation 3 K g)⁻¹ * τ) := by group
    _ = slConjugation 3 K g := by rw [h1, mul_one]

end CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof
