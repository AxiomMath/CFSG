module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourKernelGraph
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.KFacts Matrix

variable {k : Type*} [Field k]

theorem dualAut_ne_one [Finite k] {n : ℕ} (hn : 3 ≤ n) : dualAut n k ≠ 1 := fun h =>
  ProjectivePlane.dualAut_not_mem_semilinearAutGroup hn (h ▸ one_mem _)

theorem fieldAut_ne_one [Finite k] {n : ℕ} (hn : 3 ≤ n) {σ : k ≃+* k} (hσ : σ ≠ 1) :
    fieldAut n k σ ≠ 1 := fun h =>
  hσ (eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 σ (by rw [map_one, one_mul, h])).1

theorem isGraphField_dualAut_mul_fieldAut [Finite k] {n : ℕ} (hn : 3 ≤ n) {σ : k ≃+* k}
    (hσ : σ ≠ 1) : (stdPinnedPSL n k).IsGraphField (dualAut n k * fieldAut n k σ) :=
  PinnedAut.isGraphField_of_mem _ (Set.mem_singleton _) (dualAut_ne_one hn) ⟨σ, rfl⟩
    (fieldAut_ne_one hn hσ)

variable {σ : k ≃+* k}

theorem isGraphField_iff_conj (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2)
    (τ : MulAut (projectiveSL 3 k)) :
    (stdPinnedPSL 3 k).IsGraphField τ ↔
      ∃ d ∈ linearAutGroup 3 k, τ = d * (dualAut 3 k * fieldAut 3 k σ) * d⁻¹ := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  constructor
  · rintro ⟨γ, hγ, -, φ, ⟨ρ, rfl⟩, hφ1, d, hd, rfl⟩
    rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ
    subst hγ
    rcases LinearThreeFourOuter.ringEquiv_eq_one_or hσ hk ρ with rfl | rfl
    · exact absurd (map_one _) hφ1
    · exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact PinnedAut.isGraphField_conj _ hd
      (isGraphField_dualAut_mul_fieldAut le_rfl (LinearThreeFourOuter.sigma_ne_one hσ hk))

theorem graphFieldP_apply [CharP k 2] (hσ : ∀ a, σ a = a ^ 2) (x : projectiveSL 3 k) :
    LinearFieldFourKernel.graphFieldP x = (dualAut 3 k * fieldAut 3 k σ) x := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 k x
  rw [MulAut.mul_apply, fieldAut_proj, dualAut_proj, LinearFieldFourKernel.graphFieldP_proj]
  congr 1
  have hsq : LinearFieldFourKernel.sqSL g = SpecialLinearGroup.map σ.toRingHom g := by
    ext i j
    simp [LinearFieldFourKernel.sqSL, hσ, frobenius_def]
  rw [LinearFieldFourKernel.graphFieldSL, MonoidHom.comp_apply, hsq]
  rfl

theorem isGraphField_iff_graphFieldP [CharP k 2] (hk : Nat.card k = 4)
    (τ : MulAut (projectiveSL 3 k)) :
    (stdPinnedPSL 3 k).IsGraphField τ ↔
      ∃ d ∈ linearAutGroup 3 k, ∀ x, τ x = d (LinearFieldFourKernel.graphFieldP (d⁻¹ x)) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  rw [isGraphField_iff_conj hk hσ]
  refine exists_congr fun d => and_congr_right fun _ => ?_
  constructor
  · rintro rfl x
    rw [graphFieldP_apply hσ]
    rfl
  · intro h
    ext x
    rw [h, graphFieldP_apply hσ]
    rfl

theorem exists_isGraphField_eq_graphFieldP [CharP k 2] (hk : Nat.card k = 4) :
    ∃ τ : MulAut (projectiveSL 3 k), (stdPinnedPSL 3 k).IsGraphField τ ∧
      ∀ x, τ x = LinearFieldFourKernel.graphFieldP x := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  exact ⟨_, isGraphField_dualAut_mul_fieldAut le_rfl (LinearThreeFourOuter.sigma_ne_one hσ hk),
    fun x => (graphFieldP_apply hσ x).symm⟩

theorem inducesKindPSL_graphField_of_graphFieldP [CharP k 2] (hk : Nat.card k = 4)
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 k)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {d : MulAut (projectiveSL 3 k)}
    (hd : d ∈ linearAutGroup 3 k)
    (h : ∀ y, inducedAutHom L e ⟨x, hx⟩ y = d (LinearFieldFourKernel.graphFieldP (d⁻¹ y))) :
    InducesKindPSL 3 k L x .graphField :=
  ⟨e, hx, (isGraphField_iff_graphFieldP hk _).2 ⟨d, hd, h⟩⟩

end CFSG.RankThree.PartTwo.Sec4
