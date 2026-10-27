module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankOmega
public import CFSG.LocalAnalysis.StandardType.GGHypSixRestRank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

namespace D4Rank

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBHigherLinearField
open scoped Matrix

section Conj

variable {U G : Type*} [Group U] [Group G]

theorem exists_mulAut_conj (ψ : U →* G) (hinj : Function.Injective ψ) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ β : MulAut U, ∀ y, ψ (β y) = c⁻¹ * ψ y * c := by
  have hc' : c⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) := inv_mem hc
  have hm : ∀ h ∈ ψ.range, c⁻¹ * h * c ∈ ψ.range := fun h hh => by
    have := (Subgroup.mem_normalizer_iff.mp hc' h).mp hh
    rwa [inv_inv] at this
  have hm' : ∀ h ∈ ψ.range, c * h * c⁻¹ ∈ ψ.range := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp hc h).mp hh
  let r : ψ.range ≃* ψ.range :=
    { toFun := fun h => ⟨c⁻¹ * h * c, hm h h.2⟩
      invFun := fun h => ⟨c * h * c⁻¹, hm' h h.2⟩
      left_inv := fun h => Subtype.ext (by simp only; group)
      right_inv := fun h => Subtype.ext (by simp only; group)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let e : U ≃* ψ.range := MonoidHom.ofInjective hinj
  refine ⟨e.trans (r.trans e.symm), fun y => ?_⟩
  have h1 : ∀ z : ψ.range, ψ (e.symm z) = z := fun z => by
    have := congrArg Subtype.val (e.apply_symm_apply z)
    rwa [MonoidHom.ofInjective_apply] at this
  change ψ (e.symm (r (e y))) = _
  rw [h1]
  rfl

end Conj

section Semilinear

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type*} [Group G]

omit [Finite F] [CharP F 2] in
theorem reindex_symm_glFieldAut (σ : F ≃+* F) (M : GL (Fin 4 ⊕ Fin 4) F) :
    (reindexMatrixEquiv (plusIndexEquiv 4)).symm
        (glFieldAut (Fin (2 * 4)) F σ (reindexMatrixEquiv (plusIndexEquiv 4) M)) =
      glFieldEquiv (Fin 4 ⊕ Fin 4) σ M := by
  apply Units.ext
  ext i j
  rw [reindexMatrixEquiv_symm_val]
  change σ (M.val ((plusIndexEquiv 4).symm ((plusIndexEquiv 4) i))
    ((plusIndexEquiv 4).symm ((plusIndexEquiv 4) j))) = σ (M.val i j)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

omit [Finite F] in
theorem ggSpinSemilinear_of_conjAct {ψ : Sp8 F →* G} (hinj : Function.Injective ψ) {c : G}
    {β : MulAut (Sp8 F)} (hβ : ∀ y, ψ (β y) = c⁻¹ * ψ y * c)
    {g : similarityPairs (coordinateQuadPlus 4 F)}
    (hg : conjAct _ g = MulAut.congr modelEquiv8 β) :
    GGSpinSemilinear (quadPlus 4 F) ψ c := by
  obtain ⟨μ, hμ⟩ := g.2
  set e := plusIndexEquiv 4
  refine ⟨(reindexMatrixEquiv e).symm g.val.left, g.val.right, μ, fun v => ?_, fun y y' h => ?_⟩
  · have key : reindexVectorEquiv e (((reindexMatrixEquiv e).symm g.val.left).val *ᵥ
        (fun i => g.val.right (v i))) = coordinateSemilinearMap g.val (reindexVectorEquiv e v) := by
      rw [← reindexMatrixEquiv_mulVec, MulEquiv.apply_symm_apply, coordinateSemilinearMap_apply,
        matrixLinearEquiv_apply]
      rfl
    have h1 := reindexQuadraticForm_map e (quadPlus 4 F)
      (((reindexMatrixEquiv e).symm g.val.left).val *ᵥ (fun i => g.val.right (v i)))
    rw [← h1, key]
    have h2 := hμ (reindexVectorEquiv e v)
    rw [show reindexQuadraticForm e (quadPlus 4 F) = coordinateQuadPlus 4 F from rfl, h2]
    congr 2
    exact reindexQuadraticForm_map e (quadPlus 4 F) v
  · have hy' : y' = β y := hinj (h.trans (hβ y).symm)
    subst hy'
    have hα : ((conjAct _ g (model8 y) : Om8 F) : GL (Fin (2 * 4)) F) =
        ((MulAut.congr modelEquiv8 β (model8 y) : Om8 F) : GL (Fin (2 * 4)) F) := by rw [hg]
    rw [← modelEquiv8_apply, congr_apply_apply', modelEquiv8_apply, conjAct_apply,
      matrixDerivedConjugation_val] at hα
    have hval : ∀ z : Sp8 F, ((model8 z : Om8 F) : GL (Fin (2 * 4)) F) =
        reindexMatrixEquiv e (spinMatrix (quadPlus 4 F) z) := fun z => rfl
    rw [hval, modelEquiv8_apply, hval] at hα
    have h3 := congrArg (reindexMatrixEquiv e).symm hα
    rw [MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv, reindex_symm_glFieldAut] at h3
    exact h3.symm

end Semilinear

section Elem

variable {A B : Type*} [Group A] [Group B]

theorem isElemAbelian_comap {p : ℕ} {f : A →* B} (hf : Function.Injective f) {E : Subgroup B}
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.comap f) :=
  CFSG.Open.IsElemAbelian.comap hE hf

theorem isElemAbelian_map {p : ℕ} (f : A →* B) {E : Subgroup A}
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

end Elem

section Spin

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem card_le_nine_of_spin (hcls : GGD4TrialityClassInput) {G : Type} [Group G]
    (ψ : Sp8 F →* G) (hker : ψ.ker ≤ Subgroup.center (Sp8 F)) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hc3 : c ^ 3 ∈ Subgroup.centralizer (ψ.range : Set G))
    (hns : ¬ GGSpinSemilinear (quadPlus 4 F) ψ c) (E : Subgroup G) (hEψ : E ≤ ψ.range)
    (hEc : E ≤ Subgroup.centralizer ({c} : Set G)) (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  have hcen := RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := F) (n := 4)
    (by norm_num)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hcen.le
  obtain ⟨β, hβ⟩ := exists_mulAut_conj ψ hinj hc
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (Om8 F), α = MulAut.congr modelEquiv8 β := ⟨_, rfl⟩
  have hαm : ∀ y, α (model8 y) = model8 (β y) := fun y => by
    rw [hαdef]; exact congr_apply_apply' modelEquiv8 β y
  have hcomm3 : ∀ y, ψ y * c ^ 3 = c ^ 3 * ψ y := fun y =>
    Subgroup.mem_centralizer_iff.mp hc3 (ψ y) ⟨y, rfl⟩
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun y => hinj ?_
    rw [MulAut.one_apply, pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hβ,
      hβ, hβ]
    have e : c⁻¹ * (c⁻¹ * (c⁻¹ * ψ y * c) * c) * c = (c ^ 3)⁻¹ * (ψ y * c ^ 3) := by
      rw [pow_succ, pow_succ, pow_one]; group
    rw [e, hcomm3, inv_mul_cancel_left]
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, hβ3, map_one]
  have hns' : ∀ g : similarityPairs (coordinateQuadPlus 4 F), conjAct _ g ≠ α :=
    fun g hg => hns (ggSpinSemilinear_of_conjAct hinj hβ (hg.trans hαdef))
  obtain ⟨E', hE'def⟩ : ∃ E' : Subgroup (Om8 F), E' = (E.comap ψ).map model8 := ⟨_, rfl⟩
  have hE' : CFSG.Assembly.IsElemAbelian 3 E' := by
    rw [hE'def]
    exact isElemAbelian_map _ (isElemAbelian_comap hinj hE)
  have hfix : ∀ e ∈ E', α e = e := by
    rw [hE'def]
    rintro _ ⟨y, hy, rfl⟩
    rw [hαm]
    congr 1
    apply hinj
    rw [hβ]
    have h1 : ψ y * c = c * ψ y := Subgroup.mem_centralizer_singleton_iff.mp (hEc hy)
    rw [mul_assoc, h1, inv_mul_cancel_left]
  have hcard : Nat.card E' = Nat.card E := by
    rw [hE'def, Subgroup.card_map_of_injective (AutOm.spinModelPlus_injective (K := F)
      (n := 4) (by norm_num)), ← Subgroup.card_map_of_injective hinj,
      Subgroup.map_comap_eq_self hEψ]
  rw [← hcard]
  exact card_le_nine_of_classInput hcls α hα3 hns' E' hE' hfix

end Spin

section Main

theorem _root_.CFSG.StandardType.ggD4TrialityCentRankInput_of_classInput
    (hcls : GGD4TrialityClassInput) : GGD4TrialityCentRankInput :=
  fun _ _ _ f ψ _ hker _ hc hc3 hns E hEψ hEc hE =>
    card_le_nine_of_spin (F := GaloisField 2 f) hcls ψ hker hc hc3 hns E hEψ hEc hE

end Main

end D4Rank

end CFSG.StandardType
