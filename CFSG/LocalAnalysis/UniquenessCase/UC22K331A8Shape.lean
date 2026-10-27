module

public import CFSG.GH74.SectionalRankExtension
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylowAlt8
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.SignalizerFunctorTheorem CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped Pointwise

theorem k331_not_isSectionOf_sl2 {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    ¬ IsSectionOf (alternatingGroup (Fin 8)) (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rintro ⟨H, f, hf⟩
  have hA : CFSG.GH74.SectionalTwoRankLE (alternatingGroup (Fin 8)) 2 :=
    CFSG.GH74.SectionalTwoRankLE.of_surjective f hf
      (CFSG.GH74.SectionalTwoRankLE.subgroup H (CFSG.GH74.SectionalTwoRankLE.specialLinearGroup F h2))
  obtain ⟨E, -, hE16, hEsq⟩ :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.exists_elemAbelian_sixteen_of_equiv_alt8
      (Subgroup.topEquiv (G := alternatingGroup (Fin 8)))
  have hE : CFSG.Open.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => by rw [sq]; exact hEsq x hx⟩
    have ha : (a : alternatingGroup (Fin 8))⁻¹ = a := inv_eq_of_mul_eq_one_right (hEsq a a.2)
    have hb : (b : alternatingGroup (Fin 8))⁻¹ = b := inv_eq_of_mul_eq_one_right (hEsq b b.2)
    have hab : ((a : alternatingGroup (Fin 8)) * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (hEsq _ (a * b).2)
    rw [mul_inv_rev, ha, hb] at hab
    exact hab.symm
  have := hA.card_le_of_elementary E hE
  rw [hE16] at this
  norm_num at this

theorem k331_not_isSectionOf_shape {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (h₁ : (2 : F₁) ≠ 0) (h₂ : (2 : F₂) ≠ 0) (S : Shape Y F₁ F₂) :
    ¬ IsSectionOf (alternatingGroup (Fin 8)) Y := by
  intro h
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hnc : ¬ ∀ x y : alternatingGroup (Fin 8), x * y = y * x := by
    intro hc
    have := congrArg Subtype.val
      (hc ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
        ⟨Equiv.swap 0 1 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩)
    revert this
    decide
  have := S.normal₁
  have := S.normal₂
  have hcomm : ∀ a b : Y ⧸ (S.I₁ ⊔ S.I₂), a * b = b * a := by
    have htop : Subgroup.zpowers (QuotientGroup.mk' (S.I₁ ⊔ S.I₂) S.t) = ⊤ := by
      rw [← MonoidHom.map_zpowers,
        ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (S.I₁ ⊔ S.I₂)), ← S.gen,
        Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top b)
    exact zpow_mul_comm _ i j
  have hE : IsSectionOf (alternatingGroup (Fin 8)) ↥(S.I₁ ⊔ S.I₂) := by
    rcases h.of_hom (QuotientGroup.mk' (S.I₁ ⊔ S.I₂)) with h' | h'
    · rwa [QuotientGroup.ker_mk'] at h'
    · exact absurd (h'.commutative hcomm) hnc
  have := S.normal₂.subgroupOf (S.I₁ ⊔ S.I₂)
  rcases hE.of_hom (QuotientGroup.mk' (S.I₂.subgroupOf (S.I₁ ⊔ S.I₂))) with h' | h'
  · rw [QuotientGroup.ker_mk'] at h'
    exact k331_not_isSectionOf_sl2 h₂
      (h'.trans (IsSectionOf.of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe le_sup_right).trans S.e₂).symm))
  · let g : ↥S.I₁ →* ↥(S.I₁ ⊔ S.I₂) ⧸ S.I₂.subgroupOf (S.I₁ ⊔ S.I₂) :=
      (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_left)
    have hg : Function.Surjective g := by
      intro x
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective _ x
      have hy' : y ∈ (S.I₁ : Set Y) * (S.I₂ : Set Y) := by
        rw [← Subgroup.mul_normal]
        exact hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy'
      refine ⟨⟨a, ha⟩, ?_⟩
      simp only [g, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hb
    exact k331_not_isSectionOf_sl2 h₁
      ((h'.trans (IsSectionOf.of_surjective g hg)).trans (IsSectionOf.of_mulEquiv S.e₁.symm))

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
