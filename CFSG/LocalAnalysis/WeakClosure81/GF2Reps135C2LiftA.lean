module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Ctx
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}

theorem w135c2_S_normal (hctx : Is135Context Y L) [hN : ((Zc L).subgroupOf Y).Normal] :
    ((L.subgroupOf Y).map (QuotientGroup.mk' ((Zc L).subgroupOf Y))).Normal :=
  (w135_normal_of_ctx hctx).map (QuotientGroup.mk' ((Zc L).subgroupOf Y))
    (QuotientGroup.mk'_surjective ((Zc L).subgroupOf Y))

theorem w135c2_S_centralizer (hctx : Is135Context Y L) [hN : ((Zc L).subgroupOf Y).Normal] :
    Subgroup.centralizer
      (((L.subgroupOf Y).map (QuotientGroup.mk' ((Zc L).subgroupOf Y)) :
        Subgroup (↥Y ⧸ (Zc L).subgroupOf Y)) : Set (↥Y ⧸ (Zc L).subgroupOf Y)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro ybar hybar
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((Zc L).subgroupOf Y) ybar
  have hcomm : ∀ l ∈ L, ⁅(y : MulAut W), l⁆ ∈ Zc L := by
    intro l hl
    let l' : ↥Y := ⟨l, hctx.2.2.1 hl⟩
    have hl' : l' ∈ L.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hl
    have hl'mem : (QuotientGroup.mk' ((Zc L).subgroupOf Y)) l' ∈
        (L.subgroupOf Y).map (QuotientGroup.mk' ((Zc L).subgroupOf Y)) :=
      Subgroup.mem_map.mpr ⟨l', hl', rfl⟩
    have hcen := Subgroup.mem_centralizer_iff.mp hybar
      ((QuotientGroup.mk' ((Zc L).subgroupOf Y)) l') hl'mem
    have h2 : (QuotientGroup.mk' ((Zc L).subgroupOf Y)) (y * l' * y⁻¹ * l'⁻¹) = 1 := by
      have hyl : (QuotientGroup.mk' ((Zc L).subgroupOf Y)) (y * l') =
          (QuotientGroup.mk' ((Zc L).subgroupOf Y)) (l' * y) := by
        rw [map_mul, map_mul]
        exact hcen.symm
      rw [show y * l' * y⁻¹ * l'⁻¹ = (y * l') * (l' * y)⁻¹ by group]
      rw [map_mul, map_inv, hyl, mul_inv_cancel]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hZ : ((y * l' * y⁻¹ * l'⁻¹ : ↥Y) : MulAut W) ∈ Zc L :=
      Subgroup.mem_subgroupOf.mp h2
    simpa [commutatorElement_def] using hZ
  have hyZ : (y : MulAut W) ∈ Zc L := w135c2_mem_Zc_of_comm hctx y.2 hcomm
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr hyZ

theorem w135c2_S_equiv (hctx : Is135Context Y L) [hN : ((Zc L).subgroupOf Y).Normal] :
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
      ↥((L.subgroupOf Y).map (QuotientGroup.mk' ((Zc L).subgroupOf Y)))) := by
  let φ : ↥L →* ↥Y ⧸ ((Zc L).subgroupOf Y) :=
    (QuotientGroup.mk' ((Zc L).subgroupOf Y)).comp (Subgroup.inclusion hctx.2.2.1)
  have hker : Subgroup.center ↥L = φ.ker := by
    ext l
    rw [MonoidHom.mem_ker]
    change l ∈ Subgroup.center ↥L ↔
      (QuotientGroup.mk' ((Zc L).subgroupOf Y))
        (Subgroup.inclusion hctx.2.2.1 l) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change l ∈ Subgroup.center ↥L ↔
      L.subtype l ∈ (Subgroup.center ↥L).map L.subtype
    rw [Subgroup.mem_map_iff_mem L.subtype_injective]
  have hrange : φ.range = (L.subgroupOf Y).map
      (QuotientGroup.mk' ((Zc L).subgroupOf Y)) := by
    change ((QuotientGroup.mk' ((Zc L).subgroupOf Y)).comp
      (Subgroup.inclusion hctx.2.2.1)).range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem w135c2_alphaCase_S (hctx : Is135Context Y L) [hN : ((Zc L).subgroupOf Y).Normal] {A : ℕ}
    (hA : AlphaCase (↥L ⧸ Subgroup.center ↥L) A) :
    AlphaCase ↥((L.subgroupOf Y).map (QuotientGroup.mk' ((Zc L).subgroupOf Y))) A := by
  obtain ⟨e⟩ := w135c2_S_equiv hctx
  unfold AlphaCase at hA ⊢
  rcases hA with ⟨⟨e6⟩, hAeq⟩ | ⟨hLM, hAeq⟩
  · exact Or.inl ⟨⟨e.symm.trans e6⟩, hAeq⟩
  · exact Or.inr ⟨LieModel.of_mulEquiv e hLM, hAeq⟩

theorem w135c2_lieModel_S (hctx : Is135Context Y L) [hN : ((Zc L).subgroupOf Y).Normal]
    {t : StatedLieTag} {n f : ℕ} (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) t n 2 f) :
    LieModel ↥((L.subgroupOf Y).map (QuotientGroup.mk' ((Zc L).subgroupOf Y))) t n 2 f := by
  obtain ⟨e⟩ := w135c2_S_equiv hctx
  exact LieModel.of_mulEquiv e hlie

end CFSG.LocalAnalysis.WeakClosure81
