module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralInvolutionHullRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralInvolutionHullLifting

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G Q : Type*} [Group G] [Group Q]

theorem subgroup_image_equiv_normalizer_comap (f : G →* Q) (U L : Subgroup G)
    (e : L ≃* L.map f) (he : ∀ a : L, (e a : Q) = f (a : G))
    (hpre : (Subgroup.normalizer (U.map f : Set Q)).comap f =
      Subgroup.normalizer (U : Set G)) :
    ((Subgroup.normalizer (U.map f : Set Q)).subgroupOf (L.map f)).comap e.toMonoidHom =
      (Subgroup.normalizer (U : Set G)).subgroupOf L := by
  ext a
  change (e a : Q) ∈ Subgroup.normalizer (U.map f : Set Q) ↔
    (a : G) ∈ Subgroup.normalizer (U : Set G)
  rw [he a]
  change (a : G) ∈ (Subgroup.normalizer (U.map f : Set Q)).comap f ↔
    (a : G) ∈ Subgroup.normalizer (U : Set G)
  rw [hpre]

variable [Finite G] [Finite Q]

theorem subgroup_image_equiv_strongEmbedding_transport (f : G →* Q) (U L : Subgroup G)
    (e : L ≃* L.map f) (he : ∀ a : L, (e a : Q) = f (a : G))
    (hpre : (Subgroup.normalizer (U.map f : Set Q)).comap f =
      Subgroup.normalizer (U : Set G))
    (hB : fusionStronglyEmbedded
      ((Subgroup.normalizer (U.map f : Set Q)).subgroupOf (L.map f))) :
    fusionStronglyEmbedded ((Subgroup.normalizer (U : Set G)).subgroupOf L) := by
  let B := (Subgroup.normalizer (U.map f : Set Q)).subgroupOf (L.map f)
  have hn : IsStronglyEmbedded B := native_strong_embedding_of_order_conditions hB
  have hproper : B.comap e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hn.ne_top
    apply top_unique
    intro a _
    have ha : e.symm a ∈ B.comap e.toMonoidHom := htop.symm ▸ Subgroup.mem_top _
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using ha
  have hinvolution : ∃ a : L, a ∈ B.comap e.toMonoidHom ∧ IsInvolution a := by
    obtain ⟨a, ha, hai⟩ := hn.exists_involution
    refine ⟨e.symm a, ?_, IsInvolution.map_of_injective hai e.symm.toMonoidHom e.symm.injective⟩
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using ha
  have hnative := hn.comap_of_injective e.toMonoidHom e.injective hproper hinvolution
  rw [subgroup_image_equiv_normalizer_comap f U L e he hpre] at hnative
  exact order_strong_embedding_of_native hnative

theorem central_involution_hull_embedding_transport (U : Subgroup G)
    (x : Subgroup.center G)
    (e : Subgroup.normalClosure (U : Set G) ≃*
      (Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' (centralLiftKernel x)))
    (he : ∀ a : Subgroup.normalClosure (U : Set G),
      (e a : G ⧸ centralLiftKernel x) = (QuotientGroup.mk' (centralLiftKernel x)) (a : G))
    (hpre : (Subgroup.normalizer
      (U.map (QuotientGroup.mk' (centralLiftKernel x)) : Set (G ⧸ centralLiftKernel x))).comap
      (QuotientGroup.mk' (centralLiftKernel x)) = Subgroup.normalizer (U : Set G))
    (hB : fusionStronglyEmbedded
      ((Subgroup.normalizer
        (U.map (QuotientGroup.mk' (centralLiftKernel x)) : Set (G ⧸ centralLiftKernel x))).subgroupOf
        (Subgroup.normalClosure
          (U.map (QuotientGroup.mk' (centralLiftKernel x)) : Set (G ⧸ centralLiftKernel x))))) :
    fusionStronglyEmbedded ((Subgroup.normalizer (U : Set G)).subgroupOf
      (Subgroup.normalClosure (U : Set G))) := by
  apply subgroup_image_equiv_strongEmbedding_transport
    (QuotientGroup.mk' (centralLiftKernel x)) U (Subgroup.normalClosure (U : Set G)) e he hpre
  rwa [Subgroup.map_normalClosure (U : Set G) (QuotientGroup.mk' (centralLiftKernel x))
    (QuotientGroup.mk'_surjective (centralLiftKernel x))]

theorem central_involution_ti_hull_embedding_of_quotient_embedding
    (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hcard : 4 ≤ Nat.card U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (x : Subgroup.center G) (horder : orderOf (x : G) = 2)
    (hB : fusionStronglyEmbedded
      ((Subgroup.normalizer
        (U.map (QuotientGroup.mk' (centralLiftKernel x)) : Set (G ⧸ centralLiftKernel x))).subgroupOf
        (Subgroup.normalClosure
          (U.map (QuotientGroup.mk' (centralLiftKernel x)) : Set (G ⧸ centralLiftKernel x))))) :
    fusionStronglyEmbedded ((Subgroup.normalizer (U : Set G)).subgroupOf
      (Subgroup.normalClosure (U : Set G))) := by
  obtain ⟨hquasi, _, _, hmodel⟩ := central_involution_quotient_hull_native_recognition
    T U hUT hU hUel hcard hclosed hTI hnormal x hB
  obtain ⟨_, _, _, _, e, he⟩ := central_involution_hull_lifting
    T U hUT hUel hcard hclosed hTI x horder hquasi hmodel
  exact central_involution_hull_embedding_transport U x e he
    (ti_central_quotient_normalizer_preimage T U hUT hU hUel hclosed hTI hnormal
      (centralLiftKernel x) (centralLiftKernel_le_center x)) hB

end CFSG.ShultStronglyClosedTI
