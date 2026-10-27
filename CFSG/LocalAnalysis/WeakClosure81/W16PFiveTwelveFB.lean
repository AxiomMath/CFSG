module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveS
public import CFSG.LocalAnalysis.WeakClosure81.W15SixG
public import CFSG.LocalAnalysis.WeakClosure81.TwelveFour
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveEleven
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenF
import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped CFSG.Goldschmidt.G2

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.inCalAMod_kerQuotImg [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h1 : W16One G)
    (hS : Std15 G) (hV₀ : V₀ ≤ pCoreOf 2 H) (hX : Hyp167 M V₀ V U S H g X T)
    (hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T = ⊥)
    {ρ : KerQuot M X →* LGL 2 (Additive ↥(eSub V₀ X T))}
    (hρ : ∀ x : ↥X, ρ (kerQuotMk M X x) = eRep V₀ X T x) :
    InCalAMod ρ (Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
      (mBar M V₀ V hX.cex.hyp.h6.elemAbelian)) (kerQuotImg M X (conjSubgroup V g)) := by
  have hA : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hA_le_X : conjSubgroup V g ≤ X := hX.mem.2.2.A_le
  refine ⟨?_, isElemAbelian_kerQuotImg hA, ?_⟩
  · intro hbot
    exact hX.mem.2.2.not_le_ker ((kerQuotImg_eq_bot_iff hA_le_X).1 hbot)
  · intro D hD hDrel
    refine le_antisymm (fixSub_anti _ _ (Subgroup.map_mono hD)) ?_
    let P : Subgroup G := (D.comap (kerQuotMk M X)).map X.subtype
    let Dt : Subgroup G := P ⊓ conjSubgroup V g
    have hDt_le_A : Dt ≤ conjSubgroup V g := inf_le_right
    have hsub : P.subgroupOf X = D.comap (kerQuotMk M X) := by
      change ((D.comap (kerQuotMk M X)).map X.subtype).subgroupOf X =
        D.comap (kerQuotMk M X)
      exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    have hrel : Dt.relIndex (conjSubgroup V g) =
        D.relIndex (kerQuotImg M X (conjSubgroup V g)) := by
      have h1 : Dt.relIndex (conjSubgroup V g) = P.relIndex (conjSubgroup V g) :=
        Subgroup.inf_relIndex_right P (conjSubgroup V g)
      rw [h1, ← Subgroup.relIndex_subgroupOf hA_le_X, hsub, Subgroup.relIndex_comap]
      rfl
    have hm : E3.mQuot (conjSubgroup V g) Dt <
        Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
          (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) := by
      have hpow : 2 ^ E3.mQuot (conjSubgroup V g) Dt <
          2 ^ Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
            (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) := by
        rw [← E3.relIndex_eq_two_pow hA.isPGroup Dt, hrel]
        exact hDrel
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hpow
    have hcent := Hyp167.inf_centralizer_le_of_inf_eq_bot h1 hS hV₀ hX hBE
      (D := Dt) hDt_le_A hm
    intro w hw
    rw [mem_fixSub] at hw ⊢
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 ha
    change q ∈ ((conjSubgroup V g).subgroupOf X).map (kerQuotMk M X) at hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hq
    rw [hρ y]
    apply Additive.ext
    apply Subtype.ext
    rw [eRep_apply V₀ X T y w]
    have hyA : (y : G) ∈ conjSubgroup V g := Subgroup.mem_subgroupOf.1 hy
    have hcentz : ((Additive.toMul w : ↥(eSub V₀ X T)) : G) ∈
        Subgroup.centralizer (Dt : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      change d ∈ P ⊓ conjSubgroup V g at hd
      have hdP : d ∈ P := (Subgroup.mem_inf.1 hd).1
      change d ∈ (D.comap (kerQuotMk M X)).map X.subtype at hdP
      obtain ⟨u, hu, hdu⟩ := Subgroup.mem_map.1 hdP
      have hfu : kerQuotMk M X u ∈ D := hu
      have hw' : ρ (kerQuotMk M X u) w = w :=
        hw _ (Subgroup.mem_map_of_mem ρ hfu)
      have h1 : Additive.toMul (eRep V₀ X T u w) = Additive.toMul w := by
        rw [← hρ u]
        exact congrArg Additive.toMul hw'
      have hconj : (u : G) * ((Additive.toMul w : ↥(eSub V₀ X T)) : G) * (u : G)⁻¹ =
          ((Additive.toMul w : ↥(eSub V₀ X T)) : G) := by
        rw [← eRep_apply V₀ X T u w, h1]
      have hcomm : (u : G) * ((Additive.toMul w : ↥(eSub V₀ X T)) : G) =
          ((Additive.toMul w : ↥(eSub V₀ X T)) : G) * (u : G) :=
        (mul_inv_eq_iff_eq_mul).1 hconj
      rw [← hdu]
      exact hcomm
    have hz_cent : ((Additive.toMul w : ↥(eSub V₀ X T)) : G) ∈
        Subgroup.centralizer (conjSubgroup V g : Set G) :=
      hcent ⟨(Additive.toMul w).2, hcentz⟩
    have hyz : (y : G) * ((Additive.toMul w : ↥(eSub V₀ X T)) : G) =
        ((Additive.toMul w : ↥(eSub V₀ X T)) : G) * (y : G) :=
      (Subgroup.mem_centralizer_iff.1 hz_cent) (y : G) hyA
    rw [hyz]
    group

end CFSG.LocalAnalysis.WeakClosure81

end
