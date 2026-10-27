module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47K1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ne47A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1ChoiceDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_conj_cent_uOne (D : Data G) {V₀ : Subgroup G} (V : Subgroup G) {z : G}
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hC : V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) ≤
      pCoreOf 2 (centralizer ({z} : Set G)))
    {h : G} (hh : h ∈ centralizer ({z} : Set G)) {y : G}
    (hy : y ∈ conjSubgroup
      (V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) h) :
    y ∈ D.M ∧ ∀ u ∈ uOne V z, y * u * y⁻¹ = u := by
  set c : G := h * y * h⁻¹ with hc_def
  have hc_mem : c ∈ V₀ ⊓ centralizer
      ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := mem_conjSubgroup_iff.mp hy
  have hcCent : c ∈ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    hc_mem.2
  have hQh : conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) h =
      pCoreOf 2 (centralizer ({z} : Set G)) := s16c1_conjSubgroup_pCoreOf_self _ hh
  have hQh_inv : conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) h⁻¹ =
      pCoreOf 2 (centralizer ({z} : Set G)) :=
    s16c1_conjSubgroup_pCoreOf_self _ (Subgroup.inv_mem _ hh)
  have hQM : pCoreOf 2 (centralizer ({z} : Set G)) ≤ D.M := s16c1_pCoreOf_le_M D hSyl
  have hQS : pCoreOf 2 (centralizer ({z} : Set G)) ≤ D.T ⊓ centralizer ({z} : Set G) :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hSyl
  have hyQ : y ∈ pCoreOf 2 (centralizer ({z} : Set G)) :=
    hQh ▸ E3.conjSubgroup_mono_left h hC hy
  have hy_eq : y = h⁻¹ * c * h := by rw [hc_def]; group
  refine ⟨hQM hyQ, fun u hu => ?_⟩
  have huQ : u ∈ pCoreOf 2 (centralizer ({z} : Set G)) := hu.2
  have hhuQ : h * u * h⁻¹ ∈ pCoreOf 2 (centralizer ({z} : Set G)) := by
    rw [← hQh_inv]
    refine mem_conjSubgroup_iff.mpr ?_
    rw [show h⁻¹ * (h * u * h⁻¹) * h⁻¹⁻¹ = u by group]
    exact huQ
  have hcomm : (h * u * h⁻¹) * c = c * (h * u * h⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hcCent) _ (hQS hhuQ)
  have hc_conj : c * (h * u * h⁻¹) * c⁻¹ = h * u * h⁻¹ := by
    rw [← hcomm]; group
  calc y * u * y⁻¹ = h⁻¹ * c * h * u * (h⁻¹ * c * h)⁻¹ := by rw [hy_eq]
    _ = h⁻¹ * (c * (h * u * h⁻¹) * c⁻¹) * h := by group
    _ = h⁻¹ * (h * u * h⁻¹) * h := by rw [hc_conj]
    _ = u := by group

theorem r16_47_ne_two_holds (D : Data G) (hkit : OmegaKit) (hkitB : OmegaKitB)
    (hkitC : OmegaKitC) (h41 : R16_41 D) (h45b : R16_45b D) : R16_47_ne_two D := by
  intro V₀ V L hV hS hc _ _ _ x hx hSyl h47 _ hC h hh _ _ y hy
  have ctx : G47Ctx D V₀ V L hV x := G47Ctx.of_l45b h45b hS hc hx
  have hcard := s16c1_card_V_eq_two_mul_uOne hV x.val_mem h47
  obtain ⟨hyM, hU1⟩ := s16c1_conj_cent_uOne D V hSyl hC hh hy
  exact s16c1_cTilde_of_cent_uOne D hkit hkitB hkitC h41 ctx hcard hyM hU1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
