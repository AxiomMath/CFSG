module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2G1Def

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem card_img_eq_two (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (hn : E3.mQuot V (U ⊔ V₀) = 1) : Nat.card ↥(Mo.img V) = 2 := by
  have h := c.card_img_conjSubgroup h1 h5 h15 hS Mo (x := 1) H.one_mem
  rw [conjSubgroup_one, hn] at h
  simpa using h

theorem img_eq_zpowers (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (hn : E3.mQuot V (U ⊔ V₀) = 1) {t : LGL 2 Mo.W} (ht : t ∈ Mo.img V) (ht1 : t ≠ 1) :
    Mo.img V = Subgroup.zpowers t := by
  have h2 := card_img_eq_two h1 h5 h15 hS c Mo hn
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ht) ?_).symm
  rw [h2, Nat.card_zpowers]
  have h3 : orderOf t ≠ 1 := fun h => ht1 (orderOf_eq_one_iff.1 h)
  have h4 : 0 < orderOf t := orderOf_pos t
  omega

theorem img_commute_of_mem_inf (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    {r t : LGL 2 Mo.W} (hr : r ∈ Mo.img (H ⊓ M)) (ht : t ∈ Mo.img V) : r * t = t * r := by
  by_cases ht1 : t = 1
  · rw [ht1, mul_one, one_mul]
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hN : H ⊓ M ≤ normalizer (V : Set G) := by
    rw [c.cex.hyp.h6.normalizer_eq]
    exact inf_le_right
  have hmem : r ∈ normalizer (Mo.img V : Set (LGL 2 Mo.W)) :=
    Mo.img_le_normalizer inf_le_left hVH hN hr
  have hrt : r * t * r⁻¹ ∈ Mo.img V :=
    (Subgroup.mem_set_normalizer_iff.1 hmem t).1 ht
  have hcard : Nat.card ↥(Mo.img V) = 2 := card_img_eq_two h1 h5 h15 hS c Mo hn
  have hrt1 : r * t * r⁻¹ ≠ 1 := by
    intro h
    exact ht1 (by
      have := congrArg (fun z => r⁻¹ * z * r) h
      simpa [mul_assoc] using this)
  have hst : r * t * r⁻¹ = t :=
    CFSG.ShultStronglyClosedTI.eq_of_ne_one_of_card_two (Mo.img V) hcard ht ht1 hrt hrt1
  calc r * t = (r * t * r⁻¹) * r := by group
    _ = t * r := by rw [hst]

theorem mem_normalizer_sup_of_mem_inf (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {x : G} (hx : x ∈ H ⊓ M) :
    x ∈ normalizer ((U ⊔ V₀ : Subgroup G) : Set G) := by
  have hxV : x ∈ normalizer (V : Set G) := by
    rw [c.cex.hyp.h6.normalizer_eq]
    exact hx.2
  have hxI : x ∈ normalizer (conjClosure (U ⊔ V₀) H : Set G) :=
    le_normalizer_conjClosure (U ⊔ V₀) H hx.1
  have hVI : V ⊓ conjClosure (U ⊔ V₀) H = U ⊔ V₀ :=
    c.cex.inf_conjClosure_eq_sup h1 h5 h15 hS c.mem
  have hnorm : x ∈ normalizer ((V ⊓ conjClosure (U ⊔ V₀) H : Subgroup G) : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    change y ∈ V ⊓ conjClosure (U ⊔ V₀) H ↔
      x * y * x⁻¹ ∈ V ⊓ conjClosure (U ⊔ V₀) H
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_set_normalizer_iff.1 hxV y)
      (Subgroup.mem_set_normalizer_iff.1 hxI y)
  rwa [hVI] at hnorm

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
