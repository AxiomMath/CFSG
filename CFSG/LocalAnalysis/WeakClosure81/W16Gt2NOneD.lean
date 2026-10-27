module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem conjClosure_le_sup_of_img_eq (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (h : Mo.img (conjClosure V H) = Mo.img (V ⊔ conjSubgroup V g)) :
    conjClosure V H ≤ (V ⊔ conjSubgroup V g) ⊔
      (conjClosure V H ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))) := by
  set K : Subgroup G := conjClosure V H with hK
  set L : Subgroup G := V ⊔ conjSubgroup V g with hL
  set CH : Subgroup G := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) with hCH
  have hKH : K ≤ H := by rw [hK]; exact c.conjClosure_le_H
  have hLK : L ≤ K := by rw [hL, hK]; exact c.L_le_conjClosure
  have hLH : L ≤ H := hLK.trans hKH
  have himg : Mo.img K ≤ Mo.img L := by simpa [hK, hL] using h.le
  have hK_le : K ≤ L ⊔ CH := by
    rw [hCH]
    exact (Mo.img_le_img_iff (S := K) (T := L) hKH hLH).1 himg
  have hCHnormH : H ≤ Subgroup.normalizer (CH : Set G) := by
    intro x hx
    rw [hCH]
    exact mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer hx)
      (le_normalizer_conjClosure (U ⊔ V₀) H hx)
  have hLN : L ≤ Subgroup.normalizer (CH : Set G) := hLH.trans hCHnormH
  intro k hk
  have hk' : k ∈ (↑(L ⊔ CH) : Set G) := hK_le hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L CH hLN, Set.mem_mul] at hk'
  obtain ⟨l, hl, z, hz, hlk⟩ := hk'
  have hzK : z ∈ K := by
    have h1 : l⁻¹ * k ∈ K := K.mul_mem (K.inv_mem (hLK hl)) hk
    have h2 : l⁻¹ * k = z := by rw [← hlk]; group
    rwa [h2] at h1
  rw [← hlk]
  exact Subgroup.mul_mem_sup hl ⟨hzK, hz⟩

section Certified


theorem false_of_mQuot_eq_one (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    (hμ : 2 < mBar M V₀ V c.cex.hyp.h6.elemAbelian) : False := by
  obtain ⟨Mo⟩ := exists_modDataE (Fam16Q.isElemAbelian c.cex c.mem)
    (le_normalizer_conjClosure (U ⊔ V₀) H)
  exact c.not_le_sup_inf_centralizer
    (c.conjClosure_le_sup_of_img_eq Mo (c.img_conjClosure_eq_img_L h1 h5 h15 hS Mo hn hμ))

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
