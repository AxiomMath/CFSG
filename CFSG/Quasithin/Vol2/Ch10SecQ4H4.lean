module

public import CFSG.Quasithin.Vol2.Ch10SecQ4H3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.G64Statement

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] {H V : Subgroup G} {t v : G}
  (hUe : IsElemAbelian 2 (conjClosure (Subgroup.zpowers v) H))

theorem commV_zpowers_transvI (hR : IsTwoReducedIn H V) (htH : t ∈ H) (hv : v ∈ V)
    (hv1 : v ≠ 1) (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v)
    (htC : t ∉ Subgroup.centralizer (V : Set G)) :
    commV (Subgroup.zpowers (transvI hUe htH)) = Subgroup.zpowers (centreI hUe) := by
  have hHV := hR.2.1
  have ha2 := transvI_sq hUe hHV hv hv1 htr htH
  apply le_antisymm
  · rw [commV, Subgroup.closure_le]
    rintro w ⟨x, hx, u, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases zpow_eq_one_or_eq ha2 k with h | h
    · rw [h, MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h]
      rcases transvI_apply hUe hHV hv htr htH u with h' | h'
      · rw [h', mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [h', mul_comm u, mul_assoc, mul_inv_cancel, mul_one]
        exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    obtain ⟨u, hu⟩ : ∃ u, transvI hUe htH u ≠ u := by
      by_contra hall
      push Not at hall
      exact transvI_ne_one hUe hR htH hv htr htC (MulEquiv.ext hall)
    have h' := (transvI_apply hUe hHV hv htr htH u).resolve_left hu
    refine Subgroup.subset_closure ⟨transvI hUe htH, Subgroup.mem_zpowers _, u, ?_⟩
    rw [h', mul_comm u, mul_assoc, mul_inv_cancel, mul_one]

theorem card_commV_transvI (hR : IsTwoReducedIn H V) (htH : t ∈ H) (hv : v ∈ V)
    (hv1 : v ≠ 1) (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v)
    (htC : t ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card ↥(commV (Subgroup.zpowers (transvI hUe htH))) = 2 := by
  rw [commV_zpowers_transvI hUe hR htH hv hv1 htr htC, Nat.card_zpowers]
  exact orderOf_eq_prime (IntMod.sq_eq_one _) (centreI_ne_one hUe hv1)

theorem iSup_map_commV_transvI (hR : IsTwoReducedIn H V) (htH : t ∈ H) (hv : v ∈ V)
    (hv1 : v ≠ 1) (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v)
    (htC : t ∉ Subgroup.centralizer (V : Set G)) :
    (⨆ (g : MulAut (IntMod (conjClosure (Subgroup.zpowers v) H) hUe)) (_ : g ∈ autI hUe H),
      (commV (Subgroup.zpowers (transvI hUe htH))).map g.toMonoidHom) = ⊤ := by
  rw [commV_zpowers_transvI hUe hR htH hv hv1 htr htC]
  set S := ⨆ (g : MulAut (IntMod (conjClosure (Subgroup.zpowers v) H) hUe))
    (_ : g ∈ autI hUe H), (Subgroup.zpowers (centreI hUe)).map g.toMonoidHom with hS
  have hHU : H ≤ Subgroup.normalizer (conjClosure (Subgroup.zpowers v) H : Set G) :=
    le_normalizer_conjClosure _ H
  have key : ∀ (x : G) (hx : x ∈ conjClosure (Subgroup.zpowers v) H),
      IntMod.mk hUe ⟨x, hx⟩ ∈ S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine Subgroup.mem_iSup_of_mem (convI hUe ⟨h, hHU hh⟩)
        (Subgroup.mem_iSup_of_mem (convI_mem_autI hUe hh _) ?_)
      refine ⟨centreI hUe ^ k, Subgroup.zpow_mem_zpowers _ _, ?_⟩
      apply IntMod.val_injective
      show (convI hUe ⟨h, hHU hh⟩ (centreI hUe ^ k)).val = h * v ^ k * h⁻¹
      rw [convI_apply_val]
      rfl
    | one => exact S.one_mem
    | mul x y _ _ ihx ihy => exact S.mul_mem ihx ihy
    | inv x _ ih => exact S.inv_mem ih
  rw [eq_top_iff]
  intro w _
  exact key w.val w.val_mem

theorem pCoreOf_autI_conjClosure (hR : IsTwoReducedIn H V) (htH : t ∈ H) (hv : v ∈ V)
    (hv1 : v ≠ 1) (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v)
    (htC : t ∉ Subgroup.centralizer (V : Set G)) : pCoreOf 2 (autI hUe H) = ⊥ :=
  Setup.pCoreOf_autOn_eq_bot (isTwoReducedIn_conjClosure hR htH hv hv1 htr htC)

theorem isQuotientOfSQTKCat_autI [Finite G] (hsq : CFSG.SectionRank.IsSQTKCat ↥H) :
    G64.IsQuotientOfSQTKCat ↥(autI hUe H) := by
  set ρ := convHom hUe H (le_normalizer_conjClosure _ H) with hρ
  refine ⟨↥H, inferInstance, inferInstance, ρ.ker, inferInstance, hsq, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr (range_convHom hUe H _)).symm.trans
    (QuotientGroup.quotientKerEquivRange ρ).symm

theorem hyp61_autI [Finite G] (hsq : CFSG.SectionRank.IsSQTKCat ↥H) (hR : IsTwoReducedIn H V)
    (htH : t ∈ H) (hv : v ∈ V) (hv1 : v ≠ 1)
    (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v)
    (htC : t ∉ Subgroup.centralizer (V : Set G)) :
    G64.Hyp61 (autI hUe H) (transvI hUe htH) where
  pCore_eq_bot := pCoreOf_autI_conjClosure hUe hR htH hv hv1 htr htC
  quotient_sqtk := isQuotientOfSQTKCat_autI hUe hsq
  mem := transvI_mem hUe htH
  ne_one := transvI_ne_one hUe hR htH hv htr htC
  sq_eq_one := transvI_sq hUe hR.2.1 hv hv1 htr htH
  card_comm_le := by
    rw [card_commV_transvI hUe hR htH hv hv1 htr htC]
    norm_num
  span := iSup_map_commV_transvI hUe hR htH hv hv1 htr htC

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
