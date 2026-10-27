module

public import CFSG.RankThree.PartTwo.Sec21.FF81HL32Core
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Subgroup

theorem isLnq_of_mulEquiv_gl_three_two {G : Type} [Group G] {K : Subgroup G}
    (e : K ≃* GL (Fin 3) (ZMod 2)) : IsLnq 3 2 1 K :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two le_rfl
    (e.trans (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr
      (CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two (K := ZMod 2) (by simp) 3).symm)))

@[expose] def KF_L32Recognition : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (b t : X), orderOf b = 3 → Cen b = Subgroup.zpowers b →
    orderOf t = 2 → t * b * t⁻¹ = b⁻¹ → Nonempty (Cen t ≃* DihedralGroup 4) →
    IsLnq 3 2 1 (⊤ : Subgroup X)

section Certificates


theorem kf_l32Recognition : KF_L32Recognition := by
  intro X _ _ b t hb hC ht hinv ⟨e⟩
  obtain ⟨g⟩ := FF81H.nonempty_equiv_gl_three_two hb hC ht hinv e
  exact isLnq_of_mulEquiv_gl_three_two (Subgroup.topEquiv.trans g)

end Certificates

theorem isLnq_of_l32_data (hL : KF_L32Recognition) {G : Type} [Group G] [Finite G]
    (Y : Subgroup G) {b t : G} (hbY : b ∈ Y) (htY : t ∈ Y) (hb : orderOf b = 3)
    (hCb : Cen b ⊓ Y = Subgroup.zpowers b) (ht : orderOf t = 2) (hinv : t * b * t⁻¹ = b⁻¹)
    (hV : Nonempty (↥(Cen t ⊓ Y) ≃* DihedralGroup 4)) : IsLnq 3 2 1 Y := by
  obtain ⟨eV⟩ := hV
  let b' : Y := ⟨b, hbY⟩
  let t' : Y := ⟨t, htY⟩
  have hb' : orderOf b' = 3 := by rw [Subgroup.orderOf_mk]; exact hb
  have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hC' : Cen b' = Subgroup.zpowers b' := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_zpowers_iff]
    constructor
    · intro hx
      have hxc : (x : G) ∈ Cen b ⊓ Y :=
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hx), x.2⟩
      rw [hCb] at hxc
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxc
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, rfl⟩
      exact ((Commute.refl b').zpow_left k).eq
  have hinv' : t' * b' * t'⁻¹ = b'⁻¹ := Subtype.ext (by simpa using hinv)
  have hCen : Cen t' = (Cen t ⊓ Y).subgroupOf Y := by
    ext x
    simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    constructor
    · intro hx
      exact ⟨congrArg Subtype.val hx, x.2⟩
    · rintro ⟨hx, -⟩
      exact Subtype.ext hx
  let e' : Cen t' ≃* DihedralGroup 4 :=
    ((MulEquiv.subgroupCongr hCen).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)).trans eV
  have h := hL Y b' t' hb' hC' ht' hinv' ⟨e'⟩
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv Subgroup.topEquiv h

end CFSG.RankThree.PartTwo.Sec21.FF81
