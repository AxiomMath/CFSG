module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamLift

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Sylow

variable {G : Type} [Group G]

theorem relIndex_map_dvd_of_le {H : Type*} [Group H] (f : G →* H) {A B : Subgroup G}
    (hAB : A ≤ B) : (A.map f).relIndex (B.map f) ∣ A.relIndex B := by
  have heq : (A.map f).subgroupOf (B.map f) = (A.subgroupOf B).map (f.subgroupMap B) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, hay⟩
      exact ⟨⟨a, hAB ha⟩, ha, Subtype.ext hay⟩
    · rintro ⟨b, hb, hby⟩
      exact ⟨b, hb, congrArg Subtype.val hby⟩
  rw [Subgroup.relIndex, heq]
  exact Subgroup.index_map_dvd _ (f.subgroupMap_surjective B)

theorem relIndex_imgJ_dvd {J X Y : Subgroup G} (hXY : X ≤ Y) (hYJ : Y ≤ J) :
    (imgJ J X).relIndex (imgJ J Y) ∣ X.relIndex Y := by
  have h1 := relIndex_map_dvd_of_le (projJ J)
    (A := X.subgroupOf J) (B := Y.subgroupOf J) fun x hx => hXY hx
  rwa [Subgroup.relIndex_subgroupOf hYJ] at h1

theorem isSylowTwoOf_imgJ {J X H : Subgroup G} (hHJ : H ≤ J) (hXH : IsSylowTwoOf X H) :
    IsSylowTwoOf (imgJ J X) (imgJ J H) := by
  have hXJ : X ≤ J := hXH.1.trans hHJ
  refine ⟨imgJ_mono hXH.1, ?_, fun hdvd => hXH.2.2 (hdvd.trans (relIndex_imgJ_dvd hXH.1 hHJ))⟩
  have h2 : IsPGroup 2 ↥(X.subgroupOf J) :=
    hXH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hXJ).symm
  exact h2.of_surjective ((projJ J).subgroupMap _) ((projJ J).subgroupMap_surjective _)

theorem imgJ_self (J : Subgroup G) : imgJ J J = ⊤ := by
  unfold imgJ
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact QuotientGroup.mk'_surjective _

end Sylow

section Config

variable {G : Type} [Group G] [Finite G] {J D K V T₁ T₂ : Subgroup G}

namespace A5Setup

variable (h : A5Setup J D K V T₁ T₂)
include h

omit [Finite G] in
theorem J_le_normalizer : J ⊔ D ≤ Subgroup.normalizer (J : Set G) :=
  sup_le Subgroup.le_normalizer fun _ hd =>
    Subgroup.centralizer_le_normalizer (J : Set G) (h.D_le hd)

omit [Finite G] in
theorem sup_inf_J : (K ⊔ T₁) ⊓ J = K ⊔ (T₁ ⊓ J) := by
  apply le_antisymm
  · rintro x ⟨hx, hxJ⟩
    obtain ⟨k, t, hk, ht, hkt⟩ := h.exists_mul_of_mem_sup (x := ⟨x, hxJ⟩) hx
    have hx' : x = (k : G) * (t : G) := congrArg Subtype.val hkt
    rw [hx']
    exact Subgroup.mul_mem_sup hk ⟨ht, t.2⟩
  · exact sup_le (le_inf le_sup_left h.K_le) (inf_le_inf_right J le_sup_right)

omit [Finite G] in
theorem imgJ_sup_eq : imgJ J K ⊔ imgJ J T₁ = imgJ J ((K ⊔ T₁) ⊓ J) := by
  rw [h.sup_inf_J, imgJ_sup h.K_le inf_le_right, imgJ_inf]

theorem sylow_img_one : IsSylowTwoOf (imgJ J T₁) (imgJ J K ⊔ imgJ J T₁) := by
  have hMJD : K ⊔ T₁ ≤ J ⊔ D := sup_le (h.K_le.trans le_sup_left) h.T₁_le
  have hnorm : (((K ⊔ T₁) ⊓ J).subgroupOf (K ⊔ T₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun m hm =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hm, h.J_le_normalizer (hMJD hm)⟩
  have hsyl := RankOneRecog.isSylowTwoOf_inf_of_subnormal h.sylow₁ inf_le_left hnorm.isSubnormal
  have heq : T₁ ⊓ ((K ⊔ T₁) ⊓ J) = T₁ ⊓ J := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, Subgroup.mem_sup_right hx.1, hx.2⟩⟩
  rw [heq] at hsyl
  have := isSylowTwoOf_imgJ inf_le_right hsyl
  rwa [imgJ_inf, ← h.imgJ_sup_eq] at this

theorem sylow_img_two : IsSylowTwoOf (imgJ J T₂) ⊤ := by
  have hJn : (J.subgroupOf (J ⊔ D)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 h.J_le_normalizer
  have hsyl := RankOneRecog.isSylowTwoOf_inf_of_subnormal h.sylow₂ le_sup_left hJn.isSubnormal
  have := isSylowTwoOf_imgJ le_rfl hsyl
  rwa [imgJ_inf, imgJ_self] at this

theorem relIndex_img : (imgJ J T₁).relIndex (imgJ J T₂) ≤ 2 := by
  have h1 : (imgJ J T₁).relIndex (imgJ J T₂) ∣ (T₁ ⊓ J).relIndex (T₂ ⊓ J) := by
    rw [← imgJ_inf (X := T₁), ← imgJ_inf (X := T₂)]
    exact relIndex_imgJ_dvd (inf_le_inf_right J h.T₁_le_T₂) inf_le_right
  have h2 : (T₁ ⊓ J).relIndex (T₂ ⊓ J) ≤ T₁.relIndex T₂ := by
    have : T₁ ⊓ J = T₁ ⊓ (T₂ ⊓ J) := by
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun hx => ⟨hx.1, h.T₁_le_T₂ hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
    rw [this, Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_le_of_le_right inf_le_left
      (Subgroup.index_ne_zero_of_finite (H := T₁.subgroupOf T₂))
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
    (H := (T₁ ⊓ J).subgroupOf (T₂ ⊓ J)))) h1).trans (h2.trans h.relIndex_le)

end A5Setup

end Config

end CFSG.Quasithin.H13.CTK
