module

public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.E2TwoProofY

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2P

theorem subgroupOf_map_subtype_eq {Γ : Type} [Group Γ] {H : Subgroup Γ} (K₀ : Subgroup ↥H) :
    (K₀.map H.subtype).subgroupOf H = K₀ :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective K₀

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M : Subgroup Γ}

theorem exists_cComp_star (h : MinParabolic H T M) {L : Subgroup (E2.StarQuot M H)}
    (hL : L ∈ cComp (⊤ : Subgroup (E2.StarQuot M H))) :
    ∃ K : Subgroup Γ, K ∈ cComp H ∧ K ≤ H ∧ E2.star M H K = L := by
  obtain ⟨K₀, hK₀, hK₀L⟩ := map_surjOn_cComp_top (starMap M H) (starMap_surjective M H)
    (isSolvable_ker_starMap h) hL
  refine ⟨K₀.map H.subtype, map_subtype_mem_cComp hK₀, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [star_def, subgroupOf_map_subtype_eq]
    exact hK₀L

theorem sup_eq_of_star (h : MinParabolic H T M) {K : Subgroup Γ} (hKH : K ≤ H)
    (hsup : E2.star M H K ⊔ E2.star M H T = ⊤) : H = K ⊔ T := by
  have hmp := h.subgroupOf
  set K₀ := K.subgroupOf H
  set T₀ := T.subgroupOf H
  have hmap : (K₀ ⊔ T₀).map (starMap M H) = ⊤ := by
    rw [Subgroup.map_sup]
    exact hsup
  have hK₀T₀ : K₀ ⊔ T₀ = ⊤ := by
    by_contra hne
    have hlt : K₀ ⊔ T₀ < ⊤ := lt_top_iff_ne_top.mpr hne
    have hle : K₀ ⊔ T₀ ≤ M.subgroupOf H := hmp.le_of_lt le_sup_right hlt
    have h1 : (K₀ ⊔ T₀) ⊔ (starMap M H).ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h2 : (⊤ : Subgroup ↥H) ≤ M.subgroupOf H := by
      rw [← h1]
      exact sup_le hle (ker_starMap_le_subgroupOf M H)
    exact hmp.maximal.1.ne (top_le_iff.mp h2)
  have := congrArg (Subgroup.map H.subtype) hK₀T₀
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKH,
    Subgroup.map_subgroupOf_eq_of_le h.isSylow.1, Subgroup.map_top, Subgroup.range_subtype] at this
  exact this.symm

end E2P

end CFSG.Quasithin
