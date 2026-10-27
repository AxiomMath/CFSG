module

public import CFSG.Blueprint.Catalog
public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Components

variable {G : Type*} [Group G]

theorem ggIsSubnormal_subgroupOf (H : Subgroup G) {K X : Subgroup G} (h : IsSubnormal K X) :
    IsSubnormal (K.subgroupOf H) (X.subgroupOf H) := by
  induction h with
  | refl H => exact IsSubnormal.refl _
  | step hKM hNorm hMX ih =>
      refine IsSubnormal.step (Subgroup.subgroupOf_mono H hKM) ?_ ih
      rw [Subgroup.normal_subgroupOf_iff hKM] at hNorm
      rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono H hKM)]
      intro a b ha hb
      rw [Subgroup.mem_subgroupOf] at ha hb ⊢
      exact hNorm a b ha hb

theorem ggIsQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsQuasisimple A) : IsQuasisimple B := by
  have hrange : (e : A →* B).range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have hmap : (commutator A).map (e : A →* B) = commutator B := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, hrange, commutator_def]
  refine ⟨?_, ?_⟩
  · rw [← hmap, h.1, Subgroup.map_top]
    exact hrange
  · have hcenter : (Subgroup.center A).map (e : A →* B) = Subgroup.center B :=
      Subgroup.map_center_eq e
    have e' : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
      QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hcenter
    exact (MulEquiv.isSimpleGroup_congr e').mp h.2

theorem ggIsQuasisimple_subgroupOf {H K : Subgroup G} (hKH : K ≤ H) (h : IsQuasisimple ↥K) :
    IsQuasisimple ↥(K.subgroupOf H) :=
  ggIsQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm h

theorem ggIsComponentOf_subgroupOf_of_le (H : Subgroup G) {K C : Subgroup G} (hKH : K ≤ H)
    (h : IsComponentOf K C) : IsComponentOf (K.subgroupOf H) (C.subgroupOf H) :=
  ⟨Subgroup.subgroupOf_mono H h.1, ggIsSubnormal_subgroupOf H h.2.1,
    ggIsQuasisimple_subgroupOf hKH h.2.2⟩

end Components

section Models

theorem ggLieModel_centerQuot_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel (B ⧸ Subgroup.center B) t n p f) :
    CFSG.Blueprint.LieModel (A ⧸ Subgroup.center A) t n p f := by
  have hcenter : (Subgroup.center A).map (e : A →* B) = Subgroup.center B :=
    Subgroup.map_center_eq e
  have e' : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
    QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hcenter
  exact CFSG.Blueprint.LieModel.of_mulEquiv e'.symm h

theorem ggLieModel_E6_n_eq_zero {X : Type} [Group X] {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel X .E6 n p f) : n = 0 := by
  rcases h with ⟨ht, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · exact absurd ht (by decide)
  · exact hn
  · exact hn
  · exact hn

end Models

end CFSG.StandardType
