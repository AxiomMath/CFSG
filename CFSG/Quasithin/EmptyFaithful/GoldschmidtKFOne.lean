module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFHyp

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
  {X : Subgroup G} {τ f : G}

theorem KFHyp.solvable_centralizer_I_sigma (h113 : StageLemma14113)
    (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) :
    Group.IsSolvable ↥(I ⊓ Subgroup.centralizer ({τ * f} : Set G)) := by
  classical
  obtain ⟨F, -, -, -, -, -, hsolvC⟩ := h.sigma_structure h113
  have hLI : L ≤ I := h.L_le_I
  have hnorm : (L.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLI).mpr h.r.hNL
  let θ : ↥(I ⊓ Subgroup.centralizer ({τ * f} : Set G)) →* ↥I ⧸ L.subgroupOf I :=
    (QuotientGroup.mk' (L.subgroupOf I)).comp (Subgroup.inclusion inf_le_left)
  have hcard : Nat.card (↥I ⧸ L.subgroupOf I) = 12 := by
    have : Nat.card (↥I ⧸ L.subgroupOf I) = L.relIndex I := rfl
    rw [this]
    exact h.hidx
  have hsolvQ : Group.IsSolvable (↥I ⧸ L.subgroupOf I) := isSolvable_of_card_eq_twelve hcard
  let ι : ↥(L ⊓ Subgroup.centralizer ({τ * f} : Set G)) →*
      ↥(I ⊓ Subgroup.centralizer ({τ * f} : Set G)) := Subgroup.inclusion (inf_le_inf_right _ hLI)
  refine Group.isSolvable_of_ker_le_range ι θ ?_
  intro x hx
  have hx' : (Subgroup.inclusion (inf_le_left : I ⊓ Subgroup.centralizer ({τ * f} : Set G) ≤ I)
      x : ↥I) ∈ L.subgroupOf I := by
    have := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    exact this
  have hxL : (x : G) ∈ L := hx'
  exact ⟨⟨(x : G), hxL, x.2.2⟩, Subtype.ext rfl⟩

theorem KFHyp.solvable_centralizer_pair (h113 : StageLemma14113)
    (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) {v : G} (hv : v ∈ V₁) (hv1 : v ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({v, τ * f} : Set G)) := by
  have hsolv := h.solvable_centralizer_I_sigma h113
  have hle : Subgroup.centralizer ({v, τ * f} : Set G) ≤
      I ⊓ Subgroup.centralizer ({τ * f} : Set G) := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨h.hCv v hv hv1 ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hg _ (Set.mem_insert _ _)
    · rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hg _ (Set.mem_insert_of_mem _ rfl)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end CFSG.Quasithin.SBd19F
