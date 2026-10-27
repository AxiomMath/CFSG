module

public import CFSG.Quasithin.EmptyFaithful.A38c8J4
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem equiv_J4_of_isSylowIn
    {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (h : IsSporadic .J4 ↥(CFSG.generalizedFitting G)) :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) := by
  have hL : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  have hTs : IsSylowTwoOf T ⊤ := ⟨hT.1, hT.2.1, hT.2.2⟩
  have hTL : T ≤ CFSG.generalizedFitting G := by
    intro t ht
    obtain ⟨x, hx, hconj⟩ := A38c8.exists_mem_inf_inner_of_odd_outer hL hTs
      (A38c8.center_eq_bot_of_isSporadic_j4 h) (A38c8.odd_card_outer_of_isSporadic_j4 h) t ht
    have hxL : x ∈ CFSG.generalizedFitting G := (Subgroup.mem_inf.1 hx).2
    have hc : x⁻¹ * t ∈ Subgroup.centralizer (CFSG.generalizedFitting G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hconj y hy
      calc y * (x⁻¹ * t) = x⁻¹ * (x * y * x⁻¹) * t := by group
        _ = x⁻¹ * (t * y * t⁻¹) * t := by rw [h1]
        _ = x⁻¹ * t * y := by group
    have hxt : x⁻¹ * t ∈ CFSG.generalizedFitting G := CFSG.centralizer_generalizedFitting_le G hc
    have := Subgroup.mul_mem _ hxL hxt
    simpa using this
  have htop : CFSG.generalizedFitting G = ⊤ := by
    rwa [sup_eq_left.mpr hTL] at hFT
  obtain ⟨e⟩ := h
  exact ⟨((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩

end CFSG.Quasithin.RonanE114
