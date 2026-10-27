module

public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2_component_jointCentralizer {G : Type} [Group G] (H L J D : Subgroup G)
    (x : G) (hx : x ∈ D)
    (hL : IsComponentOf L (H ⊓ Subgroup.centralizer ({x} : Set G)))
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    IsComponentOf J (H ⊓ Subgroup.centralizer (D : Set G)) := by
  have hCD : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hx)
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer (D : Set G))
      (H ⊓ Subgroup.centralizer (D : Set G)) := by
    have h := hL.2.1.inf (Subgroup.centralizer (D : Set G))
    rwa [inf_assoc, inf_eq_right.2 hCD] at h
  have hJle : J ≤ H ⊓ Subgroup.centralizer (D : Set G) :=
    le_inf (hJ.1.trans (le_trans inf_le_left (le_trans hL.1 inf_le_left)))
      (hJ.1.trans inf_le_right)
  exact ⟨hJle, hJ.2.1.trans hsub, hJ.2.2⟩

theorem ggQ2_bstar_centralizer_nbr_eq_zpowers (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  have hK1 : GGQTwoK1 p B Bs x D J := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  refine le_antisymm ?_ ?_
  · intro b hb
    have hcomm : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
      have hbot : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hb.2))
      rw [hbot]
      exact bot_le
    exact hK1 y K hnb b hb.1 hcomm
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨hS.1.1.2.1.1 hnb.1.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnb.1.2.2.2.1 hk)

theorem ggQ2_isComponentOf_jointCentralizer {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) :
    IsComponentOf J (ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G)) := by
  have hxD : x ∈ D := hS.1.1.2.2.1.2.2.2.1
  have hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1
  have hL : IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer ({x} : Set G)) :=
    hLcomp.of_le_of_le (le_inf (le_ggG0_left p B x L D J) hLcomp.1) inf_le_right
  have hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.2.1
  exact ggQ2_component_jointCentralizer (ggG0 p B x L D J) L J D x hxD hL hJ

end CFSG.StandardType

end
