module

public import CFSG.Milestones.ASVolI.B610.FinA
public import CFSG.Milestones.ASVolI.B610.BlkF
public import CFSG.Milestones.ASVolI.B610.FamG

public section

namespace CFSG.Quasithin.B610T.Fin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem burnsideB610_le_twoResidual_sup_of_card_three {H V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hLH : L ≤ H) (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (h3 : Nat.card (autI hV L) = 3) :
    L ≤ twoResidual L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) := by
  intro l hl
  obtain ⟨a, ha, b, hb, hab, ⟨k, hk⟩, hbodd⟩ := burnsideB610_exists_two_odd l
  have hzL : Subgroup.zpowers l ≤ L := Subgroup.zpowers_le.mpr hl
  have haL : a ∈ L := hzL ha
  have hbR : b ∈ twoResidual L := F6.mem_twoResidual_of_odd (hzL hb) hbodd
  have haN : a ∈ Subgroup.normalizer (V : Set G) := hLN haL
  have hmem : convI hV ⟨a, haN⟩ ∈ autI hV L := convI_mem_autI hV haL haN
  have hd3 : orderOf (convI hV ⟨a, haN⟩) ∣ 3 := by
    have h1 : orderOf (⟨_, hmem⟩ : ↥(autI hV L)) ∣ Nat.card ↥(autI hV L) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, h3] at h1
  have hd2 : orderOf (convI hV ⟨a, haN⟩) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have e : (⟨a, haN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [← map_pow, e, map_one]
  have hcop : Nat.Coprime (2 ^ k) 3 :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (by decide))
  have hord : orderOf (convI hV ⟨a, haN⟩) = 1 := by
    have h1 := Nat.dvd_gcd hd2 hd3
    rw [hcop.gcd_eq_one] at h1
    exact Nat.dvd_one.mp h1
  rw [orderOf_eq_one_iff, convI_eq_one_iff] at hord
  rw [hab]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hLH haL, hord⟩) (Subgroup.mem_sup_left hbR)

theorem burnsideB610_isSylowTwoOf_of_card_three {H T M V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (h3 : Nat.card (autI hV L) = 3) :
    IsSylowTwoOf (autI hV (baum T) ⊓ autI hV L) (autI hV L) := by
  have hT := hMP.isSylow
  have hST : baum T ≤ T := inf_le_left
  have hSN : baum T ≤ Subgroup.normalizer (V : Set G) := hST.trans (hT.1.trans hred.2.1)
  refine ⟨inf_le_right, (B2F.isPGroup_autI hV (hT.2.1.to_le hST) hSN).to_le inf_le_left,
    fun h2 => ?_⟩
  have hdvd : ((autI hV (baum T) ⊓ autI hV L).subgroupOf (autI hV L)).index ∣ 3 := by
    rw [← h3]
    exact Dvd.intro_left _ (Subgroup.card_mul_index _)
  have h23 := h2.trans hdvd
  omega

theorem burnsideB610_case_one {H T M V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V) (hL : IsSubnormal L H)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hnat : IsNaturalL2Prime 1 L V) :
    (∀ s ∈ baum T, ∀ hs : s ∈ Subgroup.normalizer (V : Set G),
        convI hV ⟨s, hs⟩ ∈ Subgroup.normalizer ((autI hV L : Subgroup (MulAut (IntMod V hV))) :
          Set (MulAut (IntMod V hV)))) ∧
      IsSylowTwoOf (baum T) (⨆ l ∈ L, (baum T).map (MulAut.conj l).toMonoidHom) ∧
      (twoResidual L = L →
        omegaOneCenterOf (thompsonJ T) =
          (⁅V, L⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
            (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (L : Set G))) := by
  classical
  have hLH : L ≤ H := TwoBlk.burnsideB610_le_of_isSubnormal hL
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hred.2.1
  have h3 : Nat.card (autI hV L) = 3 := TwoBlk.burnsideB610_card_autI_eq_three hV hLN hnat
  obtain ⟨ι, S, X, DX, hFam, i₀, hi₀, hLX, hcomm, hnorm⟩ :=
    burnsideB610_twoFamTarget_holds G H T M V L hMP hred hJ hL hnat
  obtain ⟨hR1, hR2, -, hR4⟩ := hFam.main (n := 1) le_rfl (by rw [Nat.card_zmod]; norm_num)
    hMP hred hJ
  exact burnsideB610_concl hV hMP hred hJ hLH hLX hcomm hnorm hR1 (hR2 i₀ hi₀) (hR4 i₀ hi₀)
    (burnsideB610_le_twoResidual_sup_of_card_three hV hLH hLN h3)
    (burnsideB610_isSylowTwoOf_of_card_three hV hMP hred h3)

end CFSG.Quasithin.B610T.Fin
