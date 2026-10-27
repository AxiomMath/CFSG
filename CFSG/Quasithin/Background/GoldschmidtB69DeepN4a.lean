module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepG2Aux
public import CFSG.Quasithin.Background.GoldschmidtB69DeepOrdD
public import CFSG.Quasithin.Background.GoldschmidtB69DeepOrdA
public import CFSG.Quasithin.Background.GoldschmidtB69DeepSecData
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

theorem asB69NoG2_proved
    (h22 : E2.E22StatementNoN) :
    AsB69NoG2 := by
  intro V _ _ hV X T M A L hH W hW B hBA hB hc
  obtain ⟨ℓ, hℓs, hcent, hLbq, hIrr, hFstar, hLbn, -⟩ := sectionFittingData hV hH hW
  obtain ⟨⟨H₀, _, _, hsq, hkg, φ, hφ⟩, hmp, hO2, -, -, -, hL, -⟩ := hH
  obtain ⟨⟨n, hn, -, hn2⟩, -⟩ := hc
  obtain ⟨F, _, πF, hπF, hfam⟩ := exists_quotient_e22C h22 hmp.subgroupOf ⟨hsq, hkg⟩ φ hφ
    (isComponentOf_subgroupOf hL)
  have hFs : IsSimpleGroup F := hfam.toFam.isSimpleGroup
  let e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  obtain ⟨c, hcodd, hcard⟩ := exists_odd_card_mul hL.2.2
    (fun z hz => odd_orderOf_of_mem_center_comp hO2 hL hz) ℓ hℓs hcent
    (πF.comp e0.symm.toMonoidHom) (hπF.comp e0.symm.surjective)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.QuasithinUnique.Bridge.TypeList.exists_equiv_of_g2Natural hn
  have hn1 : 1 ≤ n := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hK
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · obtain rfl : n = 1 := by omega
    have h2 : Nat.card K = 2 := by simpa using hK
    have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
    have hLJ : autSec L W (W ⊓ fixV L) ≤ ffJ (autSec (L ⊔ A) W (W ⊓ fixV L)) :=
      le_ffJ_of_fitting hS2 hFstar.symm hLbq hIrr hB
    have hJG := CFSG.QuasithinUnique.Bridge.TypeList.ffJ_le_self (autSec (L ⊔ A) W (W ⊓ fixV L))
    set J := ffJ (autSec (L ⊔ A) W (W ⊓ fixV L)) with hJdef
    have hnorm : ((autSec L W (W ⊓ fixV L)).subgroupOf J).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hLbn _ (hJG g.2) _ hx
    let iso : ↥(autSec L W (W ⊓ fixV L)) ≃*
        ↥(((autSec L W (W ⊓ fixV L)).subgroupOf J).map e.symm.toMonoidHom) :=
      (Subgroup.subgroupOfEquivOfLe hLJ).symm.trans
        (e.symm.subgroupMap ((autSec L W (W ⊓ fixV L)).subgroupOf J))
    have hperf : Group.IsPerfect ↥(((autSec L W (W ⊓ fixV L)).subgroupOf J).map
        e.symm.toMonoidHom) := by
      have : Group.IsPerfect ↥(autSec L W (W ⊓ fixV L)) := hLbq.1
      exact Group.IsPerfect.ofSurjective (f := iso.toMonoidHom) iso.surjective
    have hnt : Nontrivial ↥(autSec L W (W ⊓ fixV L)) := nontrivial_autSec hW
    have hne : (((autSec L W (W ⊓ fixV L)).subgroupOf J).map e.symm.toMonoidHom) ≠ ⊥ := by
      rw [← Subgroup.nontrivial_iff_ne_bot]
      exact iso.injective.nontrivial
    have h6048 := card_eq_6048_of_normal h2
      (Subgroup.Normal.map hnorm e.symm.toMonoidHom e.symm.surjective)
      (Subgroup.isPerfect_iff.1 hperf) hne
    rw [← Nat.card_congr iso.toEquiv] at h6048
    exact E22FamC.not_card_6048 hfam hcodd (by rw [← hcard]; exact h6048)
  · have heq : ffJ (autSec (L ⊔ A) W (W ⊓ fixV L)) = autSec L W (W ⊓ fixV L) := hn2 hge
    let eL : ↥(quasithinG2 K) ≃* ↥(autSec L W (W ⊓ fixV L)) :=
      e.trans (MulEquiv.subgroupCongr heq)
    have hcardL : Nat.card ↥(autSec L W (W ⊓ fixV L)) =
        Nat.card K ^ 6 * ((Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1)) := by
      rw [← Nat.card_congr eL.toEquiv]
      exact card_quasithinG2_1527d hK
    rw [hcardL, hK] at hcard
    exact E22FamC.not_card_g2 hfam hge hcodd hcard.symm

end B69

end CFSG.Quasithin
