module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Alt
public import CFSG.GroupTheory.OrderThreeActionTwoGroup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.H.A5W CFSG.QuasithinUnique.A5.Delta5
open scoped commutatorElement

namespace FA5

variable {G : Type} [Group G] [Finite G] {L S : Subgroup G}

theorem relIndex_borelOf_eq_three
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (e : OTwoQuot L ≃* alternatingGroup (Fin 5))
    (hSL : S ≤ L) : S.relIndex (borelOf L S) = 3 := by
  obtain ⟨D, hDB, hD3, hDS, hsup⟩ := exists_cartan_three hsyl e
  rw [inf_eq_left.mpr hSL] at hDS hsup
  have hBN : borelOf L S ≤ Subgroup.normalizer (S : Set G) := by
    simpa [inf_eq_left.mpr hSL] using F1.borelOf_le_normalizer L S
  have hDN : D ≤ Subgroup.normalizer (S : Set G) := hDB.trans hBN
  calc S.relIndex (borelOf L S) = S.relIndex (D ⊔ S) := by rw [sup_comm, hsup]
    _ = S.relIndex D := F1.relIndex_sup_eq_of_le_normalizer hDN
    _ = (S ⊓ D).relIndex D := (Subgroup.inf_relIndex_right (H := S) (K := D)).symm
    _ = (⊥ : Subgroup G).relIndex D := by rw [inf_comm, hDS]
    _ = Nat.card D := Subgroup.relIndex_bot_left D
    _ = 3 := hD3

theorem borelOf_eq_sup_cartan_of_le {D : Subgroup G}
    (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hquot : OTwoQuot L ≃* alternatingGroup (Fin 5))
    (hSL : S ≤ L) (hDL : D ≤ L)
    (hDN : D ≤ Subgroup.normalizer (S : Set G))
    (hD3 : Nat.card D = 3) (hDnotS : ¬ D ≤ S) :
    S ⊔ D = borelOf L S := by
  classical
  have hrelD : S.relIndex (S ⊔ D) = 3 :=
    CFSG.GroupTheory.relIndex_sup_eq_three_of_not_le hD3 hDN hDnotS
  have hrelB : S.relIndex (borelOf L S) = 3 :=
    relIndex_borelOf_eq_three hsyl hquot hSL
  have hS_borel : S ≤ borelOf L S := by
    rw [borelOf, inf_eq_left.mpr hSL]
    exact le_inf hSL Subgroup.le_normalizer
  have hD_borel : D ≤ borelOf L S := by
    rw [borelOf, inf_eq_left.mpr hSL]
    exact le_inf hDL hDN
  have hle : S ⊔ D ≤ borelOf L S := sup_le hS_borel hD_borel
  have hcard1 : Nat.card ↥(S ⊔ D) = 3 * Nat.card ↥S := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := S ⊔ D)
    rw [show S ⊓ (S ⊔ D) = S from inf_eq_left.mpr le_sup_left, hrelD] at h
    omega
  have hcard2 : Nat.card ↥(borelOf L S) = 3 * Nat.card ↥S := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := borelOf L S)
    rw [show S ⊓ borelOf L S = S from inf_eq_left.mpr hS_borel, hrelB] at h
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])

end FA5

end CFSG.Quasithin
