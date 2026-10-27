module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.E1TwoAbs

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section BarCard

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem card_barRad_eq_relIndex (B : Subgroup Q) :
    Nat.card (E1.barRad Q B) = (CFSG.solvableRadical Q).relIndex B := by
  have := Subgroup.relIndex_ker (K := B) (QuotientGroup.mk' (CFSG.solvableRadical Q))
  rw [QuotientGroup.ker_mk'] at this
  exact this.symm

theorem inf_solvableRadical_eq_inf_pCore (h : E1.IsTwoClosed (CFSG.solvableRadical Q))
    {B : Subgroup Q} (hB : IsPGroup 2 B) :
    CFSG.solvableRadical Q ⊓ B = CFSG.Open.pCore 2 Q ⊓ B := by
  obtain ⟨P, hP, hPn⟩ := h
  have hPnorm : P.Normal := E1.normal_of_isSylowIn_of_normal hP hPn
  have hO2R : CFSG.Open.pCore 2 Q ≤ CFSG.solvableRadical Q :=
    A3.le_solvableRadical inferInstance
      (E1.isSolvable_of_isPGroup_two (CFSG.LieType.BorelTits.pCore_isPGroup 2))
  refine le_antisymm ?_ (inf_le_inf_right _ hO2R)
  refine le_inf ?_ inf_le_right
  have h1 : CFSG.solvableRadical Q ⊓ B ≤ P :=
    E1.le_of_isSylowIn_of_normal hP hPn inf_le_left (hB.to_le inf_le_right)
  exact h1.trans (CFSG.LieType.BorelTits.le_pCore 2 hPnorm hP.isPGroup)

end BarCard

section Ambient

variable {G : Type u} [Group G] [Finite G]

theorem card_le_of_isE {j : ℕ} {H S A K : Subgroup G} (hS : IsSylowIn 2 S H) (hAS : A ≤ S)
    (hA : IsElemAbelian 2 A) (hK : E1.IsE j H S A K) :
    A ≤ K ∧ Nat.card A ≤ 2 ^ j * Nat.card ↥(A ⊓ pCoreOf 2 K) := by
  have h1 : A ≤ E1.tauOf H S A := le_sup_left.trans (E1.le_tauOf hS hAS hA)
  have hAK : A ≤ K := (h1.trans hK.2.1).trans inf_le_right
  refine ⟨hAK, ?_⟩
  have hBA : Nat.card (A.subgroupOf K) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hinf : Nat.card ↥(CFSG.Open.pCore 2 ↥K ⊓ A.subgroupOf K) =
      Nat.card ↥(A ⊓ pCoreOf 2 K) := by
    have h2 : (CFSG.Open.pCore 2 ↥K ⊓ A.subgroupOf K).map K.subtype = pCoreOf 2 K ⊓ A := by
      rw [Subgroup.map_inf _ _ _ K.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hAK]
      rfl
    rw [← Subgroup.card_map_of_injective K.subtype_injective, h2, inf_comm]
  rcases hK.2.2.2 with ⟨hE, hcard⟩ | ⟨hE, hcard⟩
  · rw [E1.card_barO2_eq_relIndex] at hcard
    have h3 := Subgroup.relIndex_mul_card (H := CFSG.Open.pCore 2 ↥K) (K := A.subgroupOf K)
    rw [hinf, hBA] at h3
    rw [← h3]
    exact Nat.mul_le_mul_right _ hcard
  · rw [card_barRad_eq_relIndex] at hcard
    have hB2 : IsPGroup 2 (A.subgroupOf K) :=
      (B2F.isPGroup_of_isElemAbelian hA).of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
    have h3 := Subgroup.relIndex_mul_card (H := CFSG.solvableRadical ↥K) (K := A.subgroupOf K)
    rw [inf_solvableRadical_eq_inf_pCore hE.1 hB2, hinf, hBA] at h3
    rw [← h3]
    exact Nat.mul_le_mul_right _ hcard

end Ambient

end E3

end CFSG.Quasithin
