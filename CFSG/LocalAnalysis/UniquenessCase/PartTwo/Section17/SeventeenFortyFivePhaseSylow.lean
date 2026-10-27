module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup
open scoped Pointwise commutatorElement

theorem phase45_isSylowOf_two_sup {X : Type} [Group X] [Finite X] {L A T : Subgroup X}
    (hLn : L.Normal) (hA : Odd (Nat.card A)) (hT : IsPGroup 2 T)
    (hAT : (A : Set X) * (T : Set X) = (T : Set X) * (A : Set X))
    (hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L) :
    CFSG.ABGLocalTools.IsSylowOf 2 T (L ⊔ (A ⊔ T)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : L.Normal := hLn
  have hTLidx : ¬ 2 ∣ (T ⊓ L).relIndex L :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hTL).2.2
  have hAL : (A : Set X) * (L : Set X) = (L : Set X) * (A : Set X) := by
    rw [← Subgroup.mul_normal A L, sup_comm, Subgroup.normal_mul L A]
  have hM : ((L ⊔ T : Subgroup X) : Set X) = (L : Set X) * (T : Set X) :=
    Subgroup.normal_mul L T
  have hpermAM : (A : Set X) * ((L ⊔ T : Subgroup X) : Set X) =
      ((L ⊔ T : Subgroup X) : Set X) * (A : Set X) := by
    calc (A : Set X) * ((L ⊔ T : Subgroup X) : Set X)
        = (A : Set X) * ((L : Set X) * (T : Set X)) := by rw [hM]
      _ = ((A : Set X) * (L : Set X)) * (T : Set X) := by rw [mul_assoc]
      _ = ((L : Set X) * (A : Set X)) * (T : Set X) := by rw [hAL]
      _ = (L : Set X) * ((A : Set X) * (T : Set X)) := by rw [mul_assoc]
      _ = (L : Set X) * ((T : Set X) * (A : Set X)) := by rw [hAT]
      _ = ((L : Set X) * (T : Set X)) * (A : Set X) := by rw [mul_assoc]
      _ = ((L ⊔ T : Subgroup X) : Set X) * (A : Set X) := by rw [hM]
  have hTM : T ≤ L ⊔ T := le_sup_right
  have hMG : L ⊔ T ≤ L ⊔ (A ⊔ T) :=
    sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hrel1 : ¬ 2 ∣ T.relIndex (L ⊔ T) := by
    rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal L T,
      ← Subgroup.inf_relIndex_right T L]
    exact hTLidx
  have hrel2 : ¬ 2 ∣ (L ⊔ T).relIndex (L ⊔ (A ⊔ T)) := by
    rw [show L ⊔ (A ⊔ T) = A ⊔ (L ⊔ T) by ac_rfl,
      CFSG.ABGTheoremB.TotallyInverted.Omnibus.relIndex_sup_of_mul_comm hpermAM]
    exact fun h => hA.not_two_dvd_nat (h.trans (Subgroup.relIndex_dvd_card (L ⊔ T) A))
  have hmul := Subgroup.relIndex_mul_relIndex T (L ⊔ T) (L ⊔ (A ⊔ T)) hTM hMG
  have hnot : ¬ 2 ∣ T.relIndex (L ⊔ (A ⊔ T)) := by
    rw [← hmul]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
    · exact hrel1 h'
    · exact hrel2 h'
  exact CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hTM.trans hMG, hT, hnot⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
