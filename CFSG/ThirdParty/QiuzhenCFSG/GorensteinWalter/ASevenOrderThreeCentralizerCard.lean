module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenOrderThreeKleinFourThreeCycle
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Centralizer order of a Klein-four-centralized element of order three -/

noncomputable section

namespace CFSG.GorensteinWalter

private abbrev A7C := alternatingGroup (Fin 7)
private abbrev S7C := Equiv.Perm (Fin 7)

/-- An order-three element of `A7` centralized by a Klein four has centralizer
of order `36` in `A7`. -/
public theorem aSeven_order_three_centralizer_card_eq_thirty_six_of_kleinFour
    (u : alternatingGroup (Fin 7)) (huOrder : orderOf u = 3)
    (V : Subgroup (alternatingGroup (Fin 7))) (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer
      ({u} : Set (alternatingGroup (Fin 7)))) :
    Nat.card (Subgroup.centralizer
      ({u} : Set (alternatingGroup (Fin 7)))) = 36 := by
  have hu3 :=
    aSeven_isThreeCycle_of_order_three_and_kleinFour_centralizer
      u huOrder V hVK hVcent
  change (u : S7C).cycleType = {3} at hu3
  let up : S7C := u
  let C : Subgroup S7C := Subgroup.centralizer ({up} : Set S7C)
  let A : Subgroup S7C := alternatingGroup (Fin 7)
  let D : Subgroup S7C := C ⊓ A
  have hCcard : Nat.card C = 72 := by
    dsimp [C]
    rw [Equiv.Perm.nat_card_centralizer,
      show up.cycleType = {3} by simpa [up] using hu3]
    norm_num
  have hCnotA : ¬ C ≤ A := by
    intro hCA
    have hfixed :=
      (Equiv.Perm.centralizer_le_alternating_iff.mp
        (by simpa [C, A] using hCA)).2.1
    rw [show up.cycleType = {3} by simpa [up] using hu3] at hfixed
    norm_num at hfixed
  obtain ⟨c, hcC, hcA⟩ := SetLike.not_le_iff_exists.mp hCnotA
  have hAindex : A.index = 2 := alternatingGroup.index_eq_two
  have hrel : D.relIndex C = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨c, hcC, ?_⟩
    intro b hbC
    have hbcC : b * c ∈ C := C.mul_mem hbC hcC
    by_cases hbA : b ∈ A
    · right
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbC, hbA⟩
      · intro hbc
        have hbcA : b * c ∈ A := (Subgroup.mem_inf.mp hbc).2
        have hiff : b * c ∈ A ↔ (b ∈ A ↔ c ∈ A) :=
          Subgroup.mul_mem_iff_of_index_two hAindex
        exact hcA ((hiff.mp hbcA).1 hbA)
    · left
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbcC,
          (Subgroup.mul_mem_iff_of_index_two hAindex).2
            (iff_of_false hbA hcA)⟩
      · intro hbD
        exact hbA ((Subgroup.mem_inf.mp hbD).2)
  have hrel' : (D.subgroupOf C).index = 2 := hrel
  have hDleC : D ≤ C := inf_le_left
  have hcardSub : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleC).toEquiv
  have hcardC : Nat.card D * 2 = Nat.card C := by
    have h := Subgroup.card_mul_index (D.subgroupOf C)
    rw [hcardSub, hrel'] at h
    exact h
  have hDcard : Nat.card D = 36 := by omega
  have hmap :
      (Subgroup.centralizer ({u} : Set A7C)).map A7C.subtype = D := by
    ext p
    constructor
    · rintro ⟨x, hxC, rfl⟩
      constructor
      · change (x : S7C) ∈ C
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxC
        exact congrArg Subtype.val hcomm
      · exact x.2
    · rintro ⟨hpC, hpA⟩
      refine ⟨⟨p, hpA⟩, ?_, rfl⟩
      have hx : (⟨p, hpA⟩ : A7C) ∈
          Subgroup.centralizer ({u} : Set A7C) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyA : y = u := by simpa using hy
        subst y
        have hcomm := (Subgroup.mem_centralizer_iff.mp hpC)
          (u : S7C) (by simp [up])
        exact Subtype.ext hcomm
      exact hx
  have hcardMap : Nat.card (Subgroup.centralizer ({u} : Set A7C)) =
      Nat.card ((Subgroup.centralizer ({u} : Set A7C)).map A7C.subtype) := by
    exact Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({u} : Set A7C)) A7C.subtype
        A7C.subtype_injective).toEquiv
  rw [hcardMap, hmap, hDcard]

end CFSG.GorensteinWalter
