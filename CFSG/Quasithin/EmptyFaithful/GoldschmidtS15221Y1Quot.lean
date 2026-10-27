module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Odd
public import CFSG.Quasithin.EmptyFaithful.S152He4Quot
public import CFSG.Quasithin.EmptyFaithful.S152Y06

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_le_alternating {α : Type} [DecidableEq α] [Fintype α]
    (A : Subgroup (Equiv.Perm α)) : oTwoUpper A ≤ alternatingGroup α := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]
  rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h | h
  · exact h
  · exfalso
    have h1 : Equiv.Perm.sign x ^ orderOf x = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [h, Odd.neg_one_pow hx.2] at h1
    exact absurd h1 (by decide)

theorem card_alternatingGroup_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem relIndex_pCoreOf_of_quot_perm {Y S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hY : Y = oTwoUpper Y) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hq : Nonempty (OTwoQuot (Y ⊔ S) ≃* Equiv.Perm (Fin 3))) :
    (pCoreOf 2 Y).relIndex Y = 3 := by
  obtain ⟨e⟩ := hq
  have hYP : Y ≤ Y ⊔ S := le_sup_left
  have hSP : S ≤ Y ⊔ S := le_sup_right
  have hPN : Y ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 Y) (hSY.trans (normalizer_le_normalizer_pCoreOf 2 Y))
  have hle1 : pCoreOf 2 Y ≤ pCoreOf 2 (Y ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYP) hPN (pCoreOf_isPGroup 2 Y)
  have heq : Y ⊓ pCoreOf 2 (Y ⊔ S) = pCoreOf 2 Y :=
    le_antisymm (inf_pCoreOf_le_pCoreOf hYP) (le_inf (pCoreOf_le 2 Y) hle1)
  have hcard := He4.card_imageOTwoQuot_mul hYP
  rw [heq] at hcard
  have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 Y) Y
  rw [inf_of_le_left (pCoreOf_le 2 Y)] at h2
  have hpos : 0 < Nat.card (pCoreOf 2 Y) := Nat.card_pos
  have hrel : (pCoreOf 2 Y).relIndex Y = Nat.card (imageOTwoQuot (Y ⊔ S) Y) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h2, hcard]
  rw [hrel]
  have hY' : imageOTwoQuot (Y ⊔ S) Y = oTwoUpper (imageOTwoQuot (Y ⊔ S) Y) :=
    (congrArg (imageOTwoQuot (Y ⊔ S)) hY).trans (S152Y.imageOTwoQuot_oTwoUpper hYP)
  have hA : (imageOTwoQuot (Y ⊔ S) Y).map e.toMonoidHom =
      oTwoUpper ((imageOTwoQuot (Y ⊔ S) Y).map e.toMonoidHom) := by
    rw [oTwoUpper_map]
    exact congrArg (Subgroup.map e.toMonoidHom) hY'
  have hAalt : (imageOTwoQuot (Y ⊔ S) Y).map e.toMonoidHom ≤ alternatingGroup (Fin 3) := by
    rw [hA]
    exact oTwoUpper_le_alternating _
  have hcardA : Nat.card ((imageOTwoQuot (Y ⊔ S) Y).map e.toMonoidHom) =
      Nat.card (imageOTwoQuot (Y ⊔ S) Y) := Subgroup.card_map_of_injective e.injective
  have hdvd : Nat.card (imageOTwoQuot (Y ⊔ S) Y) ∣ 3 := by
    have := Subgroup.card_dvd_of_le hAalt
    rw [hcardA, card_alternatingGroup_three] at this
    exact this
  have hne : imageOTwoQuot (Y ⊔ S) Y ≠ ⊥ := by
    intro hbot
    have htop : imageOTwoQuot (Y ⊔ S) S = ⊤ := by
      have h1 := imageOTwoQuot_self_eq_top (Y ⊔ S)
      rw [imageOTwoQuot_sup hYP hSP, hbot, bot_sup_eq] at h1
      exact h1
    have h2' : IsPGroup 2 (OTwoQuot (Y ⊔ S)) := by
      have := isPGroup_imageOTwoQuot' (M := Y ⊔ S) hS2
      rw [htop] at this
      exact this.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2'
    have h6 : Nat.card (OTwoQuot (Y ⊔ S)) = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    rw [h6] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 6)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · exact absurd (Subgroup.card_eq_one.mp h1) hne
  · exact h1

end CFSG.Quasithin.S15221
