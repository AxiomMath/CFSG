module

public import CFSG.Quasithin.Vol2.Ch11SecSZK6
public import CFSG.Quasithin.Vol2.Ch11SecSFF
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G]

theorem card_small :
    Nat.card ↥(alternatingGroup (Fin 6)) = 2 ^ 3 * 45 ∧
      Nat.card ↥(alternatingGroup (Fin 7)) = 2 ^ 3 * 315 ∧
      Nat.card ↥(alternatingGroup (Fin 5)) = 2 ^ 2 * 15 ∧
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 2 ^ 3 * 21 := by
  refine ⟨card_alt6 ⟨MulEquiv.refl _⟩, card_alt7 ⟨MulEquiv.refl _⟩, card_alt5 ⟨MulEquiv.refl _⟩, ?_⟩
  rw [card_SL_three' (K := ZMod 2) (n := 1) (by rw [Nat.card_zmod]; norm_num)]
  decide

theorem TypeData.not_list325 {T L I : Subgroup G} (hD : TypeData ↥(autOn L (fsuV T I))) :
    ¬ List325Three T L I := by
  obtain ⟨h6, h7, -, -⟩ := card_small
  rintro (⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | he | he | he | he)
  · exact hD.not_SL3 hK e
  · exact hD.not_Sp4 hK e
  · obtain ⟨e⟩ := he
    exact hD.false_of_iso_lt e (by rw [h6]; norm_num)
  · exact hD.notSL4 he
  · obtain ⟨e⟩ := he
    exact hD.not_SL5 e
  · obtain ⟨e⟩ := he
    exact hD.false_of_iso_lt e (by rw [h7]; norm_num)

theorem TypeData.not_type328 (hF : Facts02) {T L V : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hD : TypeData ↥(autOn L V)) :
    ¬ Type328 T L V := by
  obtain ⟨h6, h7, h5, h32⟩ := card_small
  have hle : autOn L V ≤ autOn (L ⊔ T) V := Subgroup.map_mono fun _ hx => Subgroup.mem_sup_left hx
  have hne : autOn L V ≠ ⊥ := by
    intro hb
    have := hD.le_card
    rw [hb, Subgroup.card_bot] at this
    omega
  have := autOn_normal_subgroupOf (V := V) (sup_le Subgroup.le_normalizer hTL)
  rintro (⟨n, hL⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | he | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
      he | he | he | he | ⟨-, hc, -⟩ | ⟨n, hn, ⟨e⟩⟩ | he)
  · exact hD.not_PSL2 hL
  · exact hD.not_SL3 hK e
  · obtain ⟨e⟩ := he
    exact hD.false_of_iso_lt e (by rw [h32]; norm_num)
  · exact hD.not_Sp4 hK e
  · exact hD.not_G2 hF hK e
  · obtain ⟨e⟩ := he
    exact hD.false_of_iso_lt e (by rw [h5]; norm_num)
  · obtain ⟨e⟩ := he
    exact hD.false_of_iso_lt e (by rw [h7]; norm_num)
  · obtain ⟨e⟩ := he
    exact hD.false_of_iso_lt e (by rw [h6]; norm_num)
  · obtain ⟨e⟩ := he
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Nat.card_congr e.toEquiv, h7] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have := hD.le_card
    omega
  · exact hD.not_tripleA6 hc
  · have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
      isSimpleGroup_SL_zmod_two (by omega)
    have hB : IsSimpleGroup ↥(autOn (L ⊔ T) V) := @MulEquiv.isSimpleGroup _ _ _ _ hs e
    have hAB := eq_of_normal_of_isSimpleGroup hle hB hne
    have e' := (MulEquiv.subgroupCongr hAB).trans e
    rcases hn with rfl | rfl
    · exact hD.notSL4 ⟨e'⟩
    · exact hD.not_SL5 e'
  · exact hD.notSL4 he

end CFSG.Quasithin.Vol2.Ch11.SecS
