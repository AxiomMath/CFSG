module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317C
public import CFSG.Quasithin.H13.A7NatAssembly
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace L3317

variable {G : Type} [Group G]

theorem card_commV_of_natural {L T : Subgroup G} [IsMulCommutative ↥(vPlus L T)]
    (hnat : AlternatingNatural (autOn L (vPlus L T)) (commVPlus L T L) ⊥ 7)
    (hWV : ⁅vPlus L T, L⁆ ≤ vPlus L T) : Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 6 := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hnat
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_bot] at hu
    exact Subgroup.mem_bot.2 (Subtype.ext hu)
  let e3 : (↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec) ≃*
      ↥(FFModel.altDn 7).sec :=
    (MulEquiv.ofBijective (QuotientGroup.mk' _)
      ⟨A7.altDn_seven_mk_injective, QuotientGroup.mk_surjective⟩).symm
  have hsec : Nat.card ↥(FFModel.altDn 7).sec = 64 := by
    show Nat.card ↥(G6.coreMod 7) = 64
    rw [Nat.card_congr A7.coreModSevenEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
      A7.nat_card_evenWeight_seven]
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWV).toEquiv,
    Nat.card_congr (MulEquiv.ofBijective β ⟨hinj, hβs⟩).toEquiv, Nat.card_congr e3.toEquiv, hsec]
  norm_num

end L3317

theorem stmt3_3_17_of
    (h6 : Stmt3_3_6) (h8 : Stmt3_3_8) (h10 : Stmt3_3_10)
    (h12 : Step3_3_12R) (h14 : Stmt3_3_14) : Stmt3_3_17 := by
  intro G _ _ T M L D h ⟨e⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨_, hc⟩ := L3317.alt7_cases h8 h10 h14 h e
  rcases hc with hnat | hc4
  · exact L3317.card_commV_of_natural hnat (L3317.commV_le_vPlus h)
  · exfalso
    obtain ⟨e', hQ⟩ := L3317.exists_equiv_map_le_stabFS h e hTL
    obtain ⟨hM₁, ht₁, hn₁, hO₁, -⟩ := L3317.mOne_facts (D := D) h e' hML hTL hc4
    obtain ⟨hM₂, ht₂, hO₂, hinn₂, -⟩ := L3317.mTwo_facts h10 h e' hQ hML hTL hc4
    obtain ⟨Y, hY, -, hPSL, hInn, -⟩ := step3_3_15R_of h6 h14 h12 G T M L D (L3317.mOne L T)
      _ h hM₁ hM₂ (L3317.sup_eq_mOne_mTwo h10 h e' hQ hML hTL hc4) hO₁ hO₂ ht₁ ht₂
    rcases hY with rfl | rfl
    · exact hn₁ hPSL
    · exact hinn₂ hInn

end CFSG.Quasithin.H13
