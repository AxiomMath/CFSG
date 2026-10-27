module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

@[expose] def Stmt12_5_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 5 1

structure Hyp125 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) : Prop where
  hyp : Hyp1223 G T L V
  quot : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
  card : Nat.card V = 2 ^ 10
  irred : IsIrreducibleUnder L V

@[expose] def Elim125 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp125 G T L V → False

theorem stmt12_5_1_of_elim125 (h1222 : Stmt12_2_2) (helim : Elim125) : Stmt12_5_1 := by
  intro G _ _ T L V hH hq
  obtain ⟨e⟩ := hq
  rcases h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow with hA | h3
  · exact absurd hA hH.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨-, -, -, hc, hmod⟩ := hall V hH.irrPlus
  have hQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 9999360 :=
    (Nat.card_congr e.toEquiv).trans card_sl_five_zmod_two
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    center_eq_bot_of_mulEquiv_sl (by norm_num) e
  rcases hmod with ⟨n, hn, ⟨e'⟩, hnat⟩ | ⟨⟨e'⟩, -, -⟩ | ⟨-, hcard, hirr⟩ |
      ⟨m, hm5, hm8, ⟨φ, hφ, -⟩, -⟩ | ⟨-, φ, hφ, -⟩ | ⟨hU, -⟩ | ⟨-, hZ3, -, -⟩
  · have h := hQ.symm.trans (Nat.card_congr e'.toEquiv)
    rcases hn with rfl | rfl | rfl
    · rw [card_sl_three_zmod_two] at h
      omega
    · rw [card_sl_four_zmod_two] at h
      omega
    · exact ⟨hc, hnat⟩
  · exfalso
    have h := hQ.symm.trans (Nat.card_congr e'.toEquiv)
    rw [card_sl_three_zmod_two] at h
    omega
  · exact (helim G T L V ⟨hH, ⟨e⟩, hcard, hirr⟩).elim
  · exact (card_alternating_ne_five hm5 hm8
      ((card_eq_of_surjective_alternating hH.quasisimple hZ hm5 φ hφ).symm.trans hQ)).elim
  · exfalso
    have hc7 := card_eq_of_surjective_alternating hH.quasisimple hZ (by norm_num) φ hφ
    rw [nat_card_alternatingGroup, hQ] at hc7
    norm_num [Nat.factorial] at hc7
  · exfalso
    rw [card_of_lieModel_psu_three_three hU] at hQ
    omega
  · exfalso
    rw [hZ, Subgroup.card_bot] at hZ3
    omega

end CFSG.Quasithin.H13
