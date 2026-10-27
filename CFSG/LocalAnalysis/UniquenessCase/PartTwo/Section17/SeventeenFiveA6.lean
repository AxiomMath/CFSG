module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarConjShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeJ2Local17
public import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.Quasithin.H13.A5Rows
public import CFSG.GroupTheory.StronglyEmbeddedTwoResidual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_5_A6Module (D : Data G) (V₀ V : Subgroup G) : Prop :=
  Hyp125 D V₀ V →
    ∀ L : Subgroup G, L ∈ calC D.M →
      Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6)) → D.k = 1 →
      Nat.card V₀ ≤ 4 ∧ InFSq 1 (L ⊔ D.T)

theorem not_thin8_of_barO2Z_altSix {L : Subgroup G}
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6))) :
    ¬ F08.Thin8 L := by
  refine Inputs1719.not_thin_of_pRank_three ?_
  obtain ⟨e⟩ := hshape
  have hbar : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarO2Z17 L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (show 1 < 3 by norm_num) e]
    exact CFSG.Quasithin.H13.A5.two_le_pRank_alt6
  have hL2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
    CFSG.GroupTheory.two_le_pRank_of_quotient (O2ZIn17 L) Nat.prime_three (by norm_num) hbar
  rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L]

theorem three_dvd_card_of_barO2Z_altSix {L : Subgroup G}
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6))) :
    3 ∣ Nat.card L := by
  obtain ⟨e⟩ := hshape
  have hcard : Nat.card L = Nat.card (BarO2Z17 L) * Nat.card (O2ZIn17 L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (O2ZIn17 L)
  have h360 : Nat.card (BarO2Z17 L) = 360 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4]
    norm_num
  rw [hcard, h360]
  exact ⟨120 * Nat.card (O2ZIn17 L), by ring⟩

section Certified


theorem gap17_5_A6_of {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h111 : W3Thm111 G) (h126 : R126 D)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h77 : Inputs1719.W4Lem7_7) (h106 : Inputs1719.W4Lem10_6Q)
    (hMod : Gap17_5_A6Module D V₀ V) :
    ∀ L : Subgroup G, L ∈ calC D.M →
      Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6)) → D.k = 1 → False := by
  intro L hL hshape hk
  obtain ⟨h4, hFSq⟩ := hMod hV L hL hshape hk
  have hnt : ¬ F08.Thin8 L := not_thin8_of_barO2Z_altSix hshape
  have hLM : L ≤ D.M := hL.1.le
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      exact barSub_ne_bot_of_not_thin_bot h869 h127 hV hL hnt
    · exact barSub_ne_bot_of_not_thin hV hC117 hL hnt
  have hU : UniqueMax D.M (L ⊔ D.T) := Inputs1719.uniqueMax_sup_T_of_not_thin h869 hL hnt
  have hUc : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uniqueMax_conjClosure_of_not_thin h869 hL hnt
  have hm : MBarGT D.M V₀ V 3 := h1669 h4
  have hb : bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2 :=
    bBar_conjClosure_le_two_of_A6 hV h77 h106 hL hshape
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    have h2 : D.k = 2 := (Data.k_eq_two_iff D).2 hns
    omega
  have h3H : 3 ∣ Nat.card ↥(L ⊔ D.T) :=
    (three_dvd_card_of_barO2Z_altSix hshape).trans
      (Subgroup.card_dvd_of_le (show L ≤ L ⊔ D.T from le_sup_left))
  have hO2 : ∀ g : G, g ∉ D.M → ¬ twoResidual (L ⊔ D.T) ≤ conjSubgroup D.M g :=
    CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded Nat.prime_three
      (by norm_num)
      (sup_le hLM D.sylowM.le) h3H hsp
  exact false_of_bBar_le_two D hx h61 h66 h127 h1114 h162 hTor h1482 h183 h111 h126 hk hV hL
    hL1 hU hUc hFSq hb hm hO2

theorem seventeen_five_of_A6Module {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) (h82 : F08.R82 D) (h880 : F08.R880 D)
    (hKA1 : Inputs1719.K_A7Permuting)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h111 : W3Thm111 G) (h126 : R126 D)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h77 : Inputs1719.W4Lem7_7) (h106 : Inputs1719.W4Lem10_6Q)
    (hMod : Gap17_5_A6Module D V₀ V) :
    R17_5At D V₀ V := by
  refine seventeen_five_of_no_A6 h17_1 h82 h880 hKA1 fun L hL hshape => ?_
  exact gap17_5_A6_of hV hx h61 h66 h127 h1114 h162 hTor h1482 h183 h111 h126 h869 hC117
    h1669 h77 h106 hMod L hL hshape (k_eq_one_of_alt_six h880 hL hshape)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
