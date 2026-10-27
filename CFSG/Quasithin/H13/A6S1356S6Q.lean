module

public import CFSG.Quasithin.H13.A6S1356S6
public import CFSG.Quasithin.Background.C124AsmStmt
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement Pointwise

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem isBlock_of_C124SQTK
    (hC124 : C124StatementSQTK (G := G))
    (h1222 : Stmt12_2_2) (hS6 : ¬ autOn T V ≤ autOn L V) {g : G} (hg : conjSub g S.V2 = S.W0) :
    IsBlock2 (L ⊔ T) L ∧ CFSG.Quasithin.IsAltBlockType L 6 := by
  obtain ⟨t, htT, hρt⟩ := S.exists_T_45 hS6
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
    intro x hx
    have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * T :=
      Subgroup.coe_mul_of_right_le_normalizer_left L T S.T_le_NL
    have hx' : x ∈ (L : Set G) * T := by
      rw [← hmul]
      exact hx
    obtain ⟨l, hl, t', ht', rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨l, hl, t', ht', rfl⟩
  have hcharL : CharTwo L := A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful
  have hVL : ⁅V, L⁆ ≠ ⊥ := by
    rw [S.irr.2.2.2.1]
    exact S.irr.2.1
  have hQR : pCoreOf 2 (L ⊔ T) ≤ S.R45 := by
    rw [← S.cT]
    exact S.Q_le_R45
  rcases hC124 (L ⊔ T) T V L S.R45 6
      (charTwo_sup_of_normalizes S.h13.sylow.1 S.T_le_NL hcharL)
      (sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
        S.h13.faithful.1.2.2.2) S.reduced
      (A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right) hLT S.h13.faithful.1.2.1 hcharL hVL
      S.isAltQuotient_L hQR S.R45_le_T
      (Or.inr (Or.inr (Or.inr ⟨rfl, S.card_autOn_R45 htT hρt⟩))) with
    ⟨C, hC1, hCB, hCchar, hCN⟩ | hchi | ⟨hblk, hexc | h6 | hhat⟩
  · exact absurd (S.normalizer_le_M_of_char S.R45_le_T hC1 hCB hCchar hCN)
      (S.normalizer_R45_not_le h1222 hS6 hg)
  · exact (S.not_isChiBlock hchi).elim
  · exact (S.not_isExcA7Block hexc).elim
  · exact ⟨hblk, h6⟩
  · exact (S.not_isHatA6Block hhat).elim

end Setting4

theorem input1356TwoS6_of_sqtk
    (hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G)) (h1222 : Stmt12_2_2)
    (hB : Input1356TwoS6Block) : Input1356TwoS6 := by
  intro G _ _ T L V S hNS hS6 g hW
  have hcardW : Nat.card ↥(conjSub g S.V2) = 4 := by rw [A5.card_conjSub', S.card_V2]
  obtain ⟨a, haW, b, hbW, hpair⟩ := S.exists_pairHyp hW hcardW
  rcases zmod2_cases (dot (S.frame.ψ ⟨a, hW haW⟩ : P6) (S.frame.ψ ⟨b, hW hbW⟩ : P6)) with
    hd | hd
  ·
    obtain ⟨σ, hσW, hσs⟩ := isoWit _ _ hpair hd
    obtain ⟨l, hlL, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσs)
    refine ⟨l, hlL, (S.conjSub_pre_eq (Y := W2sub) S.card_V2 hW hcardW haW hbW l
      fun y hy => ?_).symm⟩
    rw [hl]
    exact hσW _ hy
  ·
    exfalso
    obtain ⟨l, -, hl⟩ := S.exists_L_conjSub_W0 hW hcardW haW hbW hpair hd
    have hg : conjSub ((l : G)⁻¹ * g) S.V2 = S.W0 := by
      rw [conjSub_mul, ← hl, conjSub_conjSub_inv]
    obtain ⟨hblk, h6⟩ := S.isBlock_of_C124SQTK (hC124 G) h1222 hS6 hg
    exact hB G T L V S hNS hS6 hblk h6 _ hg

end CFSG.Quasithin.H13.A6
