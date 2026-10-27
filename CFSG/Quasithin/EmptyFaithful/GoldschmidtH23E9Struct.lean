module

public import CFSG.Quasithin.EmptyFaithful.T1521SReduce
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9Types
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9Cut

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Struct15121E9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15120Types T Mc M Z₁ L →
    ((CharTwo L ∧ IsBlock2 (g1_1516 Z₁) L ∧ (IsAltType L 5 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)) ∨
      (IsComponentOf L (g1_1516 Z₁) ∧
        (IsBender1516 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ (∃ n : ℕ, IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
          ∃ n : ℕ, IsPSp4 2 n (↥L ⧸ CFSG.pCore 2 ↥L)))) →
    (∃ H : Subgroup G, H ≤ M ⊓ mZ1516 Mc Z₁ ∧ NrmE9Prop (s1516 T Z₁) L H) ∨
    (∀ Y : Subgroup G, Y ≤ M ⊓ g1_1516 Z₁ →
        Y ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) → IsPGroup 5 ↥Y →
        ((s1516 T Z₁ : Set G) * (Y : Set G) = (Y : Set G) * (s1516 T Z₁ : Set G)) →
        ⁅V₂, Y⁆ = V₂ → ⁅L, Y⁆ = ⊥) ∨
    NoE16 (s1516 T Z₁) L

theorem struct15121E9_conclusion {T Mc M Z₁ V₂ L : Subgroup G}
    (h18 : Lemma15118Concl T Mc M Z₁)
    (horb : conjSubgroupsBy (g1_1516 Z₁) L = conjSubgroupsBy (s1516 T Z₁) L)
    (hBL : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤ mZ1516 Mc Z₁)
    (hNJ : Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ≤ M)
    (hd : NrmE9 (s1516 T Z₁) L ∨ Exc5 (g1_1516 Z₁) (s1516 T Z₁) L ∨ NoE16 (s1516 T Z₁) L) :
    (∃ H : Subgroup G, H ≤ M ⊓ mZ1516 Mc Z₁ ∧ NrmE9Prop (s1516 T Z₁) L H) ∨
    (∀ Y : Subgroup G, Y ≤ M ⊓ g1_1516 Z₁ →
        Y ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) → IsPGroup 5 ↥Y →
        ((s1516 T Z₁ : Set G) * (Y : Set G) = (Y : Set G) * (s1516 T Z₁ : Set G)) →
        ⁅V₂, Y⁆ = V₂ → ⁅L, Y⁆ = ⊥) ∨
    NoE16 (s1516 T Z₁) L := by
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516' h18
  rcases hd with ⟨H, hHB, hHP⟩ | hE | hN
  · exact Or.inl ⟨H, le_inf (hHP.1.trans hNJ) (hHB.trans (conjJoin_le_of_le hBL hSM)), hHP⟩
  · refine Or.inr (Or.inl ?_)
    intro Y hYMG hYJ hYp hSY _
    have hYX : Y ≤ g1_1516 Z₁ := hYMG.trans inf_le_right
    have hYK : Y ≤ Subgroup.normalizer (conjJoin (s1516 T Z₁) L : Set G) := fun y hy =>
      mem_normalizer_conjJoin_of_orbits (s1516_le_g1 T Z₁) horb (hYX hy)
    exact hE Y hYX hYJ hYK hYp hSY
  · exact Or.inr (Or.inr hN)

theorem struct15121E9_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hcutB : TypeCutBlock1521)
    (hcutC : TypeCutComp1521) (hcutAlt : TypeCutCompAlt1521) (hFam : FamE9) : Struct15121E9 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 hant
  have hq := hC.qtfe
  have hM := hC.mf
  have hS := hC.setting
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hS.pCore_g1_ne_bot hq hM
  have hS1 : s1516 T Z₁ ≠ ⊥ := fun h =>
    hpc (le_bot_iff.1 (h ▸ pCoreOf_le_of_isSylowTwoOf h18.four))
  have hNJ : Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS h18.four.2.1 hS1).trans h17.cgs
  have hLN : ¬ L ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) := fun h =>
    h20.2.1 (h.trans hNJ)
  have hSQ : IsSQTKIn (g1_1516 Z₁) := h18.five.2.2.sqtk
  have hStd : Std1521 (g1_1516 Z₁) (s1516 T Z₁) L := ⟨hSQ, h18.four, hL.comp, h20.1, hLN⟩
  have horb := (a3Orbits_of_a37_a38 h37 h38 (g1_1516 Z₁) (s1516 T Z₁) L hSQ h18.four hL.comp).1
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516' h18
  have hMLS : s1516 T Z₁ ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := inf_le_inf_right L hSM
  have key : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤ mZ1516 Mc Z₁ ∧
      (NrmE9 (s1516 T Z₁) L ∨ Exc5 (g1_1516 Z₁) (s1516 T Z₁) L ∨ NoE16 (s1516 T Z₁) L) := by
    rcases hant with ⟨hchar, hbl, hty⟩ | ⟨hco, hcty⟩
    · have hshort : IsShort2 L := hbl.1
      have hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
        isQuasisimple_pCoreQuot_of_block1521d hshort hty
      obtain ⟨hLJ, h2⟩ := h20.2.2.1 hchar
      rcases h2 with h2A | h2B | h2C
      · have hBor := borelOver_le_of_isBorelOfBlock1521 (L := L) (P := mZ1516 Mc Z₁ ⊓ L)
          (Q := s1516 T Z₁ ⊓ L) h20.1 (card_ne_three_of_isQuasisimple1521 hqs) h2A.2.2 hMLS
          inf_le_right
        exact ⟨hBor.trans inf_le_left,
          hFam G (g1_1516 Z₁) (s1516 T Z₁) L hStd (Or.inl ⟨hchar, hLJ, hbl, hty⟩)⟩
      · exact absurd h2B.2 (hcutB G L hshort hty).1
      · exact absurd h2C.1 (hcutB G L hshort hty).2
    · obtain ⟨hZ, h3⟩ := h20.2.2.2 hco
      have hZ₁T : Z₁ ≤ T := fun z hz => hS.V_le_T hq hM (hS.z1_le_V hz)
      have hz : CentralMoving1521 (s1516 T Z₁) L :=
        centralMoving1521_of_ctx h18
          (Subgroup.isPerfect_iff.1 (Group.IsPerfect.mk hco.2.2.1)) hL.not_le hZ₁T
      rcases h3 with h3A | h3B | h3C | h3D | h3E | h3A6 | h3A7
      · have hBor := borelOver_le_of_isBorelIn1521 (L := L) (P := mZ1516 Mc Z₁ ⊓ L)
          (Q := s1516 T Z₁ ⊓ L) h20.1 h3A.2 hMLS
        exact ⟨hBor.trans inf_le_left,
          hFam G (g1_1516 Z₁) (s1516 T Z₁) L hStd (Or.inr ⟨hco, hZ, hz, Or.inl h3A.1⟩)⟩
      · have hBor : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤
            mZ1516 Mc Z₁ ⊓ L := by
          rcases h3B.2 with hB | hP
          · exact borelOver_le_of_isBorelIn1521 (L := L) (P := mZ1516 Mc Z₁ ⊓ L)
              (Q := s1516 T Z₁ ⊓ L) h20.1 hB hMLS
          · exact borelOver_le_of_isParabolic1521 (L := L) (P := mZ1516 Mc Z₁ ⊓ L)
              (Q := s1516 T Z₁ ⊓ L) h20.1 hP.1 hMLS
        exact ⟨hBor.trans inf_le_left,
          hFam G (g1_1516 Z₁) (s1516 T Z₁) L hStd (Or.inr ⟨hco, hZ, hz, Or.inr h3B.1⟩)⟩
      · exact absurd (Or.inl h3C) (hcutC G L hco.2.2 hcty)
      · exact absurd (Or.inr (Or.inl h3D)) (hcutC G L hco.2.2 hcty)
      · exact absurd (Or.inr (Or.inr h3E)) (hcutC G L hco.2.2 hcty)
      · exact absurd (Or.inl h3A6) (hcutAlt G L hco.2.2 hcty)
      · exact absurd (Or.inr h3A7) (hcutAlt G L hco.2.2 hcty)
  exact struct15121E9_conclusion h18 horb key.1 hNJ key.2

end CFSG.Quasithin.E9
