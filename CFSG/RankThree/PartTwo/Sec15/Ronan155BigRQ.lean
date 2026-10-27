module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155SplitDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155StepDefs
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigTools
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorr
public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProofBlock

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof155R2

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem step155RQKWBig_of (h152 : Item152Big A (lB A))
    (h153 : Ronan153Big.Item153Big A (lB A)) : Step155RQKWBig A c L := by
  intro h X K Y M T P J hC hXb _ _ _ _ hXJ _
  have hKb : Big152 K := big152_k hC hXb
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hXQ : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (P ⊔ J) : Set G) :=
    (hXJ.trans le_sup_right).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hXN : X ≤ Subgroup.normalizer (n155 A K : Set G) :=
    (hC.le_k.trans (Subgroup.le_normalizer.trans
      (normalizer_le_n155w_big h153 hC.mem_k hKb))).trans Subgroup.le_normalizer
  exact le_normalizer_of_isPGroup_of_le_normalizer_big h h152 h153 hC.mem_k hKb
    (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hC.le_k
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _).to_le inf_le_left) inf_le_right
    (Late.le_normalizer_inf hXQ hXN)

theorem step155RQNWBig_of (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (hK : Step155RQKWBig A c L) :
    Step155RQNWBig A c L :=
  fun h X K Y M T P J hC hXb hmax hab hJM hJ0 hXJ D =>
    Proof155w.inf_n155_le_pCoreOf_w h h1444 h146 hbot hC hmax hab hJ0 hXJ D.mem_p.prop.1.1
      (D.mem_p.prop.1.2.trans inf_le_left) D.le_tp D.le_qp D.norm_rq
      (hK h X K Y M T P J hC hXb hmax hab hJM hJ0 hXJ D)

theorem b155_le_n155_of_end155N_of_w_big (h : Sec14Std G A c L)
    (h153 : Ronan153Big.Item153Big A (lB A)) (h315 : Item3_15)
    (h316 : Sec19.Item316) (hBXW : Step155BXW A c L) (hsubn : Step155BSubn2W A c L)
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hXb : Big152 X)
    (hmax : MaxT155 A X K T) (hab : Above155w A X) (hE : End155N A X K Y M T P)
    (hW : w155 A M X ≠ ⊥ → w155 A M X = delta A (lB A) (w155 A M X) ∧
      (w155 A M X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ∨
        Hyp315 (CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X) (CFSG.Open.pCoreOf 2 Y) ∨
        ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ CFSG.Open.pCoreOf 2 Y ∧
          (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic ∧
          w155 A M X ≤ Subgroup.normalizer (C : Set G))) : b155 A M X ≤ n155 A K := by
  set R := CFSG.Open.pCoreOf 2 Y with hR
  have hR1 : R ≠ ⊥ := hC.isY.1.1.2
  have hRchar : (R.subgroupOf R).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.topCharacteristic
  have hM' : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC.mem_m
  obtain ⟨hYM, -, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM'
  have hXN : X ≤ n155 A K :=
    hC.le_k.trans (Subgroup.le_normalizer.trans
      (normalizer_le_n155w_big h153 hC.mem_k (big152_k hC hXb)))
  have hWN : w155 A M X ≤ n155 A K := by
    by_cases hW1 : w155 A M X = ⊥
    · rw [hW1]
      exact bot_le
    · obtain ⟨hWΔ, hWR | hyp | ⟨C, hC1, hCR, hCc, hWC⟩⟩ := hW hW1
      · calc w155 A M X = delta A (lB A) (w155 A M X) := hWΔ
          _ ≤ delta A (lB A) (Subgroup.normalizer (R : Set G)) := delta_mono hWR
          _ ≤ n155 A K := hE.claim R hR1 le_rfl hRchar
      · rcases exists_char_normal_of_hyp315 h315 hyp with ⟨C, hC1, hCR, hCc, hRWC⟩ | hbl
        · calc w155 A M X = delta A (lB A) (w155 A M X) := hWΔ
            _ ≤ delta A (lB A) (Subgroup.normalizer (C : Set G)) :=
              delta_mono (le_sup_right.trans hRWC)
            _ ≤ n155 A K := hE.claim C hC1 hCR hCc
        · exfalso
          have hRWM : CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X ≤ M :=
            sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYM)
              ((Subgroup.map_subtype_le _).trans
                ((oPrimeResidualOf_le_self 3 _).trans (inf_le_left.trans (delta_le M))))
          exact h.not_inCatalog (h316 G h.isSimpleGroup h.nonabelian h.kProper h.charTwoType
            h.evenRank_eq M _ hC.mem_m.1 (Proof153Block.isScriptLBlock_map_subtype hbl hRWM
              (hsubn h X K Y M T P hC hmax hab hE hW1 hbl)))
      · calc w155 A M X = delta A (lB A) (w155 A M X) := hWΔ
          _ ≤ delta A (lB A) (Subgroup.normalizer (C : Set G)) := delta_mono hWC
          _ ≤ n155 A K := hE.claim C hC1 hCR hCc
  exact (hBXW h X K Y M T P hC hmax hab hE).trans (sup_le hXN hWN)

theorem false_of_end155N_of_wP_big (h : Sec14Std G A c L)
    (h153 : Ronan153Big.Item153Big A (lB A)) (h315 : Item3_15)
    (h316 : Sec19.Item316) (hBXW : Step155BXW A c L)
    (hsubn : Step155BSubn2W A c L) (hfr : Step155FrattiniNWP A c L)
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hXb : Big152 X)
    (hmax : MaxT155 A X K T) (hab : Above155w A X) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hW : w155 A M X ≠ ⊥ → w155 A M X = delta A (lB A) (w155 A M X) ∧
      (w155 A M X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ∨
        Hyp315 (CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X) (CFSG.Open.pCoreOf 2 Y) ∨
        ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ CFSG.Open.pCoreOf 2 Y ∧
          (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic ∧
          w155 A M X ≤ Subgroup.normalizer (C : Set G))) : False :=
  hC.not_le (hfr h X K Y M T P hC hmax hab hE hRP
    (b155_le_n155_of_end155N_of_w_big h h153 h315 h316 hBXW hsubn hC hXb hmax hab hE hW))

end CFSG.RankThree.PartTwo.Sec15.Ronan155Big
