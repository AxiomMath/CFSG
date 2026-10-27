module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pAb
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pNon
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22p
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pGlue
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45WForm
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45WSymp
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45W
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Core2
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K2
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Shape
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45R21
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45R23
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45N2
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45R25
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Split
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Compl
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45R26
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45R27
public import CFSG.LocalAnalysis.UniquenessCase.UC1K43Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

theorem base45_of_hyp45 [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] {ρ : Representation (ZMod p) G V} (h : Hyp45 p G V ρ D) : Base45 p G D where
  prime := Fact.out
  odd := h.odd
  ne_three := p_ne_three h
  kgroup := h.kgroup
  card_three := h.card_three
  gen := h.gen
  Op := uc45_Op h
  center_cyclic := uc45_center h
  noAbel2 := K43.noAbelianD_of_k42 UC6.k42_uc6 h.odd h.kgroup h.faithful h.card_three h.fix
  noOdd := fun q hq hq2 hq3 hqp Q hQ hN hDQ => by
    by_contra hne
    have := (UC6.k42_uc6 p Fact.out G h.kgroup V ρ h.faithful q 3 hq Nat.prime_three hqp
      (Ne.symm (p_ne_three h)) hq3 D h.card_three h.fix Q hQ hne hN hDQ).2.1
    exact hq2 this
  quat := fun T hT2 hT0 hN hDT hZ =>
    (k43_holds p h.odd G h.kgroup V ρ h.faithful D h.card_three h.fix T hT2 hT0 hN hDT hZ).1

theorem uc45_Q8 (h : Base45 p G D)
    (hcl : commutator ↥(Xof G) ≤ Subgroup.center ↥(Xof G))
    (hZX : ZXof G ≤ Subgroup.center G) (hT : Tof G D ≠ ⊥) :
    Nonempty (↥(Tof G D) ≃* QuaternionGroup 2) := by
  obtain ⟨h2, hN, hDT, hcyc⟩ := uc45_T_hyp h hcl hZX
  exact h.quat _ h2 hT hN hDT hcyc

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open UC46

theorem k45Odd_of_pieces (hSz1 : SimpleThreePrimeIsSz)
    (hSz2 : SzOrder3Aut) (hPairSp : PairSp) (hInsp : InspPairShape) : K45Odd := by
  intro p _ G _ _ V _ _ _ ρ D h
  have hB : Base45 p G D := base45_of_hyp45 h.toHyp45
  by_cases hK : Kof G = ⊥
  · exact Or.inl (Subgroup.commutator_top_right_eq_bot_iff_le_center.1 hK)
  · refine Or.inr ?_
    have hAbs : K22p.K22pAbs := k22pAbs_of chiefAb_holds chiefNon_holds
    have hK22 := uc45_K22p_of hAbs hSz1 hSz2 hB
    have hcl := uc45_class_two hB
    have hZX := uc45_ZX_le hB
    have hT := uc45_T_ne_bot hB hK22 hK
    have pre : Pre45 p G D := ⟨hB, hK22, hZX, hcl, uc45_Q8 hB hcl.1 hZX hT⟩
    have hSymp : SympData := sympData_of_form sympForm_holds
    have hPair : PairX := pairX_of_pairSp hSymp hPairSp
    have hKX := uc45_K_eq_X (core2_of hAbs hSz1 hSz2) hPair pre
    have front : Front45 p G D :=
      ⟨pre, h.rank, h.perfect, hKX, uc45_X_gen h.card_three h.gen hKX⟩
    have hHW := r2_H_le_wker hSymp front
    have hker := r2_wker_eq hSymp front
    have ctx : Ctx45 p G D := ⟨front, uc45_alt5 hPair hInsp front hker⟩
    have hH := r2_H_eq_XZ sympForm_holds front hHW (r2_centralizer_X front)
    have hcard := r2_card_X hSymp ctx hker
    have hD5 := n2_xDelta5 hSymp ctx hker
    exact r2_A5Q8D8 ctx (r2_center_two ctx hH hD5) hcard
      (r2_H_eq_X ctx hH (uc45_complement splitDelta5_holds ctx hH hD5))

end CFSG.LocalAnalysis.UniquenessCase.UCK
