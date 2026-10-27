module

public import CFSG.Quasithin.H13.GoldschmidtC137Tail
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.GoldschmidtC137U33Ent

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem isPSU_of_lieModel {Q : Type} [Group Q] (h : LieModel Q .PSU 3 3 1) : IsPSU 3 3 1 Q := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact h
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · cases ht

theorem center_eq_bot_of_simple_card {Q : Type} [Group Q] [Finite Q] (hs : IsSimpleGroup Q)
    (hc : ¬ (Nat.card Q).Prime) : Subgroup.center Q = ⊥ := by
  haveI : (Subgroup.center Q).Normal := inferInstance
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have hcomm : IsMulCommutative Q := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center Q := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.1 ha) b).symm⟩⟩
    letI : CommGroup Q :=
      { (inferInstance : Group Q) with mul_comm := fun a b => hcomm.is_comm.comm a b }
    exact hc IsSimpleGroup.prime_card

theorem isPSU_quot_center {Q : Type} [Group Q] (h : IsPSU 3 3 1 Q) (hc : Subgroup.center Q = ⊥) :
    IsPSU 3 3 1 (Q ⧸ Subgroup.center Q) := by
  obtain ⟨hadm, K, hK, hKf, hKc, ⟨e⟩⟩ := h
  exact ⟨hadm, K, hK, hKf, hKc, ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot).trans e⟩⟩

theorem isRankTwoLie2Derived_u33 [Finite G] {L : Subgroup G}
    (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have hc : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    center_eq_bot_of_simple_card (isSimple_u33 hlie) (by rw [card_of_psu33 hlie]; norm_num)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (isPSU_quot_center (isPSU_of_lieModel hlie) hc)))))))

structure U33Cfg [Finite G] (X T V L P M : Subgroup G) : Prop where
  hSQ : SQTKGroup ↥X
  hC : CharTwo X
  hT : IsSylowTwoOf T X
  hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  hL : L ∈ cComp X
  hL2 : CharTwo L
  hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1
  hTP : T ≤ P
  hPM : P ≤ M
  hMX : M < X
  hmax : ∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X
  hPeq : P = M
  hred : IsTwoReducedIn X V
  hVL : ⁅V, L⁆ = V
  hV0 : V ≠ ⊥

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
include h

theorem hLX : L ≤ X := le_of_mem_cComp h.hL

theorem hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod h.hT h.hprod h.hL

theorem hXN : X ≤ normalizer (V : Set G) := h.hred.2.1

theorem hVe : IsElemAbelian 2 V := h.hred.2.2.1

theorem hLN : L ≤ normalizer (V : Set G) := h.hLX.trans h.hXN

theorem hPX : P < X := lt_of_le_of_lt h.hPM h.hMX

theorem hVL' : ⁅V, L⁆ ≠ ⊥ := by
  rw [h.hVL]
  exact h.hV0

theorem hOL : pCoreOf 2 L ≤ centralizer (V : Set G) :=
  (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans h.hLX)
    (h.hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)).trans
    (C124.pCoreOf_le_centralizer h.hred)

theorem hkerL : pCoreOf 2 L = L ⊓ centralizer (V : Set G) :=
  pCoreOf_eq_inf_u33 h.hVe h.hLN (isSimple_u33 h.hlie) h.hOL h.hVL'

theorem toBaum : BaumCtx X T V L P :=
  ⟨h.hT, h.hprod, h.hL, h.hL2, Or.inl (isQuasisimple_u33 h.hlie), isRankTwoLie2Derived_u33 h.hlie,
    h.hTP, h.hPX, h.hred, h.hVL', by
      rw [← h.hkerL, ← pCoreOf_subgroupOf_eq h.hLX]
      exact pCoreOf_le_oTwoPhi _⟩

theorem isPGroup_C : IsPGroup 2 ↥(X ⊓ centralizer (V : Set G)) := by
  intro d
  have hdX : (d : G) ∈ X := d.2.1
  obtain ⟨k, hk⟩ := C124.exists_pow_mem_of_prod h.hLX h.hn h.hT.1 h.hT.2.1 hdX (h.hprod _ hdX)
  have hkC : (d : G) ^ 2 ^ k ∈ centralizer (V : Set G) := by
    have := d.2.2
    exact Subgroup.pow_mem _ this _
  have hkO : (d : G) ^ 2 ^ k ∈ pCoreOf 2 L := by
    rw [h.hkerL]
    exact ⟨hk, hkC⟩
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hkO⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have hj' : ((d : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  rw [← pow_mul, ← pow_add] at hj'
  simpa using hj'

theorem C_le_Q : X ⊓ centralizer (V : Set G) ≤ pCoreOf 2 X :=
  le_pCoreOf_of_le_normalizer 2 inf_le_left h.toBaum.hXC h.isPGroup_C

theorem C_le_R : X ⊓ centralizer (V : Set G) ≤ pCoreOf 2 P := h.C_le_Q.trans h.toBaum.hQR

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
