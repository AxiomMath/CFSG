
module

public import CFSG.Sporadic.Schreier.PairJ3Order
public import CFSG.Sporadic.Schreier.PairJ3CountBase
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.Sporadic.Schreier.PairSimple
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairJ3Check
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public meta import CFSG.Sporadic.Schreier.PairJ3Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.J3.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.J3.Data

@[expose] public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.ComponentClassification.OuterAutomorphisms

theorem j3_bs_eq : PairJ3.bs = j3Chain.base.toList.map Fin.val := j3Chain_base.symm

theorem j3_groups : PairJ3.groups.flatten = List.range j3Chain.baseCount := by
  rw [j3Chain_baseCount]
  rfl

theorem PairJ3.parCount_eq (f : List (Array ℕ) → Bool) (bl : List (Array (Array ℕ))) :
    PairJ3.parCount f bl = countW f bl [] := by
  cases bl with
  | nil => rfl
  | cons B Bs => exact countWPar_eq (by norm_num) f B Bs

theorem j3_gens :
    ∀ l < PairJ3.gens.size, Rep 6156 PairJ3.gens[l]! (j3Gen l) ∧
      Rep 6156 PairJ3.gensInv[l]! (j3Gen l)⁻¹ ∧ j3Gen l ∈ j3Chain.originalSubgroup := by
  intro l hl
  have hl2 : l < 2 := hl
  have hinv := (j3CertOK_parts.2.2.2.2.1 l (by omega)).2
  have e1 : PairJ3.gens[l]! = j3StrongArrs[l]! := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairJ3.gens]
    · simp [PairJ3.gens]
  have e2 : PairJ3.gensInv[l]! = (rawInvs 6156 j3StrongArrs)[l]! := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairJ3.gensInv]
    · simp [PairJ3.gensInv]
  rw [e1, e2]
  exact ⟨rep_j3Gen (by omega), (rep_permOfArr hinv).2, j3Gen_mem l hl2⟩

theorem j3_reps
    (c : List (Array ℕ) × Array (Array ℕ) × Array ℕ × Array ℕ)
    (hc : c ∈ PairJ3.cl) : ∃ x ∈ j3Chain.originalSubgroup, RepW 6156 c.1 x := by
  simp only [PairJ3.cl, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  subst hc
  exact ⟨j3Gen 0, j3Gen_mem 0 (by norm_num), repW_j3wA⟩

theorem j3_card_order
    (m : ℕ) (hm : 0 < m) :
    Nat.card {x : j3Chain.originalSubgroup // orderOf x = m} =
      PairJ3.parCount (ordPred PairJ3.bs m) PairJ3.blocks := by
  rw [card_orderOf_coe, PairJ3.parCount_eq]
  exact card_eq_countW j3ChainArrays (by norm_num) PairJ3.chain_check.1 j3_groups
    (Pr := fun g => orderOf g = m) fun w g hw hg => ordB_iff j3_baseFaithful j3_bs_lt hw hg hm

def j3a : j3P := ⟨j3Gen 0, j3Gen_mem_P 0 (by norm_num)⟩

def j3b : j3P := ⟨j3Gen 1, j3Gen_mem_P 1 (by norm_num)⟩

end CFSG.Sporadic.Schreier
