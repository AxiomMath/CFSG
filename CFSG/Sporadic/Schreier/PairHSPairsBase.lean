
module

public import CFSG.Sporadic.Schreier.PairHSOrder
public import CFSG.Sporadic.Schreier.PairHSCountBase
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.Sporadic.Schreier.PairSimple
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairHSCheck
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.Schreier.PairHSFaithfulInputs
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.HS.Data

@[expose] public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.ComponentClassification.OuterAutomorphisms

theorem hs_bs_eq : PairHS.bs = hsChain.base.toList.map Fin.val := hsChain_base.symm

theorem hs_groups : PairHS.groups.flatten = List.range hsChain.baseCount := by
  rw [hsChain_baseCount]
  rfl

theorem PairHS.parCount_eq (f : List (Array ℕ) → Bool) (bl : List (Array (Array ℕ))) :
    PairHS.parCount f bl = countW f bl [] := by
  cases bl with
  | nil => rfl
  | cons B Bs => exact countWPar_eq (by norm_num) f B Bs

theorem hs_gens :
    ∀ l < PairHS.gens.size, Rep 3850 PairHS.gens[l]! (hsGen l) ∧
      Rep 3850 PairHS.gensInv[l]! (hsGen l)⁻¹ ∧ hsGen l ∈ hsChain.originalSubgroup := by
  intro l hl
  have hl2 : l < 2 := hl
  have hinv := (hsCertOK_parts.2.2.1 l (by omega)).2
  have e1 : PairHS.gens[l]! = hsStrongArrs[l]! := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairHS.gens]
    · simp [PairHS.gens]
  have e2 : PairHS.gensInv[l]! = (rawInvs 3850 hsStrongArrs)[l]! := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairHS.gensInv]
    · simp [PairHS.gensInv]
  rw [e1, e2]
  exact ⟨rep_hsGen (by omega), (rep_permOfArr hinv).2, hsGen_mem l hl2⟩

theorem hs_reps
    (c : List (Array ℕ) × Array (Array ℕ) × Array ℕ × Array ℕ)
    (hc : c ∈ PairHS.cl) : ∃ x ∈ hsChain.originalSubgroup, RepW 3850 c.1 x := by
  have hab : ∀ t ∈ PairHS.wA ++ PairHS.wB, ∃ h ∈ hsChain.originalSubgroup, Rep 3850 t h := by
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [PairHS.wA, List.mem_singleton] at ht
      rw [ht]
      exact ⟨hsGen 0, hsGen_mem 0 (by norm_num), rep_hsGen (by norm_num)⟩
    · rw [PairHS.wB, List.mem_singleton] at ht
      rw [ht]
      exact ⟨hsGen 1, hsGen_mem 1 (by norm_num), rep_hsGen (by norm_num)⟩
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
  refine exists_repW_of_forall fun t ht => hab t ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact List.mem_append_left _ ht
  · obtain ⟨l, hl, htl⟩ := List.mem_flatten.1 ht
    rw [(List.mem_replicate.1 hl).2] at htl
    rcases mem_patW htl with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ h

theorem hs_card_order
    (m : ℕ) (hm : 0 < m) :
    Nat.card {x : hsChain.originalSubgroup // orderOf x = m} =
      PairHS.parCount (ordPred PairHS.bs m) PairHS.blocks := by
  rw [card_orderOf_coe, PairHS.parCount_eq]
  exact card_eq_countW hsChainArrays (by norm_num) PairHS.chain_check.1 hs_groups
    (Pr := fun g => orderOf g = m) fun w g hw hg => ordB_iff hs_baseFaithful hs_bs_lt hw hg hm

def hsa0 : hsP := ⟨hsGen 0, hsGen_mem_P 0 (by norm_num)⟩

def hsa1 : hsP := ⟨hsGen 1, hsGen_mem_P 1 (by norm_num)⟩

end CFSG.Sporadic.Schreier
