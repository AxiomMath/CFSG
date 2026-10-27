
module

public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.Schreier.PairHeCheck
public import CFSG.Sporadic.Schreier.PairHeCountTwoBase
public import CFSG.Sporadic.Schreier.PairHeTriple1Base
public import CFSG.Sporadic.Schreier.PairCounts
public import CFSG.Sporadic.Schreier.PairClassCover
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.PairHeCheckInputs
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairHeCheck
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Sporadic.Schreier.ImagePairs
public import Mathlib

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB

theorem he_bs_eq : PairHe.bs = heChain.base.toList.map Fin.val := by
  rw [heChain_base_toList]
  rfl

theorem he_groups : heGroups.flatten = List.range heChain.baseCount := rfl

theorem he_baseFaithful :
    BaseFaithful heChain.originalSubgroup PairHe.bs := by
  rw [he_bs_eq]
  exact baseFaithful_of_valid heChain_valid.1

theorem he_bs_lt : ∀ b ∈ PairHe.bs, b < 8330 := by
  decide

theorem heGenPerm_mem_orig {k : ℕ} (hk : k < 2) : heGenPerm k ∈ heChain.originalSubgroup :=
  heP_eq_originalSubgroup ▸ heGenPerm_mem hk

theorem repW_hewA : RepW 8330 PairHe.wA (heGenPerm 0) :=
  RepW.single (rep_heGen (by norm_num))

theorem repW_hewB : RepW 8330 PairHe.wB (heGenPerm 1) :=
  RepW.single (rep_heGen (by norm_num))

theorem he_gens :
    ∀ l < PairHe.gens.size, Rep 8330 PairHe.gens[l]! (heGenPerm l) ∧
      Rep 8330 PairHe.gensInv[l]! (heGenPerm l)⁻¹ ∧ heGenPerm l ∈ heChain.originalSubgroup := by
  intro l hl
  have hl2 : l < 2 := hl
  have e1 : PairHe.gens[l]! = heGen l := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairHe.gens]
    · simp [PairHe.gens]
  have e2 : PairHe.gensInv[l]! = invCand 8330 (heGen l) := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairHe.gensInv]
    · simp [PairHe.gensInv]
  rw [e1, e2]
  exact ⟨rep_heGen hl2, rep_heGen_inv hl2, heGenPerm_mem_orig hl2⟩

theorem he_cl_eq : PairHe.cl = [(PairHe.wA, PairHe.closureOf PairHe.wA),
    (PairHe.wT, PairHe.closureOf PairHe.wT)] :=
  rfl

@[expose] def heT1 : Equiv.Perm (Fin 8330) := (heGenPerm 0 * heGenPerm 1 ^ 3) ^ 4

theorem heT1_mem : heT1 ∈ heChain.originalSubgroup :=
  pow_mem (mul_mem (heGenPerm_mem_orig (by norm_num))
    (pow_mem (heGenPerm_mem_orig (by norm_num)) 3)) 4

theorem repW_hewT : RepW 8330 PairHe.wT heT1 := by
  have hp := repW_patW repW_hewA repW_hewB [false, true, true, true]
  have e : ([false, true, true, true].map fun b => if b then heGenPerm 1 else heGenPerm 0).prod =
      heGenPerm 0 * heGenPerm 1 ^ 3 := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.false_eq_true,
      ↓reduceIte, mul_one, pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e] at hp
  have h4 := RepW.flatten (List.Forall₂.cons hp (List.Forall₂.cons hp (List.Forall₂.cons hp
    (List.Forall₂.cons hp List.Forall₂.nil))))
  have e4 : [heGenPerm 0 * heGenPerm 1 ^ 3, heGenPerm 0 * heGenPerm 1 ^ 3,
      heGenPerm 0 * heGenPerm 1 ^ 3, heGenPerm 0 * heGenPerm 1 ^ 3].reverse.prod = heT1 := by
    simp only [heT1, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.prod_cons, List.prod_nil, mul_one, pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e4] at h4
  exact h4

theorem rep_t1Arr : Rep 8330 PairHe.t1Arr heT1 := fun x => by
  rw [PairHe.t1Arr, getElem!_ofFn_nat _ x.2]
  exact repW_hewT x

theorem repW_hewT1 : RepW 8330 PairHe.wT1 heT1 :=
  RepW.single rep_t1Arr

theorem he_card_order (m : ℕ) (hm : 0 < m) :
    Nat.card {x : heChain.originalSubgroup // orderOf x = m} = countOrd PairHe.bs m heBlocks := by
  rw [card_orderOf_coe, countOrd_eq]
  exact card_eq_countW heChainArrays (by norm_num) heChain_check.1 he_groups
    (Pr := fun g => orderOf g = m) fun w g hw hg => ordB_iff he_baseFaithful he_bs_lt hw hg hm

theorem he_orderOf_of_word
    {w : List (Array ℕ)} {x : Equiv.Perm (Fin 8330)} (hw : RepW 8330 w x)
    (hx : x ∈ heChain.originalSubgroup) {m : ℕ} (hm : 0 < m) (h : ordB PairHe.bs w m = true) :
    orderOf x = m :=
  (ordB_iff he_baseFaithful he_bs_lt hw hx hm).1 h

theorem orderOf_heGenPerm_zero :
    orderOf (heGenPerm 0) = 2 :=
  he_orderOf_of_word repW_hewA (heGenPerm_mem_orig (by norm_num)) (by norm_num)
    PairHe.word_orders.1

theorem orderOf_heT1 :
    orderOf heT1 = 2 := by
  have h := PairHe.classes.1
  rw [he_cl_eq] at h
  exact he_orderOf_of_word repW_hewT heT1_mem (by norm_num)
    (h (PairHe.wT, PairHe.closureOf PairHe.wT) (List.mem_cons_of_mem _ List.mem_cons_self))

@[expose] def hePartners (x : Equiv.Perm (Fin 8330)) : ℕ :=
  Nat.card {y : heChain.originalSubgroup //
    orderOf (y : Equiv.Perm (Fin 8330)) = 7 ∧ PatRel PairHe.conds x y}

theorem hePartners_conj {c : Equiv.Perm (Fin 8330)} (hc : c ∈ heChain.originalSubgroup)
    (x : Equiv.Perm (Fin 8330)) : hePartners (c * x * c⁻¹) = hePartners x := by
  let e : heChain.originalSubgroup ≃ heChain.originalSubgroup :=
    (MulAut.conj (⟨c, hc⟩ : heChain.originalSubgroup)).toEquiv
  refine (Nat.card_congr (e.subtypeEquiv fun y => ?_)).symm
  have he : ((e y : heChain.originalSubgroup) : Equiv.Perm (Fin 8330)) = c * y * c⁻¹ := rfl
  rw [he, patRel_conj, ← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem hePartners_rep
    {w : List (Array ℕ)} {x : Equiv.Perm (Fin 8330)} (hw : RepW 8330 w x)
    (hx : x ∈ heChain.originalSubgroup) :
    hePartners x = countPair PairHe.bs 7 w PairHe.conds heBlocks := by
  rw [hePartners, countPair_eq]
  exact card_eq_countW heChainArrays (by norm_num) heChain_check.1 he_groups
    (Pr := fun y => orderOf y = 7 ∧ PatRel PairHe.conds x y) fun y yg hy hyP => by
      rw [pairPred, Bool.and_eq_true, ordB_iff he_baseFaithful he_bs_lt hy hyP (by norm_num),
        condsOK_iff he_baseFaithful he_bs_lt hw hy hx hyP (by decide)]
      rfl

@[expose] def heFix (g : Equiv.Perm (Fin 8330)) : ℕ := Nat.card {x : Fin 8330 // g x = x}

theorem countP_fix_of_rep {A : Array ℕ} {g : Equiv.Perm (Fin 8330)} (h : Rep 8330 A g) :
    (List.range 8330).countP (fun i => A[i]! == i) = heFix g := by
  classical
  have e : ∀ x ∈ List.finRange 8330, ((fun i => A[i]! == i) ∘ Fin.val) x = true ↔
      decide (g x = x) = true := fun x _ => by
    rw [Function.comp_apply, h x, beq_iff_eq, decide_eq_true_eq, Fin.val_inj]
  have hu : (Finset.univ : Finset (Fin 8330)).val = (List.finRange 8330 : Multiset (Fin 8330)) :=
    rfl
  rw [← List.map_coe_finRange_eq_range, List.countP_map, List.countP_congr e, heFix,
    Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_def, Finset.filter_val, hu,
    Multiset.filter_coe, Multiset.coe_card, List.countP_eq_length_filter]

theorem heFix_conj (c x : Equiv.Perm (Fin 8330)) : heFix (c * x * c⁻¹) = heFix x := by
  refine Nat.card_congr (c.symm.subtypeEquiv fun y => ?_)
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  constructor
  · intro h
    have := congrArg c.symm h
    simpa using this
  · intro h
    simp [h]

@[expose] def heInvols : List (Equiv.Perm (Fin 8330)) :=
  (enumeration heChain).filter fun h => decide (orderOf h = 2)

theorem mem_heInvols {x : Equiv.Perm (Fin 8330)} :
    x ∈ heInvols ↔ x ∈ heChain.originalSubgroup ∧ orderOf x = 2 := by
  rw [heInvols, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff heChain heChain_valid.1]

theorem heInvols_nodup : heInvols.Nodup :=
  (enumeration_nodup heChain heChain_valid.1).filter _

@[expose] def heE1 : List (Equiv.Perm (Fin 8330)) :=
  (PairHe.closureOf PairHe.wA).1.toList.map (nfElt 8330 heStrongArrs heBase.toArray)

@[expose] def heE2 : List (Equiv.Perm (Fin 8330)) :=
  (PairHe.closureOf PairHe.wT).1.toList.map (nfElt 8330 heStrongArrs heBase.toArray)

theorem he_closure_sizes :
    (PairHe.closureOf PairHe.wA).1.size = 24990 ∧ (PairHe.closureOf PairHe.wT).1.size = 187425 := by
  have h := PairHe.classes.2.2.2
  rw [he_cl_eq] at h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  exact h

theorem heE1_length : heE1.length = 24990 := by
  rw [heE1, List.length_map, Array.length_toList, he_closure_sizes.1]

theorem heE2_length : heE2.length = 187425 := by
  rw [heE2, List.length_map, Array.length_toList, he_closure_sizes.2]

theorem he_closure_conj
    {w : List (Array ℕ)} {x₀ : Equiv.Perm (Fin 8330)}
    (hw : RepW 8330 w x₀) (hx₀ : x₀ ∈ heChain.originalSubgroup)
    (h : closureOK PairHe.levels PairHe.bs PairHe.gens PairHe.gensInv w (PairHe.closureOf w).1
      (PairHe.closureOf w).2.1 (PairHe.closureOf w).2.2 = true) :
    ∀ e ∈ (PairHe.closureOf w).1.toList.map (nfElt 8330 heStrongArrs heBase.toArray),
      ∃ d ∈ heChain.originalSubgroup, e = d * x₀ * d⁻¹ := by
  intro e he
  obtain ⟨nf, hnf, rfl⟩ := List.mem_map.1 he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hnf
  rw [Array.length_toList] at hk
  have := closureOK_spec heChainArrays (chainCheckFacts heChain_check.1) heChain_valid.1
    he_baseFaithful he_bs_lt he_gens hw hx₀ h k hk
  rw [getElem!_pos _ k hk] at this
  obtain ⟨-, d, hd, hde⟩ := this
  exact ⟨d, hd, by simpa [Array.getElem_toList] using hde⟩

theorem heE1_conj :
    ∀ e ∈ heE1, ∃ d ∈ heChain.originalSubgroup, e = d * heGenPerm 0 * d⁻¹ := by
  have h := PairHe.classes.2.1
  rw [he_cl_eq] at h
  exact he_closure_conj repW_hewA (heGenPerm_mem_orig (by norm_num))
    (h (PairHe.wA, PairHe.closureOf PairHe.wA) List.mem_cons_self)

theorem heE2_conj :
    ∀ e ∈ heE2, ∃ d ∈ heChain.originalSubgroup, e = d * heT1 * d⁻¹ := by
  have h := PairHe.classes.2.1
  rw [he_cl_eq] at h
  exact he_closure_conj repW_hewT heT1_mem
    (h (PairHe.wT, PairHe.closureOf PairHe.wT) (List.mem_cons_of_mem _ List.mem_cons_self))

theorem he_conj_orderOf {c x : Equiv.Perm (Fin 8330)} : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

end CFSG.Sporadic.Schreier
