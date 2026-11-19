
module

public import CFSG.Sporadic.Co2Schreier.ThirdCheckBase
public import CFSG.Sporadic.Co2Schreier.ChainsBase
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheckBase
public meta import CFSG.Sporadic.Co2Schreier.CoreCheckBase
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

abbrev thL : Array TLev := thirdLevels witRec

abbrev thB : Array ℕ := witRec.third.baseIndices.toArray

structure ThirdFacts : Prop where
  base_size : (thB.size == 13) = true
  base_lt : allLt 13 (fun j => decide (thB[j]! < 2300)) = true
  L_size : (thL.size == 13) = true
  sizes : ((thL.toList.map fun T => T.tr.size) ==
    [2300, 891, 896, 96, 30, 1, 4, 1, 1, 1, 1, 1, 2]) = true
  tr : allLt 13 (fun j => eqA 2300 thL[j]!.tr[0]! (idA 2300) &&
    allLt thL[j]!.tr.size (fun k => isInvA 2300 thL[j]!.tr[k]! (invCand 2300 thL[j]!.tr[k]!) &&
      fixesFirst thB thL[j]!.tr[k]! j &&
      siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 thL[j]!.tr[k]! &&
      allLt k (fun k' => (thL[j]!.tr[k]!)[thB[j]!]! != (thL[j]!.tr[k']!)[thB[j]!]!))) = true
  u_inv : isInvA 2300 uArr (invCand 2300 uArr) = true
  u_fix : fixesFirst thB uArr 12 = true
  dfs : (dfsCnt thL thB uArr 12 13 0 (idA 2300) == 1474560) = true

def tsz (j : ℕ) : ℕ := thL[j]!.tr.size

def bpt (j : ℕ) : Fin 2300 := ⟨thB[j]! % 2300, Nat.mod_lt _ (by norm_num)⟩

def thT (j k : ℕ) : Equiv.Perm (Fin 2300) := permOfArr 2300 thL[j]!.tr[k]!

def stabB (j : ℕ) : Subgroup (Equiv.Perm (Fin 2300)) where
  carrier := {g | g ∈ co2P ∧ ∀ i < j, g (bpt i) = bpt i}
  mul_mem' := fun {a b} ha hb => ⟨co2P.mul_mem ha.1 hb.1, fun i hi => by
    rw [Equiv.Perm.mul_apply, hb.2 i hi, ha.2 i hi]⟩
  one_mem' := ⟨co2P.one_mem, fun _ _ => rfl⟩
  inv_mem' := fun {a} ha => ⟨co2P.inv_mem ha.1, fun i hi => by
    rw [Equiv.Perm.inv_eq_iff_eq, ha.2 i hi]⟩

theorem mem_stabB {j : ℕ} {g : Equiv.Perm (Fin 2300)} :
    g ∈ stabB j ↔ g ∈ co2P ∧ ∀ i < j, g (bpt i) = bpt i := Iff.rfl

theorem stabB_zero : stabB 0 = co2P := by
  ext g
  rw [mem_stabB]
  simp

theorem stabB_succ_le (j : ℕ) : stabB (j + 1) ≤ stabB j := fun _ hg =>
  ⟨hg.1, fun i hi => hg.2 i (by omega)⟩

theorem chain_card_eq {c t : ℕ → ℕ} {n : ℕ} (h : ∀ j < n, t j * c (j + 1) ≤ c j)
    (hn : 1 ≤ c n) (ht : ∀ j < n, 0 < t j) (h0 : c 0 ≤ ∏ j ∈ Finset.range n, t j) :
    ∀ j ≤ n, c j = ∏ i ∈ Finset.Ico j n, t i := by
  have low : ∀ m j, j + m = n → ∏ i ∈ Finset.Ico j n, t i ≤ c j := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [show j = n by omega, Finset.Ico_self, Finset.prod_empty]
      exact hn
    | succ m ih =>
      intro j hj
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega)]
      calc t j * ∏ i ∈ Finset.Ico (j + 1) n, t i ≤ t j * c (j + 1) :=
            Nat.mul_le_mul_left _ (ih (j + 1) (by omega))
        _ ≤ c j := h j (by omega)
  have up : ∀ j ≤ n, (∏ i ∈ Finset.range j, t i) * c j ≤ c 0 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Finset.prod_range_succ, mul_assoc]
      calc (∏ i ∈ Finset.range j, t i) * (t j * c (j + 1)) ≤
            (∏ i ∈ Finset.range j, t i) * c j := Nat.mul_le_mul_left _ (h j (by omega))
        _ ≤ c 0 := ih (by omega)
  intro j hj
  have hpos : 0 < ∏ i ∈ Finset.range j, t i :=
    Finset.prod_pos fun i hi => ht i (by simp at hi; omega)
  have hsplit := Finset.prod_range_mul_prod_Ico t hj
  refine le_antisymm ?_ (low (n - j) j (by omega))
  have h1 := (up j hj).trans h0
  rw [← hsplit] at h1
  exact Nat.le_of_mul_le_mul_left h1 hpos

def prodFrom (k : ℕ → ℕ) : ℕ → ℕ → Equiv.Perm (Fin 2300)
  | 0, _ => 1
  | f + 1, j => thT j (k j) * prodFrom k f (j + 1)

theorem prodFrom_congr {k k' : ℕ → ℕ} : ∀ (f j : ℕ), (∀ i, j ≤ i → k i = k' i) →
    prodFrom k f j = prodFrom k' f j
  | 0, _, _ => rfl
  | f + 1, j, h => by
    rw [prodFrom, prodFrom, h j le_rfl, prodFrom_congr f (j + 1) fun i hi => h i (by omega)]

end CFSG.Sporadic.Co2Schreier
