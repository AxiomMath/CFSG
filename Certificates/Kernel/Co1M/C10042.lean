
module

public import Mathlib.Data.Finset.Card
public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Monster.GMS.S365Native
public import CFSG.Monster.GMS.S365Facts
public import CFSG.Sporadic.Co1.Module.InvData
public import Certificates.Data.CFSGNative.Co1.S365Coset
public import Certificates.Data.CFSGNative.Co1.S365CentPath
public import CFSG.Monster.GMS.S365CosetInputs
public import Certificates.Kernel.Co1M.K42T0
public import Certificates.Kernel.Co1M.K42T1
public import Certificates.Kernel.Co1M.K42T2
public import Certificates.Kernel.Co1M.K42T3
public import Certificates.Kernel.Co1M.C10037
public import CFSG.Certificates.Kernel.SortTreeSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KC.VecK CFSG.KC.M1F2 CFSG.KD.Co1M CFSG.KC.SortTree CFSG.KLie.CT
  CFSG.KC.BfsT CFSG.KC.Bfs CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365CentNative

theorem lt42 {a b c : ℕ} (h : a < b) (e : b = c) : a < c := e ▸ h

theorem t42_slices : ∀ q < 488, t42S q = true := by
  intro q hq
  by_cases h0 : q < 122
  · exact T42x0.all q h0
  have e : ∀ a, a ≤ q → Nat.add a (q - a) = q := fun a ha => by
    change a + (q - a) = q
    omega
  by_cases h1 : q < 244
  · have := T42x1.all (q - 122) (lt42 (b := 122) (by omega) rfl)
    unfold t42F1 at this
    rwa [e 122 (by omega)] at this
  by_cases h2 : q < 366
  · have := T42x2.all (q - 244) (lt42 (b := 122) (by omega) rfl)
    unfold t42F2 at this
    rwa [e 244 (by omega)] at this
  · have := T42x3.all (q - 366) (lt42 (b := 122) (by omega) rfl)
    unfold t42F3 at this
    rwa [e 366 (by omega)] at this

theorem t42_chunk : ∀ c < 7797, chunkOK act42 3 (fun _ => true) 40 C42tab 498960 24 5 19 64 c =
    true := by
  intro c hc
  have h := t42_slices (c / 16) (by omega)
  unfold t42S t42K at h
  have := (CFSG.KC.SortTree.allN_iff _ _).1 h (c % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (c / 16) 16) (c % 16) = c := by
    change c / 16 * 16 + c % 16 = c
    omega
  rwa [e] at this

theorem t42_tree : treeOK act42 3 (fun _ => true) 40 C42tab 498960 24 5 19 64 7797 = true := by
  unfold treeOK
  rw [CFSG.KC.SortTree.andB_true_iff, CFSG.KC.SortTree.ble_iff, CFSG.KC.SortTree.allN_iff]
  exact ⟨by norm_num, t42_chunk⟩

theorem nIf42 (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem canonK_eq (x y v : Nat) : canonK x y v = canon4 x y v := by
  unfold canonK canon4 minK
  simp only [nIf42, Nat.ble_eq, Nat.min_def]
  rfl

theorem canon4_cases (v : ℕ) :
    ∃ k, (k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) ∧ canon4 2 4 v = v ^^^ k := by
  unfold canon4
  rcases min_choice (min v (v ^^^ 2)) (min (v ^^^ 4) (v ^^^ 2 ^^^ 4)) with h | h
  · rcases min_choice v (v ^^^ 2) with h' | h'
    · exact ⟨0, by simp, by rw [h, h', Nat.xor_zero]⟩
    · exact ⟨2, by simp, by rw [h, h']⟩
  · rcases min_choice (v ^^^ 4) (v ^^^ 2 ^^^ 4) with h' | h'
    · exact ⟨4, by simp, by rw [h, h']⟩
    · exact ⟨6, by simp, by rw [h, h', Nat.xor_assoc]; rfl⟩

theorem xor42_cancel (v k : ℕ) : v ^^^ k ^^^ k = v := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem canon4_xor2 (v : ℕ) : canon4 2 4 (v ^^^ 2) = canon4 2 4 v := by
  unfold canon4
  rw [xor42_cancel]
  omega

theorem canon4_xor4 (v : ℕ) : canon4 2 4 (v ^^^ 4) = canon4 2 4 v := by
  unfold canon4
  have e1 : v ^^^ 4 ^^^ 2 = v ^^^ 2 ^^^ 4 := by
    rw [Nat.xor_assoc, Nat.xor_comm 4 2, ← Nat.xor_assoc]
  rw [xor42_cancel, e1, xor42_cancel]
  omega

theorem canon4_xorK {v k : ℕ} (hk : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) :
    canon4 2 4 (v ^^^ k) = canon4 2 4 v := by
  rcases hk with rfl | rfl | rfl | rfl
  · rw [Nat.xor_zero]
  · exact canon4_xor2 v
  · exact canon4_xor4 v
  · rw [show (6 : ℕ) = 2 ^^^ 4 by decide, ← Nat.xor_assoc, canon4_xor4, canon4_xor2]

theorem fix42K {l k : ℕ} (hl : l < 3) (hk : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) :
    vmF 24 (CFSG.KC.Co1F2.getL 0 [CT0, CT1, CT2] l) k = k := by
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl <;> exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem act42_canon {l : ℕ} (hl : l < 3) (v : ℕ) :
    act42 l (canon4 2 4 v) = canon4 2 4 (vmF 24 (CFSG.KC.Co1F2.getL 0 [CT0, CT1, CT2] l) v) := by
  obtain ⟨k, hk, e⟩ := canon4_cases v
  unfold act42
  rw [canonK_eq, e, CFSG.KC.GmsPath.vmF_xor, fix42K hl hk, canon4_xorK hk]

theorem reach42_word {x : ℕ} (h : Reach act42 3 40 x) : ∃ w : List ℕ, (∀ l ∈ w, l < 3) ∧
    canon4 2 4 (w.foldl (fun acc l => vmF 24 (CFSG.KC.Co1F2.getL 0 [CT0, CT1, CT2] l) acc) 40) =
      x := by
  induction h with
  | root => exact ⟨[], by simp, by decide⟩
  | step l hl _ ih =>
    obtain ⟨w, hw, e⟩ := ih
    refine ⟨w ++ [l], fun l' h' => ?_, ?_⟩
    · rcases List.mem_append.1 h' with h' | h'
      · exact hw l' h'
      · rw [List.mem_singleton.1 h']
        exact hl
    · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← e, act42_canon hl]

theorem valF24_lt (x : ℕ) : valF 24 x < 2 ^ 24 := by
  unfold valF maskN pw2
  change x &&& (1 <<< 24 - 1) < 2 ^ 24
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem tree42_fact : ∃ R : Finset ℕ, R.card = 498960 ∧ ∀ r ∈ R, r < 2 ^ 24 ∧
    ∃ w : List ℕ, (∀ l ∈ w, l < 3) ∧ canon4 2 4 (applyPath cosetRowsT w cosetBase) = r := by
  obtain ⟨hreach, -, hlt, -⟩ := tree_sound t42_tree
  refine ⟨(Finset.range 498960).image fun i => valF 24 (C42tab i), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd e (Nat.ne_of_lt (hlt i j h hj))
    · exact absurd e (Nat.ne_of_gt (hlt j i h hi))
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨w, hw, e⟩ := reach42_word (hreach i (Finset.mem_range.1 hi))
    refine ⟨valF24_lt _, w, hw, ?_⟩
    rw [cosetRowsT_eq, applyPath_eq _ hw]
    exact e

theorem rows42_fix : (cosetRowsT.all fun Mt => isFixedN Mt 2 && isFixedN Mt 4) = true := by
  rw [cosetRowsT_eq, List.all_toArray]
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, isFixedN, vec_unpack]
  quickRfl

theorem pat42 : pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4
    cosetBase = true := by
  rw [pat4_eq]
  quickRfl

theorem c10042_neg :
    notB (chunkOK act42 3 (fun _ => true) 41 C42tab 498960 24 5 19 64 0) = true ∧
    notB (chunkOK (fun l v => act42 (Nat.mod (Nat.add l 1) 3) v) 3 (fun _ => true) 40 C42tab
      498960 24 5 19 64 100) = true :=
  ⟨by quickRfl, by quickRfl⟩

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.S365CentNative in
open Certificates in
theorem c10042 :
    (cosetRowsT.all fun Mt => isFixedN Mt 2 && isFixedN Mt 4) = true ∧
    pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 cosetBase =
      true ∧
    countBelow (pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4)
      16777216 0 = 1995840 ∧
    ∃ R : Finset ℕ, R.card = 498960 ∧ ∀ r ∈ R, r < 2 ^ 24 ∧ ∃ w : List ℕ, (∀ l ∈ w, l < 3) ∧
      canon4 2 4 (applyPath cosetRowsT w cosetBase) = r :=
  ⟨rows42_fix, pat42, count37, tree42_fact⟩

end CertificateChecks.KernelCo1M

end
