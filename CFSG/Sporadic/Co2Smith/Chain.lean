module

public import CFSG.Sporadic.Co2Smith.Complement
public import Certificates.Certificate16039
public import CFSG.Sporadic.Co2Smith.OrbitIndex

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

attribute [local instance] vAction

theorem mixLetters_two : mixLetters.elt 2 = aE := rfl

theorem mixLetters_three : mixLetters.elt 3 = bE := rfl

theorem mWord_cons
    (k : ℕ) (w : List ℕ) : mWord (k :: w) = mixLetters.elt k * mWord w := rfl

theorem mWord_nil : mWord [] = 1 := rfl

theorem mWord_mem_S0 :
    ∀ w : List ℕ, (∀ k ∈ w, k = 2 ∨ k = 3) → mWord w ∈ S0
  | [], _ => by rw [mWord_nil]; exact S0.one_mem
  | k :: w, hw => by
    rw [mWord_cons]
    refine S0.mul_mem ?_ (mWord_mem_S0 w fun j hj => hw j (List.mem_cons_of_mem _ hj))
    rcases hw k List.mem_cons_self with rfl | rfl
    · rw [mixLetters_two]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [mixLetters_three]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def chainRows (k : ℕ) : Array (Array ℕ) :=
  Array.map (Native.mRows seedRowsArr) Native.chainGens[k]!

@[expose] def chainRec (k : ℕ) : Array ℕ × Array ℕ × Array ℕ :=
  Native.orbitBFS (Native.vecStep (chainRows k)) (chainRows k).size Native.chainBase[k]! 100

theorem chain_spec {k : ℕ} (hk : k < 6) :
    (∀ j < k, ∀ (i : ℕ) (hi : i < (chainRows k).size),
      Native.colAct (chainRows k)[i] Native.chainBase[j]! = Native.chainBase[j]!) ∧
    (chainRec k).1[0]! = Native.chainBase[k]! ∧
    ∀ i < Native.chainOrb[k]!,
      (Native.posMapN (chainRec k).1).getD (chainRec k).1[i]! (chainRec k).1.size = i ∧
      (i = 0 ∨ ((chainRec k).2.1[i]! < i ∧ (chainRec k).2.2[i]! < (chainRows k).size ∧
        (chainRec k).1[i]! = Native.vecStep (chainRows k) (chainRec k).2.2[i]!
          (chainRec k).1[(chainRec k).2.1[i]!]!)) := by
  have h := chain_check
  simp only [Native.chainOK, Native.treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, decide_eq_true_eq, and_assoc, Array.all_eq_true,
    Bool.not_false, Bool.true_or, and_true] at h
  obtain ⟨-, -, -, h⟩ := h
  obtain ⟨h1, -, -, -, h2, h3⟩ := h k hk
  exact ⟨h1, h2, h3⟩

theorem chainGens_letters :
    ∀ k < 6, ∀ i < (Native.chainGens[k]!).size,
    ∀ x ∈ (Native.chainGens[k]!)[i]!, x = 2 ∨ x = 3 :=
  Certificates.certificate16039

theorem chainBase_lt : ∀ k < 6, Native.chainBase[k]! < 2 ^ 22 := by decide

theorem chainRows_size (k : ℕ) : (chainRows k).size = (Native.chainGens[k]!).size :=
  Array.size_map ..

@[expose] noncomputable def chainElt
    (k i : ℕ) : K := mWord (Native.chainGens[k]!)[i]!

theorem chainElt_mem_S0
    {k i : ℕ} (hk : k < 6) (hi : i < (Native.chainGens[k]!).size) :
    chainElt k i ∈ S0 :=
  mWord_mem_S0 _ (chainGens_letters k hk i hi)

theorem chainElt_val
    {k i : ℕ} (hk : k < 6) (hi : i < (Native.chainGens[k]!).size) :
    (chainElt k i).val.val = rowsMatrix 22 (chainRows k)[i]! := by
  rw [chainRows, getElem!_map_of_lt _ _ hi, chainElt, mWord_val]
  intro x hx
  rcases chainGens_letters k hk i hi x hx with rfl | rfl <;> norm_num

@[expose] noncomputable def chainStab : ℕ → Subgroup K
  | 0 => S0
  | k + 1 => chainStab k ⊓ MulAction.stabilizer K (vec Native.chainBase[k]!)

theorem mem_chainStab {g : K} : ∀ k, g ∈ chainStab k ↔
    g ∈ S0 ∧ ∀ j < k, g • vec Native.chainBase[j]! = vec Native.chainBase[j]!
  | 0 => by simp [chainStab]
  | k + 1 => by
    rw [chainStab, Subgroup.mem_inf, mem_chainStab k, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨⟨hS, hj⟩, hk⟩
      refine ⟨hS, fun j hj' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | rfl
      · exact hj j h
      · exact hk
    · rintro ⟨hS, hj⟩
      exact ⟨⟨hS, fun j h => hj j (Nat.lt_succ_of_lt h)⟩, hj k (Nat.lt_succ_self k)⟩

abbrev chainT (k : ℕ) : Subgroup K :=
  Subgroup.closure {g | ∃ i < (Native.chainGens[k]!).size, chainElt k i = g}

theorem chainT_le
    {k : ℕ} (hk : k < 6) : chainT k ≤ chainStab k := by
  rw [chainT, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [SetLike.mem_coe, mem_chainStab]
  refine ⟨chainElt_mem_S0 hk hi, fun j hj => ?_⟩
  have hi' : i < (chainRows k).size := by rw [chainRows_size]; exact hi
  rw [smul_V_def, mulVec_vec (chainElt_val hk hi), getElem!_pos (chainRows k) i hi',
    (chain_spec hk).1 j hj i hi']

theorem chain_mem_orbit
    {k : ℕ} (hk : k < 6) : ∀ i < Native.chainOrb[k]!,
    vec (chainRec k).1[i]! ∈ MulAction.orbit (chainT k) (vec Native.chainBase[k]!) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, h0, h⟩ := chain_spec hk
    rcases (h i hi).2 with rfl | ⟨hp, hl, heq⟩
    · rw [h0]; exact MulAction.mem_orbit_self _
    · have hl' : (chainRec k).2.2[i]! < (Native.chainGens[k]!).size := by
        rwa [← chainRows_size]
      rw [heq, Native.vecStep, ← rowsMatrix_mulVec_vec, ← chainElt_val hk hl', ← smul_V_def]
      exact smul_mem_orbit_closure (ih _ hp (hp.trans hi)) ⟨_, hl', rfl⟩

theorem chainRec_lt
    {k : ℕ} (hk : k < 6) {i : ℕ} (hi : i < Native.chainOrb[k]!) :
    (chainRec k).1[i]! < 2 ^ 22 := by
  obtain ⟨-, h0, h⟩ := chain_spec hk
  rcases (h i hi).2 with rfl | ⟨-, -, heq⟩
  · rw [h0]; exact chainBase_lt k hk
  · rw [heq, Native.vecStep]; exact colAct_lt _ _

theorem chain_injective {k : ℕ} (hk : k < 6) :
    Function.Injective fun i : Fin Native.chainOrb[k]! => vec (chainRec k).1[(i : ℕ)]! := by
  intro i j hij
  have h := (chain_spec hk).2.2
  have e := vec_injective (chainRec_lt hk i.2) (chainRec_lt hk j.2) hij
  apply Fin.ext
  rw [← (h i i.2).1, ← (h j j.2).1, e]

theorem chain_relIndex
    {k : ℕ} (hk : k < 6) :
    Native.chainOrb[k]! ≤ (chainStab (k + 1)).relIndex (chainStab k) :=
  le_relIndex_of_orbit (chainT_le hk) (vec Native.chainBase[k]!) _ (chain_injective hk)
    fun i => chain_mem_orbit hk i i.2

theorem chainStab_succ_le
    (k : ℕ) : chainStab (k + 1) ≤ chainStab k := inf_le_left

theorem chainStab_le_S0 : ∀ k, chainStab k ≤ S0
  | 0 => le_rfl
  | k + 1 => (chainStab_succ_le k).trans (chainStab_le_S0 k)

theorem relIndex_chainStab_succ (k : ℕ) :
    (chainStab (k + 1)).relIndex S0 =
      (chainStab (k + 1)).relIndex (chainStab k) * (chainStab k).relIndex S0 :=
  (Subgroup.relIndex_mul_relIndex _ _ _ (chainStab_succ_le k) (chainStab_le_S0 k)).symm

theorem relIndex_chainStab_six :
    1451520 ≤ (chainStab 6).relIndex S0 := by
  have h0 : (chainStab 0).relIndex S0 = 1 := Subgroup.relIndex_self _
  rw [relIndex_chainStab_succ, relIndex_chainStab_succ, relIndex_chainStab_succ,
    relIndex_chainStab_succ, relIndex_chainStab_succ, relIndex_chainStab_succ, h0, mul_one]
  have e0 := chain_relIndex (k := 0) (by norm_num)
  have e1 := chain_relIndex (k := 1) (by norm_num)
  have e2 := chain_relIndex (k := 2) (by norm_num)
  have e3 := chain_relIndex (k := 3) (by norm_num)
  have e4 := chain_relIndex (k := 4) (by norm_num)
  have e5 := chain_relIndex (k := 5) (by norm_num)
  rw [show Native.chainOrb[0]! = 63 from rfl] at e0
  rw [show Native.chainOrb[1]! = 32 from rfl] at e1
  rw [show Native.chainOrb[2]! = 15 from rfl] at e2
  rw [show Native.chainOrb[3]! = 8 from rfl] at e3
  rw [show Native.chainOrb[4]! = 3 from rfl] at e4
  rw [show Native.chainOrb[5]! = 2 from rfl] at e5
  calc (1451520 : ℕ) = 2 * (3 * (8 * (15 * (32 * 63)))) := by norm_num
    _ ≤ _ := Nat.mul_le_mul e5 (Nat.mul_le_mul e4 (Nat.mul_le_mul e3 (Nat.mul_le_mul e2
        (Nat.mul_le_mul e1 e0))))

theorem res_spec :
    (∀ j < 6, Native.zetaComb Native.colsA[j]! =
        Native.colAct (Native.mRows seedRowsArr [2]) Native.zetaVecs[j]! ∧
      Native.zetaComb Native.colsB[j]! =
        Native.colAct (Native.mRows seedRowsArr [3]) Native.zetaVecs[j]!) ∧
    ∀ k < 6, ∃ c < 64, Native.zetaComb c = Native.chainBase[k]! := by
  have h := res_check
  simp only [Native.resOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨h1, -, h3⟩ := h
  exact ⟨h1, h3⟩

noncomputable abbrev Zfix :
    Subgroup K := fixingSubgroup K (Zsub : Set V)

theorem mem_Zsub_vec_zetaComb
    (c : ℕ) : vec (Native.zetaComb c) ∈ Zsub := by
  rw [vec_zetaComb]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs
  · exact zetaV_mem i
  · exact Submodule.zero_mem _

theorem chainBase_mem_Zsub
    {k : ℕ} (hk : k < 6) : vec Native.chainBase[k]! ∈ Zsub := by
  obtain ⟨c, -, hc⟩ := res_spec.2 k hk
  rw [← hc]
  exact mem_Zsub_vec_zetaComb c

theorem S0_inf_Zfix_le :
    Zfix ⊓ S0 ≤ chainStab 6 := by
  rintro g ⟨hZ, hS⟩
  rw [mem_chainStab]
  exact ⟨hS, fun j hj => (mem_fixingSubgroup_iff K).mp hZ _ (chainBase_mem_Zsub hj)⟩

theorem card_S0_ge :

    1451520 * Nat.card (Zfix ⊓ S0 : Subgroup K) ≤ Nat.card S0 := by
  have h1 := Subgroup.relIndex_mul_card Zfix S0
  have : (Zfix ⊓ S0).IsFiniteRelIndex S0 := Subgroup.isFiniteRelIndex_of_finiteIndex
  have h2 : (chainStab 6).relIndex S0 ≤ (Zfix ⊓ S0).relIndex S0 :=
    Subgroup.relIndex_le_of_le_left S0_inf_Zfix_le Subgroup.relIndex_ne_zero
  rw [Subgroup.inf_relIndex_right] at h2
  rw [← h1]
  exact Nat.mul_le_mul_right _ (relIndex_chainStab_six.trans h2)

end CFSG.Sporadic.Co2Smith
