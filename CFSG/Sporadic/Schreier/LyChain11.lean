module

public import CFSG.Sporadic.Schreier.LyWords
public import CFSG.Sporadic.Schreier.LyChainBound
public import CFSG.Sporadic.SchreierLemmas.CentralSchreierLift
public import CFSG.Sporadic.Schreier.LyCheckCover
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.Sporadic.LySchreier

open Native SchreierLemmas

@[expose] def pStar (j : ℕ) (x : Fin 11) : Fin 11 :=
  ⟨(cPerms[j]!)[x.val]! % 11, Nat.mod_lt _ (by norm_num)⟩

@[expose] def pStarInv (j : ℕ) (y : Fin 11) : Fin 11 :=
  ((List.finRange 11).find? fun x => pStar j x = y).getD 0

theorem pStar_pStarInv : ∀ j : Fin 12, ∀ y : Fin 11, pStar j (pStarInv j y) = y := by
  decide +kernel

theorem pStarInv_pStar : ∀ j : Fin 12, ∀ x : Fin 11, pStarInv j (pStar j x) = x := by
  decide +kernel

@[expose] def pPerm (j : ℕ) : Equiv.Perm (Fin 11) :=
  if h : j < 12 then ⟨pStar j, pStarInv j, pStarInv_pStar ⟨j, h⟩, pStar_pStarInv ⟨j, h⟩⟩ else 1

theorem pPerm_apply {j : ℕ} (hj : j < 12) (x : Fin 11) : pPerm j x = pStar j x := by
  simp [pPerm, hj]

@[expose] def pGen (i : Fin 2) : Equiv.Perm (Fin 11) := pPerm i

@[expose] def strongList : List (FreeGroup (Fin 2)) :=
  extendByWords [FreeGroup.of 0, FreeGroup.of 1] cDerivations.toList

@[expose] def strongF (j : ℕ) : FreeGroup (Fin 2) := strongList.getD j 1

theorem cDerivations_length : cDerivations.toList.length = 10 := rfl

theorem derivations_idx : ∀ k < cDerivations.toList.length, ∀ l ∈ cDerivations.toList[k]!,
    letterIdx l < 2 + k := by
  decide +kernel

theorem derivations_perm : ∀ k < cDerivations.toList.length,
    evalWord pPerm cDerivations.toList[k]! = pPerm (2 + k) := by
  decide +kernel

theorem lift_strongF {j : ℕ} (hj : j < 12) : FreeGroup.lift pGen (strongF j) = pPerm j := by
  rw [strongF, strongList, map_getD_extendByWords]
  simp only [List.map_cons, List.map_nil, FreeGroup.lift_apply_of]
  have h10 : cDerivations.size = 10 := rfl
  refine extendByWords_getD_eq _ _ pPerm (fun j hj => ?_) derivations_idx derivations_perm j
    (by simp only [List.length_cons, List.length_nil, Array.length_toList, h10]; omega)
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j <;> rfl

theorem strongF_zero : strongF 0 = FreeGroup.of 0 := by
  rw [strongF, strongList, extendByWords_getD_of_lt _ _ (by simp)]
  rfl

theorem strongF_one : strongF 1 = FreeGroup.of 1 := by
  rw [strongF, strongList, extendByWords_getD_of_lt _ _ (by simp)]
  rfl

@[expose] def chainOrbit (i : ℕ) : Finset (Fin 11) :=
  ((chainOrbits[i]!).map fun n => (⟨n % 11, Nat.mod_lt _ (by norm_num)⟩ : Fin 11)).toFinset

@[expose] def lyChain : SchreierWordChain (Fin 11) 2 where
  strongCount := 12
  le_strongCount := by norm_num
  strong j := strongF j
  strong_original i := by
    fin_cases i
    · exact strongF_zero
    · exact strongF_one
  baseCount := 11
  base i := i
  orbit i := chainOrbit i
  transversal i x := ((twWord i x).map strongF).prod

@[expose] def twPerm (i x : ℕ) : Equiv.Perm (Fin 11) := ((twWord i x).map pPerm).prod

theorem twWord_valid : ∀ i : Fin 11, ∀ x : Fin 11, ∀ j ∈ twWord i x,
    j < 12 ∧ ∀ l : Fin 11, l.val < i.val → pPerm j l = l := by
  decide +kernel

theorem twWord_base : ∀ i : Fin 11, twWord i i = [] := by decide +kernel

theorem twPerm_base : ∀ i : Fin 11, ∀ y ∈ chainOrbit i, twPerm i y i = y := by decide +kernel

theorem chain_base_mem : ∀ i : Fin 11, i ∈ chainOrbit i := by decide +kernel

theorem chain_orbit_closed : ∀ i : Fin 11, ∀ x ∈ chainOrbit i, ∀ j : Fin 12,
    (∀ l : Fin 11, l.val < i.val → pPerm j l = l) → pPerm j x ∈ chainOrbit i := by
  decide +kernel

theorem chain_no_terminal : ∀ j : Fin 12, ¬∀ l : Fin 11, pPerm j l = l := by decide +kernel

theorem chain_orbit_card : ∏ i ∈ Finset.range 11, (chainOrbit i).card = 19958400 := by
  decide +kernel

theorem lift_strong (j : Fin lyChain.strongCount) :
    FreeGroup.lift pGen (lyChain.strong j) = pPerm j :=
  lift_strongF j.2

theorem lift_transversal {i : Fin lyChain.baseCount} {x : Fin 11} :
    FreeGroup.lift pGen (lyChain.transversal i x) = twPerm i x := by
  change FreeGroup.lift pGen ((twWord i x).map strongF).prod = ((twWord i x).map pPerm).prod
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  exact lift_strongF (twWord_valid i x j hj).1

theorem mem_levelSet {i : ℕ} {j : Fin lyChain.strongCount} :
    j ∈ lyChain.levelSet pGen i ↔ ∀ l : Fin 11, l.val < i → pPerm j l = l := by
  change (∀ l : Fin 11, l.val < i → FreeGroup.lift pGen (lyChain.strong j) l = l) ↔ _
  rw [lift_strong]

theorem transversal_mem (i : Fin lyChain.baseCount) (x : Fin 11) :
    lyChain.transversal i x ∈ lyChain.levelSubgroup pGen i := by
  change ((twWord i x).map strongF).prod ∈ _
  apply Subgroup.list_prod_mem
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
  obtain ⟨hj12, hfix⟩ := twWord_valid i x j hj
  exact Subgroup.subset_closure ⟨⟨j, hj12⟩, mem_levelSet.2 hfix, rfl⟩

theorem transversal_base (i : Fin lyChain.baseCount) :
    FreeGroup.lift pGen (lyChain.transversal i (lyChain.base i)) (lyChain.base i) =
      lyChain.base i := by
  change FreeGroup.lift pGen ((twWord i i).map strongF).prod i = i
  rw [twWord_base i]
  rfl

theorem chain_hbase (i : Fin lyChain.baseCount) : lyChain.base i ∈ lyChain.orbit i :=
  chain_base_mem i

theorem chain_horbit (i : Fin lyChain.baseCount) (x : Fin 11) (hx : x ∈ lyChain.orbit i)
    (j : Fin lyChain.strongCount) (hj : j ∈ lyChain.levelSet pGen i) :
    FreeGroup.lift pGen (lyChain.strong j) x ∈ lyChain.orbit i := by
  rw [lift_strong]
  exact chain_orbit_closed i x hx j (mem_levelSet.1 hj)

theorem chain_htermZ {G : Type*} [Group G] (c : Fin 2 → G) (Z : Subgroup G) :
    ∀ j ∈ lyChain.levelSet pGen lyChain.baseCount, FreeGroup.lift c (lyChain.strong j) ∈ Z := by
  intro j hj
  exact absurd (fun l => (mem_levelSet.1 hj) l l.2) (chain_no_terminal j)

theorem sign_eq_one_of_swaps (L : List (Fin 11 × Fin 11)) (hne : ∀ t ∈ L, t.1 ≠ t.2)
    (hev : Even L.length) : Equiv.Perm.sign (L.map fun t => Equiv.swap t.1 t.2).prod = 1 := by
  rw [map_list_prod, List.map_map]
  have : (L.map (Equiv.Perm.sign ∘ fun t => Equiv.swap t.1 t.2)) = L.map fun _ => -1 :=
    List.map_congr_left fun t ht => by simp [Equiv.Perm.sign_swap (hne t ht)]
  rw [this, List.map_const', List.prod_replicate, hev.neg_one_pow]

@[expose] def pGen0Swaps : List (Fin 11 × Fin 11) :=
  [(1, 7), (1, 4), (1, 5), (1, 10), (1, 2), (1, 9)]

@[expose] def pGen1Swaps : List (Fin 11 × Fin 11) :=
  [(0, 8), (0, 9), (0, 4), (0, 5), (0, 2), (1, 3), (1, 10), (6, 7)]

theorem pGen0_eq : pGen 0 = (pGen0Swaps.map fun t => Equiv.swap t.1 t.2).prod := by
  decide +kernel

theorem pGen1_eq : pGen 1 = (pGen1Swaps.map fun t => Equiv.swap t.1 t.2).prod := by
  decide +kernel

theorem pGen_mem_alternating (i : Fin 2) : pGen i ∈ alternatingGroup (Fin 11) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  fin_cases i
  · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, pGen0_eq]
    exact sign_eq_one_of_swaps _ (by decide +kernel) ⟨3, rfl⟩
  · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, pGen1_eq]
    exact sign_eq_one_of_swaps _ (by decide +kernel) ⟨4, rfl⟩

theorem card_alternating_eleven : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem twPerm_fix : ∀ i x l : Fin 11, l.val < i.val → twPerm i x l = l := by decide +kernel

theorem closure_pGen_eq : Subgroup.closure (Set.range pGen) = alternatingGroup (Fin 11) := by
  have hle : Subgroup.closure (Set.range pGen) ≤ alternatingGroup (Fin 11) :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact pGen_mem_alternating i)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_alternating_eleven, ← chain_orbit_card]
  apply prod_card_le_card_of_witnesses _
    (fun i => (⟨i % 11, Nat.mod_lt _ (by norm_num)⟩ : Fin 11))
  intro i hi y hy
  have hi' : i < 11 := hi
  have hb : ∀ l (hl : l < 11), (⟨l % 11, Nat.mod_lt _ (by norm_num)⟩ : Fin 11) = ⟨l, hl⟩ :=
    fun l hl => Fin.ext (Nat.mod_eq_of_lt hl)
  refine ⟨twPerm i y, ?_, fun l hl => ?_, ?_⟩
  · rw [← FreeGroup.range_lift_eq_closure]
    exact ⟨lyChain.transversal ⟨i, hi'⟩ y, lift_transversal⟩
  · rw [Equiv.Perm.smul_def, hb l (by omega)]
    exact twPerm_fix ⟨i, hi'⟩ y ⟨l, by omega⟩ hl
  · rw [Equiv.Perm.smul_def, hb i hi']
    exact twPerm_base ⟨i, hi'⟩ y hy

theorem ofFn_get! {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

@[expose] def RepP (P : Array ℕ) (π : Equiv.Perm (Fin 11)) : Prop :=
  ∀ x : Fin 11, P[x.val]! = (π x).val

theorem RepP.eq {P : Array ℕ} {π ρ : Equiv.Perm (Fin 11)} (hπ : RepP P π) (hρ : RepP P ρ) :
    π = ρ := by
  ext x
  rw [← hπ x, ← hρ x]

theorem repP_id11 : RepP id11 1 := by
  intro x
  rw [id11, ofFn_get! _ x.isLt]
  rfl

theorem RepP.comp {P Q : Array ℕ} {π ρ : Equiv.Perm (Fin 11)} (hP : RepP P π) (hQ : RepP Q ρ) :
    RepP (compP P Q) (π * ρ) := by
  intro x
  rw [compP, ofFn_get! _ x.isLt]
  simp only
  rw [hQ x, hP (ρ x)]
  rfl

theorem cPerms_lt : ∀ j : Fin 12, ∀ x : Fin 11, (cPerms[j.val]!)[x.val]! < 11 := by
  decide +kernel

theorem repP_pArr {j : ℕ} (hj : j < 12) : RepP (pArr j) (pPerm j) := by
  intro x
  rw [pPerm_apply hj, pStar, pArr]
  exact (Nat.mod_eq_of_lt (cPerms_lt ⟨j, hj⟩ x)).symm

theorem repP_foldl (L : List ℕ) (hL : ∀ j ∈ L, j < 12) {P : Array ℕ} {π : Equiv.Perm (Fin 11)}
    (hP : RepP P π) : RepP (L.foldl (fun P j => compP P (pArr j)) P) (π * (L.map pPerm).prod) := by
  induction L generalizing P π with
  | nil => simpa using hP
  | cons j L ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih (fun j' hj' => hL j' (List.mem_cons_of_mem _ hj'))
      (hP.comp (repP_pArr (hL j List.mem_cons_self)))

theorem repP_tPArr (i x : Fin 11) : RepP (tPArr i x) (twPerm i x) := by
  have := repP_foldl (twWord i x) (fun j hj => (twWord_valid i x j hj).1) repP_id11
  rwa [one_mul] at this

theorem RepP.inv_of_check {P Q : Array ℕ} {π : Equiv.Perm (Fin 11)} (hP : RepP P π)
    (hc : compP P Q = id11) (hQ : ∀ y : Fin 11, Q[y.val]! < 11) : RepP Q π⁻¹ := by
  intro y
  have e := congrArg (fun A : Array ℕ => A[y.val]!) hc
  simp only [compP, id11, ofFn_get! _ y.isLt] at e
  have h1 := hP ⟨Q[y.val]!, hQ y⟩
  rw [e] at h1
  have : π ⟨Q[y.val]!, hQ y⟩ = y := Fin.ext h1.symm
  have hq : π⁻¹ y = ⟨Q[y.val]!, hQ y⟩ := by rw [Equiv.Perm.inv_eq_iff_eq]; exact this.symm
  rw [hq]

end CFSG.Sporadic.LySchreier
