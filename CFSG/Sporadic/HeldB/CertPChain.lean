module

public import CFSG.Sporadic.HeldB.CertPChainCheck
public import CFSG.Certificates.NativeSchreierCard
public import Mathlib.Tactic.IntervalCases

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def heGenPerm (k : ℕ) : Equiv.Perm (Fin 8330) := permOfArr 8330 (heGen k)

@[expose] def heStrongPerm (j : ℕ) : Equiv.Perm (Fin 8330) := permOfArr 8330 (heStrong j)

theorem heGenArrs_get {k : ℕ} (hk : k < 2) : heGenArrs[k]! = heGen k := by
  rw [heGenArrs, getElem!_pos _ k (by simp [hk]), Array.getElem_ofFn]

theorem heStrongArrs_get {j : ℕ} (hj : j < 9) : heStrongArrs[j]! = heStrong j := by
  rw [heStrongArrs, getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn]

theorem rep_heGen
    {k : ℕ} (hk : k < 2) : Rep 8330 (heGen k) (heGenPerm k) := by
  have h : isInvA 8330 heGenArrs[k]! (invCand 8330 heGenArrs[k]!) = true := by
    interval_cases k
    · exact heChain_check.2.2.1
    · exact heChain_check.2.2.2
  rw [heGenArrs_get hk] at h
  exact (rep_permOfArr h).1

theorem rep_heGen_inv {k : ℕ} (hk : k < 2) :
    Rep 8330 (invCand 8330 (heGen k)) (heGenPerm k)⁻¹ := by
  have h : isInvA 8330 heGenArrs[k]! (invCand 8330 heGenArrs[k]!) = true := by
    interval_cases k
    · exact heChain_check.2.2.1
    · exact heChain_check.2.2.2
  rw [heGenArrs_get hk] at h
  exact (rep_permOfArr h).2

theorem heChain_facts :
    ChainCheckFacts 8330 heGenArrs heStrongArrs heBase.toArray heWords 4 :=
  chainCheckFacts heChain_check.1

theorem rep_heStrong
    {j : ℕ} (hj : j < 9) : Rep 8330 (heStrong j) (heStrongPerm j) := by
  have hj' : j < heStrongArrs.size := by simpa [heStrongArrs] using hj
  have h := heChain_facts.strong_inv j hj'
  rw [rawInvs, getElem!_pos (heStrongArrs.map (invCand 8330)) j (by simpa using hj'),
    Array.getElem_map, ← getElem!_pos heStrongArrs j hj', heStrongArrs_get hj] at h
  exact (rep_permOfArr h).1

@[expose] def heChain : RawSchreierDatum 8330 where
  degree_pos := by decide
  originalCount := 2
  strongCount := 9
  baseCount := 5
  originalCount_le := by decide
  original := Vector.ofFn fun k : Fin 2 => heGenPerm k
  strong := Vector.ofFn fun j : Fin 9 => heStrongPerm j
  base := #v[0, 1, 2, 3, 4]
  base_distinct := by decide
  derivation j _ := toLetters j.val heWords[(j : ℕ)]!

@[expose, irreducible] def heP : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure {heGenPerm 0, heGenPerm 1}

theorem heChain_original_get (k : Fin heChain.originalCount) :
    heChain.original.get k = heGenPerm k := by
  change (Vector.ofFn fun k : Fin 2 => heGenPerm k).get k = heGenPerm k
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

theorem heChain_strong_get (j : Fin heChain.strongCount) :
    heChain.strong.get j = heStrongPerm j := by
  change (Vector.ofFn fun j : Fin 9 => heStrongPerm j).get j = heStrongPerm j
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

theorem heChain_original_toList : heChain.original.toList = [heGenPerm 0, heGenPerm 1] := by
  change (Vector.ofFn fun k : Fin 2 => heGenPerm k).toList = _
  rw [Vector.toList_ofFn, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

theorem heP_eq_originalSubgroup : heP = heChain.originalSubgroup := by
  rw [heP, RawSchreierDatum.originalSubgroup, heChain_original_toList]
  congr 1
  ext g
  simp

theorem heChain_base_toList : heChain.base.toList.map Fin.val = heBase := by decide

theorem heChainArrays :
    ChainArrays heChain heGenArrs heStrongArrs heBase.toArray heWords where
  orig_size := by simp [heGenArrs]; rfl
  strong_size := by simp [heStrongArrs]; rfl
  base_size := rfl
  orig k := by
    have hk : (k : ℕ) < 2 := k.2
    rw [heGenArrs_get hk, heChain_original_get]
    exact rep_heGen hk
  strong j := by
    have hj : (j : ℕ) < 9 := j.2
    rw [heStrongArrs_get hj, heChain_strong_get]
    exact rep_heStrong hj
  base_val i := by
    have hi : (i : ℕ) < 5 := i.2
    change (((#v[0, 1, 2, 3, 4] : Vector (Fin 8330) 5).get ⟨i, hi⟩ : Fin 8330) : ℕ) =
      heBase.toArray[(i : ℕ)]!
    obtain ⟨i, hi⟩ := i
    revert i
    decide
  deriv _ _ := rfl

theorem heChain_valid :
    ValidSchreier heChain ∧ ∀ i : Fin heChain.baseCount,
    heChain.orbitSize i = ((rawLevels 8330 heStrongArrs heBase.toArray)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK heChainArrays (by norm_num) heChain_check.1

theorem heChain_orbitSizes :
    (List.finRange heChain.baseCount).map heChain.orbitSize = [8330, 4480, 3, 18, 2] := by
  have h := heChain_check.2.1
  rw [rawOrbitSizes] at h
  rw [← h]
  apply List.ext_getElem
  · simp [rawLevels, heBase]
    rfl
  · intro k h1 h2
    have hk : k < (rawLevels 8330 heStrongArrs heBase.toArray).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [heChain_valid.2]
    show ((rawLevels 8330 heStrongArrs heBase.toArray)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem heChain_orbitSize (i : Fin heChain.baseCount) :
    heChain.orbitSize i = [8330, 4480, 3, 18, 2][(i : ℕ)]! := by
  rw [← heChain_orbitSizes]
  rw [getElem!_pos _ (i : ℕ) (by simp)]
  simp

theorem card_heP : Nat.card heP = 4030387200 := by
  rw [heP_eq_originalSubgroup,
    card_originalSubgroup_of_chainOK heChainArrays (by norm_num) heChain_check.1,
    heChain_check.2.1]
  rfl

theorem mem_heP_iff_siftA
    {g : Array ℕ} {G : Equiv.Perm (Fin 8330)} (hG : Rep 8330 g G) :
    siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0 g = true ↔
      G ∈ heP := by
  rw [heP_eq_originalSubgroup]
  exact siftA_iff_mem_originalSubgroup heChainArrays (by norm_num) heChain_check.1 hG

theorem heGenPerm_mem {k : ℕ} (hk : k < 2) : heGenPerm k ∈ heP := by
  rw [heP]
  interval_cases k
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem eq_one_of_fix_base {g : Equiv.Perm (Fin 8330)} (hg : g ∈ heP)
    (hfix : ∀ b : Fin 8330, (b : ℕ) < 5 → g b = b) : g = 1 := by
  have hQ := heChain_valid.1
  have hmem : g ∈ heChain.levelSubgroup heChain.baseCount := by
    rw [heChain.mem_levelSubgroup_iff hQ heChain.baseCount le_rfl]
    refine ⟨by rwa [← heP_eq_originalSubgroup], fun b hb => hfix b ?_⟩
    rw [List.take_of_length_le (by simp)] at hb
    have hb' : (b : ℕ) ∈ heChain.base.toList.map Fin.val := List.mem_map_of_mem hb
    rw [heChain_base_toList] at hb'
    simp only [heBase, List.mem_cons, List.not_mem_nil, or_false] at hb'
    omega
  rw [heChain.levelSubgroup_terminal_eq_bot hQ] at hmem
  exact hmem

theorem heP_orbit_zero :
    MulAction.orbit heP (0 : Fin 8330) = Set.univ := by
  rw [heP_eq_originalSubgroup]
  have h0 : (0 : ℕ) < heChain.baseCount := by decide
  have horb := RawSchreierDatum.orbitPoints_eq_orbit heChain ⟨0, h0⟩
  rw [RawSchreierDatum.levelSubgroup_zero_eq_original heChain heChain_valid.1] at horb
  have hcard : Nat.card (heChain.orbitPoints ⟨0, h0⟩) = 8330 := by
    rw [← RawSchreierDatum.orbitSize_eq_card, heChain_orbitSize]
    rfl
  rw [horb, show heChain.base.get ⟨0, h0⟩ = 0 from rfl] at hcard
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq, hcard]

theorem heP_pretransitive :
    MulAction.IsPretransitive heP (Fin 8330) := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ MulAction.orbit heP (0 : Fin 8330) := by rw [heP_orbit_zero]; trivial
  have hy : y ∈ MulAction.orbit heP (0 : Fin 8330) := by rw [heP_orbit_zero]; trivial
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

end CFSG.Sporadic.HeldB
