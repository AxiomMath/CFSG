module

public import CFSG.Monster.B.Co2.ChainSpec

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open Native CFSG.Certificates

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits

abbrev lbArr : Array ℕ := (orbitLabel 2300 chainOrbits).1

abbrev psArr : Array ℕ := (orbitLabel 2300 chainOrbits).2

abbrev recArr : Array (Array ℕ × Array ℕ × Array ℕ) :=
  chainOrbits.map fun o => orbitRecord 2300 o[0]! stabGens

structure StabFacts : Prop where
  base0 : chainBase[0]! = 0
  first0 : (chainOrbits[0]!)[0]! = 0
  idx_lt : ∀ k < chainStabIdx.size, chainStabIdx[k]! < 20
  idx_mono : ∀ k, k + 1 < chainStabIdx.size → chainStabIdx[k]! < chainStabIdx[k + 1]!
  idx_iff : ∀ j < 20, ((chainStrong[j]!)[0]! = 0 ↔ chainStabIdx.contains j = true)
  orbs_size : chainOrbits.size = 3
  recs_size : recArr.size = 3
  size : ∀ t < 3, chainOrbits[t]!.size = chainOrbitSizes[t]!
  size_pos : ∀ t < 3, 0 < chainOrbitSizes[t]!
  mem_lt : ∀ t < 3, ∀ k < chainOrbitSizes[t]!, (chainOrbits[t]!)[k]! < 2300
  mem_lb : ∀ t < 3, ∀ k < chainOrbitSizes[t]!, lbArr[(chainOrbits[t]!)[k]!]! = t
  sorted : ∀ t < 3, ∀ k, k + 1 < chainOrbitSizes[t]! →
    (chainOrbits[t]!)[k]! < (chainOrbits[t]!)[k + 1]!
  lb_lt : ∀ z < 2300, lbArr[z]! < 3
  ps_lt : ∀ z < 2300, psArr[z]! < chainOrbitSizes[lbArr[z]!]!
  ps_eq : ∀ z < 2300, (chainOrbits[lbArr[z]!]!)[psArr[z]!]! = z
  closed : ∀ t < 3, ∀ k < chainOrbitSizes[t]!, ∀ j < stabGens.size,
    (stabGens[j]!)[(chainOrbits[t]!)[k]!]! < 2300 ∧
      lbArr[(stabGens[j]!)[(chainOrbits[t]!)[k]!]!]! = t
  reach : ∀ t < 3, ∀ k < chainOrbitSizes[t]!,
    0 < recArr[t]!.1[(chainOrbits[t]!)[k]!]! ∧
      (recArr[t]!.1[(chainOrbits[t]!)[k]!]! = 1 → (chainOrbits[t]!)[k]! = (chainOrbits[t]!)[0]!) ∧
      (recArr[t]!.1[(chainOrbits[t]!)[k]!]! ≠ 1 →
        recArr[t]!.2.1[(chainOrbits[t]!)[k]!]! < 2300 ∧
        lbArr[recArr[t]!.2.1[(chainOrbits[t]!)[k]!]!]! = t ∧
        recArr[t]!.1[recArr[t]!.2.1[(chainOrbits[t]!)[k]!]!]! + 1 =
          recArr[t]!.1[(chainOrbits[t]!)[k]!]! ∧
        recArr[t]!.2.2[(chainOrbits[t]!)[k]!]! < stabGens.size ∧
        (stabGens[recArr[t]!.2.2[(chainOrbits[t]!)[k]!]!]!)[recArr[t]!.2.1[(chainOrbits[t]!)[k]!]!]! =
          (chainOrbits[t]!)[k]!)

private theorem deg_unit_eq : deg () = 2300 := rfl

private theorem lbArr_eq : (orbitLabel 2300 chainOrbits).1 = lbArr := rfl

private theorem psArr_eq : (orbitLabel 2300 chainOrbits).2 = psArr := rfl

private theorem recArr_eq :
    chainOrbits.map (fun o => orbitRecord 2300 o[0]! stabGens) = recArr := rfl

theorem stabFacts : StabFacts := by
  have h := co2ChainCertOK_eq_true
  simp only [co2ChainCertOK, Bool.and_eq_true] at h
  have h' := h.2
  simp only [stabCheck, orbitsOK, Bool.and_eq_true, beq_iff_eq, deg_unit_eq, and_assoc] at h'
  obtain ⟨c1, c0, c2, c3, c4, o1, o2, o3, o4, o5, o6, o7⟩ := h'
  have hS : chainStrong.size = 20 := chainFacts.strong_size
  refine ⟨c1, c0, fun k hk => ?_, fun k hk => ?_, fun j hj => ?_, o1, ?_, fun t ht => ?_,
    fun t ht => ?_, fun t ht k hk => ?_, fun t ht k hk => ?_, fun t ht k hk => ?_,
    fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun t ht k hk j hj => ?_,
    fun t ht k hk => ?_⟩
  all_goals try rw [← lbArr_eq]
  all_goals try rw [← psArr_eq]
  all_goals try rw [← recArr_eq]
  rotate_left 3
  · exact o3
  rotate_right 3
  · have := of_decide_eq_true (allLt_spec c2 hk)
    rwa [hS] at this
  · exact of_decide_eq_true (allLt_spec c3 (by omega))
  · have := allLt_spec c4 (by rwa [hS] : j < chainStrong.size)
    simp only [beq_iff_eq] at this
    constructor
    · intro h0
      rw [← this]
      simpa using h0
    · intro hc
      rw [← this] at hc
      simpa using hc
  · have := allLt_spec o4 ht
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at this
    exact this.1
  · have := allLt_spec o4 ht
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at this
    exact this.2.1
  · have := allLt_spec o4 ht
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at this
    have := allLt_spec this.2.2.1 hk
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact of_decide_eq_true this.1
  · have := allLt_spec o4 ht
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at this
    have := allLt_spec this.2.2.1 hk
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.2
  · have := allLt_spec o4 ht
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at this
    exact of_decide_eq_true (allLt_spec this.2.2.2 (by omega))
  · have := allLt_spec o5 hz
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact of_decide_eq_true this.1.1
  · have := allLt_spec o5 hz
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact of_decide_eq_true this.1.2
  · have := allLt_spec o5 hz
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.2
  · have := allLt_spec (allLt_spec (allLt_spec o6 ht) hk) hj
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨of_decide_eq_true this.1, this.2⟩
  · have := allLt_spec (allLt_spec o7 ht) hk
    simp only [Bool.and_eq_true] at this
    obtain ⟨hd, hif⟩ := this
    refine ⟨of_decide_eq_true hd, fun h1 => ?_, fun h1 => ?_⟩
    · split at hif
      · exact beq_iff_eq.1 hif
      · exact absurd h1 ‹_›
    · split at hif
      · exact absurd ‹_› h1
      · simp only [Bool.and_eq_true, beq_iff_eq] at hif
        obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hif
        exact ⟨of_decide_eq_true a1, a2, a3, of_decide_eq_true a4, a5⟩

theorem chainStabIdx_size : chainStabIdx.size = 18 := rfl

theorem stabGens_size : stabGens.size = chainStabIdx.size := by
  simp [stabGens]

theorem stabGens_get {j : ℕ} (hj : j < stabGens.size) :
    stabGens[j]! = chainStrong[chainStabIdx[j]!]! := by
  have hj' : j < chainStabIdx.size := by rwa [stabGens_size] at hj
  rw [getElem!_pos stabGens j hj, getElem!_pos chainStabIdx j hj']
  simp [stabGens]

theorem rep_stabGens {j : ℕ} (hj : j < stabGens.size) :
    Rep 2300 stabGens[j]! (strongPerm chainStabIdx[j]!) := by
  rw [stabGens_get hj]
  exact rep_strong (stabFacts.idx_lt j (by rwa [stabGens_size] at hj))

theorem mem_stabIdx_iff (j : ℕ) : j ∈ stabIdx ↔ j ∈ chainStabIdx.toList := Iff.rfl

theorem lt_of_mem_stabIdx {j : ℕ} (hj : j ∈ stabIdx) : j < 20 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
  have hk' : k < chainStabIdx.size := by simpa [stabIdx] using hk
  have := stabFacts.idx_lt k hk'
  rw [getElem!_pos chainStabIdx k hk'] at this
  simpa [stabIdx] using this

theorem mem_stabIdx_iff_fix
    {j : ℕ} (hj : j < 20) : j ∈ stabIdx ↔ strongPerm j 0 = 0 := by
  rw [mem_stabIdx_iff, Array.mem_toList_iff, ← Array.contains_iff_mem, ← stabFacts.idx_iff j hj,
    Fin.ext_iff, ← (rep_strong hj) 0]
  rfl

@[expose] def stabGenSet : Set (Equiv.Perm Ω) := {g | ∃ j ∈ stabIdx, strongPerm j = g}

theorem mem_stabGenSet_of_lt {j : ℕ} (hj : j < stabGens.size) :
    strongPerm chainStabIdx[j]! ∈ stabGenSet := by
  refine ⟨chainStabIdx[j]!, ?_, rfl⟩
  have hj' : j < chainStabIdx.size := by rwa [stabGens_size] at hj
  rw [getElem!_pos chainStabIdx j hj']
  exact Array.getElem_mem_toList hj'

theorem exists_of_mem_stabGenSet {g : Equiv.Perm Ω} (hg : g ∈ stabGenSet) :
    ∃ j < stabGens.size, strongPerm chainStabIdx[j]! = g := by
  obtain ⟨i, hi, rfl⟩ := hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
  have hk' : k < chainStabIdx.size := by simpa [stabIdx] using hk
  refine ⟨k, by rwa [stabGens_size], ?_⟩
  rw [getElem!_pos chainStabIdx k hk']
  simp [stabIdx]

theorem chainQ_originalSubgroup : chainQ.originalSubgroup = Pgrp := by
  rw [RawSchreierDatum.originalSubgroup, Pgrp]
  congr 1
  ext g
  simp [chainQ]

theorem chainQ_base_zero : chainQ.base.get ⟨0, by decide⟩ = 0 := rfl

theorem chainQ_base_take_one : chainQ.base.toList.take 1 = [0] := rfl

theorem levelSubgroup_zero :
    chainQ.levelSubgroup 0 = Pgrp :=
  (chainQ.levelSubgroup_zero_eq_original validSchreier_chainQ).trans chainQ_originalSubgroup

theorem mem_levelSubgroup_one
    {g : Equiv.Perm Ω} :
    g ∈ chainQ.levelSubgroup 1 ↔ g ∈ Pgrp ∧ g 0 = 0 := by
  rw [chainQ.mem_levelSubgroup_iff validSchreier_chainQ 1 (by decide), chainQ_originalSubgroup,
    chainQ_base_take_one]
  simp

theorem levelGenerators_one :
    {s | s ∈ chainQ.levelGenerators 1} = stabGenSet := by
  ext g
  rw [Set.mem_ofPred_eq, levelGenerators_eq (by norm_num), List.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj20 := levelIdx_lt hj
    refine ⟨j, (mem_stabIdx_iff_fix hj20).2 ?_, rfl⟩
    rw [levelIdx, List.mem_filter] at hj
    have hfix := hj.2
    simp only [fixesFirst, allLt_iff, beq_iff_eq] at hfix
    have h0 := hfix 0 (by norm_num)
    rw [stabFacts.base0] at h0
    apply Fin.ext
    rw [← (rep_strong hj20) 0]
    exact h0
  · rintro ⟨j, hj, rfl⟩
    have hj20 := lt_of_mem_stabIdx hj
    refine ⟨j, ?_, rfl⟩
    rw [levelIdx, List.mem_filter, chainFacts.strong_size]
    refine ⟨List.mem_range.2 hj20, ?_⟩
    simp only [fixesFirst, allLt_iff, beq_iff_eq]
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [stabFacts.base0]
    have := congrArg Fin.val ((mem_stabIdx_iff_fix hj20).1 hj)
    rw [← (rep_strong hj20) 0] at this
    exact this

theorem map_stabilizer_eq :
    (MulAction.stabilizer Pgrp (0 : Ω)).map Pgrp.subtype = Pgrp ⊓ MulAction.stabilizer _ (0 : Ω) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, hg0⟩
    exact ⟨⟨g, hg⟩, hg0, rfl⟩

theorem closure_stabGenSet :
    Subgroup.closure stabGenSet = (MulAction.stabilizer Pgrp (0 : Ω)).map Pgrp.subtype := by
  rw [map_stabilizer_eq, ← levelGenerators_one]
  change chainQ.levelSubgroup 1 = _
  ext g
  rw [mem_levelSubgroup_one, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rfl

theorem orbitLengths_prod :
    ∏ i : Fin chainQ.baseCount, Nat.card (chainQ.orbitPoints i) =
    42305421312000 := by
  have e : ∀ i : Fin chainQ.baseCount, Nat.card (chainQ.orbitPoints i) = orbitLengths[i.val]! :=
    fun i => card_orbitPoints i.2
  simp only [e]
  change ∏ i : Fin 10, orbitLengths[i.val]! = _
  rw [Fin.prod_univ_eq_prod_range (fun i => orbitLengths[i]!) 10]
  simp [Finset.prod_range_succ, orbitLengths]

theorem natCard_Pgrp :
    Nat.card Pgrp = 42305421312000 := by
  rw [← chainQ_originalSubgroup, chainQ.original_card_eq_orbit_product validSchreier_chainQ,
    orbitLengths_prod]

theorem orbit_Pgrp_zero :
    MulAction.orbit Pgrp (0 : Ω) = Set.univ := by
  have h1 := chainQ.orbitPoints_eq_orbit ⟨0, by decide⟩
  have h2 := card_orbitPoints (i := 0) (by norm_num)
  change chainQ.orbitPoints ⟨0, _⟩ = MulAction.orbit (chainQ.levelSubgroup 0) (chainQ.base.get _)
    at h1
  rw [levelSubgroup_zero, chainQ_base_zero] at h1
  rw [h1] at h2
  rw [Set.eq_univ_iff_ncard, ← Nat.card_coe_set_eq, h2]
  simp [orbitLengths]

instance isPretransitive_Pgrp :
    MulAction.IsPretransitive Pgrp Ω := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ MulAction.orbit Pgrp (0 : Ω) := by rw [orbit_Pgrp_zero]; trivial
  have hy : y ∈ MulAction.orbit Pgrp (0 : Ω) := by rw [orbit_Pgrp_zero]; trivial
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

theorem natCard_stabilizer_Pgrp :
    Nat.card (MulAction.stabilizer Pgrp (0 : Ω)) = 18393661440 := by
  have h := (MulAction.stabilizer Pgrp (0 : Ω)).card_mul_index
  have hΩ : Nat.card Ω = 2300 := by simp [Ω]
  rw [MulAction.index_stabilizer_of_transitive, natCard_Pgrp, hΩ] at h
  have h2 : Nat.card (MulAction.stabilizer Pgrp (0 : Ω)) * 2300 = 18393661440 * 2300 := by
    rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

@[expose] def stabOrbitRoot (t : ℕ) : Ω := toFin (stabOrbit t)[0]!

theorem stabOrbit_length
    {t : ℕ} (ht : t < 3) : (stabOrbit t).length = chainOrbitSizes[t]! := by
  rw [stabOrbit, Array.length_toList, stabFacts.size t ht]

theorem stabOrbit_getElem! {t k : ℕ} : (stabOrbit t)[k]! = (chainOrbits[t]!)[k]! := by
  rw [stabOrbit, Array.getElem!_toList]

theorem mem_stabOrbit_iff {t : ℕ} (ht : t < 3) {z : ℕ} :
    z ∈ stabOrbit t ↔ z < 2300 ∧ lbArr[z]! = t := by
  constructor
  · intro hz
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
    have hk' : k < chainOrbitSizes[t]! := by rwa [← stabOrbit_length ht]
    have e : (stabOrbit t)[k] = (chainOrbits[t]!)[k]! := by
      rw [← stabOrbit_getElem!, getElem!_pos (stabOrbit t) k hk]
    rw [e]
    exact ⟨stabFacts.mem_lt t ht k hk', stabFacts.mem_lb t ht k hk'⟩
  · rintro ⟨hz, hl⟩
    have h1 := stabFacts.ps_eq z hz
    have h2 := stabFacts.ps_lt z hz
    rw [hl] at h1 h2
    rw [← h1, ← stabOrbit_getElem!, getElem!_pos (stabOrbit t) _ (by rwa [stabOrbit_length ht])]
    exact List.getElem_mem _

theorem stabOrbit_cover
    (z : ℕ) (hz : z < 2300) : ∃ t < 3, z ∈ stabOrbit t :=
  ⟨lbArr[z]!, stabFacts.lb_lt z hz, (mem_stabOrbit_iff (stabFacts.lb_lt z hz)).2 ⟨hz, rfl⟩⟩

@[expose] def stabOrbitSet (t : ℕ) : Set Ω := {x | (x : ℕ) ∈ stabOrbit t}

theorem stabOrbitRoot_mem
    {t : ℕ} (ht : t < 3) : stabOrbitRoot t ∈ stabOrbitSet t := by
  have hpos := stabFacts.size_pos t ht
  have h0 := stabFacts.mem_lt t ht 0 hpos
  rw [stabOrbitSet, Set.mem_ofPred_eq, stabOrbitRoot, stabOrbit_getElem!, toFin_val h0,
    mem_stabOrbit_iff ht]
  exact ⟨h0, stabFacts.mem_lb t ht 0 hpos⟩

theorem stabGenSet_smul_mem
    {t : ℕ} (ht : t < 3) {g : Equiv.Perm Ω} (hg : g ∈ stabGenSet)
    {x : Ω} (hx : x ∈ stabOrbitSet t) : g • x ∈ stabOrbitSet t := by
  obtain ⟨j, hj, rfl⟩ := exists_of_mem_stabGenSet hg
  rw [stabOrbitSet, Set.mem_ofPred_eq, mem_stabOrbit_iff ht] at hx ⊢
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem ((mem_stabOrbit_iff ht).2 hx)
  have hk' : k < chainOrbitSizes[t]! := by rwa [← stabOrbit_length ht]
  have e : (x : ℕ) = (chainOrbits[t]!)[k]! := by
    rw [← hkx, ← stabOrbit_getElem!, getElem!_pos (stabOrbit t) k hk]
  obtain ⟨hlt, hlb⟩ := stabFacts.closed t ht k hk' j hj
  rw [← e, (rep_stabGens hj).apply x.2] at hlt hlb
  refine ⟨(Equiv.Perm.smul_def _ x).symm ▸ hlt, ?_⟩
  rw [Equiv.Perm.smul_def]
  exact hlb

theorem smul_mem_orbit_closure_aux
    {S : Set (Equiv.Perm Ω)} {s : Equiv.Perm Ω} (hs : s ∈ S)
    {x y : Ω} (hy : y ∈ MulAction.orbit (Subgroup.closure S) x) :
    s • y ∈ MulAction.orbit (Subgroup.closure S) x :=
  MulAction.mem_orbit_of_mem_orbit (⟨s, Subgroup.subset_closure hs⟩ : Subgroup.closure S) hy

theorem orbit_subset_stabOrbitSet {t : ℕ} (ht : t < 3) :
    MulAction.orbit (Subgroup.closure stabGenSet) (stabOrbitRoot t) ⊆ stabOrbitSet t := by
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  exact CFSG.Perm.smul_mem_of_finite_of_mem_closure (Set.toFinite _)
    (fun s hs x hx => stabGenSet_smul_mem ht hs hx) hg (stabOrbitRoot_mem ht)

theorem stabOrbitSet_subset_orbit
    {t : ℕ} (ht : t < 3) :
    stabOrbitSet t ⊆ MulAction.orbit (Subgroup.closure stabGenSet) (stabOrbitRoot t) := by
  intro x hx
  suffices key : ∀ d, ∀ k < chainOrbitSizes[t]!,
      recArr[t]!.1[(chainOrbits[t]!)[k]!]! = d →
        toFin (chainOrbits[t]!)[k]! ∈ MulAction.orbit (Subgroup.closure stabGenSet) (stabOrbitRoot t) by
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
    have hk' : k < chainOrbitSizes[t]! := by rwa [← stabOrbit_length ht]
    have e : x = toFin (chainOrbits[t]!)[k]! := by
      apply Fin.ext
      rw [toFin_val (stabFacts.mem_lt t ht k hk'), ← stabOrbit_getElem!,
        getElem!_pos (stabOrbit t) k hk, hkx]
    rw [e]
    exact key _ k hk' rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hk hd
    obtain ⟨hd0, h1, h2⟩ := stabFacts.reach t ht k hk
    by_cases hd1 : recArr[t]!.1[(chainOrbits[t]!)[k]!]! = 1
    · rw [h1 hd1]
      have : toFin (chainOrbits[t]!)[0]! = stabOrbitRoot t := by
        rw [stabOrbitRoot, stabOrbit_getElem!]
      rw [this]
      exact MulAction.mem_orbit_self _
    · obtain ⟨hp, hpl, hdep, hj, himg⟩ := h2 hd1
      set p := recArr[t]!.2.1[(chainOrbits[t]!)[k]!]! with hpdef
      have hpm : p ∈ stabOrbit t := (mem_stabOrbit_iff ht).2 ⟨hp, hpl⟩
      obtain ⟨kp, hkp, hkpe⟩ := List.getElem_of_mem hpm
      have hkp' : kp < chainOrbitSizes[t]! := by rwa [← stabOrbit_length ht]
      have epk : (chainOrbits[t]!)[kp]! = p := by
        rw [← stabOrbit_getElem!, getElem!_pos (stabOrbit t) kp hkp, hkpe]
      have ihp := ih (recArr[t]!.1[p]!) (by omega) kp hkp' (by rw [epk])
      rw [epk] at ihp
      set j := recArr[t]!.2.2[(chainOrbits[t]!)[k]!]! with hjdef
      have hsm := smul_mem_orbit_closure_aux (mem_stabGenSet_of_lt hj) ihp
      have e : strongPerm chainStabIdx[j]! • toFin p = toFin (chainOrbits[t]!)[k]! := by
        apply Fin.ext
        rw [Equiv.Perm.smul_def, ← (rep_stabGens hj).apply (toFin p).2, toFin_val hp,
          toFin_val (stabFacts.mem_lt t ht k hk), himg]
      rw [← e]
      exact hsm

theorem orbit_closure_eq
    {t : ℕ} (ht : t < 3) :
    MulAction.orbit (Subgroup.closure stabGenSet) (stabOrbitRoot t) = stabOrbitSet t :=
  (orbit_subset_stabOrbitSet ht).antisymm (stabOrbitSet_subset_orbit ht)

theorem mem_orbit_stabilizer_iff
    {x y : Ω} :
    y ∈ MulAction.orbit (MulAction.stabilizer Pgrp (0 : Ω)) x ↔
      y ∈ MulAction.orbit (Subgroup.closure stabGenSet) x := by
  rw [closure_stabGenSet]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g.1.1, ⟨g, g.2, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨g, ⟨h, hh, rfl⟩⟩, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem orbit_stabilizer_eq
    {t : ℕ} (ht : t < 3) :
    MulAction.orbit (MulAction.stabilizer Pgrp (0 : Ω)) (stabOrbitRoot t) = stabOrbitSet t := by
  rw [← orbit_closure_eq ht]
  ext y
  exact mem_orbit_stabilizer_iff

theorem stabOrbit_nodup
    {t : ℕ} (ht : t < 3) : (stabOrbit t).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hj' : j < chainOrbitSizes[t]! := by rwa [← stabOrbit_length ht]
  have key : ∀ d, ∀ i, i + d + 1 < chainOrbitSizes[t]! →
      (chainOrbits[t]!)[i]! < (chainOrbits[t]!)[i + d + 1]! := by
    intro d
    induction d with
    | zero => intro i hi; exact stabFacts.sorted t ht i hi
    | succ d ih =>
      intro i hi
      exact lt_trans (ih i (by omega)) (stabFacts.sorted t ht (i + d + 1) (by omega))
  have := key (j - i - 1) i (by omega)
  rw [show i + (j - i - 1) + 1 = j by omega] at this
  rw [← getElem!_pos (stabOrbit t) i hi, ← getElem!_pos (stabOrbit t) j hj, stabOrbit_getElem!,
    stabOrbit_getElem!]
  exact this

theorem ncard_stabOrbitSet
    {t : ℕ} (ht : t < 3) : (stabOrbitSet t).ncard = (stabOrbit t).length := by
  have hset : stabOrbitSet t = toFin '' {z | z ∈ stabOrbit t} := by
    ext x
    simp only [stabOrbitSet, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hx
      exact ⟨x, hx, Fin.ext (toFin_val x.2)⟩
    · rintro ⟨z, hz, rfl⟩
      rwa [toFin_val ((mem_stabOrbit_iff ht).1 hz).1]
  rw [hset, Set.InjOn.ncard_image]
  · rw [show {z | z ∈ stabOrbit t} = ((stabOrbit t).toFinset : Set ℕ) by ext; simp,
      Set.ncard_coe_finset, List.toFinset_card_of_nodup ((stabOrbit_nodup ht).imp ne_of_lt)]
  · intro a ha b hb hab
    have h1 := congrArg Fin.val hab
    rwa [toFin_val ((mem_stabOrbit_iff ht).1 ha).1, toFin_val ((mem_stabOrbit_iff ht).1 hb).1]
      at h1

theorem stabOrbit_zero : stabOrbit 0 = [0] := by
  have hlen : (stabOrbit 0).length = 1 := by
    rw [stabOrbit_length (by norm_num)]
    rfl
  obtain ⟨z, hz⟩ := List.length_eq_one_iff.1 hlen
  have h0 : (stabOrbit 0)[0]! = 0 := by rw [stabOrbit_getElem!]; exact stabFacts.first0
  rw [hz] at h0 ⊢
  simp only [List.getElem!_cons_zero] at h0
  rw [h0]

theorem native_short_stabilizer_order_and_suborbits :
    ValidSchreier chainQ ∧
    chainQ.base.toList.map Fin.val = [0, 1, 2, 4, 5, 3, 6, 7, 9, 8] ∧
    (List.finRange chainQ.baseCount).map (fun i => Nat.card (chainQ.orbitPoints i)) =
      [2300, 891, 336, 160, 6, 4, 2, 2, 2, 2] ∧
    chainQ.originalSubgroup = Pgrp ∧
    Nat.card Pgrp = 42305421312000 ∧ MulAction.IsPretransitive Pgrp Ω ∧
    Nat.card (MulAction.stabilizer Pgrp (0 : Ω)) = 18393661440 ∧
    (∀ j ∈ stabIdx, j < chainQ.strongCount) ∧
    (∀ j : Fin chainQ.strongCount, (j : ℕ) ∈ stabIdx ↔ chainQ.strong.get j 0 = 0) ∧
    Subgroup.closure {g | ∃ j : Fin chainQ.strongCount, (j : ℕ) ∈ stabIdx ∧ chainQ.strong.get j = g} =
      (MulAction.stabilizer Pgrp (0 : Ω)).map Pgrp.subtype ∧
    stabOrbit 0 = [0] ∧ (List.range 3).map (fun t => (stabOrbit t).length) = [1, 891, 1408] ∧
    (∀ t < 3, (stabOrbit t).Pairwise (· < ·)) ∧
    (∀ x : Ω, ∃ t < 3, (x : ℕ) ∈ stabOrbit t) ∧
    (∀ t < 3, MulAction.orbit (MulAction.stabilizer Pgrp (0 : Ω)) (stabOrbitRoot t) =
      {x : Ω | (x : ℕ) ∈ stabOrbit t}) ∧
    (List.range 3).map (fun t =>
      (MulAction.orbit (MulAction.stabilizer Pgrp (0 : Ω)) (stabOrbitRoot t)).ncard) =
      [1, 891, 1408] := by
  have hlen : (List.range 3).map (fun t => (stabOrbit t).length) = [1, 891, 1408] := by
    rw [List.map_congr_left (fun t ht => stabOrbit_length (List.mem_range.1 ht))]
    decide +kernel
  refine ⟨validSchreier_chainQ, by decide +kernel, ?_, chainQ_originalSubgroup, natCard_Pgrp,
    isPretransitive_Pgrp, natCard_stabilizer_Pgrp, fun j hj => lt_of_mem_stabIdx hj,
    fun j => ?_, ?_, stabOrbit_zero, hlen, fun t ht => stabOrbit_nodup ht,
    fun x => stabOrbit_cover x x.2, fun t ht => orbit_stabilizer_eq ht, ?_⟩
  · rw [List.map_congr_left (fun i _ => card_orbitPoints i.2)]
    decide +kernel
  · have e : chainQ.strong.get j = strongPerm j := chainQ_strong_get j
    rw [e]
    exact mem_stabIdx_iff_fix j.2
  · rw [← closure_stabGenSet]
    congr 1
    ext g
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, (chainQ_strong_get j).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, lt_of_mem_stabIdx hj⟩, hj, chainQ_strong_get _⟩
  · rw [← hlen]
    apply List.map_congr_left
    intro t ht
    rw [orbit_stabilizer_eq (List.mem_range.1 ht), ncard_stabOrbitSet (List.mem_range.1 ht)]

end CFSG.Monster.B.Co2
