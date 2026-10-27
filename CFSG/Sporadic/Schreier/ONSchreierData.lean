module

public import CFSG.Sporadic.Schreier.ONSeparatingBase
public import CFSG.Sporadic.Schreier.ONWordDatum

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Sporadic.ON CFSG.Certificates

@[expose] def baseFin : List (Fin N) :=
  Data.baseList.map fun b => ⟨b % N, Nat.mod_lt _ (by norm_num)⟩

theorem baseFin_nodup : baseFin.Nodup := by
  apply base_facts.2.1.map_on
  intro x hx y hy h
  have h1 := congrArg Fin.val h
  simp only at h1
  rwa [Nat.mod_eq_of_lt (base_facts.2.2 x hx), Nat.mod_eq_of_lt (base_facts.2.2 y hy)] at h1

theorem baseFin_length : baseFin.length = 29 := by
  rw [baseFin, List.length_map, base_facts.1]

theorem two_le_words :
    [a0, a1].length ≤ Data.strongWords.size := by
  show 2 ≤ Data.strongWords.size
  rw [words_facts.1]
  decide

@[expose] def sgen
    (j : ℕ) : Equiv.Perm (Fin N) := wordStrong [a0, a1] Data.strongWords j

@[expose] def QON :
    RawSchreierDatum N :=
  RawSchreierDatum.ofWords N (by norm_num) [a0, a1] Data.strongWords two_le_words baseFin
    baseFin_nodup

@[expose] def beta (i j : Fin N) : ZMod 3 := pairing i j

@[expose] def lineRegs0
    (r : ℕ) : Equiv.Perm (Fin nL) :=
  if r = 1 then d0 else if r = 2 then d1 else 1

@[expose] def lineRegs :
    ℕ → Equiv.Perm (Fin nL) := runProgram lineRegs0 Data.subgroupProgram

@[expose] def lineSubgroup :
    Subgroup (Equiv.Perm (Fin nL)) :=
  Subgroup.closure {lineRegs 1, lineRegs 2}

theorem runProgram_mem {G : Type*} [Group G] (K : Subgroup G) :
    ∀ (prog : List Data.Instr) (regs : ℕ → G), (∀ r, regs r ∈ K) →
      ∀ r, runProgram regs prog r ∈ K
  | [], _, h => h
  | .mu a b c :: rest, regs, h => runProgram_mem K rest _ fun r => by
      by_cases hr : r = c
      · subst hr; simp only [Function.update_self]; exact mul_mem (h a) (h b)
      · rw [Function.update_of_ne hr]; exact h r
  | .iv a b :: rest, regs, h => runProgram_mem K rest _ fun r => by
      by_cases hr : r = b
      · subst hr; simp only [Function.update_self]; exact inv_mem (h a)
      · rw [Function.update_of_ne hr]; exact h r

theorem lineSubgroup_le :
    lineSubgroup ≤ Pl := by
  rw [lineSubgroup, Subgroup.closure_le]
  have hregs : ∀ r, lineRegs r ∈ Pl := runProgram_mem Pl _ _ fun r => by
    unfold lineRegs0
    split_ifs
    · exact d0_mem
    · exact d1_mem
    · exact one_mem _
  rintro _ (rfl | rfl)
  · exact hregs 1
  · exact hregs 2

theorem sgen_mem :
    ∀ j, sgen j ∈ Pv := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < 2
    · rw [sgen, wordStrong_of_lt _ _ (by simpa using hj)]
      interval_cases j
      · exact a0_mem
      · exact a1_mem
    · rw [sgen, wordStrong_of_ge _ _ (by simp; omega)]
      apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
      rintro _ ⟨h, rfl⟩
      exact ih h.val h.isLt

theorem cert_on_schreier_action_data :
    QON.originalCount = 2 ∧ QON.strongCount = 7 ∧ QON.baseCount = 29 ∧
      QON.original.toList = [a0, a1] ∧
      (∀ j : Fin QON.strongCount, QON.strong.get j = sgen j) ∧
      sgen 0 = a0 ∧ sgen 1 = a1 ∧
      (∀ j, 2 ≤ j → sgen j = Quiver.SchreierGraph.evalWord (fun h : Fin j => sgen h)
        (ptoLetters j Data.strongWords[j]!)) ∧
      (∀ i : Fin QON.baseCount, ((QON.base.get i : Fin N) : ℕ) = baseIndex i) ∧
      (∀ (j : Fin QON.strongCount) (hj : QON.originalCount ≤ j.val),
        QON.derivation j hj = ptoLetters j.val Data.strongWords[j.val]!) ∧
      (∀ j, sgen j ∈ Pv) ∧ (∀ i j : Fin N, beta i j = pairing i j) ∧
      lineSubgroup = Subgroup.closure {lineRegs 1, lineRegs 2} ∧ lineSubgroup ≤ Pl := by
  refine ⟨rfl, words_facts.1, baseFin_length, ofWords_original_toList,
    fun j => ofWords_strong_get j, wordStrong_of_lt _ _ (by simp),
    wordStrong_of_lt _ _ (by simp), fun j hj => wordStrong_of_ge _ _ (by simpa using hj),
    fun i => ?_, fun _ _ => rfl, sgen_mem, fun _ _ => rfl, rfl, lineSubgroup_le⟩
  have hi : i.val < baseFin.length := i.isLt
  have hi' : i.val < Data.baseList.length := by simpa [baseFin] using hi
  rw [show QON.base.get i = baseFin[i.val] from ofWords_base_get i]
  simp only [baseFin, List.getElem_map]
  rw [Nat.mod_eq_of_lt (base_facts.2.2 _ (List.getElem_mem hi')),
    baseIndex_eq (by rw [base_facts.1] at hi'; exact hi')]

end CFSG.ONSchreier
