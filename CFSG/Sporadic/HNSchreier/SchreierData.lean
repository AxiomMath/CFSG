module

public import CFSG.Sporadic.HNSchreier.Faithful
public import CFSG.Sporadic.Schreier.ONWordDatum
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import Certificates.Certificate2102
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Certificates.SchreierPointSift

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Certificates CFSG.ONSchreier CFSG.Sporadic.HNSchreier.Native Matrix

@[expose] def baseFin : List X :=
  Data.baseList.map fun b => ⟨b % hnsData.n, Nat.mod_lt _ (by rw [hns_n]; norm_num)⟩

theorem baseFin_nodup : baseFin.Nodup := by
  apply base_facts.2.1.map_on
  intro x hx y hy h
  have h1 := congrArg Fin.val h
  simp only [hns_n] at h1
  rwa [Nat.mod_eq_of_lt (base_facts.2.2 x hx), Nat.mod_eq_of_lt (base_facts.2.2 y hy)] at h1

theorem baseFin_length : baseFin.length = 22 := by
  rw [baseFin, List.length_map, base_facts.1]

theorem two_le_words : [a0, a1].length ≤ Data.strongWords.size := by
  rw [words_facts.1]
  decide

@[expose] def sgen (j : ℕ) : Equiv.Perm X := wordStrong [a0, a1] Data.strongWords j

@[expose] def QHN : RawSchreierDatum hnsData.n :=
  RawSchreierDatum.ofWords hnsData.n (by rw [hns_n]; norm_num) [a0, a1] Data.strongWords
    two_le_words baseFin baseFin_nodup

@[expose] def beta (i j : X) : ZMod 5 := pairing i j

@[expose] def permRegs0 (r : ℕ) : Equiv.Perm X := if r = 1 then a0 else if r = 2 then a1 else 1

@[expose] def permRegs : ℕ → Equiv.Perm X := runProg permRegs0 Data.subgroupProgram

@[expose] def HP : Subgroup (Equiv.Perm X) := Subgroup.closure {permRegs 1, permRegs 2}

theorem runProg_mem {G : Type*} [Group G] (K : Subgroup G) :
    ∀ (prog : List (ℕ × ℕ × ℕ)) (regs : ℕ → G), (∀ r, regs r ∈ K) →
      ∀ r, runProg regs prog r ∈ K
  | [], _, h => h
  | (a, b, c) :: rest, regs, h => runProg_mem K rest _ fun r => by
      by_cases hr : r = c
      · subst hr; simp only [Function.update_self]; exact mul_mem (h a) (h b)
      · rw [Function.update_of_ne hr]; exact h r

theorem a0_mem : a0 ∈ PH := Subgroup.subset_closure (Set.mem_insert _ _)

theorem a1_mem : a1 ∈ PH := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem HP_le : HP ≤ PH := by
  rw [HP, Subgroup.closure_le]
  have hregs : ∀ r, permRegs r ∈ PH := runProg_mem PH _ _ fun r => by
    unfold permRegs0
    split_ifs
    · exact a0_mem
    · exact a1_mem
    · exact one_mem _
  rintro _ (rfl | rfl)
  · exact hregs 1
  · exact hregs 2

theorem sgen_mem : ∀ j, sgen j ∈ PH := by
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

@[expose] def baseIndex (k : ℕ) : ℕ := Data.baseList.getD k 0

theorem baseIndex_lt {k : ℕ} (hk : k < 22) : baseIndex k < nPts := by
  rw [baseIndex, List.getD_eq_getElem _ _ (by rw [base_facts.1]; exact hk)]
  exact base_facts.2.2 _ (List.getElem_mem _)

theorem cert_hn_schreier_action_data :
    QHN.originalCount = 2 ∧ QHN.strongCount = 9 ∧ QHN.baseCount = 22 ∧
      QHN.original.toList = [a0, a1] ∧
      (∀ j : Fin QHN.strongCount, QHN.strong.get j = sgen j) ∧
      sgen 0 = a0 ∧ sgen 1 = a1 ∧
      (∀ j, 2 ≤ j → sgen j = Quiver.SchreierGraph.evalWord (fun h : Fin j => sgen h)
        (ptoLetters j Data.strongWords[j]!)) ∧
      (∀ i : Fin QHN.baseCount, ((QHN.base.get i : X) : ℕ) = baseIndex i) ∧
      (∀ (j : Fin QHN.strongCount) (hj : QHN.originalCount ≤ j.val),
        QHN.derivation j hj = ptoLetters j.val Data.strongWords[j.val]!) ∧
      (∀ j, sgen j ∈ PH) ∧ HP = Subgroup.closure {permRegs 1, permRegs 2} ∧ HP ≤ PH ∧
      ∀ i j : X, beta i j = vL i ⬝ᵥ (formM *ᵥ vL j) := by
  refine ⟨rfl, words_facts.1, baseFin_length, ofWords_original_toList,
    fun j => ofWords_strong_get j, wordStrong_of_lt _ _ (by simp),
    wordStrong_of_lt _ _ (by simp), fun j hj => wordStrong_of_ge _ _ (by simpa using hj),
    fun i => ?_, fun _ _ => rfl, sgen_mem, rfl, HP_le, fun i j => ?_⟩
  · have hi : i.val < baseFin.length := i.isLt
    have hi' : i.val < Data.baseList.length := by simpa [baseFin] using hi
    rw [show QHN.base.get i = baseFin[i.val] from ofWords_base_get i]
    simp only [baseFin, List.getElem_map]
    have hlt : Data.baseList[i.val] < hnsData.n := base_facts.2.2 _ (List.getElem_mem hi')
    rw [Nat.mod_eq_of_lt hlt, baseIndex, List.getD_eq_getElem _ _ hi']
  · rw [beta, pairing, ite_eq_left ⟨by rw [orbitL_length]; exact i.isLt,
      by rw [orbitL_length]; exact j.isLt⟩]

open CFSG.Sporadic.Th.Native CFSG.ONSchreier.Native in
theorem natTab_getElem! {t : Table} {i : ℕ} (hi : i < t.size) : (natTab t)[i]! = ap t i := by
  rw [natTab, getElem!_pos _ i (by simpa using hi), Array.getElem_map, ap,
    getElem!_pos t i hi]

open CFSG.Sporadic.F5.Native CFSG.ONSchreier.Native in
theorem prep_a0 :
    PRep hnsData.n (natTab (hnsData.orbit ()).alpha) a0 := fun x => by
  rw [natTab_getElem! (by rw [hnsBase.alpha_size]; exact x.isLt), a0_apply, f0_eq x.isLt]

open CFSG.Sporadic.F5.Native CFSG.ONSchreier.Native in
theorem prep_a1 :
    PRep hnsData.n (natTab (hnsData.orbit ()).beta) a1 := fun x => by
  rw [natTab_getElem! (by rw [hnsBase.beta_size]; exact x.isLt), a1_apply, f1_eq x.isLt]

end CFSG.Sporadic.HNSchreier
