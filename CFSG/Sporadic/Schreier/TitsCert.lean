module

public import CFSG.Sporadic.Schreier.TitsCertCheck
public import CFSG.Sporadic.Schreier.TitsChain
public import Mathlib.GroupTheory.GroupAction.Transitive

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def titsGen (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsGenArrs[i]!

@[expose] def titsA : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure (Set.range fun i : Fin 4 => titsGen i)

@[expose] def titsDGen (j : ℕ) : Equiv.Perm (Fin 1755) :=
  tcomm (wordIn 4 titsGen (titsU j)) (wordIn 4 titsGen (titsV j))

@[expose] def titsD : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure (Set.range fun j : Fin 2 => titsDGen j)

@[expose] def titsEGen (j : ℕ) : Equiv.Perm (Fin 1755) :=
  tcomm (wordIn 2 titsDGen (titsPerfR j)) (wordIn 2 titsDGen (titsPerfS j))

@[expose] def titsE : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure (Set.range fun j : Fin 2 => titsEGen j)

@[expose] def titsP (i : ℕ) : Equiv.Perm (Fin 8775) := permOfArr 8775 titsFlagArrs[i]!

@[expose] def titsBeta (j : Fin 8775) : Fin 1755 := finPt 1755 titsBetaArr[(j : ℕ)]!

theorem titsGenArrs_size : titsGenArrs.size = 4 := titsChains_check.1

theorem titsAmbientArrs_size :
    titsAmbientArrs.size = 14 := titsChains_check.2.1

theorem titsDerivedArrs_size :
    titsDerivedArrs.size = 13 := titsChains_check.2.2.1

theorem titsPerfectArrs_size :
    titsPerfectArrs.size = 12 := titsChains_check.2.2.2.1

@[expose] def titsQA : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsAmbientArrs 4
    (by rw [titsAmbientArrs_size]; norm_num) (finList 1755 titsAmbientBase) (by decide)
    (wordsArr 4 14 titsAmbientDerivations)

@[expose] def titsQD : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsDerivedArrs 2
    (by rw [titsDerivedArrs_size]; norm_num) (finList 1755 titsDerivedBase) (by decide)
    (wordsArr 2 13 titsDerivedDerivations)

@[expose] def titsQE : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsPerfectArrs 2
    (by rw [titsPerfectArrs_size]; norm_num) (finList 1755 titsPerfectBase) (by decide)
    (wordsArr 2 12 titsPerfectDerivations)

@[expose] def titsT (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsDerivedArrs[i]!

theorem titsGen_rep
    {i : ℕ} (hi : i < 4) : Rep 1755 titsGenArrs[i]! (titsGen i) :=
  rep_of_allPermsOK titsChains_check.2.2.2.2.1 (by rw [titsGenArrs_size]; exact hi)

theorem titsGen_inv {i : ℕ} (hi : i < 4) :
    isInvA 1755 titsGenArrs[i]! (invCand 1755 titsGenArrs[i]!) = true :=
  isInvA_of_allPermsOK titsChains_check.2.2.2.2.1 (by rw [titsGenArrs_size]; exact hi)

theorem titsDArr_rep
    {j : ℕ} (hj : j < 2) : Rep 1755 (titsDArr j) (titsDGen j) := by
  obtain ⟨hu, hv, hu', hv', -⟩ := titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  exact rep_commArr (rep_wordArr (by rw [titsGenArrs_size]) (fun i hi => titsGen_rep hi)
    (fun i hi => titsGen_inv hi) hu) (rep_wordArr (by rw [titsGenArrs_size])
      (fun i hi => titsGen_rep hi) (fun i hi => titsGen_inv hi) hv) hu' hv'

theorem titsDArrs_get {i : ℕ} (hi : i < 2) : titsDArrs[i]! = titsDArr i :=
  getElem!_ofFn_of_lt _ hi

theorem titsEArr_rep
    {j : ℕ} (hj : j < 2) : Rep 1755 (titsEArr j) (titsEGen j) := by
  have hd : ∀ i < 2, Rep 1755 titsDArrs[i]! (titsDGen i) := fun i hi => by
    rw [titsDArrs_get hi]
    exact titsDArr_rep hi
  have hdi : ∀ i < 2, isInvA 1755 titsDArrs[i]! (invCand 1755 titsDArrs[i]!) = true :=
    fun i hi => by
      rw [titsDArrs_get hi]
      exact (titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 i hi).2.2.1
  obtain ⟨hr, hs, -, hr', hs', -⟩ := titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
  have hsz : 2 ≤ titsDArrs.size := by simp [titsDArrs]
  exact rep_commArr (rep_wordArr hsz hd hdi hr) (rep_wordArr hsz hd hdi hs) hr' hs'

theorem titsAmbient_perm
    {i : ℕ} (hi : i < 4) : permOfArr 1755 titsAmbientArrs[i]! = titsGen i :=
  eq_of_eqA (rep_of_allPermsOK titsChains_check.2.2.2.2.2.1 (by rw [titsAmbientArrs_size]; omega))
    (titsGen_rep hi) (titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi)

theorem titsDerived_perm
    {j : ℕ} (hj : j < 2) : permOfArr 1755 titsDerivedArrs[j]! = titsDGen j :=
  eq_of_eqA (rep_of_allPermsOK titsChains_check.2.2.2.2.2.2.1 (by rw [titsDerivedArrs_size]; omega))
    (titsDArr_rep hj) (titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).2.2.2.2

theorem titsPerfect_perm
    {j : ℕ} (hj : j < 2) : permOfArr 1755 titsPerfectArrs[j]! = titsEGen j :=
  eq_of_eqA (rep_of_allPermsOK titsChains_check.2.2.2.2.2.2.2.1
    (by rw [titsPerfectArrs_size]; omega))
    (titsEArr_rep hj) (titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj).2.2.2.2.2

theorem titsQA_valid : ValidSchreier titsQA :=
  (valid_ofArrays titsChains_check.2.2.2.2.2.1 (by norm_num : 0 < 4)
    titsChains_check.2.2.2.2.2.2.2.2.1).1

theorem titsQD_valid : ValidSchreier titsQD :=
  (valid_ofArrays titsChains_check.2.2.2.2.2.2.1 (by norm_num : 0 < 4)
    titsChains_check.2.2.2.2.2.2.2.2.2.1).1

theorem titsQE_valid : ValidSchreier titsQE :=
  (valid_ofArrays titsChains_check.2.2.2.2.2.2.2.1 (by norm_num : 0 < 4)
    titsChains_check.2.2.2.2.2.2.2.2.2.2.1).1

theorem titsQA_original : titsQA.originalSubgroup = titsA := by
  have hf : (fun i : Fin 4 => permOfArr 1755 titsAmbientArrs[(i : ℕ)]!) =
      fun i : Fin 4 => titsGen i :=
    funext fun i => titsAmbient_perm i.2
  rw [titsQA, originalSubgroup_ofArrays, hf]
  rfl

theorem titsQD_original : titsQD.originalSubgroup = titsD := by
  have hf : (fun i : Fin 2 => permOfArr 1755 titsDerivedArrs[(i : ℕ)]!) =
      fun i : Fin 2 => titsDGen i :=
    funext fun i => titsDerived_perm i.2
  rw [titsQD, originalSubgroup_ofArrays, hf]
  rfl

theorem titsQE_original : titsQE.originalSubgroup = titsE := by
  have hf : (fun i : Fin 2 => permOfArr 1755 titsPerfectArrs[(i : ℕ)]!) =
      fun i : Fin 2 => titsEGen i :=
    funext fun i => titsPerfect_perm i.2
  rw [titsQE, originalSubgroup_ofArrays, hf]
  rfl

theorem card_titsA : Nat.card titsA = 35942400 := by
  rw [← titsQA_original, titsQA, card_ofArrays titsChains_check.2.2.2.2.2.1 (by norm_num : 0 < 4)
    titsChains_check.2.2.2.2.2.2.2.2.1, titsChains_check.2.2.2.2.2.2.2.2.2.2.2.1]
  rfl

theorem card_titsD : Nat.card titsD = 17971200 := by
  rw [← titsQD_original, titsQD, card_ofArrays titsChains_check.2.2.2.2.2.2.1 (by norm_num : 0 < 4)
    titsChains_check.2.2.2.2.2.2.2.2.2.1, titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.1]
  rfl

theorem card_titsE : Nat.card titsE = 17971200 := by
  rw [← titsQE_original, titsQE, card_ofArrays titsChains_check.2.2.2.2.2.2.2.1
    (by norm_num : 0 < 4) titsChains_check.2.2.2.2.2.2.2.2.2.2.1,
    titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  rfl

theorem titsQD_base_zero
    (h0 : 0 < titsQD.baseCount) : titsQD.base.get ⟨0, h0⟩ = 0 := by
  have h := RawSchreierDatum.ofArrays_base_toList (n := 1755) (hn := by norm_num)
    (S := titsDerivedArrs) (k := 2) (hk := by rw [titsDerivedArrs_size]; norm_num)
    (base := finList 1755 titsDerivedBase) (hb := by decide)
    (W := wordsArr 2 13 titsDerivedDerivations)
  have e : titsQD.base.get ⟨0, h0⟩ = titsQD.base.toList[0]'(by simpa using h0) := by
    simp [Vector.get]
  rw [e]
  simp only [titsQD, h]
  rfl

theorem titsD_pretransitive :
    MulAction.IsPretransitive titsD (Fin 1755) := by
  rw [MulAction.isPretransitive_iff_base (0 : Fin 1755)]
  intro x
  have h0 : 0 < titsQD.baseCount := by
    show 0 < (finList 1755 titsDerivedBase).length
    decide
  have hfull : ((rawLevels 1755 titsDerivedArrs (baseArr 1755 titsDerivedBase))[0]!).pts.size =
      1755 := levelSize_of_orbitSizes titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)
  obtain ⟨g, hg, hgx⟩ : ∃ g ∈ titsQD.originalSubgroup, g (titsQD.base.get ⟨0, h0⟩) = x :=
    exists_mem_ofArrays_apply_base titsChains_check.2.2.2.2.2.2.1 (by norm_num : 0 < 4)
      titsChains_check.2.2.2.2.2.2.2.2.2.1 h0 hfull x
  rw [titsQD_base_zero h0] at hgx
  rw [titsQD_original] at hg
  exact ⟨⟨g, hg⟩, hgx⟩

theorem titsQA_original_toList :
    titsQA.original.toList = List.ofFn fun i : Fin 4 => titsGen i := by
  show (Vector.ofFn fun i : Fin 4 => permOfArr 1755 titsAmbientArrs[(i : ℕ)]!).toList = _
  rw [Vector.toList_ofFn]
  exact congrArg List.ofFn (funext fun i => titsAmbient_perm i.2)

theorem titsQD_original_toList :
    titsQD.original.toList = List.ofFn fun j : Fin 2 => titsDGen j := by
  show (Vector.ofFn fun i : Fin 2 => permOfArr 1755 titsDerivedArrs[(i : ℕ)]!).toList = _
  rw [Vector.toList_ofFn]
  exact congrArg List.ofFn (funext fun i => titsDerived_perm i.2)

theorem titsQE_original_toList :
    titsQE.original.toList = List.ofFn fun j : Fin 2 => titsEGen j := by
  show (Vector.ofFn fun i : Fin 2 => permOfArr 1755 titsPerfectArrs[(i : ℕ)]!).toList = _
  rw [Vector.toList_ofFn]
  exact congrArg List.ofFn (funext fun i => titsPerfect_perm i.2)

theorem CERT_Tits_Schreier_validity :
    ValidSchreier titsQA ∧ ValidSchreier titsQD ∧ ValidSchreier titsQE ∧
    titsQA.original.toList = (List.ofFn fun i : Fin 4 => titsGen i) ∧
    titsQD.original.toList = (List.ofFn fun j : Fin 2 => titsDGen j) ∧
    titsQE.original.toList = (List.ofFn fun j : Fin 2 => titsEGen j) ∧
    titsQA.originalSubgroup = titsA ∧ titsQD.originalSubgroup = titsD ∧
    titsQE.originalSubgroup = titsE ∧
    titsQA.base.toList.map Fin.val = [1, 3, 6, 5, 12, 24] ∧
    titsQD.base.toList.map Fin.val = [0, 1, 5, 6, 24, 12] ∧
    titsQE.base.toList.map Fin.val = [0, 1, 3, 5, 6, 12, 24] ∧
    List.ofFn titsQA.orbitSize = [1755, 80, 8, 2, 4, 4] ∧
    List.ofFn titsQD.orbitSize = [1755, 10, 8, 8, 8, 2] ∧
    List.ofFn titsQE.orbitSize = [1755, 10, 8, 2, 8, 4, 2] ∧
    Nat.card titsA = 35942400 ∧ Nat.card titsD = 17971200 ∧ Nat.card titsE = 17971200 ∧
    MulAction.IsPretransitive titsD (Fin 1755) := by
  refine ⟨titsQA_valid, titsQD_valid, titsQE_valid, titsQA_original_toList,
    titsQD_original_toList, titsQE_original_toList, titsQA_original, titsQD_original,
    titsQE_original, ?_, ?_, ?_, ?_, ?_, ?_, card_titsA, card_titsD, card_titsE,
    titsD_pretransitive⟩
  · rw [titsQA, RawSchreierDatum.ofArrays_base_toList]
    decide
  · rw [titsQD, RawSchreierDatum.ofArrays_base_toList]
    decide
  · rw [titsQE, RawSchreierDatum.ofArrays_base_toList]
    decide
  · exact (orbitSizes_ofArrays titsChains_check.2.2.2.2.2.1 (by norm_num : 0 < 4)
      titsChains_check.2.2.2.2.2.2.2.2.1).trans titsChains_check.2.2.2.2.2.2.2.2.2.2.2.1
  · exact (orbitSizes_ofArrays titsChains_check.2.2.2.2.2.2.1 (by norm_num : 0 < 4)
      titsChains_check.2.2.2.2.2.2.2.2.2.1).trans titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact (orbitSizes_ofArrays titsChains_check.2.2.2.2.2.2.2.1 (by norm_num : 0 < 4)
      titsChains_check.2.2.2.2.2.2.2.2.2.2.1).trans titsChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsGen_mem_titsA {i : ℕ} (hi : i < 4) : titsGen i ∈ titsA :=
  Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem titsDGen_mem_titsA (j : ℕ) : titsDGen j ∈ titsA :=
  tcomm_mem (wordIn_mem (fun _ hi => titsGen_mem_titsA hi) _)
    (wordIn_mem (fun _ hi => titsGen_mem_titsA hi) _)

theorem titsDGen_mem_titsD {j : ℕ} (hj : j < 2) : titsDGen j ∈ titsD :=
  Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem titsD_le_titsA : titsD ≤ titsA :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨j, rfl⟩; exact titsDGen_mem_titsA j)

theorem titsEGen_mem_titsD (j : ℕ) : titsEGen j ∈ titsD :=
  tcomm_mem (wordIn_mem (fun _ hi => titsDGen_mem_titsD hi) _)
    (wordIn_mem (fun _ hi => titsDGen_mem_titsD hi) _)

theorem titsE_le_titsD : titsE ≤ titsD :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨j, rfl⟩; exact titsEGen_mem_titsD j)

theorem titsT_mem_titsD {i : ℕ} (hi : i < 13) : titsT i ∈ titsD := by
  rw [← titsQD_original]
  exact strong_mem_ofArrays titsChains_check.2.2.2.2.2.2.1 (by norm_num : 0 < 4)
    titsChains_check.2.2.2.2.2.2.2.2.2.1 (by rw [titsDerivedArrs_size]; exact hi)

theorem titsT_eq_strongOf {i : ℕ} (hi : i < 13) :
    titsT i = strongOf 2 titsDGen titsDerivedDerivations i := by
  have hk : 2 ≤ titsDerivedArrs.size := by simp [titsDerivedArrs_size]
  have hc : rawChainOK 1755 (titsDerivedArrs.extract 0 2) titsDerivedArrs
      (baseArr 1755 titsDerivedBase) (wordsArr 2 titsDerivedArrs.size titsDerivedDerivations) 4 =
        true := by
    rw [titsDerivedArrs_size]
    exact titsChains_check.2.2.2.2.2.2.2.2.2.1
  have hi' : i < titsDerivedArrs.size := by simpa [titsDerivedArrs_size] using hi
  have h := strong_eq_strongOf hk titsChains_check.2.2.2.2.2.2.1 hc i hi'
  rw [titsT, h]
  have key : ∀ j,
      strongOf 2 (fun i => permOfArr 1755 titsDerivedArrs[i]!) titsDerivedDerivations j =
      strongOf 2 titsDGen titsDerivedDerivations j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases hj : j < 2
      · rw [strongOf_of_lt hj, strongOf_of_lt hj, titsDerived_perm hj]
      · rw [strongOf_of_le (by omega), strongOf_of_le (by omega)]
        exact wordIn_congr (fun h hh => ih h hh) _
  exact key i

end CFSG.Sporadic.Schreier.Tits
