module

public import CFSG.Sporadic.Schreier.J1ChainCheck
public import CFSG.Sporadic.Schreier.J1Faithful

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem chainCheckFacts_of_chainRecordCheck {c : ChainRecord} {n : ℕ} (h : c.check n = true) :
    ChainCheckFacts n c.origArrs c.strongArrs c.baseArr c.wordArrs 1 := by
  simp only [ChainRecord.check, arraysOK, Bool.and_eq_true] at h
  exact chainCheckFacts h.2.2

theorem j1_generators_eq :
    J1Certificate.chain.generators = [j1A1List, j1A2List] := by
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.1 j1_cert_generators_length
  rw [j1A1List, j1A2List, hxy]
  rfl

theorem j1_closure_generators :
    Subgroup.closure {g | ∃ a ∈ J1Certificate.chain.generators, arrPerm 3080 a = g} = j1P := by
  rw [j1_generators_eq]
  congr 1
  ext g
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, j1A1, j1A2]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem fam_j1_order :
    ∃ Q : RawSchreierDatum 3080, J1Certificate.chain.Records Q ∧ ValidSchreier Q ∧
      Q.base.toList.map (fun b : Fin 3080 => (b : ℕ)) = [0, 1, 2] ∧
      (List.finRange Q.baseCount).map Q.orbitSize = [3080, 19, 3] ∧
      Q.orderCertificate = 175560 ∧ Q.originalSubgroup = j1P ∧ Nat.card j1P = 175560 ∧
      Nat.card NativeSporadic.J1 = 175560 := by
  obtain ⟨Q, hrec, hQ, hsub, hcard⟩ := ChainRecord.exists_records_of_check j1_chain_check
  have hF := chainCheckFacts_of_chainRecordCheck j1_chain_check
  have hA := hrec.2.2
  have hP : Q.originalSubgroup = j1P := hsub.trans j1_closure_generators
  have hsizes : (List.finRange Q.baseCount).map Q.orbitSize = [3080, 19, 3] := by
    rw [← j1_chain_orbitSizes, ChainRecord.orbitSizes, rawOrbitSizes]
    apply List.ext_getElem (by simp [ChainArrays.chainLevels_size, hA.base_size])
    intro k h1 h2
    simp only [List.length_map, List.length_finRange] at h1
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList, Fin.cast_mk]
    rw [hA.orbitSize_eq hF h1, ChainArrays.chainLevels_getElem]
  have hPcard : Nat.card j1P = 175560 := by
    rw [← hP, hcard, j1_chain_orbitSizes]
    rfl
  refine ⟨Q, hrec, hQ, ?_, hsizes, ?_, hP, hPcard, ?_⟩
  · have hb : Q.baseCount = 3 := by
      rw [← hA.base_size]
      simp [ChainRecord.baseArr, j1_chain_base]
    rw [hA.base_toList hF, List.map_map, hb]
    change (List.range 3).map (fun k => J1Certificate.chain.baseArr[k]! % 3080) = [0, 1, 2]
    rw [ChainRecord.baseArr, j1_chain_base]
    decide
  · rw [RawSchreierDatum.orderCertificate, hsizes]
    rfl
  · rw [Nat.card_congr j1PermEquiv.toEquiv, hPcard]

end CFSG.Sporadic.Schreier
