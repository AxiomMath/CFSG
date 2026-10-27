module

public import CFSG.Monster.B.Mathieu.ChainCheck

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def imageList {n : ℕ} (g : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun i => (g i : ℕ)

theorem imageList_length {n : ℕ} (g : Equiv.Perm (Fin n)) : (imageList g).length = n := by
  simp [imageList]

theorem rep_imageList {n : ℕ} (g : Equiv.Perm (Fin n)) : Rep n (imageList g).toArray g := by
  intro x
  rw [getElem!_pos (imageList g).toArray (x : ℕ) (by simp [imageList])]
  simp [imageList]

theorem permOfArr_eq_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change t[(x : ℕ)]! = _
  exact h x

theorem arrPerm_imageList {n : ℕ} (g : Equiv.Perm (Fin n)) : arrPerm n (imageList g) = g :=
  permOfArr_eq_of_rep (rep_imageList g)

theorem exists_root_chain {r : GroupRecord} {n N : ℕ} {a b : Equiv.Perm (Fin n)}
    (hcheck : r.chain.check n = true) (hsize : (r.chain.orbitSizes n).prod = N)
    (hgens : r.chain.generators = [imageList a, imageList b]) :
    ∃ Q : RawSchreierDatum n, r.chain.Records Q ∧ ValidSchreier Q ∧ Q.orderCertificate = N ∧
      Q.originalSubgroup = Subgroup.closure {a, b} ∧ Nat.card (Subgroup.closure {a, b}) = N := by
  obtain ⟨Q, hrec, hQ, hsub, hcard⟩ := ChainRecord.exists_records_of_check hcheck
  have hab : Subgroup.closure {g | ∃ x ∈ r.chain.generators, arrPerm n x = g} =
      Subgroup.closure {a, b} := by
    congr 1
    ext g
    rw [hgens]
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      arrPerm_imageList, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  rw [hab] at hsub
  refine ⟨Q, hrec, hQ, ?_, hsub, ?_⟩
  · rw [RawSchreierDatum.orderCertificate_eq_card Q hQ, hcard, hsize]
  · rw [← hsub, hcard, hsize]

end CFSG.Monster.B.Mathieu
