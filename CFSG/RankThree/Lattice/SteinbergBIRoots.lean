module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley

theorem toVec_ofFn {n : ℕ} (v : Fin n → ℤ) : toVec n (List.ofFn v) = v := by
  funext i
  simp [toVec, vget]

theorem ofFn_toVec {n : ℕ} {l : List ℤ} (hl : l.length = n) : List.ofFn (toVec n l) = l := by
  subst hl
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp [toVec, vget, List.getElem?_eq_getElem h₂]

theorem isRoot_iff_exists_mem {τ : Tag} {v : Fin τ.rank → ℤ} :
    IsRoot τ v ↔ ∃ l ∈ τ.artifactRoots, v = toVec τ.rank l := by
  rw [isRoot_iff_mem_artifactRoots]
  constructor
  · intro h
    exact ⟨_, h, (toVec_ofFn v).symm⟩
  · rintro ⟨l, hl, rfl⟩
    rwa [ofFn_toVec (length_of_mem_artifactRoots hl)]

theorem isRoot_toVec {τ : Tag} {l : List ℤ} (hl : l ∈ τ.artifactRoots) :
    IsRoot τ (toVec τ.rank l) :=
  isRoot_iff_exists_mem.2 ⟨l, hl, rfl⟩

theorem forall_isRoot_iff {τ : Tag} (P : (Fin τ.rank → ℤ) → Prop) :
    (∀ v, IsRoot τ v → P v) ↔ ∀ l ∈ τ.artifactRoots, P (toVec τ.rank l) := by
  constructor
  · exact fun h l hl => h _ (isRoot_toVec hl)
  · intro h v hv
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hv
    exact h l hl

theorem toVec_injOn_artifactRoots (τ : Tag) :
    Set.InjOn (toVec τ.rank) {l | l ∈ τ.artifactRoots} := by
  intro l hl l' hl' h
  rw [← ofFn_toVec (length_of_mem_artifactRoots hl), ← ofFn_toVec (length_of_mem_artifactRoots hl'),
    h]

theorem ncard_isRoot_and {τ : Tag} (P : (Fin τ.rank → ℤ) → Prop) [DecidablePred P] :
    {v | IsRoot τ v ∧ P v}.ncard =
      (τ.artifactRoots.filter fun l => decide (P (toVec τ.rank l))).length := by
  classical
  have hset : {v | IsRoot τ v ∧ P v} =
      ((τ.artifactRoots.filter fun l => decide (P (toVec τ.rank l))).map
        (toVec τ.rank)).toFinset := by
    ext v
    simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨hv, hP⟩
      obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hv
      exact ⟨l, ⟨hl, hP⟩, rfl⟩
    · rintro ⟨l, ⟨hl, hP⟩, rfl⟩
      exact ⟨isRoot_toVec hl, hP⟩
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
  · rw [List.length_map]
  · refine List.Nodup.map_on ?_ ((nodup_artifactRoots τ).filter _)
    intro l hl l' hl' h
    exact toVec_injOn_artifactRoots τ (List.mem_of_mem_filter hl) (List.mem_of_mem_filter hl') h

end CFSG.RankThree.Lattice
