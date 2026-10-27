module

public import CFSG.LocalAnalysis.StandardType.GGK0LCDefs
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private lemma lk0xlcdata_getD_ofFn {n : ℕ} (f : Fin n → ℤ) (i : Fin n) :
    (List.ofFn f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

private lemma lk0xlcdata_box_of_check (τ : Tag) (hrList : List ℤ)
    (hhr : ∀ i : Fin τ.rank, hrList.getD i.val 0 = (hr τ i : ℤ))
    (hcheck : ∀ r ∈ τ.artifactRoots, ∀ i : Fin τ.rank,
      -(hrList.getD i.val 0) ≤ r.getD i.val 0 ∧ r.getD i.val 0 ≤ hrList.getD i.val 0)
    (hroot : IsRoot τ (theta τ)) (hpos : ∀ i, 0 < hr τ i) : KacBox τ := by
  refine ⟨?_, hroot, hpos⟩
  intro γ hγ i
  have hmem : List.ofFn γ ∈ τ.artifactRoots := isRoot_iff_mem_artifactRoots.1 hγ
  have h := hcheck _ hmem i
  rw [lk0xlcdata_getD_ofFn γ i, hhr i] at h
  exact h

theorem kacBox_F4 : KacBox .F4 := by
  refine lk0xlcdata_box_of_check .F4 [2, 3, 4, 2] ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · exact isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  · decide +kernel

theorem kacBox_E6 : KacBox .E6 := by
  refine lk0xlcdata_box_of_check .E6 [1, 2, 2, 3, 2, 1] ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · exact isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  · decide +kernel

theorem kacBox_E7 : KacBox .E7 := by
  refine lk0xlcdata_box_of_check .E7 [2, 2, 3, 4, 3, 2, 1] ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · exact isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  · decide +kernel

theorem kacCentred_F4 : KacCentred .F4 1 := by
  refine ⟨!![2, 3, 4, 2; 3, 6, 8, 4; 2, 4, 6, 3; 1, 2, 3, 2], ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem kacCentred_E6 : KacCentred .E6 3 := by
  refine ⟨!![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4;
    6, 9, 12, 18, 12, 6; 4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4], ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem kacCentred_E7 : KacCentred .E7 2 := by
  refine ⟨!![4, 4, 6, 8, 6, 4, 2; 4, 7, 8, 12, 9, 6, 3; 6, 8, 12, 16, 12, 8, 4;
    8, 12, 16, 24, 18, 12, 6; 6, 9, 12, 18, 15, 10, 5; 4, 6, 8, 12, 10, 8, 4;
    2, 3, 4, 6, 5, 4, 3], ?_, ?_⟩
  · decide +kernel
  · decide +kernel

end CFSG.StandardType.GGK0LC

end
