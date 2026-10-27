module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertPerm

public section

namespace CFSG.StandardType.TestLin

@[expose] def d6cGens : List (Vn 5 × Vn 5) :=
  [(![1, 2, 0, 0, 0], ![1, 2, 0, 0, 0]),
   (![0, 1, 2, 0, 0], ![0, 1, 2, 0, 0]),
   (![0, 0, 1, 2, 0], ![0, 0, 1, 2, 0]),
   (![0, 0, 0, 1, 2], ![0, 0, 0, 1, 2]),
   (![0, 0, 0, 0, 1], ![1, 1, 1, 1, 2])]
@[expose] def d6cSets : List (List (Vn 5)) :=
  []
@[expose] def d6cPats : List ((Vn 5 × Vn 5) × PatV 5) :=
  [((![0, 0, 0, 0, 1], ![0, 0, 0, 0, 2]), .symw [4] 3),
   ((![0, 0, 0, 0, 2], ![0, 0, 0, 0, 1]), .symw [4] 3),
   ((![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1]), .symw [] 4),
   ((![0, 0, 0, 1, 1], ![2, 2, 2, 1, 1]), .symw [] 4),
   ((![0, 0, 0, 1, 2], ![1, 1, 1, 2, 0]), .symw [] 4),
   ((![0, 0, 0, 1, 2], ![2, 2, 2, 0, 1]), .symw [4] 3),
   ((![0, 0, 0, 2, 2], ![0, 0, 0, 2, 2]), .symw [] 4),
   ((![0, 0, 0, 2, 2], ![1, 1, 1, 2, 2]), .symw [] 4),
   ((![0, 0, 1, 1, 2], ![2, 2, 0, 0, 1]), .symw [] 4),
   ((![0, 0, 1, 2, 2], ![1, 1, 2, 0, 0]), .symw [] 4),
   ((![0, 1, 1, 1, 1], ![0, 2, 2, 2, 2]), .symw [4, 3, 2, 1] 0),
   ((![0, 1, 1, 1, 2], ![0, 2, 2, 2, 1]), .symw [4] 3),
   ((![0, 1, 1, 2, 2], ![1, 0, 0, 2, 2]), .symw [4, 3] 2),
   ((![0, 1, 1, 2, 2], ![2, 1, 1, 0, 0]), .symw [] 4),
   ((![0, 1, 2, 2, 2], ![0, 2, 1, 1, 1]), .symw [] 4),
   ((![0, 2, 2, 2, 2], ![0, 1, 1, 1, 1]), .symw [4, 3, 2, 1] 0),
   ((![1, 1, 1, 1, 2], ![0, 0, 0, 0, 1]), .symw [4] 3),
   ((![1, 1, 1, 1, 2], ![2, 2, 2, 2, 0]), .symw [] 4),
   ((![1, 1, 1, 2, 2], ![0, 0, 0, 2, 2]), .symw [] 4),
   ((![1, 1, 1, 2, 2], ![1, 1, 1, 2, 2]), .symw [] 4),
   ((![1, 1, 2, 2, 2], ![1, 1, 0, 0, 0]), .symw [] 4),
   ((![1, 1, 2, 2, 2], ![1, 1, 2, 2, 2]), .symw [4, 3, 2] 1),
   ((![1, 2, 2, 2, 2], ![0, 1, 1, 1, 1]), .symw [4, 3, 2, 1] 0),
   ((![1, 2, 2, 2, 2], ![2, 0, 0, 0, 0]), .symw [] 4)]
@[expose] def d6cReps : List (Vn 5 × Vn 5) :=
  []
@[expose] def d6cS2 : List (S2V 5) :=
  []

@[expose] def d6cS (k : Fin 5) : Vn 5 ≃ₗ[ZMod 3] Vn 5 := letLin (letAt d6cGens k)

theorem d6c_certOK : certOK d6cGens (oneN 5) d6cSets d6cPats d6cReps d6cS2 = true := by
  decide +kernel

theorem d6c_cov : permCovB 5 d6cPats = true := by
  decide +kernel

theorem d6c_adj : ∀ i : Fin 4, letAt d6cGens i =
    (Pi.single i.castSucc 1 - Pi.single i.succ 1, Pi.single i.castSucc 1 - Pi.single i.succ 1) := by
  decide +kernel

theorem d6c_test : ∀ A Mg : Subgroup (Vn 5 ≃ₗ[ZMod 3] Vn 5),
    TestHyp (Subgroup.closure (Set.range d6cS)) (oneN 5) A Mg →
    ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (oneN 5) r →
    ∀ t ∈ A, IsRefl t → ¬ FixesLine (oneN 5) t → t ∈ Mg :=
  linTest_perm_of_certOK d6cS d6cGens rfl (fun _ => rfl)
    (permGroup_le_of_gens d6cS d6cGens (fun _ => rfl) (by norm_num) d6c_adj)
    d6c_certOK d6c_cov

end CFSG.StandardType.TestLin

end
