module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualG2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.Rank2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin (IsPSL IsSL3 IsPSp4 IsG2)

variable {K : Type} [Field K]

theorem sl3_residualOvergroupsAt' [Finite K] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    ResidualOvergroupsAt (SpecialLinearGroup (Fin 3) K) (unitriangular 3 K)
      (fun j : Fin 2 => Q3 K j) := by
  have hB := isSolvable_upperTriangular (n := 3) (K := K) hK
  have h := residualOvergroupsAt_of_rank_two_data
    (π := MonoidHom.id (SpecialLinearGroup (Fin 3) K)) Function.surjective_id
    (V := unitriangular 3 K) (B := upperTriangular 3 K) (Q := Q3 K) (H := H3 K)
    (by rw [MonoidHom.ker_id]; exact bot_le) (unitriangular_le_upperTriangular 3 K)
    (fun j => by rw [Q3_eq]; exact upperTriangular_le_flagStabilizer _)
    Q3_ne covBy_Q3 (fun A hVA hAt => contained_in_Q3 hVA hAt) hB commutator_Q3_le
    (fun j A hVA hAQ hAns => H3_le_of_nonsolvable hB j hVA hAQ hAns)
  simpa [Subgroup.map_id] using h

theorem isSylowTwoOf_unitriangular' [Finite K] [CharP K 2] :
    IsSylowTwoOf (unitriangular 3 K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  exact hP ▸ isSylowTwoOf_top_of_sylow P

theorem exists_residualOvergroupsAt
    {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 1 ≤ f)
    (htype : IsPSL 3 2 f Y ∨ IsSL3 (2 ^ f) Y ∨ IsPSp4 2 f Y ∨ IsG2 2 f Y) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) : ∃ P : Fin 2 → Subgroup Y, ResidualOvergroupsAt Y U P := by
  rcases htype with h | h | h | h
  · obtain ⟨_, _, _, _, _, _, _, hP, _⟩ := even_rank_two_residual_linear h hU
    exact ⟨_, hP⟩
  · obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    obtain ⟨φ', -, hres⟩ := (sl3_residualOvergroupsAt' ⟨f, hK⟩).exists_iso_of_isSylow
      (φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm)
      isSylowTwoOf_unitriangular' hU
    exact ⟨_, hres⟩
  · obtain ⟨_, _, _, _, _, _, _, hP, _⟩ := even_rank_two_residual_symplectic h hU
    exact ⟨_, hP⟩
  · obtain ⟨_, _, _, _, _, _, _, hP, _⟩ := even_rank_two_residual_G2 h hU
    exact ⟨_, hP⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.Rank2
