module

public import CFSG.Monster.B.Mathieu.M23SylowCheck
public import CFSG.Sporadic.Schreier.M23Pinned

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Schreier

theorem fam_M23_sylow_normal_generation :
    ∃ r : GroupRecord, MathieuCertificateK "M23" = some r ∧
      r.sylows.map (·.prime) = [2, 3, 5, 7, 11, 23] ∧
      (∀ p : ℕ, p.Prime → (p ∣ 10200960 ↔ p ∈ r.sylows.map (·.prime))) ∧
      r.sylows.map (fun s => (s.prime, s.normalGeneration.length)) =
        [(2, 35), (3, 4), (5, 1), (7, 1), (11, 1), (23, 1)] ∧
      r.rootGens 23 = [m23PermA, m23PermB] ∧
      ∀ s ∈ r.sylows,
        SylowFacts CFSG.Blueprint.NativeSporadic.M23 10200960 [m23PermA, m23PermB] s := by
  have hprimes : m23Record.sylows.map (·.prime) = [2, 3, 5, 7, 11, 23] := by
    have := congrArg (List.map Prod.fst) m23_sylow_counts
    rw [List.map_map] at this
    exact this
  refine ⟨m23Record, mathieuCertificate_M23, hprimes, ?_, m23_sylow_counts,
    rootGens_eq m23_generators, m23_sylow_check⟩
  rw [hprimes]
  exact prime_dvd_iff_mem (by norm_num) (l := [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11, 23]) (by simp)
    (fun p => by simp)

end CFSG.Monster.B.Mathieu
