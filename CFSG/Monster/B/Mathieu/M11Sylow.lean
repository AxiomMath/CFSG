module

public import CFSG.Monster.B.Mathieu.M11SylowCheck
public import CFSG.Sporadic.Schreier.M11Pinned

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

theorem fam_M11_sylow_normal_generation :
    ∃ r : GroupRecord, MathieuCertificateK "M11" = some r ∧
      r.sylows.map (·.prime) = [2, 3, 5, 11] ∧
      (∀ p : ℕ, p.Prime → (p ∣ 7920 ↔ p ∈ r.sylows.map (·.prime))) ∧
      r.sylows.map (fun s => (s.prime, s.normalGeneration.length)) =
        [(2, 5), (3, 4), (5, 1), (11, 1)] ∧
      r.rootGens 11 = [m11gA, m11gB] ∧
      ∀ s ∈ r.sylows, SylowFacts CFSG.Blueprint.NativeSporadic.M11 7920 [m11gA, m11gB] s := by
  have hprimes : m11Record.sylows.map (·.prime) = [2, 3, 5, 11] := by
    have := congrArg (List.map Prod.fst) m11_sylow_counts
    rw [List.map_map] at this
    exact this
  refine ⟨m11Record, mathieuCertificate_M11, hprimes, ?_, m11_sylow_counts,
    rootGens_eq m11_generators, m11_sylow_check⟩
  rw [hprimes]
  exact prime_dvd_iff_mem (by norm_num) (l := [2, 2, 2, 2, 3, 3, 5, 11]) (by simp)
    (fun p => by simp)

end CFSG.Monster.B.Mathieu
