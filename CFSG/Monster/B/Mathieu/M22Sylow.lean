module

public import CFSG.Monster.B.Mathieu.M22SylowCheck
public import CFSG.Monster.B.Mathieu.M22Check

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Sporadic.Mathieu

theorem fam_M22_sylow_normal_generation :
    ∃ r : GroupRecord, MathieuCertificateK "M22" = some r ∧
      r.sylows.map (·.prime) = [2, 3, 5, 7, 11] ∧
      (∀ p : ℕ, p.Prime → (p ∣ 443520 ↔ p ∈ r.sylows.map (·.prime))) ∧
      r.sylows.map (fun s => (s.prime, s.normalGeneration.length)) =
        [(2, 35), (3, 4), (5, 1), (7, 1), (11, 1)] ∧
      r.rootGens 22 = [m22gA, m22gB] ∧
      ∀ s ∈ r.sylows, SylowFacts CFSG.Blueprint.NativeSporadic.M22 443520 [m22gA, m22gB] s := by
  have hprimes : m22Record.sylows.map (·.prime) = [2, 3, 5, 7, 11] := by
    have := congrArg (List.map Prod.fst) m22_sylow_counts
    rw [List.map_map] at this
    exact this
  refine ⟨m22Record, mathieuCertificate_M22, hprimes, ?_, m22_sylow_counts,
    rootGens_eq m22_generators, m22_sylow_check⟩
  rw [hprimes]
  exact prime_dvd_iff_mem (by norm_num) (l := [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11]) (by simp)
    (fun p => by simp)

end CFSG.Monster.B.Mathieu
