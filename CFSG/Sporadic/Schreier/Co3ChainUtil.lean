module

public import CFSG.Certificates.NativeSchreierArrays

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2

theorem orbitSizes_eq_of_valid {n : ℕ} {Q : RawSchreierDatum n} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : base.size = Q.baseCount)
    (hsz : ∀ i : Fin Q.baseCount, Q.orbitSize i = ((rawLevels n S base)[(i : ℕ)]!).pts.size) :
    (List.finRange Q.baseCount).map Q.orbitSize = rawOrbitSizes n S base := by
  rw [rawOrbitSizes]
  apply List.ext_getElem
  · simp [rawLevels, hb]
  · intro k h1 h2
    have hk : k < (rawLevels n S base).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [hsz]
    show ((rawLevels n S base)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem ofArrays_originalSubgroup {n : ℕ} {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ}
    {hk : k ≤ S.size} {base : List (Fin n)} {hb : base.Nodup} {W : Array (List ℤ)} :
    (RawSchreierDatum.ofArrays n hn S k hk base hb W).originalSubgroup =
      Subgroup.closure (Set.range fun i : Fin k => permOfArr n S[(i : ℕ)]!) := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  change g ∈ (Vector.ofFn fun i : Fin k => permOfArr n S[(i : ℕ)]!).toList ↔ _
  rw [Vector.toList_ofFn, List.mem_ofFn, Set.mem_range]

theorem orbit_base_eq_univ {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (h0 : 0 < Q.baseCount) (hsize : Q.orbitSize ⟨0, h0⟩ = n) :
    MulAction.orbit Q.originalSubgroup (Q.base.get ⟨0, h0⟩) = Set.univ := by
  have horb := RawSchreierDatum.orbitPoints_eq_orbit Q ⟨0, h0⟩
  rw [RawSchreierDatum.levelSubgroup_zero_eq_original Q hQ] at horb
  have hcard : Nat.card (Q.orbitPoints ⟨0, h0⟩) = n := by
    rw [← RawSchreierDatum.orbitSize_eq_card, hsize]
  rw [horb] at hcard
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq, hcard]

end CFSG.Sporadic.Schreier.Co3
