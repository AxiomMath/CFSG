
module

public import CFSG.Sporadic.Co2Rank3.FactsBase
public import CFSG.Sporadic.Co2Rank3.OrbitLabels

@[expose] public noncomputable section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Sporadic.Co2Rank3.Native MulAction

theorem recOK_spec {gens : Array (Array ℕ)} {rec : Array ℕ × Array ℕ × Array ℕ × Array ℕ}
    {roots : List (ℕ × ℕ)} {Gs : ℕ → Equiv.Perm (Fin 2300)} (h : recOK gens rec roots = true)
    (hrep : ∀ k < gens.size, Rep 2300 gens[k]! (Gs k)) :
    (∀ x y : Fin 2300, y ∈ orbit (Subgroup.closure {g | ∃ k < gens.size, Gs k = g}) x ↔
      rec.1[(y : ℕ)]! = rec.1[(x : ℕ)]!) ∧
    (∀ x : Fin 2300, ∃ r ∈ roots, r.1 = rec.1[(x : ℕ)]!) ∧
    (∀ r ∈ roots, rec.1[r.1]! = r.1) ∧
    (∀ r ∈ roots, ∀ hr : r.1 < 2300,
      (orbit (Subgroup.closure {g | ∃ k < gens.size, Gs k = g}) (⟨r.1, hr⟩ : Fin 2300)).ncard =
        r.2) := by
  simp only [recOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hF := orbitFacts_of_orbitsOK h1
  obtain ⟨hl1, hl2⟩ := labelsOK_spec h2
  refine ⟨fun x y => mem_orbit_iff_lab hF hrep, fun x => hl1 x x.2, hl2, fun r hr hr' => ?_⟩
  rw [ncard_orbit_eq hF hrep, ← h3 r hr, labCount]
  simp only [hl2 r hr]

theorem orbit_co2P0_zero : orbit co2P0 (0 : Fin 2300) = {0} :=
  orbit_subgroup_eq_singleton fun _ hk => mem_stabilizer_iff.1 hk.2

theorem co2P_exists_smul
    (x y : Fin 2300) : ∃ g ∈ co2P, g • x = y := by
  have := co2P_transitive
  obtain ⟨⟨g, hg⟩, h⟩ := MulAction.exists_smul_eq co2P x y
  exact ⟨g, hg, h⟩

theorem co2P_htr
    (x : Fin 2300) : ∃ g ∈ co2P, g • (0 : Fin 2300) = x := co2P_exists_smul 0 x

theorem co2P_eq_closure_gens :
    co2P = Subgroup.closure {g | ∃ k < co2OrigArrs.size, co2Gen k = g} := by
  rw [co2P, co2OrigArrs_size]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · left; rfl
    · right; rfl

end CFSG.Sporadic.Co2Rank3
