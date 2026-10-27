module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.LocalAnalysis.ComponentInitial Subgroup

theorem uc22sp207_exists_conj_cover {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] {X : Type} [Group X] [Finite X] (α : SpecialLinearGroup (Fin m) K →* X)
    (hα : Function.Surjective α) (S : Sylow 2 X) :
    ∃ c : X, (LinearFlag.unitriangular m K).map ((MulAut.conj c).toMonoidHom.comp α) =
      (S : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := m) hm
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X (Q.mapSurjective hα) S
  refine ⟨c, ?_⟩
  rw [← Subgroup.map_map, ← hQ, ← Sylow.coe_mapSurjective hα, ← hc]
  exact (LinearFlag.coe_sylow_smul c _).symm

theorem uc22sp207_comap_eq_flagStabilizer {m : ℕ} (_hm : 1 ≤ m) {K : Type} [Field K]
    {X : Type} [Group X] (α : SpecialLinearGroup (Fin m) K →* X) {S : Subgroup X}
    (hS : (LinearFlag.unitriangular m K).map α = S) {Y : Subgroup X}
    (hY : normalizer (S : Set X) ≤ Y) :
    (∀ i ∈ LinearFlag.borelOvergroupCuts (Y.comap α), 1 ≤ i ∧ i < m) ∧
      Y.comap α = LinearFlag.flagStabilizer m K (LinearFlag.borelOvergroupCuts (Y.comap α)) := by
  have hB : LinearFlag.upperTriangular m K ≤ Y.comap α := by
    intro b hb
    refine hY ?_
    rw [← hS]
    refine Subgroup.le_normalizer_map α ⟨b, ?_, rfl⟩
    rw [LinearFlag.normalizer_unitriangular]
    exact hb
  refine ⟨fun i ⟨hi, hin, _⟩ => ⟨hi, hin⟩, (LinearFlag.borel_overgroups _ hB).1⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
