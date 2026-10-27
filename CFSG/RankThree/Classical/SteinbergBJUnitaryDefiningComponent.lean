module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.RankThreeEven (localRank)

theorem unitary_defining_prime_actual_component_parameter_restriction {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬p ∣ Nat.card N) (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {n f : ℕ}
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n p f) :
    (n = 3 ∧ 1 ≤ f ∧ f ≤ 3) ∨ (n = 4 ∧ f = 1) := by
  have hL := localRank_le_of_le_quotient hp (by omega) N hN L
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨φ, hφ, hker⟩ :=
    CFSG.RankThree.CentralLift.exists_top_cover (e.trans (unitaryPSUEquiv h (by omega)).symm)
  have hw := unitary_defining_prime_central_cover_two_local_rank_witness ⊤ h hp3 hn φ hφ hker
  rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
  · have h1 := hw.2.2.1 1 le_rfl (by norm_num)
    rw [one_pow, mul_one] at h1
    exact Or.inl ⟨rfl, hf, by omega⟩
  · have h2 := hw.2.2.2 rfl
    exact Or.inr ⟨rfl, by omega⟩
  · have h4 := hw.2.2.1 2 (by norm_num) (by omega)
    omega

end CFSG.RankThree.Classical
