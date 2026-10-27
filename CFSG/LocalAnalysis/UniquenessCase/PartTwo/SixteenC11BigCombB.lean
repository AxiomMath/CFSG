module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigOrb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCombBA
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c11_big_no_a2_odd {n : ℕ} (hn : ¬ 2 ∣ n) {E : Subgroup (Equiv.Perm (Fin n))}
    (hE : IsElemAbelian 2 E) (hE1 : E ≠ ⊥)
    (hB : ∀ B : Subgroup (Equiv.Perm (Fin n)), B ≤ E → B.relIndex E ≤ 2 →
      ∀ q : (FFModel.symDn n).Mod,
        (∀ σ ∈ B, (FFModel.symDn_isActionModel n).modAct σ q = q) →
          ∀ σ ∈ E, (FFModel.symDn_isActionModel n).modAct σ q = q) :
    False := by
  obtain ⟨j, hj_ne, hj_inv, -, -⟩ := s16c11_big_a2_orbits (Or.inl hn) hE hE1 hB
  have hj2 : j ^ 2 = 1 := by
    ext i
    simp [pow_two, hj_inv i]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (α := Fin n) (p := 2) (n := 1)
    (by simpa [Fintype.card_fin] using hn) (by simpa using hj2)
  exact hj_ne a ha

theorem s16c11_big_a2_ten {E : Subgroup (Equiv.Perm (Fin 10))} (hE : IsElemAbelian 2 E)
    (hE1 : E ≠ ⊥)
    (hB : ∀ B : Subgroup (Equiv.Perm (Fin 10)), B ≤ E → B.relIndex E ≤ 2 →
      ∀ q : (FFModel.symDn 10).Mod,
        (∀ σ ∈ B, (FFModel.symDn_isActionModel 10).modAct σ q = q) →
          ∀ σ ∈ E, (FFModel.symDn_isActionModel 10).modAct σ q = q) :
    Nat.card {q : (FFModel.symDn 10).Mod //
      ∀ σ ∈ E, (FFModel.symDn_isActionModel 10).modAct σ q = q} = 16 := by
  obtain ⟨j, hj_ne, hj_inv, hj_or, hj_surj⟩ := s16c11_big_a2_orbits (Or.inr rfl) hE hE1 hB
  exact s16c11_big_combb_card_fixed_classes hj_ne hj_inv hj_or hj_surj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
