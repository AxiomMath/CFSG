module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
public import CFSG.Milestones.ASVolI.A3OddFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AbelianSylowGL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)

theorem k_CartanSylowAbelian_PSL {K : Type} [Group K] [Finite K] {m f r : ℕ} (hm3 : 3 ≤ m)
    (hmr : m < r) (hL : LieModel (K ⧸ Subgroup.center K) .PSL m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (hr : r.Prime) (hr5 : 5 ≤ r) (hrd : r ∣ 2 ^ f - 1)
    (P : Sylow r K) : IsMulCommutative (P : Subgroup K) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hf1 : 1 ≤ f := (CFSG.Blueprint.LieModel.admissible hL).2.1
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  let _ : Fintype F := Fintype.ofFinite F
  have h2f : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have hpos : 0 < 2 ^ f - 1 := by omega
  have hrle : r ≤ 2 ^ f - 1 := Nat.le_of_dvd hpos hrd
  have hk : 5 ≤ Nat.card F := by rw [hF]; omega
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  have hrF : ¬ r ∣ Nat.card F := by
    rw [hF]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)
    omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨α, hα, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_slCover (m := m') (by omega) hk hq e
  exact CFSG.ASVolI.burnsideA315x_quot_abelian α hα
    (fun R hR => CFSG.AGLEmbeddingD2.AbelianSylowGL.isMulCommutative_of_isPGroup_of_injective_GL
      hodd (d := 1) (by rwa [Fintype.card_eq_nat_card])
      (by rw [Fintype.card_eq_nat_card, pow_one, hF]; exact hrd)
      (fun j hj hj' => absurd hj' (by omega)) (by omega) Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective R hR) P P.isPGroup'

theorem k_CartanSylowAbelian_linear :
    ∀ (K : Type) [Group K] [Finite K] (t : CFSG.Open.StatedLieTag) (m f r : ℕ),
      CFSG.Open.StatedLieAdmissible t m 2 f →
        LieModel (K ⧸ Subgroup.center K) t m 2 f → CFSG.Open.IsQuasisimple K →
          Odd (Nat.card (Subgroup.center K)) →
            ((t = .PSL ∧ m = 3) ∨ (t = .PSL ∧ m = 4)) →
              r.Prime → 5 ≤ r → r ∣ 2 ^ f - 1 →
                ∀ P : Sylow r K, IsMulCommutative (P : Subgroup K) := by
  intro K _ _ t m f r _ hL hq _ ht hr hr5 hrd P
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact k_CartanSylowAbelian_PSL (by norm_num) (by omega) hL hq hr hr5 hrd P
  · exact k_CartanSylowAbelian_PSL (by norm_num) (by omega) hL hq hr hr5 hrd P

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
