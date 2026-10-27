module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Out

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.RankThree.GF2n.Stroth80
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {K : Type} [Field K] [Finite K]

theorem s16g_card_dvd_of_norm {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) {E : Subgroup (MulAut (Multiplicative (ι → K)))}
    (hEN : E ≤ s16gNorm Γ) :
    Nat.card E ∣ Nat.card (RingAut K) * Nat.card (GL ι K) := by
  obtain ⟨θ, -, hker⟩ := s16g_exists_theta hΓ
  let φ : ↥E →* RingAut K := θ.comp (Subgroup.inclusion hEN)
  let Ksub : Subgroup (MulAut (Multiplicative (ι → K))) := φ.ker.map E.subtype
  have hKsubN : Ksub ≤ s16gNorm Γ := by
    rintro y ⟨x, -, rfl⟩
    exact hEN x.2
  have hKsubL : Ksub ≤ s16gLin ι K := by
    rintro y ⟨x, hx, rfl⟩
    have hx' : θ (Subgroup.inclusion hEN x) = 1 := by
      simpa [φ] using MonoidHom.mem_ker.mp hx
    exact (hker (Subgroup.inclusion hEN x)).1 hx'
  obtain ⟨F, -, hFmap⟩ := s16g_exists_matrix_subgroup hKsubN hKsubL
  have hkerdvd : Nat.card φ.ker ∣ Nat.card (GL ι K) := by
    rw [show Nat.card φ.ker = Nat.card F by
      rw [show Nat.card φ.ker = Nat.card Ksub from
          (Subgroup.card_map_of_injective E.subtype_injective).symm,
        ← hFmap,
        Subgroup.card_map_of_injective (s16gNatHom_injective (ι := ι) (K := K))]]
    exact Subgroup.card_subgroup_dvd_card F
  have hrangedvd : Nat.card φ.range ∣ Nat.card (RingAut K) :=
    Subgroup.card_subgroup_dvd_card φ.range
  have hdvd : Nat.card φ.ker * Nat.card φ.range ∣
      Nat.card (RingAut K) * Nat.card (GL ι K) := by
    rw [mul_comm (Nat.card (RingAut K)) (Nat.card (GL ι K))]
    exact Nat.mul_dvd_mul hkerdvd hrangedvd
  rwa [show Nat.card E = Nat.card φ.ker * Nat.card φ.range from
    (Subgroup.card_ker_mul_card_range φ).symm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
