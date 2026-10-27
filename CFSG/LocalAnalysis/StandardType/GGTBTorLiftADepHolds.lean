module

public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGTWRowGenDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem ggTorEnn_eq_zero_of_dvd_pred {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (lab : LargeEvenLabel) (h : p ∣ 2 ^ lab.n - 1) : ggTorEnn p lab = 0 := by
  have h1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
  unfold ggTorEnn
  rw [if_neg]
  intro h2
  have h3 : p ∣ (2 ^ lab.n + 1) - (2 ^ lab.n - 1) := Nat.dvd_sub h2 h
  have h4 : (2 ^ lab.n + 1) - (2 ^ lab.n - 1) = 2 := by omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

private theorem ggTorEnn_eq_one_of_dvd_succ {p : ℕ} (lab : LargeEvenLabel) (h : p ∣ 2 ^ lab.n + 1) :
    ggTorEnn p lab = 1 := by
  unfold ggTorEnn
  rw [if_pos h]

theorem ggTBTorLiftAFrom_four_holds :
    GGTBTorLiftAFrom 4 := by
  intro p hp hp2 lab hlab htag h4 hdvd hM h63
  rcases htag with htag | htag
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at htag h4 hdvd hM ⊢
    subst htag
    have hM' : p ∣ 2 ^ n - 1 := by simpa [ggTorM] using hM
    have hEnn : ggTorEnn p ⟨.A, l, n⟩ = 0 := ggTorEnn_eq_zero_of_dvd_pred hp hp2 _ hM'
    rw [hEnn]
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hM'
    have hr : l - 1 - 0 = l + 1 - 2 := by omega
    refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
    rw [hr]
    exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le (by omega)))
  · have hpq : p ∣ 2 ^ lab.n + 1 := by simpa [ggTorM, htag] using hM
    have hEnn : ggTorEnn p lab = 1 := ggTorEnn_eq_one_of_dvd_succ lab hpq
    have hrank : lab.rank - 1 - ggTorEnn p lab = ggUnitaryTorusRank p (lab.rank + 1) := by
      rw [hEnn]
      unfold ggUnitaryTorusRank
      rw [if_pos hdvd]
      omega
    rw [hrank]
    exact largeEvenLabelAll_torusLift_twA hlab htag hp hpq

theorem ggTBTorLiftADepRows_holds :
    GGTBTorLiftADepRows := by
  intro p hp hp2 lab hlab htag h6 hdvd hM
  exact ggTBTorLiftAFrom_four_holds p hp hp2 lab hlab htag (by omega) hdvd hM
    (fun h => by omega)

end CFSG.StandardType

end
