module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements
import CFSG.LocalAnalysis.StandardType.GGQ2OrthSmallRank

public section

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

open CFSG CFSG.Assembly CFSG.StandardType

theorem linA1FourVacuous_holds : LinA1FourVacuous := by
  intro G _ _ H E hInn hE hC
  obtain ⟨hperf, lab, -, hraw⟩ := hInn
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hS, _, _⟩ := hQ
  change lab = ⟨.A, 1, 2⟩ at hS
  subst lab
  simp only at hraw
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨-, -, θ, -, hEN, hInd⟩ := hQK
  have hK4 : Nat.card K = 4 := by
    simpa using hK
  have hbot : E ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (H : Set G) := hx.2
    have hx3 : x ^ 3 = 1 := hE.2 x hx.1
    have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.centralizer (H : Set G))) :=
      (Nat.prime_three.coprime_iff_not_dvd).mpr hC
    have hdvdC : orderOf x ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hxC
    have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hord1 : orderOf x = 1 :=
      (Nat.coprime_comm.mp (hcop.coprime_dvd_right hdvdC)).eq_one_of_dvd hdvd3
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hord1)
  exact not_le.mpr
    (CFSG.StandardType.GGQ2Frame.OrthPlacement.card_lt_three_pow_four_of_linearRecipe
      (Or.inr ⟨rfl, hK4⟩) hperf hE hEN hbot hInd)

end CFSG.StandardType.GGQ2Frame.LinPlacement
