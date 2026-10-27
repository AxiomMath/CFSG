module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveOrb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem s16c13bcA_orbit_eq_of_odd {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    (hnat : NatOmegaPlus H (⊤ : Subgroup W) ⊥ 4 2) {w₁ w₂ : W} (h₁ : w₁ ≠ 1) (h₂ : w₂ ≠ 1)
    (o₁ : Odd (Nat.card (MulAction.orbit ↥H w₁)))
    (o₂ : Odd (Nat.card (MulAction.orbit ↥H w₂))) : w₂ ∈ MulAction.orbit ↥H w₁ := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hR⟩ := hnat
  letI := hKf
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hKcard])
  obtain ⟨φ, hφ0, hφ⟩ := s16c13bcA_nat_orbit_transfer
    (Γ := StatedOmega (StatedQuadPlus (4 / 2) K)) hR
  have hv₁ : φ w₁ ≠ 0 := fun h => h₁ ((hφ0 w₁).mp h)
  have hv₂ : φ w₂ ≠ 0 := fun h => h₂ ((hφ0 w₂).mp h)
  obtain ⟨-, hc₁⟩ := hφ w₁ w₁
  obtain ⟨-, hc₂⟩ := hφ w₂ w₂
  obtain ⟨hmem, -⟩ := hφ w₁ w₂
  have o₁' : Odd (Nat.card (MulAction.orbit ↥(StatedOmega (StatedQuadPlus 2 K)) (φ w₁))) := by
    rw [← hc₁]
    exact o₁
  have o₂' : Odd (Nat.card (MulAction.orbit ↥(StatedOmega (StatedQuadPlus 2 K)) (φ w₂))) := by
    rw [← hc₂]
    exact o₂
  exact hmem.mpr (s16c13bcA_omega_orbit_unique hcard4 hv₁ hv₂ o₁' o₂')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
