module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup
open scoped Matrix

abbrev omegaModelOfCoords {W : Type} [CommGroup W] {F : Type} [Field F] [Finite F]
    [CharP F 2] (h4 : 4 ≤ Nat.card F) (ψ : W ≃* Multiplicative (Fin 2 ⊕ Fin 2 → F)) :
    OmegaModel W :=
  { K := F, four_le := h4, e := ψ }

theorem omegaModelOfCoords_omega_le {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (ε : ↥H ≃* ↥(StatedOmega (StatedQuadPlus 2 F)))
    (ψ : W ≃* Multiplicative (Fin 2 ⊕ Fin 2 → F)) (hψ : NatCoordsOmegaPlus H F ε ψ) :
    (omegaModelOfCoords h4 ψ).omega ≤ H := by
  let S : OmegaModel W := omegaModelOfCoords h4 ψ
  change S.omega ≤ H
  intro h hh
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hh
  have hact : S.actHom γ = ((ε.symm ⟨γ, hγ⟩ : ↥H) : MulAut W) := by
    refine MulEquiv.ext fun w => S.vec_injective ?_
    rw [S.actHom_vec]
    show (γ : Matrix OmI OmI S.K) *ᵥ S.vec w =
      Multiplicative.toAdd (ψ (((ε.symm ⟨γ, hγ⟩ : ↥H) : MulAut W) w))
    rw [hψ (ε.symm ⟨γ, hγ⟩) w, MulEquiv.apply_symm_apply]
    rfl
  rw [hact]
  exact (ε.symm ⟨γ, hγ⟩).2

theorem k_K_Omega4Plus_nonsingPoint_holds : K_Omega4Plus_nonsingPoint := by
  intro W _ _ H p n hn2 _hΩ _hN hp hcong F _ _ hF ε ψ hψ v hv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := n) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_of_le (by norm_num) hn2
  have hpq : p ∣ Nat.card F + 1 := by
    rw [hF]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  let S : OmegaModel W := omegaModelOfCoords h4 ψ
  have hSH : S.omega ≤ H := omegaModelOfCoords_omega_le h4 ε ψ hψ
  have hQ : S.Q v ≠ 0 := by
    change StatedQuadPlus 2 F (Multiplicative.toAdd (ψ v)) ≠ 0
    exact hv
  refine ⟨ptCent S.omega0 v, ?_, S.isPerfect_ptCent_omega0 hQ, ?_, ?_⟩
  · intro e he
    exact hSH (S.omega0_le_omega he.1)
  · rw [S.card_ptCent_omega0 hQ]
    exact dvd_mul_of_dvd_right
      (CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_sq_sub_one hpq) (Nat.card S.K)
  · intro e he
    have h2 : e • v = v := MulAction.mem_stabilizer_iff.mp he.2
    simpa [MulAut.smul_def] using h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
