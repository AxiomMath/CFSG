module

public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem

private theorem ggR1E6Det_three_ne_zero {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ((3 : ℤ) : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  simpa using h

theorem ggR1E6_det {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {n f : ℕ} :
    ∀ C, GGIntCartan (coxeterMatrix (ggU .E6 n f).D.isFiniteType) C →
      ((C.det : ℤ) : ZMod p) ≠ 0 := by
  intro C hC
  have hC0 : GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6) := by
    rw [show Tag.cartan .E6 = CartanMatrix.E 6 from cartanE_eq 6]
    exact ggIntCartan_E₆
  revert C
  simp only [ggU, lieUniversal]
  change ∀ C : Matrix (Fin 6) (Fin 6) ℤ,
      GGIntCartan (coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6)) C →
      ((C.det : ℤ) : ZMod p) ≠ 0
  intro C hC
  have hM : coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6) =
      CoxeterMatrix.E₆ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6) hC0
  rw [hM] at hC
  change GGIntCartan CoxeterMatrix.E₆ C at hC
  rcases hC.eq_or_eq_transpose ggIntCartan_E₆ ggAtMostOneMultipleEdge_E₆ with h | h
  · rw [h, CartanMatrix.E₆_det]
    exact ggR1E6Det_three_ne_zero hp hp3
  · rw [h, Matrix.det_transpose, CartanMatrix.E₆_det]
    exact ggR1E6Det_three_ne_zero hp hp3

end CFSG.StandardType

end
