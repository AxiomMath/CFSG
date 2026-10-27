module

public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggR1E7_det {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n f : ℕ} :
    ∀ C, GGIntCartan (coxeterMatrix (ggU .E7 n f).D.isFiniteType) C →
      ((C.det : ℤ) : ZMod p) ≠ 0 := by
  intro C hC
  have hC0 : GGIntCartan CoxeterMatrix.E₇ (Tag.cartan .E7) := by
    rw [show Tag.cartan .E7 = CartanMatrix.E 7 from cartanE_eq 7]
    exact ggIntCartan_E₇
  have hunit : ((2 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  revert C
  simp only [ggU, lieUniversal]
  intro C hC
  have hM : coxeterMatrix (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7) =
      CoxeterMatrix.E₇ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7) hC0
  rw [hM] at hC
  rcases GGIntCartan.eq_or_eq_transpose hC ggIntCartan_E₇ ggAtMostOneMultipleEdge_E₇ with
    h | h
  · rw [h]
    change (((CartanMatrix.E 7).det : ℤ) : ZMod p) ≠ 0
    rw [CartanMatrix.E₇_det]
    exact hunit
  · rw [h]
    change ((((CartanMatrix.E 7).transpose).det : ℤ) : ZMod p) ≠ 0
    rw [Matrix.det_transpose, CartanMatrix.E₇_det]
    exact hunit

end CFSG.StandardType

end
