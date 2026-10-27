module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2OrthCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrMain
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveAbel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem s1611e3_modelRF3_orthMinus {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : m = 3 ∨ m = 4) {b c : K}
    (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    S16C11ModelRF3 (FFModel.nat
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hpoly' : ∀ t : ZMod 2, t ^ 2 + e b * t + e c ≠ 0 := by
    intro t h0
    apply hpoly (e.symm t)
    apply e.injective
    simpa using h0
  have hbc : e b = 1 ∧ e c = 1 := by
    have h0 := hpoly' 0
    have h1 := hpoly' 1
    generalize e b = x at h0 h1 ⊢
    generalize e c = y at h0 h1 ⊢
    revert x y
    decide
  obtain ⟨hb, hc⟩ := hbc
  have hmap := CFSG.ClassicalInvolution.Upgrade.map_closure_preserving e
    (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := m) (b := b) (c := c) e hb hc)
  exact s16c11_modelRF3_of_ringEquiv e hmap (s16c11_modelRF3_orthMinus_zmod_struct hm)

theorem s1611e3_rf3_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {L L₀ : Subgroup (MulAut W)} {J : Subgroup W} {n : ℕ} (hn : n = 6 ∨ n = 8)
    (hL₀ : IsOMinus ↥L₀ n 1) (hL : IsOmegaMinus ↥L n 1) (hle : L ≤ L₀)
    (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) (hN : NatOmegaMinus L J ⊥ n 1) :
    S16C11RF3 L₀ J := by
  obtain ⟨K, hKf, hKfin, b, c, hKcard, hpoly, hreal⟩ :=
    s16c11_orth_realizes hn hle hL₀ hL hJ hN
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hm : n / 2 = 3 ∨ n / 2 = 4 := by rcases hn with rfl | rfl <;> simp
  exact s16c11_rf3_of_modelRF3 (FFModel.nat_faithful _) hreal
    (s1611e3_modelRF3_orthMinus hKcard hm hpoly)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
