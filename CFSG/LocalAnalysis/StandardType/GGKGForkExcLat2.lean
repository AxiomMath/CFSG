module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggKGEl_conj_injective
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)}
    (F : ExcFrame τ K p E) :
    Function.Injective (fun x : adjointGroup τ K =>
      F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * F.D.g0) := by
  intro x y h
  have h' : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) := by
    have := congrArg (fun z => F.D.g0 * z * F.D.g0⁻¹) h
    simpa [mul_assoc] using this
  exact Subtype.ext (baseChangeGL_injective (f := algebraMap K (AlgebraicClosure K)) h')

theorem ggKGEl_zetaPow_pow_eq_one {L : Type} [Field L] {p : ℕ} (ζ : Lˣ)
    (hζ : IsPrimitiveRoot ζ p) (a : ℤ) : (ζ ^ a) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]

theorem ggKGEl_eq_zetaPow_of_pow_eq_one {L : Type} [Field L] {p : ℕ} [NeZero p] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot ζ p) {b : Lˣ} (hb : b ^ p = 1) :
    ∃ y : ℤ, b = ζ ^ y := by
  have hζL : IsPrimitiveRoot (ζ : L) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have hbL : (b : L) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hb, Units.val_one]
  obtain ⟨k, -, hk⟩ := hζL.eq_pow_of_pow_eq_one hbL
  exact ⟨k, Units.ext (by simpa using hk.symm)⟩

end CFSG.StandardType

end
