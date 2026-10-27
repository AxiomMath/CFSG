module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
public import CFSG.LinearAlgebra.FrobeniusPowerNormalizer
public import CFSG.HardMathSupport.Lang.Proving.CubeClassField
meta import Lean.Elab.Tactic.Omega

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

theorem exists_cubic_normalizer_of_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) {G : Subgroup (GL ι K)}
    (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hcard : (Nat.card G : K) ≠ 0)
    {X : GL ι K} (hXG : X ∈ G) {l : Kˣ}
    (hX : X ^ 3 = GeneralLinearGroup.scalar ι l)
    (hl : ∀ μ : Kˣ, μ ^ 3 ≠ l) {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    ∃ E : GL ι K, (E : Matrix ι ι K).det = 1 ∧
      (∀ Y ∈ G, Y ^ 3 = 1 → E * Y * E⁻¹ = Y) ∧
      E * X * E⁻¹ = GeneralLinearGroup.scalar ι ζ * X := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨E, hdet, hFrob⟩ :=
    CFSG.LinearAlgebra.exists_conj_eq_pow_card_GL_of_fintype hcomm hcard
  have hlpow : l ^ (Nat.card K - 1) = 1 := by
    rw [← Nat.card_units K]
    exact pow_card_eq_one'
  let β : Kˣ := l ^ ((Nat.card K - 1) / 3)
  have hβ3 : β ^ 3 = 1 := by
    dsimp [β]
    rw [← pow_mul, Nat.div_mul_cancel h3, hlpow]
  have hβne : β ≠ 1 := by
    intro hβ
    obtain ⟨μ, hμ⟩ :=
      (CFSG.HardMathSupport.Lang.Proving.exists_cube_iff_pow_eq_one h3 l).mpr hβ
    exact hl μ hμ
  have hβ : IsPrimitiveRoot β 3 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hβ3 hβne)
  have hq : Nat.card K = 3 * ((Nat.card K - 1) / 3) + 1 := by
    have := Nat.div_mul_cancel h3
    have := Finite.one_lt_card (α := K)
    omega
  have hEX : E * X * E⁻¹ = GeneralLinearGroup.scalar ι β * X := by
    rw [hFrob X hXG, ← Nat.card_eq_fintype_card, hq, pow_add, pow_mul, hX,
      ← map_pow, pow_one]
  let θ := MulAut.conj E
  have hθX : θ X = GeneralLinearGroup.scalar ι β * X := hEX
  have hθscalar : ∀ s : Kˣ,
      θ (GeneralLinearGroup.scalar ι s) = GeneralLinearGroup.scalar ι s := by
    intro s
    change E * GeneralLinearGroup.scalar ι s * E⁻¹ = _
    rw [← (commute_scalar s E).eq, mul_inv_cancel_right]
  have hθpow : ∀ k : ℕ, (θ ^ k) X = GeneralLinearGroup.scalar ι (β ^ k) * X := by
    intro k
    induction k with
    | zero => simp
    | succ k hk =>
      rw [pow_succ', MulAut.mul_apply, hk, map_mul, hθscalar, hθX,
        ← mul_assoc, ← map_mul, ← pow_succ]
  have hζK : (ζ : K) ^ 3 = 1 := by simpa using congrArg (fun s : Kˣ => (s : K)) hζ
  obtain ⟨k, -, hk⟩ := (IsPrimitiveRoot.coe_units_iff.mpr hβ).eq_pow_of_pow_eq_one hζK
  have hkU : β ^ k = ζ := Units.ext (by simpa using hk)
  refine ⟨E ^ k, ?_, ?_, ?_⟩
  · have hdetU : GeneralLinearGroup.det E = 1 := Units.ext hdet
    change (GeneralLinearGroup.det (E ^ k) : K) = 1
    rw [map_pow, hdetU, one_pow, Units.val_one]
  · intro Y hYG hY3
    have hθY : θ Y = Y := by
      change E * Y * E⁻¹ = Y
      rw [hFrob Y hYG, ← Nat.card_eq_fintype_card, hq, pow_add, pow_mul, hY3,
        one_pow, pow_one, one_mul]
    have hθpowY : ∀ j : ℕ, (θ ^ j) Y = Y := by
      intro j
      induction j with
      | zero => simp
      | succ j hj => rw [pow_succ', MulAut.mul_apply, hj, hθY]
    change MulAut.conj (E ^ k) Y = Y
    rw [map_pow]
    exact hθpowY k
  · change MulAut.conj (E ^ k) X = _
    rw [map_pow]
    exact hkU ▸ hθpow k

end CFSG.StandardType.TypeA.PGLTor
