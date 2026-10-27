module

public import CFSG.RankThree.PartOne.S15K.PSylowSub
public import CFSG.RankThree.PartOne.S15K.CommonEigen
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Transvection

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]

@[expose] def rankOne (H : LinearMap.BilinForm E W) (v : W) : Module.End E W :=
  LinearMap.smulRight (H v) v

theorem rankOne_apply (H : LinearMap.BilinForm E W) (v u : W) : rankOne H v u = H v u • v := rfl

theorem rankOne_mul_self {H : LinearMap.BilinForm E W} {v : W} (hvv : H v v = 0) :
    rankOne H v * rankOne H v = 0 :=
  LinearMap.ext fun u => by simp [rankOne_apply, hvv]

@[expose] def tvEnd (H : LinearMap.BilinForm E W) (v : W) (x : E) : Module.End E W :=
  1 + x • rankOne H v

theorem tvEnd_apply (H : LinearMap.BilinForm E W) (v : W) (x : E) (u : W) :
    tvEnd H v x u = u + (x * H v u) • v := by
  simp [tvEnd, rankOne_apply, smul_smul]

theorem tvEnd_zero (H : LinearMap.BilinForm E W) (v : W) : tvEnd H v 0 = 1 := by simp [tvEnd]

theorem tvEnd_mul {H : LinearMap.BilinForm E W} {v : W} (hvv : H v v = 0) (x y : E) :
    tvEnd H v x * tvEnd H v y = tvEnd H v (x + y) := by
  have h := rankOne_mul_self hvv
  unfold tvEnd
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h, smul_zero,
    add_zero, add_smul]
  abel

@[expose] def tvUnit {H : LinearMap.BilinForm E W} {v : W} (hvv : H v v = 0) (x : E) :
    LinearMap.GeneralLinearGroup E W :=
  ⟨tvEnd H v x, tvEnd H v (-x), by rw [tvEnd_mul hvv, add_neg_cancel, tvEnd_zero],
    by rw [tvEnd_mul hvv, neg_add_cancel, tvEnd_zero]⟩

@[expose] def tvHomSp {H : LinearMap.BilinForm E W} {v : W} (hvv : H v v = 0) :
    Multiplicative E →* LinearMap.GeneralLinearGroup E W where
  toFun x := tvUnit hvv (Multiplicative.toAdd x)
  map_one' := Units.ext (tvEnd_zero H v)
  map_mul' x y := Units.ext (by
    simp only [Units.val_mul, toAdd_mul]
    exact (tvEnd_mul hvv _ _).symm)

theorem val_tvHomSp {H : LinearMap.BilinForm E W} {v : W} (hvv : H v v = 0) (x : E) :
    ((tvHomSp hvv (Multiplicative.ofAdd x) : LinearMap.GeneralLinearGroup E W) : Module.End E W) =
      tvEnd H v x := rfl

theorem tvEnd_isometry {H : LinearMap.BilinForm E W} (hH : H.IsAlt) (v : W) (x : E) (u w : W) :
    H (tvEnd H v x u) (tvEnd H v x w) = H u w := by
  have hvv : H v v = 0 := hH v
  rw [tvEnd_apply, tvEnd_apply]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hvv]
  have hneg : H u v = - H v u := (LinearMap.IsAlt.neg hH v u).symm
  rw [hneg]
  ring

theorem tvHomSp_mem {H : LinearMap.BilinForm E W} (hH : H.IsAlt) {v : W} (hvv : H v v = 0)
    (x : Multiplicative E) : tvHomSp hvv x ∈ sesqUnitaryGroup H :=
  fun u w => tvEnd_isometry hH v _ u w

theorem mul_tvEnd {H : LinearMap.BilinForm E W} {v : W} {h : Module.End E W}
    (hiso : ∀ u w, H (h u) (h w) = H u w) {lam : E} (hv : h v = lam • v) (x : E) :
    h * tvEnd H v x = tvEnd H v (lam ^ 2 * x) * h := by
  have hN : h * rankOne H v = lam ^ 2 • (rankOne H v * h) := by
    refine LinearMap.ext fun u => ?_
    have h1 : lam * H v (h u) = H v u := by
      have := hiso v u
      rwa [hv, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
    simp only [Module.End.mul_apply, rankOne_apply, map_smul, hv, LinearMap.smul_apply, smul_smul]
    congr 1
    calc H v u * lam = lam * H v u := mul_comm _ _
      _ = lam * (lam * H v (h u)) := by rw [h1]
      _ = lam ^ 2 * H v (h u) := by ring
  unfold tvEnd
  rw [mul_add, mul_one, add_mul, one_mul, mul_smul_comm, hN, smul_mul_assoc, smul_smul]
  congr 2
  ring

end Transvection

section Main

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] [CharP E 2] {p : ℕ}

theorem psylowSub_sesqUnitary_alt [FiniteDimensional E W] (hp : p.Prime) {ζ : E}
    (hζ : IsPrimitiveRoot ζ p) (H : LinearMap.BilinForm E W) (hH : H.IsAlt)
    (hsep : ∀ v : W, v ≠ 0 → ∃ u, H v u ≠ 0) : PSylowSub p (sesqUnitaryGroup H) := by
  classical
  intro P hPY hcomm hpow hP1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    have : (ζ - 1) ^ 2 = 0 := by linear_combination hζ.pow_eq_one + (1 - ζ) * h2
    exact hζ.ne_one hp.one_lt (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this))
  obtain ⟨⟨g₀, hg₀P⟩, hg₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hP1
  set g₀' : ↥P := ⟨g₀, hg₀P⟩ with hg₀'
  let T : ↥P → Module.End E W := fun h => ((h : LinearMap.GeneralLinearGroup E W) : Module.End E W)
  have hTpow : ∀ h, T h ^ p = 1 := fun h => by
    have := hpow (h : LinearMap.GeneralLinearGroup E W) h.2
    simp only [T]
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hTcomm : ∀ h h', T h * T h' = T h' * T h := fun h h' => by
    simp only [T]
    rw [← Units.val_mul, ← Units.val_mul, hcomm _ h.2 _ h'.2]
  have hT1 : T g₀' ≠ 1 := by
    intro h
    apply hg₀1'
    exact Subtype.ext (Units.ext h)
  obtain ⟨ξ, v₀, hv₀0, hv₀, hξ1⟩ := exists_eigen_ne_one hp hp2 hζ (hTpow g₀') hT1
  let A : Module.End E W := T g₀' - ξ • 1
  let U : Submodule E W := LinearMap.ker A
  have hUmem : ∀ w, w ∈ U ↔ T g₀' w = ξ • w := fun w => by
    rw [LinearMap.mem_ker]
    show (T g₀' - ξ • 1) w = 0 ↔ _
    rw [LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hUne : U ≠ ⊥ := fun h => hv₀0 ((Submodule.mem_bot E).1 (h ▸ (hUmem v₀).2 hv₀))
  have hUstab : ∀ h : ↥P, ∀ w ∈ U, T h w ∈ U := by
    intro h w hw
    rw [hUmem] at hw ⊢
    have hc : T g₀' (T h w) = T h (T g₀' w) := by
      have := congrArg (fun f => f w) (hTcomm g₀' h)
      simpa using this
    rw [hc, hw, map_smul]
  obtain ⟨v, hvU, hv0, hvc⟩ := exists_common_eigenvector hp.pos hζ T hTcomm hTpow hUne hUstab
  choose lam hlam using hvc
  have hlam0 : ∀ h : ↥P, lam h ≠ 0 := by
    intro h h0
    apply hv0
    have h1 : T h v = 0 := by rw [hlam, h0, zero_smul]
    have h2 : (((h : LinearMap.GeneralLinearGroup E W)⁻¹ : LinearMap.GeneralLinearGroup E W) :
        Module.End E W) (T h v) = v := by
      have := congrArg (fun f : Module.End E W => f v)
        (Units.inv_mul (h : LinearMap.GeneralLinearGroup E W))
      simp only [Module.End.mul_apply, Module.End.one_apply] at this
      exact this
    rw [← h2, h1, map_zero]
  have hlam_g : lam g₀' = ξ := by
    have h1 : ξ • v = lam g₀' • v := ((hUmem v).1 hvU).symm.trans (hlam g₀')
    exact (smul_left_injective E hv0 h1).symm
  have hvv : H v v = 0 := hH v
  have hrel : ∀ (h : ↥P) (x : E), (h : LinearMap.GeneralLinearGroup E W) *
      tvHomSp hvv (Multiplicative.ofAdd x) =
      tvHomSp hvv (Multiplicative.ofAdd (lam h ^ 2 * x)) * (h : LinearMap.GeneralLinearGroup E W) :=
    fun h x => Units.ext (by
      rw [Units.val_mul, Units.val_mul, val_tvHomSp, val_tvHomSp]
      exact mul_tvEnd (fun u w => hPY h.2 u w) (hlam h) x)
  have hξsq : ξ ^ 2 ≠ 1 := by
    intro h
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    have : (ξ - 1) ^ 2 = 0 := by linear_combination h + (1 - ξ) * h2
    exact hξ1 (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this))
  have hτ : tvHomSp hvv (Multiplicative.ofAdd 1) ≠ 1 := by
    intro h
    obtain ⟨u, hu⟩ := hsep v hv0
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup E W => (g : Module.End E W) u) h
    simp only [val_tvHomSp, tvEnd_apply, Units.val_one, Module.End.one_apply, one_mul] at h1
    have h2 : H v u • v = 0 := by
      have := congrArg (fun z => z - u) h1
      simpa using this
    exact hu ((smul_eq_zero.1 h2).resolve_right hv0)
  obtain ⟨S, hSr, hS1, hS2, hS3, hS4⟩ := exists_good_of_scaling (tvHomSp hvv) (P := P) hτ
    (fun h hh => ⟨lam ⟨h, hh⟩ ^ 2, pow_ne_zero 2 (hlam0 _), fun x => hrel ⟨h, hh⟩ x⟩)
    ⟨g₀, hg₀P, ξ ^ 2, hξsq, fun x => by
      have := hrel g₀' x
      rw [hlam_g] at this
      exact this⟩
  refine ⟨S, ?_, hS1, hS2, hS3, hS4⟩
  rw [hSr]
  rintro _ ⟨y, rfl⟩
  exact tvHomSp_mem hH hvv y

end Main

end CFSG.RankThree.PartOne.S15K
