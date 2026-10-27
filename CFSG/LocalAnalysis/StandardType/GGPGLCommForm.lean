module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormPairing
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic

public section

namespace CFSG.StandardType.CommForm

open Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type*} [Field K]

@[expose] noncomputable def scomm (x y : GL κ K) : Kˣ := by
  classical
  exact if h : ∃ u : Kˣ, x * y = GeneralLinearGroup.scalar κ u * (y * x) then h.choose else 1

theorem scomm_spec {x y : GL κ K}
    (h : ∃ u : Kˣ, x * y = GeneralLinearGroup.scalar κ u * (y * x)) :
    x * y = GeneralLinearGroup.scalar κ (scomm x y) * (y * x) := by
  rw [scomm, dif_pos h]
  exact h.choose_spec

theorem scomm_eq [Nonempty κ] {x y : GL κ K} {u : Kˣ}
    (h : x * y = GeneralLinearGroup.scalar κ u * (y * x)) : scomm x y = u := by
  refine TypeA.PGLTor.eq_of_scalar_mul_eq (x := y * x) ?_
  rw [← scomm_spec (x := x) (y := y) ⟨u, h⟩, h]

variable {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V]

section ScalarCommutator

variable {x y z : GL κ K} {u v : Kˣ}

private theorem cfScalarSwap (c d : Kˣ) (w : GL κ K) :
    GeneralLinearGroup.scalar κ c * (GeneralLinearGroup.scalar κ d * w) =
      GeneralLinearGroup.scalar κ d * (GeneralLinearGroup.scalar κ c * w) := by
  have hcd : GeneralLinearGroup.scalar κ c * GeneralLinearGroup.scalar κ d =
      GeneralLinearGroup.scalar κ d * GeneralLinearGroup.scalar κ c := by
    rw [← map_mul, ← map_mul, mul_comm c d]
  rw [← mul_assoc, hcd, mul_assoc]

private theorem cfRelScalarLeft (c : Kˣ)
    (h : x * y = GeneralLinearGroup.scalar κ u * (y * x)) :
    (GeneralLinearGroup.scalar κ c * x) * y =
      GeneralLinearGroup.scalar κ u * (y * (GeneralLinearGroup.scalar κ c * x)) := by
  have hy : y * (GeneralLinearGroup.scalar κ c * x) =
      GeneralLinearGroup.scalar κ c * (y * x) := by
    rw [← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm c y, mul_assoc]
  calc (GeneralLinearGroup.scalar κ c * x) * y
      = GeneralLinearGroup.scalar κ c * (x * y) := by rw [mul_assoc]
    _ = GeneralLinearGroup.scalar κ c *
        (GeneralLinearGroup.scalar κ u * (y * x)) := by rw [h]
    _ = GeneralLinearGroup.scalar κ u *
        (y * (GeneralLinearGroup.scalar κ c * x)) := by
          rw [hy, cfScalarSwap c u (y * x)]

private theorem cfRelScalarRight (c : Kˣ)
    (h : x * y = GeneralLinearGroup.scalar κ u * (y * x)) :
    x * (GeneralLinearGroup.scalar κ c * y) =
      GeneralLinearGroup.scalar κ u *
        ((GeneralLinearGroup.scalar κ c * y) * x) := by
  have hx : x * (GeneralLinearGroup.scalar κ c * y) =
      GeneralLinearGroup.scalar κ c * (x * y) := by
    rw [← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm c x, mul_assoc]
  calc x * (GeneralLinearGroup.scalar κ c * y)
      = GeneralLinearGroup.scalar κ c * (x * y) := hx
    _ = GeneralLinearGroup.scalar κ c *
        (GeneralLinearGroup.scalar κ u * (y * x)) := by rw [h]
    _ = GeneralLinearGroup.scalar κ u *
        ((GeneralLinearGroup.scalar κ c * y) * x) := by
          rw [cfScalarSwap c u (y * x)]
          congr 1
          simp only [mul_assoc]

private theorem cfRelMulLeft
    (hx : x * z = GeneralLinearGroup.scalar κ u * (z * x))
    (hy : y * z = GeneralLinearGroup.scalar κ v * (z * y)) :
    (x * y) * z = GeneralLinearGroup.scalar κ (u * v) * (z * (x * y)) := by
  calc (x * y) * z = x * (y * z) := by rw [mul_assoc]
    _ = x * (GeneralLinearGroup.scalar κ v * (z * y)) := by rw [hy]
    _ = GeneralLinearGroup.scalar κ v * (x * (z * y)) := by
          conv_lhs => rw [← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm v x, mul_assoc]
    _ = GeneralLinearGroup.scalar κ v * ((x * z) * y) := by simp only [mul_assoc]
    _ = GeneralLinearGroup.scalar κ v *
        ((GeneralLinearGroup.scalar κ u * (z * x)) * y) := by rw [hx]
    _ = GeneralLinearGroup.scalar κ (u * v) * (z * (x * y)) := by
          rw [map_mul]
          conv_lhs => simp only [mul_assoc]
          rw [cfScalarSwap v u (z * (x * y))]
          conv_rhs => simp only [mul_assoc]

private theorem cfRelMulRight
    (hx : x * y = GeneralLinearGroup.scalar κ u * (y * x))
    (hy : x * z = GeneralLinearGroup.scalar κ v * (z * x)) :
    x * (y * z) = GeneralLinearGroup.scalar κ (u * v) * ((y * z) * x) := by
  have hshift : y * (GeneralLinearGroup.scalar κ v * (z * x)) =
      GeneralLinearGroup.scalar κ v * (y * (z * x)) := by
    rw [← mul_assoc, ← TypeA.PGLTor.scalar_mul_comm v y, mul_assoc]
  have hyz : y * (z * x) = (y * z) * x := by rw [mul_assoc]
  calc x * (y * z) = (x * y) * z := by rw [mul_assoc]
    _ = (GeneralLinearGroup.scalar κ u * (y * x)) * z := by rw [hx]
    _ = GeneralLinearGroup.scalar κ u * (y * (x * z)) := by simp only [mul_assoc]
    _ = GeneralLinearGroup.scalar κ u *
        (y * (GeneralLinearGroup.scalar κ v * (z * x))) := by rw [hy]
    _ = GeneralLinearGroup.scalar κ (u * v) * ((y * z) * x) := by
          rw [map_mul, hshift, hyz]
          simp only [mul_assoc]

private theorem cfRelConj (S : GL κ K)
    (h : x * y = GeneralLinearGroup.scalar κ u * (y * x)) :
    (S * x * S⁻¹) * (S * y * S⁻¹) =
      GeneralLinearGroup.scalar κ u * ((S * y * S⁻¹) * (S * x * S⁻¹)) := by
  have hS : S * GeneralLinearGroup.scalar κ u * S⁻¹ =
      GeneralLinearGroup.scalar κ u := by
    rw [← TypeA.PGLTor.scalar_mul_comm u S, mul_assoc, mul_inv_cancel, mul_one]
  calc (S * x * S⁻¹) * (S * y * S⁻¹) = S * (x * y) * S⁻¹ := by group
    _ = S * (GeneralLinearGroup.scalar κ u * (y * x)) * S⁻¹ := by rw [h]
    _ = (S * GeneralLinearGroup.scalar κ u * S⁻¹) * (S * (y * x) * S⁻¹) := by group
    _ = GeneralLinearGroup.scalar κ u * (S * (y * x) * S⁻¹) := by rw [hS]
    _ = GeneralLinearGroup.scalar κ u * ((S * y * S⁻¹) * (S * x * S⁻¹)) := by
          congr 1
          group

private theorem cfScommScalarBoth [Nonempty κ] (c d : Kˣ) {u : Kˣ}
    (h : x * y = GeneralLinearGroup.scalar κ u * (y * x)) :
    scomm (GeneralLinearGroup.scalar κ c * x)
      (GeneralLinearGroup.scalar κ d * y) = u :=
  scomm_eq (cfRelScalarRight d (cfRelScalarLeft c h))

private theorem cfScommSelf [Nonempty κ] (x : GL κ K) : scomm x x = 1 := by
  apply scomm_eq
  rw [map_one, one_mul]

private theorem cfConjPow {x y : GL κ K} {u : Kˣ}
    (h : x * y = GeneralLinearGroup.scalar κ u * (y * x)) (n : ℕ) :
    x ^ n * y * (x ^ n)⁻¹ = GeneralLinearGroup.scalar κ (u ^ n) * y := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : x * y * x⁻¹ = GeneralLinearGroup.scalar κ u * y := by
        rw [h]
        group
      have hx1 : x * GeneralLinearGroup.scalar κ (u ^ n) =
          GeneralLinearGroup.scalar κ (u ^ n) * x :=
        (TypeA.PGLTor.scalar_mul_comm (u ^ n) x).symm
      have hx : x * (GeneralLinearGroup.scalar κ (u ^ n) * y) * x⁻¹ =
          GeneralLinearGroup.scalar κ (u ^ n) * (x * y * x⁻¹) := by
        calc x * (GeneralLinearGroup.scalar κ (u ^ n) * y) * x⁻¹
            = (x * GeneralLinearGroup.scalar κ (u ^ n)) * y * x⁻¹ := by
                simp only [mul_assoc]
          _ = (GeneralLinearGroup.scalar κ (u ^ n) * x) * y * x⁻¹ := by rw [hx1]
          _ = GeneralLinearGroup.scalar κ (u ^ n) * (x * y * x⁻¹) := by group
      calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹
          = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by group
        _ = x * (GeneralLinearGroup.scalar κ (u ^ n) * y) * x⁻¹ := by rw [ih]
        _ = GeneralLinearGroup.scalar κ (u ^ n) * (x * y * x⁻¹) := hx
        _ = GeneralLinearGroup.scalar κ (u ^ n) *
            (GeneralLinearGroup.scalar κ u * y) := by rw [hstep]
        _ = GeneralLinearGroup.scalar κ (u ^ (n + 1)) * y := by
              rw [pow_succ, map_mul]
              group

end ScalarCommutator

section Exponent

variable [NeZero p] {ζ : Kˣ}

omit [Fact p.Prime] in
private theorem cfExp_exists (hζ : IsPrimitiveRoot ζ p) {u : Kˣ} (hu : u ^ p = 1) :
    ∃ i < p, ζ ^ i = u :=
  hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p u).mpr hu)

private noncomputable def cfExp (hζ : IsPrimitiveRoot ζ p) (u : Kˣ) : ZMod p := by
  classical
  exact if hu : u ^ p = 1 then ((cfExp_exists hζ hu).choose : ZMod p) else 0

private theorem cfExp_spec (hζ : IsPrimitiveRoot ζ p) (u : Kˣ) (hu : u ^ p = 1) :
    ζ ^ (cfExp hζ u).val = u := by
  obtain ⟨hi, hval⟩ := (cfExp_exists hζ hu).choose_spec
  rw [cfExp, dif_pos hu, ZMod.val_natCast_of_lt hi]
  exact hval

private theorem cfExp_eq (hζ : IsPrimitiveRoot ζ p) {u : Kˣ} (hu : u ^ p = 1)
    {k : ZMod p} (hk : ζ ^ k.val = u) : cfExp hζ u = k := by
  obtain ⟨hi, hval⟩ := (cfExp_exists hζ hu).choose_spec
  rw [cfExp, dif_pos hu]
  apply ZMod.val_injective p
  rw [ZMod.val_natCast_of_lt hi]
  exact hζ.pow_inj hi (ZMod.val_lt k) (hval.trans hk.symm)

private theorem cfExp_one (hζ : IsPrimitiveRoot ζ p) :
    cfExp (p := p) hζ (1 : Kˣ) = 0 := by
  apply cfExp_eq hζ (one_pow p)
  rw [ZMod.val_zero, pow_zero]

private theorem cfExp_mul (hζ : IsPrimitiveRoot ζ p) {u v : Kˣ}
    (hu : u ^ p = 1) (hv : v ^ p = 1) :
    cfExp hζ (u * v) = cfExp hζ u + cfExp hζ v := by
  have huv : (u * v) ^ p = 1 := by
    rw [mul_pow, hu, hv, one_mul]
  apply cfExp_eq hζ huv
  rw [ZMod.val_add,
    ← pow_eq_pow_mod ((cfExp hζ u).val + (cfExp hζ v).val) hζ.pow_eq_one,
    pow_add, cfExp_spec hζ u hu, cfExp_spec hζ v hv]

end Exponent

section Lift

variable {B : E → GL κ K}

private theorem bScalarOne
    (hB : ∀ a b : E, ∃ c : Kˣ, B (a * b) = GeneralLinearGroup.scalar κ c * (B a * B b)) :
    ∃ c : Kˣ, B 1 = GeneralLinearGroup.scalar κ c := by
  obtain ⟨c, hc⟩ := hB 1 1
  have h1 : B 1 = GeneralLinearGroup.scalar κ c * (B 1 * B 1) := by simpa using hc
  have h2 : B 1 = B 1 * (GeneralLinearGroup.scalar κ c * B 1) := by
    conv_lhs => rw [h1]
    conv_lhs => rw [← mul_assoc, TypeA.PGLTor.scalar_mul_comm c (B 1), mul_assoc]
  have h3 : (1 : GL κ K) = GeneralLinearGroup.scalar κ c * B 1 := by
    have h2' : B 1 * 1 = B 1 * (GeneralLinearGroup.scalar κ c * B 1) := by
      simpa using h2
    exact mul_left_cancel h2'
  refine ⟨c⁻¹, ?_⟩
  have h4 : B 1 = (GeneralLinearGroup.scalar κ c)⁻¹ := by
    have h5 := congrArg (fun w => (GeneralLinearGroup.scalar κ c)⁻¹ * w) h3
    simpa [← mul_assoc] using h5.symm
  simpa using h4

omit [Fact p.Prime] in
private theorem bExistsScalarPow
    (hB : ∀ a b : E, ∃ c : Kˣ, B (a * b) = GeneralLinearGroup.scalar κ c * (B a * B b))
    (hexp : ∀ a : E, a ^ p = 1) (a : E) :
    ∃ c : Kˣ, (B a) ^ p = GeneralLinearGroup.scalar κ c := by
  obtain ⟨c0, hc0⟩ := bScalarOne hB
  have key : ∀ k : ℕ, ∃ c : Kˣ,
      B (a ^ k) = GeneralLinearGroup.scalar κ c * (B a) ^ k := by
    intro k
    induction k with
    | zero => exact ⟨c0, by simpa using hc0⟩
    | succ k ih =>
        obtain ⟨c, hc⟩ := ih
        obtain ⟨d, hd⟩ := hB (a ^ k) a
        refine ⟨d * c, ?_⟩
        rw [pow_succ, hd, hc, map_mul, pow_succ]
        group
  obtain ⟨c, hc⟩ := key p
  rw [hexp a] at hc
  have hsc : GeneralLinearGroup.scalar κ c0 =
      GeneralLinearGroup.scalar κ c * (B a) ^ p := by
    rw [← hc0, hc]
  have hX : (B a) ^ p = (GeneralLinearGroup.scalar κ c)⁻¹ *
      GeneralLinearGroup.scalar κ c0 := by
    rw [hsc, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨c⁻¹ * c0, ?_⟩
  rw [hX, map_mul, map_inv]

private theorem bExistsScomm
    (hB : ∀ a b : E, ∃ c : Kˣ, B (a * b) = GeneralLinearGroup.scalar κ c * (B a * B b))
    (hcomm : ∀ a b : E, a * b = b * a) (a b : E) :
    ∃ u : Kˣ, B a * B b = GeneralLinearGroup.scalar κ u * (B b * B a) := by
  obtain ⟨c, hc⟩ := hB a b
  obtain ⟨d, hd⟩ := hB b a
  have h1 : GeneralLinearGroup.scalar κ c * (B a * B b) =
      GeneralLinearGroup.scalar κ d * (B b * B a) := by
    rw [← hc, ← hd, hcomm a b]
  refine ⟨c⁻¹ * d, ?_⟩
  calc B a * B b = (GeneralLinearGroup.scalar κ c)⁻¹ *
        (GeneralLinearGroup.scalar κ c * (B a * B b)) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ = (GeneralLinearGroup.scalar κ c)⁻¹ *
        (GeneralLinearGroup.scalar κ d * (B b * B a)) := by rw [h1]
    _ = GeneralLinearGroup.scalar κ (c⁻¹ * d) * (B b * B a) := by
          rw [map_mul, map_inv]
          group

private noncomputable def sFun (B : E → GL κ K) (a b : E) : Kˣ :=
  scomm (B a) (B b)

private theorem sFun_spec [Nonempty κ]
    (hB : ∀ a b : E, ∃ c : Kˣ, B (a * b) = GeneralLinearGroup.scalar κ c * (B a * B b))
    (hcomm : ∀ a b : E, a * b = b * a) (a b : E) :
    B a * B b = GeneralLinearGroup.scalar κ (sFun B a b) * (B b * B a) := by
  simpa [sFun] using scomm_spec (bExistsScomm hB hcomm a b)

omit [Fact p.Prime] in
private theorem sFun_pow [Nonempty κ]
    (hB : ∀ a b : E, ∃ c : Kˣ, B (a * b) = GeneralLinearGroup.scalar κ c * (B a * B b))
    (hcomm : ∀ a b : E, a * b = b * a) (hexp : ∀ a : E, a ^ p = 1) (a b : E) :
    sFun B a b ^ p = 1 := by
  obtain ⟨c, hc⟩ := bExistsScalarPow hB hexp a
  have hspec : B a * B b = GeneralLinearGroup.scalar κ (sFun B a b) * (B b * B a) :=
    sFun_spec hB hcomm a b
  have hconj := cfConjPow hspec p
  have hcentral : (B a) ^ p * B b * ((B a) ^ p)⁻¹ = B b := by
    rw [hc, TypeA.PGLTor.scalar_mul_comm c (B b), mul_assoc, mul_inv_cancel, mul_one]
  have h1 : GeneralLinearGroup.scalar κ (sFun B a b ^ p) * B b = B b :=
    hconj.symm.trans hcentral
  have h2 : GeneralLinearGroup.scalar κ (sFun B a b ^ p) = 1 := by
    have h1' : GeneralLinearGroup.scalar κ (sFun B a b ^ p) * B b = 1 * B b := by
      rw [one_mul]
      exact h1
    exact mul_right_cancel h1'
  exact TypeA.PGLTor.scalar_injective (by rw [h2, map_one])

private theorem sFun_mul_left [Nonempty κ]
    (hB : ∀ a b : E, ∃ c : Kˣ, B (a * b) = GeneralLinearGroup.scalar κ c * (B a * B b))
    (hcomm : ∀ a b : E, a * b = b * a) (a b c : E) :
    sFun B (a * b) c = sFun B a c * sFun B b c := by
  obtain ⟨d, hd⟩ := hB a b
  have hrel := cfRelScalarLeft d
    (cfRelMulLeft (sFun_spec hB hcomm a c) (sFun_spec hB hcomm b c))
  rw [← hd] at hrel
  simpa [sFun] using scomm_eq hrel

private theorem sFun_mul_right [Nonempty κ]
    (hB : ∀ a b : E, ∃ c : Kˣ, B (a * b) = GeneralLinearGroup.scalar κ c * (B a * B b))
    (hcomm : ∀ a b : E, a * b = b * a) (a b c : E) :
    sFun B a (b * c) = sFun B a b * sFun B a c := by
  obtain ⟨d, hd⟩ := hB b c
  have hrel := cfRelScalarRight d
    (cfRelMulRight (sFun_spec hB hcomm a b) (sFun_spec hB hcomm a c))
  rw [← hd] at hrel
  simpa [sFun] using scomm_eq hrel

end Lift

theorem exists_commForm [Nonempty κ] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {B : E → GL κ K}
    (hB : ∀ a b, ∃ c : Kˣ, B (a * b) = GeneralLinearGroup.scalar κ c * (B a * B b))
    (hcomm : ∀ a b : E, a * b = b * a) (hexp : ∀ a : E, a ^ p = 1) (ι : Additive E ≃+ V) :
    ∃ ω : LinearMap.BilinForm (ZMod p) V,
      (∀ a b : E,
        ζ ^ (ω (ι (Additive.ofMul a)) (ι (Additive.ofMul b))).val = scomm (B a) (B b)) ∧
      ∀ v, ω v v = 0 := by
  classical
  have hne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let om : E → E → ZMod p := fun a b => cfExp (p := p) hζ (scomm (B a) (B b))
  have om_mul_left : ∀ a b c : E, om (a * b) c = om a c + om b c := by
    intro a b c
    have hm : scomm (B (a * b)) (B c) =
        scomm (B a) (B c) * scomm (B b) (B c) := by
      simpa [sFun] using sFun_mul_left hB hcomm a b c
    have h1 : scomm (B a) (B c) ^ p = 1 := by
      simpa [sFun] using sFun_pow hB hcomm hexp a c
    have h2 : scomm (B b) (B c) ^ p = 1 := by
      simpa [sFun] using sFun_pow hB hcomm hexp b c
    change cfExp hζ (scomm (B (a * b)) (B c)) =
      cfExp hζ (scomm (B a) (B c)) + cfExp hζ (scomm (B b) (B c))
    rw [hm, cfExp_mul hζ h1 h2]
  have om_mul_right : ∀ a b c : E, om a (b * c) = om a b + om a c := by
    intro a b c
    have hm : scomm (B a) (B (b * c)) =
        scomm (B a) (B b) * scomm (B a) (B c) := by
      simpa [sFun] using sFun_mul_right hB hcomm a b c
    have h1 : scomm (B a) (B b) ^ p = 1 := by
      simpa [sFun] using sFun_pow hB hcomm hexp a b
    have h2 : scomm (B a) (B c) ^ p = 1 := by
      simpa [sFun] using sFun_pow hB hcomm hexp a c
    change cfExp hζ (scomm (B a) (B (b * c))) =
      cfExp hζ (scomm (B a) (B b)) + cfExp hζ (scomm (B a) (B c))
    rw [hm, cfExp_mul hζ h1 h2]
  have om_self : ∀ a : E, om a a = 0 := by
    intro a
    change cfExp hζ (scomm (B a) (B a)) = 0
    rw [cfScommSelf (B a), cfExp_one hζ]
  let g : V → V → ZMod p := fun v w =>
    om (Additive.toMul (ι.symm v)) (Additive.toMul (ι.symm w))
  have g_add_left : ∀ x y z : V, g (x + y) z = g x z + g y z := by
    intro x y z
    change om (Additive.toMul (ι.symm (x + y))) (Additive.toMul (ι.symm z)) =
      om (Additive.toMul (ι.symm x)) (Additive.toMul (ι.symm z)) +
        om (Additive.toMul (ι.symm y)) (Additive.toMul (ι.symm z))
    rw [map_add ι.symm x y, toMul_add]
    exact om_mul_left _ _ _
  have g_add_right : ∀ x y z : V, g x (y + z) = g x y + g x z := by
    intro x y z
    change om (Additive.toMul (ι.symm x)) (Additive.toMul (ι.symm (y + z))) =
      om (Additive.toMul (ι.symm x)) (Additive.toMul (ι.symm y)) +
        om (Additive.toMul (ι.symm x)) (Additive.toMul (ι.symm z))
    rw [map_add ι.symm y z, toMul_add]
    exact om_mul_right _ _ _
  have g_smul_left : ∀ (c : ZMod p) (x y : V), g (c • x) y = c • g x y := by
    intro c x y
    have hc : c • x = c.val • x := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul]
    have hnsmul : ∀ n : ℕ, g (n • x) y = n • g x y := by
      intro n
      induction n with
      | zero =>
          have h0 : g (0 : V) y = g 0 y + g 0 y := by
            rw [← g_add_left (x := 0) (y := 0) (z := y), add_zero]
          exact (add_left_cancel (a := g (0 : V) y) (by simpa using h0)).symm
      | succ n ih => rw [succ_nsmul, g_add_left, ih, succ_nsmul]
    rw [hc, hnsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, smul_eq_mul]
  have g_smul_right : ∀ (c : ZMod p) (x y : V), g x (c • y) = c • g x y := by
    intro c x y
    have hc : c • y = c.val • y := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul]
    have hnsmul : ∀ n : ℕ, g x (n • y) = n • g x y := by
      intro n
      induction n with
      | zero =>
          have h0 : g x (0 : V) = g x 0 + g x 0 := by
            rw [← g_add_right (x := x) (y := 0) (z := 0), add_zero]
          exact (add_left_cancel (a := g x (0 : V)) (by simpa using h0)).symm
      | succ n ih => rw [succ_nsmul, g_add_right, ih, succ_nsmul]
    rw [hc, hnsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, smul_eq_mul]
  let omega : LinearMap.BilinForm (ZMod p) V :=
    LinearMap.mk₂ (ZMod p) g g_add_left g_smul_left g_add_right g_smul_right
  refine ⟨omega, ?_, ?_⟩
  · intro a b
    have hg : omega (ι (Additive.ofMul a)) (ι (Additive.ofMul b)) = om a b := by
      change g (ι (Additive.ofMul a)) (ι (Additive.ofMul b)) = om a b
      change om (Additive.toMul (ι.symm (ι (Additive.ofMul a))))
        (Additive.toMul (ι.symm (ι (Additive.ofMul b)))) = om a b
      simp only [AddEquiv.symm_apply_apply, toMul_ofMul]
    rw [hg]
    exact cfExp_spec hζ (scomm (B a) (B b)) (by
      simpa [sFun] using sFun_pow hB hcomm hexp a b)
  · intro v
    change g v v = 0
    change om (Additive.toMul (ι.symm v)) (Additive.toMul (ι.symm v)) = 0
    exact om_self _

theorem commForm_ggLin [Nonempty κ] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {B : E → GL κ K}
    (hB : ∀ a b, ∃ c : Kˣ, B (a * b) = GeneralLinearGroup.scalar κ c * (B a * B b))
    (hcomm : ∀ a b : E, a * b = b * a) (ι : Additive E ≃+ V)
    {ω : LinearMap.BilinForm (ZMod p) V}
    (hω : ∀ a b : E,
      ζ ^ (ω (ι (Additive.ofMul a)) (ι (Additive.ofMul b))).val = scomm (B a) (B b))
    {σ : MulAut E} {S : GL κ K}
    (hσ : ∀ a, ∃ c : Kˣ, B (σ a) = GeneralLinearGroup.scalar κ c * (S * B a * S⁻¹)) (u v : V) :
    ω (ggLin (p := p) ι σ u) (ggLin (p := p) ι σ v) = ω u v := by
  classical
  have hne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hkey : ∀ a b : E, scomm (B (σ a)) (B (σ b)) = scomm (B a) (B b) := by
    intro a b
    have hspec : B a * B b =
        GeneralLinearGroup.scalar κ (scomm (B a) (B b)) * (B b * B a) :=
      scomm_spec (bExistsScomm hB hcomm a b)
    have hconj := cfRelConj (S := S) hspec
    have hscalar := cfScommScalarBoth (c := (hσ a).choose) (d := (hσ b).choose) hconj
    rw [(hσ a).choose_spec, (hσ b).choose_spec]
    exact hscalar
  have hω' : ∀ a b : E,
      ω (ι (Additive.ofMul (σ a))) (ι (Additive.ofMul (σ b))) =
        ω (ι (Additive.ofMul a)) (ι (Additive.ofMul b)) := by
    intro a b
    apply ZMod.val_injective p
    apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    rw [hω (σ a) (σ b), hkey a b, ← hω a b]
  have hv : ∀ w : V, w = ι (Additive.ofMul (Additive.toMul (ι.symm w))) := by
    intro w
    simp
  rw [ggLin_apply, ggLin_apply]
  conv_rhs => rw [hv u, hv v]
  exact hω' (Additive.toMul (ι.symm u)) (Additive.toMul (ι.symm v))

end CFSG.StandardType.CommForm
