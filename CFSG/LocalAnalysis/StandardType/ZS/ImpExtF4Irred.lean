module

public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4B3
import CFSG.LocalAnalysis.StandardType.ZS.ThroughRefl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.FFourCoord

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private def intCastMatrix : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) (ZMod p) :=
  (Int.castRingHom (ZMod p)).mapMatrix

private noncomputable def toMatrixHom {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} (ρ : A →* (V ≃ₗ[ZMod p] V))
    (e : Module.Basis (Fin 3) (ZMod p) V) : A →* Matrix (Fin 3) (Fin 3) (ZMod p) where
  toFun x := LinearMap.toMatrix e e ((ρ x : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V)
  map_one' := by
    rw [map_one, LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_id]
  map_mul' x y := by
    rw [map_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

private theorem toMatrixHom_injective {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) : Function.Injective (toMatrixHom ρ e) := by
  intro x y hxy
  exact hρ (LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix e e).injective hxy))

private theorem eq_of_toMatrixHom_eq {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) {q r : A} {L R : Matrix (Fin 3) (Fin 3) ℤ}
    (hq : toMatrixHom ρ e q = intCastMatrix L) (hr : toMatrixHom ρ e r = intCastMatrix R)
    (h : intCastMatrix (p := p) L = intCastMatrix (p := p) R) : q = r :=
  toMatrixHom_injective hρ e (by rw [hq, hr, h])

private theorem mul_ne_one_of_ne_of_involution {x y : U ≃ₗ[ZMod p] U}
    (hy : y * y = 1) (hne : x ≠ y) : x * y ≠ 1 := by
  intro h
  apply hne
  calc x = x * (y * y) := by rw [hy, mul_one]
    _ = (x * y) * y := by rw [mul_assoc]
    _ = 1 * y := by rw [h]
    _ = y := one_mul y

private theorem reflB3_order_ne {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) {x y : U ≃ₗ[ZMod p] U} (hxA : x ∈ A) (hyA : y ∈ A)
    {i j : Fin 9} (hx : toMatrixHom ρ e ⟨x, hxA⟩ = intCastMatrix (reflB3 i))
    (hy : toMatrixHom ρ e ⟨y, hyA⟩ = intCastMatrix (reflB3 j))
    (hxy : orderOf (x * y) = 4) :
    (reflB3 i * reflB3 j) ^ 2 ≠ 1 ∧ (reflB3 i * reflB3 j) ^ 3 ≠ 1 := by
  have hτinj := toMatrixHom_injective hρ e
  have hab : toMatrixHom ρ e (⟨x, hxA⟩ * ⟨y, hyA⟩) =
      intCastMatrix (reflB3 i * reflB3 j) := by
    simp only [map_mul, hx, hy]
  have hord : orderOf (toMatrixHom ρ e (⟨x, hxA⟩ * ⟨y, hyA⟩)) = 4 := by
    rw [orderOf_injective (toMatrixHom ρ e) hτinj,
      ← orderOf_injective (Subgroup.subtype A) A.subtype_injective]
    exact hxy
  constructor
  · intro h2
    have h : (toMatrixHom ρ e (⟨x, hxA⟩ * ⟨y, hyA⟩)) ^ 2 = 1 := by
      rw [hab, ← map_pow, h2, map_one]
    have hdvd : orderOf (toMatrixHom ρ e (⟨x, hxA⟩ * ⟨y, hyA⟩)) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hord] at hdvd
    norm_num at hdvd
  · intro h3
    have h : (toMatrixHom ρ e (⟨x, hxA⟩ * ⟨y, hyA⟩)) ^ 3 = 1 := by
      rw [hab, ← map_pow, h3, map_one]
    have hdvd : orderOf (toMatrixHom ρ e (⟨x, hxA⟩ * ⟨y, hyA⟩)) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hord] at hdvd
    norm_num at hdvd

private theorem reflB3_ne {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) {x y z : U ≃ₗ[ZMod p] U} (hxA : x ∈ A)
    (hyA : y ∈ A) (hzA : z ∈ A) {i j k : Fin 9}
    (hx : toMatrixHom ρ e ⟨x, hxA⟩ = intCastMatrix (reflB3 i))
    (hy : toMatrixHom ρ e ⟨y, hyA⟩ = intCastMatrix (reflB3 j))
    (hz : toMatrixHom ρ e ⟨z, hzA⟩ = intCastMatrix (reflB3 k))
    (hzx : z ≠ x) (hzy : z ≠ y) (hzxyx : z ≠ x * y * x) (hzyxy : z ≠ y * x * y)
    (hzc : z * (x * y * x) ≠ (x * y * x) * z) :
    reflB3 k ≠ reflB3 i ∧ reflB3 k ≠ reflB3 j ∧
      reflB3 k ≠ reflB3 i * reflB3 j * reflB3 i ∧
      reflB3 k ≠ reflB3 j * reflB3 i * reflB3 j ∧
      reflB3 k * (reflB3 i * reflB3 j * reflB3 i) ≠
        reflB3 i * reflB3 j * reflB3 i * reflB3 k := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hzx (Subtype.ext_iff.mp (eq_of_toMatrixHom_eq hρ e hz hx (congrArg intCastMatrix h)))
  · intro h
    exact hzy (Subtype.ext_iff.mp (eq_of_toMatrixHom_eq hρ e hz hy (congrArg intCastMatrix h)))
  · intro h
    have hR : toMatrixHom ρ e (⟨x, hxA⟩ * ⟨y, hyA⟩ * ⟨x, hxA⟩) =
        intCastMatrix (reflB3 i * reflB3 j * reflB3 i) := by
      simp only [map_mul, hx, hy]
    exact hzxyx (Subtype.ext_iff.mp (eq_of_toMatrixHom_eq hρ e hz hR (congrArg intCastMatrix h)))
  · intro h
    have hR : toMatrixHom ρ e (⟨y, hyA⟩ * ⟨x, hxA⟩ * ⟨y, hyA⟩) =
        intCastMatrix (reflB3 j * reflB3 i * reflB3 j) := by
      simp only [map_mul, hx, hy]
    exact hzyxy (Subtype.ext_iff.mp (eq_of_toMatrixHom_eq hρ e hz hR (congrArg intCastMatrix h)))
  · intro h
    have hL : toMatrixHom ρ e (⟨z, hzA⟩ * (⟨x, hxA⟩ * ⟨y, hyA⟩ * ⟨x, hxA⟩)) =
        intCastMatrix (reflB3 k * (reflB3 i * reflB3 j * reflB3 i)) := by
      simp only [map_mul, hx, hy, hz]
    have hR : toMatrixHom ρ e ((⟨x, hxA⟩ * ⟨y, hyA⟩ * ⟨x, hxA⟩) * ⟨z, hzA⟩) =
        intCastMatrix ((reflB3 i * reflB3 j * reflB3 i) * reflB3 k) := by
      simp only [map_mul, hx, hy, hz]
    exact hzc (Subtype.ext_iff.mp (eq_of_toMatrixHom_eq hρ e hL hR (congrArg intCastMatrix h)))

private theorem reflB3_hypotheses {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) {x y z : U ≃ₗ[ZMod p] U} (hxA : x ∈ A)
    (hyA : y ∈ A) (hzA : z ∈ A) {i j k : Fin 9}
    (hx : toMatrixHom ρ e ⟨x, hxA⟩ = intCastMatrix (reflB3 i))
    (hy : toMatrixHom ρ e ⟨y, hyA⟩ = intCastMatrix (reflB3 j))
    (hz : toMatrixHom ρ e ⟨z, hzA⟩ = intCastMatrix (reflB3 k))
    (hxy : orderOf (x * y) = 4) (hzx : z ≠ x) (hzy : z ≠ y)
    (hzxyx : z ≠ x * y * x) (hzyxy : z ≠ y * x * y)
    (hzc : z * (x * y * x) ≠ (x * y * x) * z) :
    (reflB3 i * reflB3 j) ^ 2 ≠ 1 ∧ (reflB3 i * reflB3 j) ^ 3 ≠ 1 ∧
      reflB3 k ≠ reflB3 i ∧ reflB3 k ≠ reflB3 j ∧
      reflB3 k ≠ reflB3 i * reflB3 j * reflB3 i ∧
      reflB3 k ≠ reflB3 j * reflB3 i * reflB3 j ∧
      reflB3 k * (reflB3 i * reflB3 j * reflB3 i) ≠
        reflB3 i * reflB3 j * reflB3 i * reflB3 k := by
  obtain ⟨h1, h2⟩ := reflB3_order_ne hρ e hxA hyA hx hy hxy
  obtain ⟨h3, h4, h5, h6, h7⟩ :=
    reflB3_ne hρ e hxA hyA hzA hx hy hz hzx hzy hzxyx hzyxy hzc
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

private theorem orderOf_eq_three_of_cube {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) {q : A} {M : Matrix (Fin 3) (Fin 3) ℤ}
    (hqM : toMatrixHom ρ e q = intCastMatrix M) (hM : M ^ 3 = 1)
    (hq1 : (q : U ≃ₗ[ZMod p] U) ≠ 1) : orderOf (q : U ≃ₗ[ZMod p] U) = 3 := by
  have hτinj := toMatrixHom_injective hρ e
  have hpow : q ^ 3 = 1 := by
    apply hτinj
    rw [map_pow, hqM, ← map_pow, hM, map_one, map_one]
  have hdvd : orderOf q ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have h3 : orderOf q = 3 := by
    rcases (Nat.dvd_prime (show Nat.Prime 3 by norm_num)).mp hdvd with h | h
    · exact absurd h (fun hq' => hq1 (congrArg Subtype.val (orderOf_eq_one_iff.mp hq')))
    · exact h
  rwa [← orderOf_injective (Subgroup.subtype A) A.subtype_injective] at h3

private theorem reflB3_conclusion_i {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) {x y z : U ≃ₗ[ZMod p] U} (hxA : x ∈ A)
    (hyA : y ∈ A) (hzA : z ∈ A) {i j k : Fin 9}
    (hx : toMatrixHom ρ e ⟨x, hxA⟩ = intCastMatrix (reflB3 i))
    (hy : toMatrixHom ρ e ⟨y, hyA⟩ = intCastMatrix (reflB3 j))
    (hz : toMatrixHom ρ e ⟨z, hzA⟩ = intCastMatrix (reflB3 k))
    (hzy : z * y ≠ 1)
    (h1 : reflB3 j * reflB3 k * reflB3 j * reflB3 i =
      reflB3 i * (reflB3 j * reflB3 k * reflB3 j))
    (h2 : (reflB3 k * reflB3 j) ^ 3 = 1) :
    y * z * y * x = x * (y * z * y) ∧ orderOf (z * y) = 3 := by
  have hL : toMatrixHom ρ e (⟨y, hyA⟩ * ⟨z, hzA⟩ * ⟨y, hyA⟩ * ⟨x, hxA⟩) =
      intCastMatrix (reflB3 j * reflB3 k * reflB3 j * reflB3 i) := by
    simp only [map_mul, hx, hy, hz]
  have hR : toMatrixHom ρ e (⟨x, hxA⟩ * (⟨y, hyA⟩ * ⟨z, hzA⟩ * ⟨y, hyA⟩)) =
      intCastMatrix (reflB3 i * (reflB3 j * reflB3 k * reflB3 j)) := by
    simp only [map_mul, hx, hy, hz]
  have hzy' : toMatrixHom ρ e (⟨z, hzA⟩ * ⟨y, hyA⟩) =
      intCastMatrix (reflB3 k * reflB3 j) := by
    simp only [map_mul, hy, hz]
  exact ⟨Subtype.ext_iff.mp (eq_of_toMatrixHom_eq hρ e hL hR (congrArg intCastMatrix h1)),
    orderOf_eq_three_of_cube hρ e hzy' h2 hzy⟩

private theorem reflB3_conclusion_ii {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) {x y z : U ≃ₗ[ZMod p] U} (hxA : x ∈ A)
    (hyA : y ∈ A) (hzA : z ∈ A) {i j k : Fin 9}
    (hx : toMatrixHom ρ e ⟨x, hxA⟩ = intCastMatrix (reflB3 i))
    (hy : toMatrixHom ρ e ⟨y, hyA⟩ = intCastMatrix (reflB3 j))
    (hz : toMatrixHom ρ e ⟨z, hzA⟩ = intCastMatrix (reflB3 k))
    (hzy : z * y ≠ 1) (h3 : reflB3 k * reflB3 i = reflB3 i * reflB3 k)
    (h4 : (reflB3 k * reflB3 j) ^ 3 = 1) :
    z * x = x * z ∧ orderOf (z * y) = 3 := by
  have hL : toMatrixHom ρ e (⟨z, hzA⟩ * ⟨x, hxA⟩) =
      intCastMatrix (reflB3 k * reflB3 i) := by simp only [map_mul, hx, hz]
  have hR : toMatrixHom ρ e (⟨x, hxA⟩ * ⟨z, hzA⟩) =
      intCastMatrix (reflB3 i * reflB3 k) := by simp only [map_mul, hx, hz]
  have hzy' : toMatrixHom ρ e (⟨z, hzA⟩ * ⟨y, hyA⟩) =
      intCastMatrix (reflB3 k * reflB3 j) := by simp only [map_mul, hy, hz]
  exact ⟨Subtype.ext_iff.mp (eq_of_toMatrixHom_eq hρ e hL hR (congrArg intCastMatrix h3)),
    orderOf_eq_three_of_cube hρ e hzy' h4 hzy⟩

private theorem reflB3_conclusion_iii {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) {x y z : U ≃ₗ[ZMod p] U} (hxA : x ∈ A)
    (hyA : y ∈ A) (hzA : z ∈ A) {i j k : Fin 9}
    (hx : toMatrixHom ρ e ⟨x, hxA⟩ = intCastMatrix (reflB3 i))
    (hy : toMatrixHom ρ e ⟨y, hyA⟩ = intCastMatrix (reflB3 j))
    (hz : toMatrixHom ρ e ⟨z, hzA⟩ = intCastMatrix (reflB3 k))
    (hxz : x * z ≠ 1) (h5 : (reflB3 i * reflB3 k) ^ 3 = 1)
    (h6 : reflB3 j * reflB3 k = reflB3 k * reflB3 j) :
    orderOf (x * z) = 3 ∧ y * z = z * y := by
  have hL : toMatrixHom ρ e (⟨y, hyA⟩ * ⟨z, hzA⟩) =
      intCastMatrix (reflB3 j * reflB3 k) := by simp only [map_mul, hy, hz]
  have hR : toMatrixHom ρ e (⟨z, hzA⟩ * ⟨y, hyA⟩) =
      intCastMatrix (reflB3 k * reflB3 j) := by simp only [map_mul, hy, hz]
  have hxz' : toMatrixHom ρ e (⟨x, hxA⟩ * ⟨z, hzA⟩) =
      intCastMatrix (reflB3 i * reflB3 k) := by simp only [map_mul, hx, hz]
  exact ⟨orderOf_eq_three_of_cube hρ e hxz' h5 hxz,
    Subtype.ext_iff.mp (eq_of_toMatrixHom_eq hρ e hL hR (congrArg intCastMatrix h6))⟩

private theorem reflB3_conclusion {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U} {ρ : A →* (V ≃ₗ[ZMod p] V)} (hρ : Function.Injective ρ)
    (e : Module.Basis (Fin 3) (ZMod p) V) {x y z : U ≃ₗ[ZMod p] U} (hxA : x ∈ A)
    (hyA : y ∈ A) (hzA : z ∈ A) {i j k : Fin 9}
    (hx : toMatrixHom ρ e ⟨x, hxA⟩ = intCastMatrix (reflB3 i))
    (hy : toMatrixHom ρ e ⟨y, hyA⟩ = intCastMatrix (reflB3 j))
    (hz : toMatrixHom ρ e ⟨z, hzA⟩ = intCastMatrix (reflB3 k))
    (hzy : z * y ≠ 1) (hxz : x * z ≠ 1)
    (h : (reflB3 j * reflB3 k * reflB3 j * reflB3 i =
          reflB3 i * (reflB3 j * reflB3 k * reflB3 j) ∧ (reflB3 k * reflB3 j) ^ 3 = 1) ∨
        (reflB3 k * reflB3 i = reflB3 i * reflB3 k ∧ (reflB3 k * reflB3 j) ^ 3 = 1) ∨
        ((reflB3 i * reflB3 k) ^ 3 = 1 ∧ reflB3 j * reflB3 k = reflB3 k * reflB3 j)) :
    (y * z * y * x = x * (y * z * y) ∧ orderOf (z * y) = 3) ∨
      (z * x = x * z ∧ orderOf (z * y) = 3) ∨
      (orderOf (x * z) = 3 ∧ y * z = z * y) := by
  rcases h with ⟨h1, h2⟩ | ⟨h3, h4⟩ | ⟨h5, h6⟩
  · exact Or.inl (reflB3_conclusion_i hρ e hxA hyA hzA hx hy hz hzy h1 h2)
  · exact Or.inr (Or.inl (reflB3_conclusion_ii hρ e hxA hyA hzA hx hy hz hzy h3 h4))
  · exact Or.inr (Or.inr (reflB3_conclusion_iii hρ e hxA hyA hzA hx hy hz hxz h5 h6))

theorem irred_cases_of_g2mmn (hp : p ≠ 2) {a b g : U ≃ₗ[ZMod p] U} (haR : IsRefl p a)
    (hbR : IsRefl p b) (hgR : IsRefl p g) (hS : SplitSupport (Subgroup.closure {a, b, g}) 3)
    (e : Module.Basis (Fin 3) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    (he : movedGroup (Subgroup.closure {a, b, g}) = g2mmn p e 0 1 1)
    (hab : orderOf (a * b) = 4) (hga : g ≠ a) (hgb : g ≠ b) (hgaba : g ≠ a * b * a)
    (hgbab : g ≠ b * a * b) (hg : g * (a * b * a) ≠ a * b * a * g) :
    (b * g * b * a = a * (b * g * b) ∧ orderOf (g * b) = 3) ∨
      (g * a = a * g ∧ orderOf (g * b) = 3) ∨ (orderOf (a * g) = 3 ∧ b * g = g * b) := by
  let A : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure {a, b, g}
  let V := HardMathSupport.Kantor79.commutatorSpace A
  let ρ := restrictHom A V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have haA : a ∈ A := Subgroup.subset_closure (by simp)
  have hbA : b ∈ A := Subgroup.subset_closure (by simp)
  have hgA : g ∈ A := Subgroup.subset_closure (by simp)
  have hρ : Function.Injective ρ := restrictHom_injective_of_splitSupport hS
  have haR' : IsRefl p (ρ ⟨a, haA⟩) := isRefl_restrictHom_of_isRefl hS haR
  have hbR' : IsRefl p (ρ ⟨b, hbA⟩) := isRefl_restrictHom_of_isRefl hS hbR
  have hgR' : IsRefl p (ρ ⟨g, hgA⟩) := isRefl_restrictHom_of_isRefl hS hgR
  have hma : ρ ⟨a, haA⟩ ∈ g2mmn p e 0 1 1 := by
    rw [← he]; exact MonoidHom.mem_range.mpr ⟨⟨a, haA⟩, rfl⟩
  have hmb : ρ ⟨b, hbA⟩ ∈ g2mmn p e 0 1 1 := by
    rw [← he]; exact MonoidHom.mem_range.mpr ⟨⟨b, hbA⟩, rfl⟩
  have hmg : ρ ⟨g, hgA⟩ ∈ g2mmn p e 0 1 1 := by
    rw [← he]; exact MonoidHom.mem_range.mpr ⟨⟨g, hgA⟩, rfl⟩
  obtain ⟨i, hi⟩ := exists_reflB3_of_isRefl hp e hma haR'
  obtain ⟨j, hj⟩ := exists_reflB3_of_isRefl hp e hmb hbR'
  obtain ⟨k, hk⟩ := exists_reflB3_of_isRefl hp e hmg hgR'
  have hgb1 : g * b ≠ 1 := mul_ne_one_of_ne_of_involution hbR.1 hgb
  have hag1 : a * g ≠ 1 := mul_ne_one_of_ne_of_involution hgR.1 (fun h => hga h.symm)
  have htri := reflB3_trichotomy i j k
    (reflB3_hypotheses hρ e haA hbA hgA hi hj hk hab hga hgb hgaba hgbab hg)
  exact reflB3_conclusion hρ e haA hbA hgA hi hj hk hgb1 hag1 htri

end CFSG.StandardType.ZS.FFourCoord

end
