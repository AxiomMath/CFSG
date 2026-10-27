module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupExt
public import CFSG.ClassicalGroups.Orthogonal.OddOrder

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec715Torus

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

section Generic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def torusLin (P : HypPair Q) (s : K) : V →ₗ[K] V where
  toFun v := v + ((s - 1) * polar Q v P.f) • P.e + ((s⁻¹ - 1) * polar Q v P.e) • P.f
  map_add' x y := by
    simp only [polar_add_left, mul_add, add_smul]
    abel
  map_smul' c x := by
    simp only [polar_smul_left_eq, RingHom.id_apply, smul_add, smul_smul]
    rw [mul_left_comm, mul_left_comm c]
    module

theorem torusLin_apply (P : HypPair Q) (s : K) (v : V) :
    torusLin P s v = v + ((s - 1) * polar Q v P.f) • P.e + ((s⁻¹ - 1) * polar Q v P.e) • P.f :=
  rfl

theorem polar_torusLin_f (P : HypPair Q) (s : K) (v : V) :
    polar Q (torusLin P s v) P.f = s * polar Q v P.f := by
  rw [torusLin_apply]
  simp only [polar_add_left, polar_smul_left_eq, P.polar_ef, P.polar_ff]
  ring

theorem polar_torusLin_e (P : HypPair Q) {s : K} (hs : s ≠ 0) (v : V) :
    polar Q (torusLin P s v) P.e = s⁻¹ * polar Q v P.e := by
  rw [torusLin_apply]
  simp only [polar_add_left, polar_smul_left_eq, P.polar_fe, P.polar_ee]
  field_simp
  ring

theorem torusLin_comp (P : HypPair Q) {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) (v : V) :
    torusLin P t (torusLin P s v) = torusLin P (s * t) v := by
  rw [torusLin_apply P t (torusLin P s v), polar_torusLin_f, polar_torusLin_e P hs]
  rw [torusLin_apply P s v, torusLin_apply P (s * t) v]
  simp only [mul_inv]
  module

theorem torusLin_one (P : HypPair Q) (v : V) : torusLin P 1 v = v := by
  simp [torusLin_apply]

theorem map_torusLin (P : HypPair Q) {s : K} (hs : s ≠ 0) (v : V) :
    Q (torusLin P s v) = Q v := by
  rw [torusLin_apply, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_smul,
    QuadraticMap.map_smul, P.Q_e, P.Q_f]
  simp only [polar_add_right, polar_add_left, polar_smul_right_eq, polar_smul_left_eq,
    P.polar_ef, polar_comm Q P.e v, polar_comm Q P.f v, smul_zero, smul_eq_mul, mul_zero,
    add_zero]
  field_simp
  ring

@[expose] def torusEquiv (P : HypPair Q) {s : K} (hs : s ≠ 0) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (torusLin P s) (torusLin P s⁻¹)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, torusLin_comp P (inv_ne_zero hs) hs, inv_mul_cancel₀ hs,
        torusLin_one, LinearMap.id_apply])
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, torusLin_comp P hs (inv_ne_zero hs), mul_inv_cancel₀ hs,
        torusLin_one, LinearMap.id_apply])

theorem torusEquiv_apply (P : HypPair Q) {s : K} (hs : s ≠ 0) (v : V) :
    torusEquiv P hs v = torusLin P s v := rfl

theorem torusEquiv_mem_orthogonalGroup (P : HypPair Q) {s : K} (hs : s ≠ 0) :
    torusEquiv P hs ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_torusLin P hs v

theorem torusEquiv_pow_apply (P : HypPair Q) {s : K} (hs : s ≠ 0) (k : ℕ) (v : V) :
    ((torusEquiv P hs) ^ k) v = torusLin P (s ^ k) v := by
  induction k generalizing v with
  | zero => simp [torusLin_one]
  | succ k ih =>
    rw [pow_succ, LinearEquiv.mul_apply, torusEquiv_apply, ih,
      torusLin_comp P hs (pow_ne_zero k hs), pow_succ, mul_comm]

theorem torusLin_app_e (P : HypPair Q) (s : K) : torusLin P s P.e = s • P.e := by
  rw [torusLin_apply, P.polar_ee, P.polar_ef]
  simp only [mul_zero, zero_smul, add_zero, mul_one]
  module

theorem torusLin_app_f (P : HypPair Q) {s : K} (hs : s ≠ 0) : torusLin P s P.f = s⁻¹ • P.f := by
  rw [torusLin_apply, P.polar_ff, P.polar_fe]
  simp only [mul_zero, zero_smul, add_zero, mul_one]
  module

theorem torusLin_app_of_perp (P : HypPair Q) (s : K) {v : V} (he : polar Q v P.e = 0)
    (hf : polar Q v P.f = 0) : torusLin P s v = v := by
  rw [torusLin_apply, he, hf]
  simp

@[expose] def pairSwap (P : HypPair Q) : HypPair Q :=
  ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩

theorem torusLin_swap (P : HypPair Q) (s : K) (v : V) :
    torusLin (pairSwap P) s v = torusLin P s⁻¹ v := by
  simp only [torusLin_apply, pairSwap, inv_inv]
  abel

end Generic

section GomTorus

open CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem odd_card_sub_one_of_charTwo : Odd (Nat.card K - 1) := by
  haveI := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have h1 : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  rw [h1]
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) (by
    exact (Nat.even_pow.mpr ⟨even_two, m.ne_zero⟩)) odd_one

theorem pow_card_sub_one_eq_one_of_ne_zero {s : K} (hs : s ≠ 0) : s ^ (Nat.card K - 1) = 1 := by
  haveI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one s hs

theorem torusEquiv_pow_card_sub_one (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0) :
    (torusEquiv P hs) ^ (Nat.card K - 1) = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [torusEquiv_pow_apply, pow_card_sub_one_eq_one_of_ne_zero hs, torusLin_one]
  rfl

@[expose] noncomputable def torusG (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K}
    (hs : s ≠ 0) : Gom (quadPlus n K) :=
  ⟨torusEquiv P hs, mem_elementaryGroup_quadPlus_of_odd_pow CharTwo.two_eq_zero hn
    (torusEquiv_mem_orthogonalGroup P hs) odd_card_sub_one_of_charTwo
    (torusEquiv_pow_card_sub_one P hs)⟩

theorem torusG_app (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0) (v : _) :
    (torusG hn P hs).app v = torusLin P s v := rfl

theorem torusG_pow (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0) :
    torusG hn P hs ^ (Nat.card K - 1) = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  show ((torusEquiv P hs) ^ (Nat.card K - 1)) v = v
  rw [torusEquiv_pow_card_sub_one]
  rfl

@[expose] def pairMap {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (P : HypPair Q) (g : Gom Q) : HypPair Q :=
  ⟨g.app P.e, g.app P.f, by rw [Gom.map_of_mem, P.Q_e], by rw [Gom.map_of_mem, P.Q_f],
    by rw [Gom.polar_app, P.polar_ef]⟩

theorem gom_polar_inv_app {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (g : Gom Q) (x y : V) : polar Q (g⁻¹.app x) y = polar Q x (g.app y) := by
  rw [← Gom.polar_app g (g⁻¹.app x) y, Gom.app_app_inv]

theorem torusG_conj (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0)
    (g : Gom (quadPlus n K)) :
    g * torusG hn P hs * g⁻¹ = torusG hn (pairMap P g) hs := by
  refine Gom.ext' fun x => ?_
  rw [Gom.app_mul, Gom.app_mul, torusG_app, torusG_app]
  simp only [torusLin_apply, Gom.map_add, Gom.map_smul, Gom.app_app_inv, gom_polar_inv_app]
  rfl

theorem torusG_comm_of_fixed (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0)
    {g : Gom (quadPlus n K)} (he : g.app P.e = P.e) (hf : g.app P.f = P.f) :
    g * torusG hn P hs = torusG hn P hs * g := by
  have hP : pairMap P g = P := by
    obtain ⟨e, f, h1, h2, h3⟩ := P
    simp only [pairMap, HypPair.mk.injEq]
    exact ⟨he, hf⟩
  have := torusG_conj hn P hs g
  rw [hP] at this
  exact (mul_inv_eq_iff_eq_mul.mp this)

theorem torusG_swap (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0) :
    torusG hn (pairSwap P) hs = (torusG hn P hs)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Gom.ext' fun x => ?_)
  rw [Gom.app_mul, torusG_app, torusG_app, torusLin_swap, torusLin_comp P hs (inv_ne_zero hs),
    mul_inv_cancel₀ hs, torusLin_one, Gom.app_one]

end GomTorus

end CFSG.RankThree.GF2n.Stroth80.Sec715Torus
