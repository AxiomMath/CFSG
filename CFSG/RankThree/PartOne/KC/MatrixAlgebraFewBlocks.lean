module

public import CFSG.RankThree.PartOne.KC.MatrixAlgebraCenter
public import CFSG.RankThree.PartOne.KC.MatrixAlgebraFieldProduct
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartOne

namespace KCMatrixAlgebra

theorem mul_inv_mem_of_pow_two_pow_mem {G : Type*} [CommGroup G] [Finite G] (σ : MulAut G)
    (hσ : ∀ (x : G) (k : ℕ), x ^ 2 ^ k = 1 → σ x = x) (C : Subgroup G)
    (hC : ∀ x ∈ C, σ x ∈ C) {g : G} {k : ℕ} (hg : g ^ 2 ^ k ∈ C) : σ g * g⁻¹ ∈ C := by
  obtain ⟨e, b, hb, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card G) Nat.card_pos.ne'
  have hgb : σ (g ^ b) = g ^ b := by
    apply hσ _ e
    rw [← pow_mul, mul_comm, ← hn, pow_card_eq_one']
  rw [map_pow] at hgb
  have hy1 : (σ g * g⁻¹) ^ b = 1 := by
    rw [mul_pow, inv_pow, hgb, mul_inv_cancel]
  have hy2 : (σ g * g⁻¹) ^ 2 ^ k ∈ C := by
    rw [mul_pow, inv_pow, ← map_pow]
    exact C.mul_mem (hC _ hg) (C.inv_mem hg)
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hb))
  obtain ⟨u, v, huv⟩ := hcop
  have huv' : ((2 ^ k : ℕ) : ℤ) * u + (b : ℤ) * v = 1 := by linarith
  have : σ g * g⁻¹ = ((σ g * g⁻¹) ^ 2 ^ k) ^ u := by
    calc σ g * g⁻¹ = (σ g * g⁻¹) ^ (((2 ^ k : ℕ) : ℤ) * u + (b : ℤ) * v) := by
          rw [huv', zpow_one]
      _ = ((σ g * g⁻¹) ^ 2 ^ k) ^ u := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hy1, one_zpow, mul_one]
  rw [this]
  exact C.zpow_mem hy2 u

variable {p : ℕ} {r : ℕ} {K : Fin r → Type*} [∀ i, Field (K i)] {m : Fin r → ℕ}
  {R : Type*} [Ring R] {A : Type*} [Group A]

theorem centerUnitsAut_apply_eq_of_pow_two_pow_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (hrp : r < p)
    (hm : ∀ i, 0 < m i) (e : R ≃+* ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i))
    (hA : IsPGroup p A) (φ : A →* RingAut R) (a : A) {x : (Subring.center R)ˣ} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : centerUnitsAut (φ a) x = x := by
  let ζ : (∀ i, K i) ≃+* Subring.center R :=
    (scalarCenterEquiv K m hm).trans (Subring.centerCongr e.symm)
  let ψ : A →* RingAut (∀ i, K i) :=
    { toFun := fun b => ζ.trans ((centerRingAut (φ b)).trans ζ.symm)
      map_one' := by
        ext c
        simp
      map_mul' := fun b c => by
        ext d
        simp }
  have hc : (ζ.symm (x : Subring.center R)) ^ 2 ^ k = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, map_one]
  have h := ringAut_apply_eq_of_pow_two_pow_eq_one hp hp2
    (ι := Fin r) (by simpa using hrp) hA ψ a hc
  have h2 := congrArg ζ h
  have h3 := congrArg Subtype.val (by simpa [ψ] using h2 :
    centerRingAut (φ a) (x : Subring.center R) = (x : Subring.center R))
  exact Units.ext (Subtype.ext (by simpa using h3))

theorem apply_eq_of_mem_center_of_pow_two_pow_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (hrp : r < p)
    (hm : ∀ i, 0 < m i) (e : R ≃+* ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i))
    (hA : IsPGroup p A) (φ : A →* RingAut R) (a : A) {z : R} (hz : z ∈ Subring.center R)
    {k : ℕ} (hzk : z ^ 2 ^ k = 1) : φ a z = z := by
  have hu : IsUnit (⟨z, hz⟩ : Subring.center R) := by
    refine IsUnit.of_pow_eq_one (n := 2 ^ k) ?_ (by positivity)
    exact Subtype.ext (by simpa using hzk)
  obtain ⟨x, hx⟩ := hu
  have hxk : x ^ 2 ^ k = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hx]
    exact Subtype.ext (by simpa using hzk)
  have := centerUnitsAut_apply_eq_of_pow_two_pow_eq_one hp hp2 hrp hm e hA φ a hxk
  have h2 := congrArg (fun y : (Subring.center R)ˣ => ((y : Subring.center R) : R)) this
  simpa [hx] using h2

end KCMatrixAlgebra

theorem matrix_algebra_few_blocks_odd_prime_action_center_two_part_fixed
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {r : ℕ} (hrp : r < p)
    {K : Fin r → Type*} [∀ i, Field (K i)] [∀ i, Finite (K i)]
    {m : Fin r → ℕ} (hm : ∀ i, 0 < m i)
    {R : Type*} [Ring R] (e : R ≃+* ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i))
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup p A) (φ : A →* RingAut R) :
    (∀ (P : Sylow 2 (Subring.center R)ˣ) (a : A), ∀ x ∈ P, centerUnitsAut (φ a) x = x) ∧
    ∀ (U C : Subgroup (Subring.center R)ˣ) (_hCU : C ≤ U)
      (hU : ∀ a : A, ∀ x ∈ U, centerUnitsAut (φ a) x ∈ U)
      (hC : ∀ a : A, ∀ x ∈ C, centerUnitsAut (φ a) x ∈ C)
      (P : Sylow 2 (U ⧸ C.subgroupOf U)) (a : A), ∀ y ∈ P,
        quotientInduced (centerUnitsAut (φ a)) U C (hU a) (hC a) y = y := by
  have hcore : ∀ (a : A) (x : (Subring.center R)ˣ) (k : ℕ), x ^ 2 ^ k = 1 →
      centerUnitsAut (φ a) x = x := fun a x k hx =>
    KCMatrixAlgebra.centerUnitsAut_apply_eq_of_pow_two_pow_eq_one hp hp2 hrp hm e hA φ a hx
  have : Finite R := Finite.of_equiv _ e.toEquiv.symm
  have : Finite (Subring.center R)ˣ := Finite.of_injective Units.val Units.val_injective
  refine ⟨fun P a x hx => ?_, fun U C _ hU hC P a y hy => ?_⟩
  · obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    exact hcore a x k (by simpa using congrArg Subtype.val hk)
  · obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
    have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hxk : ((x : (Subring.center R)ˣ)) ^ 2 ^ k ∈ C := by
      have h1 : (QuotientGroup.mk (x ^ 2 ^ k) : U ⧸ C.subgroupOf U) = 1 := by
        rw [QuotientGroup.mk_pow, hyk]
      have h2 := (QuotientGroup.eq_one_iff _).1 h1
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h2
      exact h2
    have key := KCMatrixAlgebra.mul_inv_mem_of_pow_two_pow_mem (centerUnitsAut (φ a))
      (fun z j hz => hcore a z j hz) C (hC a) hxk
    rw [quotientInduced_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := C.inv_mem key
    simpa [mul_comm] using this

end CFSG.RankThree.PartOne
