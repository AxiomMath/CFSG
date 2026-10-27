module

import CFSG.RankThree.PartTwo.Sec15.Liebeck155KFacts
import CFSG.GF2Type.Smith1979.CaseIIExclL52
import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

private theorem a5PermInv :
    ∀ w : Equiv.Perm (Fin 5), w ≠ 1 → w ^ 3 = 1 → Equiv.Perm.sign w = 1 →
      ∃ g : Equiv.Perm (Fin 5), Equiv.Perm.sign g = 1 ∧ g * w = w⁻¹ * g := by
  decide +kernel

private theorem a5PermV4 :
    ∀ w : Equiv.Perm (Fin 5), w ≠ 1 → w ^ 3 = 1 → Equiv.Perm.sign w = 1 →
      ∃ u v : Equiv.Perm (Fin 5), Equiv.Perm.sign u = 1 ∧ Equiv.Perm.sign v = 1 ∧
        u * u = 1 ∧ v * v = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * v = v * u ∧
        w * u * w⁻¹ = v ∧ w * v * w⁻¹ = u * v := by
  decide +kernel

theorem m42_a5_inv (w : alternatingGroup (Fin 5)) (hw : orderOf w = 3) :
    ∃ g : alternatingGroup (Fin 5), g * w * g⁻¹ = w⁻¹ := by
  have hw1 : (w : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h
    have : w = 1 := Subtype.ext h
    rw [this, orderOf_one] at hw
    omega
  have hw3 : (w : Equiv.Perm (Fin 5)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    exact congrArg Subtype.val this
  obtain ⟨g, hgs, hg⟩ := a5PermInv w hw1 hw3 (Equiv.Perm.mem_alternatingGroup.mp w.2)
  refine ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hgs⟩, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [mul_inv_eq_iff_eq_mul]
  exact hg


theorem m42_a5_V4 (w : alternatingGroup (Fin 5)) (hw : orderOf w = 3) :
    ∃ u v : alternatingGroup (Fin 5), u * u = 1 ∧ v * v = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      u * v = v * u ∧ w * u * w⁻¹ = v ∧ w * v * w⁻¹ = u * v := by
  have hw1 : (w : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h
    have : w = 1 := Subtype.ext h
    rw [this, orderOf_one] at hw
    omega
  have hw3 : (w : Equiv.Perm (Fin 5)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    exact congrArg Subtype.val this
  obtain ⟨u, v, hus, hvs, hu2, hv2, hu1, hv1, huv, hc, h1, h2⟩ :=
    a5PermV4 w hw1 hw3 (Equiv.Perm.mem_alternatingGroup.mp w.2)
  refine ⟨⟨u, Equiv.Perm.mem_alternatingGroup.mpr hus⟩,
    ⟨v, Equiv.Perm.mem_alternatingGroup.mpr hvs⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext hu2
  · exact Subtype.ext hv2
  · intro h; exact hu1 (congrArg Subtype.val h)
  · intro h; exact hv1 (congrArg Subtype.val h)
  · intro h; exact huv (congrArg Subtype.val h)
  · exact Subtype.ext hc
  · exact Subtype.ext h1
  · exact Subtype.ext h2

set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem l3InvPoly :
    ∀ a b c d e f g h i : ZMod 2,
      ((a * a + b * d + c * g) * a +
          (a * b + b * e + c * h) * d +
          (a * c + b * f + c * i) * g = 1) ∧
      ((a * a + b * d + c * g) * b +
          (a * b + b * e + c * h) * e +
          (a * c + b * f + c * i) * h = 0) ∧
      ((a * a + b * d + c * g) * c +
          (a * b + b * e + c * h) * f +
          (a * c + b * f + c * i) * i = 0) ∧
      ((d * a + e * d + f * g) * a +
          (d * b + e * e + f * h) * d +
          (d * c + e * f + f * i) * g = 0) ∧
      ((d * a + e * d + f * g) * b +
          (d * b + e * e + f * h) * e +
          (d * c + e * f + f * i) * h = 1) ∧
      ((d * a + e * d + f * g) * c +
          (d * b + e * e + f * h) * f +
          (d * c + e * f + f * i) * i = 0) ∧
      ((g * a + h * d + i * g) * a +
          (g * b + h * e + i * h) * d +
          (g * c + h * f + i * i) * g = 0) ∧
      ((g * a + h * d + i * g) * b +
          (g * b + h * e + i * h) * e +
          (g * c + h * f + i * i) * h = 0) ∧
      ((g * a + h * d + i * g) * c +
          (g * b + h * e + i * h) * f +
          (g * c + h * f + i * i) * i = 1) →
      ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 1 ∧ f = 0 ∧ g = 0 ∧ h = 0 ∧ i = 1) →
      ∃ p q r t u v w x z : ZMod 2,
        (p * u * z - p * v * x - q * t * z + q * v * w + r * t * x - r * u * w = 1) ∧
        ((p * a + q * d + r * g) =
          (a * a + b * d + c * g) * p + (a * b + b * e + c * h) * t + (a * c + b * f + c * i) * w) ∧
        ((p * b + q * e + r * h) =
          (a * a + b * d + c * g) * q + (a * b + b * e + c * h) * u + (a * c + b * f + c * i) * x) ∧
        ((p * c + q * f + r * i) =
          (a * a + b * d + c * g) * r + (a * b + b * e + c * h) * v + (a * c + b * f + c * i) * z) ∧
        ((t * a + u * d + v * g) =
          (d * a + e * d + f * g) * p + (d * b + e * e + f * h) * t + (d * c + e * f + f * i) * w) ∧
        ((t * b + u * e + v * h) =
          (d * a + e * d + f * g) * q + (d * b + e * e + f * h) * u + (d * c + e * f + f * i) * x) ∧
        ((t * c + u * f + v * i) =
          (d * a + e * d + f * g) * r + (d * b + e * e + f * h) * v + (d * c + e * f + f * i) * z) ∧
        ((w * a + x * d + z * g) =
          (g * a + h * d + i * g) * p + (g * b + h * e + i * h) * t + (g * c + h * f + i * i) * w) ∧
        ((w * b + x * e + z * h) =
          (g * a + h * d + i * g) * q + (g * b + h * e + i * h) * u + (g * c + h * f + i * i) * x) ∧
        ((w * c + x * f + z * i) =
          (g * a + h * d + i * g) * r + (g * b + h * e + i * h) * v +
            (g * c + h * f + i * i) * z) := by
  decide +kernel

private def mk3 (a b c d e f g h i : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![a, b, c; d, e, f; g, h, i]

private theorem mk3_mul (a b c d e f g h i p q r t u v w x z : ZMod 2) :
    mk3 a b c d e f g h i * mk3 p q r t u v w x z =
      mk3 (a * p + b * t + c * w) (a * q + b * u + c * x) (a * r + b * v + c * z)
        (d * p + e * t + f * w) (d * q + e * u + f * x) (d * r + e * v + f * z)
        (g * p + h * t + i * w) (g * q + h * u + i * x) (g * r + h * v + i * z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mk3, Matrix.mul_apply, Fin.sum_univ_three]

private theorem mk3_det (a b c d e f g h i : ZMod 2) :
    (mk3 a b c d e f g h i).det = a * e * i - a * f * h - b * d * i + b * f * g + c * d * h
      - c * e * g := by
  simp [mk3, Matrix.det_fin_three]

private theorem mk3_inj {a b c d e f g h i p q r t u v w x z : ZMod 2} :
    mk3 a b c d e f g h i = mk3 p q r t u v w x z ↔
      (a = p ∧ b = q ∧ c = r ∧ d = t ∧ e = u ∧ f = v ∧ g = w ∧ h = x ∧ i = z) := by
  constructor
  · intro h
    have e := fun i j => congrFun (congrFun h i) j
    exact ⟨by simpa [mk3] using e 0 0, by simpa [mk3] using e 0 1, by simpa [mk3] using e 0 2,
      by simpa [mk3] using e 1 0, by simpa [mk3] using e 1 1, by simpa [mk3] using e 1 2,
      by simpa [mk3] using e 2 0, by simpa [mk3] using e 2 1, by simpa [mk3] using e 2 2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

private theorem mk3_eta (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    A = mk3 (A 0 0) (A 0 1) (A 0 2) (A 1 0) (A 1 1) (A 1 2) (A 2 0) (A 2 1) (A 2 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mk3]

private theorem mk3_one : (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = mk3 1 0 0 0 1 0 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mk3]

private theorem unit_det_one {a b c d e f g h i : ZMod 2}
    (hd : a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g = 1) :
    IsUnit (mk3 a b c d e f g h i).det := by
  rw [mk3_det, hd]; exact isUnit_one

theorem m42_gl3_inv (w : GL (Fin 3) (ZMod 2)) (hw : orderOf w = 3) :
    ∃ g : GL (Fin 3) (ZMod 2), g * w * g⁻¹ = w⁻¹ := by
  have hw3 : w ^ 3 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw] at this
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw
    omega
  set S : Matrix (Fin 3) (Fin 3) (ZMod 2) := (w : Matrix (Fin 3) (Fin 3) (ZMod 2)) with hS
  have h3 : S * S * S = 1 := by
    have := congrArg Units.val hw3
    simpa [hS, pow_succ, mul_assoc] using this
  have hS1 : ¬ (S 0 0 = 1 ∧ S 0 1 = 0 ∧ S 0 2 = 0 ∧ S 1 0 = 0 ∧ S 1 1 = 1 ∧ S 1 2 = 0 ∧
      S 2 0 = 0 ∧ S 2 1 = 0 ∧ S 2 2 = 1) := by
    intro h
    apply hw1
    apply Units.ext
    rw [Units.val_one, ← hS, mk3_eta S, mk3_one, mk3_inj]
    exact h
  rw [mk3_eta S, mk3_mul, mk3_mul, mk3_one, mk3_inj] at h3
  obtain ⟨p, q, r, t, u, v, w', x, z, hdet, heq⟩ := l3InvPoly _ _ _ _ _ _ _ _ _ h3 hS1
  let g : GL (Fin 3) (ZMod 2) := Matrix.GeneralLinearGroup.mk'' (mk3 p q r t u v w' x z)
    (unit_det_one hdet)
  have e1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = mk3 p q r t u v w' x z := rfl
  have hgw : g * w = w * w * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, e1, ← hS, mk3_eta S, mk3_mul, mk3_mul,
      mk3_mul, mk3_inj]
    exact heq
  refine ⟨g, ?_⟩
  have hinv : w⁻¹ = w * w :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_succ, mul_assoc] using hw3)
  rw [hinv, hgw, mul_inv_cancel_right]


@[expose] def M42A5 {G : Type} [Group G] (M : Subgroup G) : Prop :=
  Nonempty (↥M ≃* alternatingGroup (Fin 5))

@[expose] def M42GL3 {G : Type} [Group G] (M : Subgroup G) : Prop :=
  Nonempty (↥M ≃* GL (Fin 3) (ZMod 2))

theorem m42_fact_alt5 : (Nat.card (alternatingGroup (Fin 5))) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem m42_fact_fact60 : (60 : ℕ).factorization 3 = 1 := by
  have : (60 : ℕ) = 3 * 20 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
  have h20 : (20 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h20, Nat.Prime.factorization_self Nat.prime_three]

theorem m42_fact_fact168 : (168 : ℕ).factorization 3 = 1 := by
  have : (168 : ℕ) = 3 * 56 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
  have h20 : (56 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h20, Nat.Prime.factorization_self Nat.prime_three]

section Sub

variable {G : Type} [Group G] {M : Subgroup G}

theorem M42A5.card (h : M42A5 M) : Nat.card M = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, m42_fact_alt5]

theorem M42GL3.card (h : M42GL3 M) : Nat.card M = 168 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.ComponentClassification.GHarris.card_GL32_gh]

theorem M42A5.simple (h : M42A5 M) : IsSimpleGroup ↥M := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  exact MulEquiv.isSimpleGroup e

theorem M42GL3.simple (h : M42GL3 M) : IsSimpleGroup ↥M := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  exact MulEquiv.isSimpleGroup e

theorem m42_inv_transfer {A : Type} [Group A] (e : ↥M ≃* A)
    (h : ∀ w : A, orderOf w = 3 → ∃ g : A, g * w * g⁻¹ = w⁻¹) :
    ∀ x ∈ M, orderOf x = 3 → ∃ g ∈ M, g * x * g⁻¹ = x⁻¹ := by
  intro x hx hox
  have ho : orderOf (e ⟨x, hx⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hox]
  obtain ⟨g, hg⟩ := h _ ho
  refine ⟨(e.symm g).1, (e.symm g).2, ?_⟩
  have := congrArg (fun z => (e.symm z).1) hg
  simpa using this

theorem M42A5.inv (h : M42A5 M) :
    ∀ x ∈ M, orderOf x = 3 → ∃ g ∈ M, g * x * g⁻¹ = x⁻¹ := by
  obtain ⟨e⟩ := h
  exact m42_inv_transfer e fun w hw => m42_a5_inv w hw

theorem M42GL3.inv (h : M42GL3 M) :
    ∀ x ∈ M, orderOf x = 3 → ∃ g ∈ M, g * x * g⁻¹ = x⁻¹ := by
  obtain ⟨e⟩ := h
  exact m42_inv_transfer e fun w hw => m42_gl3_inv w hw

variable [Finite G]

theorem m42_conj3 (hM : (Nat.card M).factorization 3 = 1) {x y : G} (hx : x ∈ M) (hy : y ∈ M)
    (hox : orderOf x = 3) (hoy : orderOf y = 3) :
    ∃ k ∈ M, k * x * k⁻¹ ∈ Subgroup.zpowers y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ z : ↥M, orderOf z = 3 →
      ∃ Q : Sylow 3 ↥M, (Q : Subgroup ↥M) = Subgroup.zpowers z := by
    intro z hz
    refine ⟨Sylow.ofCard (Subgroup.zpowers z) ?_, rfl⟩
    rw [Nat.card_zpowers, hz, hM]
    simp
  obtain ⟨Qx, hQx⟩ := key ⟨x, hx⟩ (by rw [Subgroup.orderOf_mk, hox])
  obtain ⟨Qy, hQy⟩ := key ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk, hoy])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) Qx Qy
  refine ⟨g.1, g.2, ?_⟩
  have hmem : (⟨x, hx⟩ : ↥M) ∈ (Qx : Subgroup ↥M) := by
    rw [hQx]; exact Subgroup.mem_zpowers _
  have h2 : g * ⟨x, hx⟩ * g⁻¹ ∈ (Qy : Subgroup ↥M) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [hQy] at h2
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h2
  exact ⟨i, by simpa using congrArg Subtype.val hi⟩



theorem m42_orderOf_conj (k x : G) : orderOf (k * x * k⁻¹) = orderOf x :=
  MulEquiv.orderOf_eq (MulAut.conj k) x

theorem m42_conj_exact (hM : (Nat.card M).factorization 3 = 1)
    (hinv : ∀ x ∈ M, orderOf x = 3 → ∃ g ∈ M, g * x * g⁻¹ = x⁻¹) {x y : G} (hx : x ∈ M)
    (hy : y ∈ M) (hox : orderOf x = 3) (hoy : orderOf y = 3) : ∃ k ∈ M, k * x * k⁻¹ = y := by
  obtain ⟨k, hk, hkx⟩ := m42_conj3 hM hx hy hox hoy
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hkx
  have hz : orderOf (k * x * k⁻¹) = 3 := by rw [m42_orderOf_conj, hox]
  have hy3 : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hoy] at this
  have hmod : y ^ (i % (3 : ℤ)) = y ^ i := by
    have := zpow_mod_orderOf y i
    rwa [hoy] at this
  have hcase : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hcase with h | h | h
  · exfalso
    rw [← hi, ← hmod, h, zpow_zero, orderOf_one] at hz
    omega
  · refine ⟨k, hk, ?_⟩
    rw [← hi, ← hmod, h, zpow_one]
  · obtain ⟨g, hg, hgy⟩ := hinv y hy hoy
    refine ⟨g * k, M.mul_mem hg hk, ?_⟩
    have hyy : y ^ i = y⁻¹ := by
      rw [← hmod, h]
      have : y ^ (2 : ℤ) * y = 1 := by
        rw [← zpow_add_one]; simpa using hy3
      exact eq_inv_of_mul_eq_one_left this
    have e1 : g * k * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
    rw [e1, ← hi, hyy]
    have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [this, hgy, inv_inv]

end Sub

section Triv

variable {G : Type} [Group G]

theorem m42_comm_A5_GL3 {Δ Λ : Subgroup G} (hΔ : M42A5 Δ) (hΛ : M42GL3 Λ)
    (hn : ∀ l ∈ Λ, ∀ d ∈ Δ, l * d * l⁻¹ ∈ Δ) : ∀ l ∈ Λ, ∀ d ∈ Δ, l * d = d * l := by
  haveI : IsSimpleGroup ↥Λ := hΛ.simple
  let ψ : ↥Λ → MulAut ↥Δ := fun l =>
    { toFun := fun d => ⟨l.1 * d.1 * l.1⁻¹, hn l.1 l.2 d.1 d.2⟩
      invFun := fun d => ⟨l.1⁻¹ * d.1 * l.1, by
        have := hn l.1⁻¹ (Λ.inv_mem l.2) d.1 d.2
        simpa using this⟩
      left_inv := fun d => by ext; simp [mul_assoc]
      right_inv := fun d => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  let φ : ↥Λ →* MulAut ↥Δ :=
    { toFun := ψ
      map_one' := by ext d; simp [ψ]
      map_mul' := fun a b => by ext d; simp [ψ, mul_assoc] }
  have hcard : Nat.card (MulAut ↥Δ) = 120 := by
    obtain ⟨e⟩ := hΔ
    have h1 := Nat.card_congr (MulAut.congr e).toEquiv
    have h2 := Nat.card_eq_of_bijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by omega))
    rw [h1, ← h2]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  haveI : Finite (MulAut ↥Δ) := Nat.finite_of_card_ne_zero (by omega)
  have hker : φ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exfalso
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
      have := Nat.card_le_card_of_injective φ hinj
      rw [hΛ.card, hcard] at this
      omega
    · exact h
  intro l hl d hd
  have hl1 : φ ⟨l, hl⟩ = 1 := by
    have : (⟨l, hl⟩ : ↥Λ) ∈ φ.ker := by rw [hker]; exact Subgroup.mem_top _
    exact this
  have := congrArg (fun a : MulAut ↥Δ => (a ⟨d, hd⟩).1) hl1
  simp only [φ, ψ, MonoidHom.coe_mk, OneHom.coe_mk] at this
  have h2 : l * d * l⁻¹ = d := by simpa using this
  calc l * d = l * d * l⁻¹ * l := by group
    _ = d * l := by rw [h2]

end Triv


theorem M42A5.of_IsLnq {G : Type} [Group G] {K : Subgroup G} (h : IsLnq 2 2 2 K) : M42A5 K :=
  CFSG.RankThree.PartTwo.Sec15.Liebeck155.nonempty_mulEquiv_alt5_of_statedClassicalModel h

theorem M42GL3.of_IsLnq {G : Type} [Group G] {L : Subgroup G} (h : IsLnq 3 2 1 L) : M42GL3 L :=
  CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two h

end CFSG.RankThree.PartTwo.Sec21.FF79
