module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGRCMonomialRefl

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

@[expose] def IsDiagonal (b : Module.Basis (Fin n) (ZMod p) U) (t : U ≃ₗ[ZMod p] U)
    (e : Fin n → (ZMod p)ˣ) : Prop :=
  ∀ k, t (b k) = (e k : ZMod p) • b k

@[expose] def IsTwistedSwap (b : Module.Basis (Fin n) (ZMod p) U) (t : U ≃ₗ[ZMod p] U)
    (x y : Fin n) (c : (ZMod p)ˣ) : Prop :=
  x ≠ y ∧ t (b x) = (c : ZMod p) • b y ∧ t (b y) = ((c⁻¹ : (ZMod p)ˣ) : ZMod p) • b x ∧
    ∀ k, k ≠ x → k ≠ y → t (b k) = b k

variable {b : Module.Basis (Fin n) (ZMod p) U}

theorem IsDiagonal.mul {s t : U ≃ₗ[ZMod p] U} {e f : Fin n → (ZMod p)ˣ}
    (hs : IsDiagonal b s e) (ht : IsDiagonal b t f) : IsDiagonal b (s * t) (e * f) := by
  intro k
  rw [LinearEquiv.mul_apply, ht k, map_smul, hs k, smul_smul, Pi.mul_apply, Units.val_mul,
    mul_comm (f k : ZMod p)]

theorem IsDiagonal.pow {s : U ≃ₗ[ZMod p] U} {e : Fin n → (ZMod p)ˣ} (hs : IsDiagonal b s e)
    (i : ℕ) : IsDiagonal b (s ^ i) (e ^ i) := by
  induction i with
  | zero => intro k; simp
  | succ i ih => rw [pow_succ, pow_succ]; exact ih.mul hs

theorem pairUnit_swap {x y : Fin n} (hxy : x ≠ y) (ζ : (ZMod p)ˣ) :
    pairUnit p y x ζ⁻¹ = pairUnit p x y ζ := by
  funext k
  by_cases hkx : k = x
  · subst hkx
    simp [pairUnit, hxy]
  · by_cases hky : k = y
    · subst hky
      simp [pairUnit, hkx]
    · simp [pairUnit, hkx, hky]

theorem IsTwistedSwap.symm {t : U ≃ₗ[ZMod p] U} {x y : Fin n} {c : (ZMod p)ˣ}
    (h : IsTwistedSwap b t x y c) : IsTwistedSwap b t y x c⁻¹ := by
  refine ⟨h.1.symm, h.2.2.1, ?_, fun k hky hkx => h.2.2.2 k hkx hky⟩
  simpa using h.2.1

theorem isTwistedSwap_permMap_swap {x y : Fin n} (hxy : x ≠ y) :
    IsTwistedSwap b (permMap p b (Equiv.swap x y)) x y 1 := by
  refine ⟨hxy, ?_, ?_, ?_⟩
  · simp [permMap]
  · simp [permMap]
  · intro k hkx hky
    simp [permMap, Equiv.swap_apply_of_ne_of_ne hkx hky]

theorem IsTwistedSwap.mul_isDiagonal {s t : U ≃ₗ[ZMod p] U} {x y : Fin n} {c d : (ZMod p)ˣ}
    (hs : IsTwistedSwap b s x y c) (ht : IsTwistedSwap b t x y d) :
    IsDiagonal b (s * t) (pairUnit p x y (d * c⁻¹)) := by
  intro k
  by_cases hkx : k = x
  · subst hkx
    simp only [LinearEquiv.mul_apply, ht.2.1, map_smul, hs.2.2.1, smul_smul, pairUnit]
    simp [Units.val_mul]
  · by_cases hky : k = y
    · subst hky
      simp only [LinearEquiv.mul_apply, ht.2.2.1, map_smul, hs.2.1, smul_smul, pairUnit]
      simp [hkx, Units.val_mul, mul_inv_rev, inv_inv, mul_comm]
    · simp only [LinearEquiv.mul_apply, ht.2.2.2 k hkx hky, hs.2.2.2 k hkx hky, pairUnit,
        if_neg hkx, if_neg hky]
      simp [Units.val_one]

theorem IsDiagonal.conj_isTwistedSwap {δ t : U ≃ₗ[ZMod p] U} {e : Fin n → (ZMod p)ˣ}
    {x y : Fin n} {c : (ZMod p)ˣ} (hδ : IsDiagonal b δ e) (ht : IsTwistedSwap b t x y c) :
    IsTwistedSwap b (δ * t * δ⁻¹) x y (c * e y * (e x)⁻¹) := by
  have hinv : ∀ k, δ⁻¹ (b k) = ((e k)⁻¹ : (ZMod p)ˣ) • b k := by
    intro k
    change δ.symm (b k) = ((e k)⁻¹ : (ZMod p)ˣ) • b k
    rw [LinearEquiv.symm_apply_eq, Units.smul_def, LinearEquiv.map_smul, hδ k]
    rw [smul_smul]
    simp
  refine ⟨ht.1, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv x]
    rw [Units.smul_def, LinearEquiv.map_smul, ht.2.1]
    rw [smul_smul]
    rw [LinearEquiv.map_smul, hδ y]
    rw [smul_smul]
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [show ((e x)⁻¹ * c * e y : (ZMod p)ˣ) = c * e y * (e x)⁻¹ by ac_rfl]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv y]
    rw [Units.smul_def, LinearEquiv.map_smul, ht.2.2.1]
    rw [smul_smul]
    rw [LinearEquiv.map_smul, hδ x]
    rw [smul_smul]
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [show ((e y)⁻¹ * c⁻¹ * e x : (ZMod p)ˣ) = (c * e y * (e x)⁻¹)⁻¹ by
      rw [mul_inv_rev, mul_inv_rev, inv_inv]
      ac_rfl]
  · intro k hkx hky
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv k]
    rw [Units.smul_def, LinearEquiv.map_smul, ht.2.2.2 k hkx hky]
    rw [LinearEquiv.map_smul, hδ k]
    rw [smul_smul]
    simp

theorem IsTwistedSwap.conj_isDiagonal {t δ : U ≃ₗ[ZMod p] U} {x y : Fin n} {c : (ZMod p)ˣ}
    {e : Fin n → (ZMod p)ˣ} (ht : IsTwistedSwap b t x y c) (hδ : IsDiagonal b δ e) :
    IsDiagonal b (t * δ * t⁻¹) (e ∘ Equiv.swap x y) := by
  have hinvx : t⁻¹ (b x) = (c : ZMod p) • b y := by
    change t.symm (b x) = (c : ZMod p) • b y
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.map_smul, ht.2.2.1, smul_smul]
    simp
  have hinvy : t⁻¹ (b y) = ((c⁻¹ : (ZMod p)ˣ) : ZMod p) • b x := by
    change t.symm (b y) = ((c⁻¹ : (ZMod p)ˣ) : ZMod p) • b x
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.map_smul, ht.2.1, smul_smul]
    simp
  have hinvk : ∀ k, k ≠ x → k ≠ y → t⁻¹ (b k) = b k := by
    intro k hkx hky
    change t.symm (b k) = b k
    rw [LinearEquiv.symm_apply_eq, ht.2.2.2 k hkx hky]
  intro k
  by_cases hkx : k = x
  · rw [hkx]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinvx]
    rw [LinearEquiv.map_smul, hδ y]
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, ht.2.2.1]
    rw [smul_smul, smul_smul]
    rw [← Units.val_mul, ← Units.val_mul]
    rw [show (c * e y * c⁻¹ : (ZMod p)ˣ) = e y by
      rw [mul_comm c (e y), mul_assoc, mul_inv_cancel, mul_one]]
    rw [Function.comp_apply, Equiv.swap_apply_left]
  · by_cases hky : k = y
    · rw [hky]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinvy]
      rw [LinearEquiv.map_smul, hδ x]
      rw [LinearEquiv.map_smul, LinearEquiv.map_smul, ht.2.1]
      rw [smul_smul, smul_smul]
      rw [← Units.val_mul, ← Units.val_mul]
      rw [show (c⁻¹ * e x * c : (ZMod p)ˣ) = e x by
        rw [mul_comm c⁻¹ (e x), mul_assoc, inv_mul_cancel, mul_one]]
      rw [Function.comp_apply, Equiv.swap_apply_right]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinvk k hkx hky]
      rw [hδ k, LinearEquiv.map_smul, ht.2.2.2 k hkx hky]
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hkx hky]

theorem IsDiagonal.permMap_conj {δ : U ≃ₗ[ZMod p] U} {e : Fin n → (ZMod p)ˣ}
    (hδ : IsDiagonal b δ e) (π : Equiv.Perm (Fin n)) :
    IsDiagonal b (permMap p b π * δ * (permMap p b π)⁻¹) (e ∘ π.symm) := by
  have hP : ∀ k, (b.equiv b π)⁻¹ (b k) = b (π.symm k) := by
    intro k
    rw [LinearEquiv.coe_inv, Module.Basis.equiv_symm]
    exact Module.Basis.equiv_apply b k b π.symm
  intro k
  simp only [LinearEquiv.mul_apply, hP, permMap]
  rw [hδ ((Equiv.symm π) k), LinearEquiv.map_smul, Module.Basis.equiv_apply, Equiv.apply_symm_apply]
  simp

theorem IsTwistedSwap.permMap_conj {t : U ≃ₗ[ZMod p] U} {x y : Fin n} {c : (ZMod p)ˣ}
    (ht : IsTwistedSwap b t x y c) (π : Equiv.Perm (Fin n)) :
    IsTwistedSwap b (permMap p b π * t * (permMap p b π)⁻¹) (π x) (π y) c := by
  have hP : ∀ k, permMap p b π (b k) = b (π k) := by
    intro k
    simp [permMap]
  have hPi : ∀ k, (permMap p b π)⁻¹ (b k) = b (π.symm k) := by
    intro k
    rw [permMap, LinearEquiv.coe_inv, Module.Basis.equiv_symm]
    exact Module.Basis.equiv_apply b k b π.symm
  refine ⟨π.injective.ne ht.1, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hPi, Equiv.symm_apply_apply, ht.2.1,
      map_smul, hP]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hPi, Equiv.symm_apply_apply, ht.2.2.1,
      map_smul, hP]
  · intro k hkx hky
    have hx : π.symm k ≠ x := by
      intro h
      apply hkx
      rw [← h, Equiv.apply_symm_apply]
    have hy : π.symm k ≠ y := by
      intro h
      apply hky
      rw [← h, Equiv.apply_symm_apply]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hPi, ht.2.2.2 (π.symm k) hx hy, hP,
      Equiv.apply_symm_apply]

theorem isDiagonal_or_isTwistedSwap_of_isRefl [Fact p.Prime] (hp2 : p ≠ 2)
    {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    (hm : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, t (b i) = c i • b (σ i)) :
    (∃ i, IsDiagonal b t (fun k => if k = i then -1 else 1)) ∨
      ∃ x y c, IsTwistedSwap b t x y c := by
  obtain ⟨σ, c, hc, htb⟩ := hm
  rcases ggRC_monomial_refl_shape hp2 b t ht σ c hc htb with
    ⟨i, hσ, hci, hcj⟩ | ⟨i, j, hij, hσ, hcij, hck⟩
  · refine Or.inl ⟨i, ?_⟩
    intro k
    rw [htb k, hσ]
    by_cases hk : k = i
    · subst hk
      simp [hci]
    · simp [hcj k hk, hk]
  · refine Or.inr ⟨i, j, Units.mk0 (c i) (hc i), ?_⟩
    refine ⟨hij, ?_, ?_, ?_⟩
    · rw [htb i, hσ, Equiv.swap_apply_left, Units.val_mk0]
    · rw [htb j, hσ, Equiv.swap_apply_right, eq_inv_of_mul_eq_one_right hcij,
        Units.val_inv_eq_inv_val, Units.val_mk0]
    · intro k hki hkj
      rw [htb k, hσ, Equiv.swap_apply_of_ne_of_ne hki hkj, hck k hki hkj]
      simp

private lemma linearEquiv_eq_one_of_apply_basis_eq (b : Module.Basis (Fin n) (ZMod p) U)
    {s : U ≃ₗ[ZMod p] U} (h : ∀ k, s (b k) = b k) : s = 1 :=
  b.ext' fun k => by simpa using h k

private lemma IsDiagonal.pow_two_eq_one {s : U ≃ₗ[ZMod p] U} {e : Fin n → (ZMod p)ˣ}
    (hs : IsDiagonal b s e) (he : ∀ k, e k ^ 2 = 1) : s ^ 2 = 1 := by
  rw [pow_two]
  refine linearEquiv_eq_one_of_apply_basis_eq b ?_
  intro k
  rw [LinearEquiv.mul_apply, hs k, map_smul, hs k, smul_smul]
  have hk : ((e k : ZMod p) * (e k : ZMod p)) = 1 := by
    rw [← Units.val_mul, ← pow_two, he k, Units.val_one]
  rw [hk, one_smul]

private lemma pairUnit_pow_two_eq_one {x y : Fin n} {e : (ZMod p)ˣ} (he : e ^ 2 = 1) :
    ∀ k, pairUnit p x y e k ^ 2 = 1 := by
  intro k
  by_cases hkx : k = x
  · simp [pairUnit, hkx, he]
  · by_cases hky : k = y
    · simp [pairUnit, hky, inv_pow, he]
    · simp [pairUnit, hkx, hky]

private lemma IsDiagonal.mul_isTwistedSwap_pow_four_eq_one
    {s t : U ≃ₗ[ZMod p] U} {e : Fin n → (ZMod p)ˣ} {x y : Fin n} {c : (ZMod p)ˣ}
    (hs : IsDiagonal b s e) (he : ∀ k, e k ^ 2 = 1)
    (ht : IsTwistedSwap b t x y c) : (s * t) ^ 4 = 1 := by
  have hs2 : s * s = 1 := by
    simpa [pow_two] using IsDiagonal.pow_two_eq_one hs he
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hconj : IsTwistedSwap b (s * t * s) x y (c * e y * (e x)⁻¹) := by
    simpa only [hsinv] using IsDiagonal.conj_isTwistedSwap hs ht
  have hdiag : IsDiagonal b ((s * t * s) * t)
      (pairUnit p x y (c * (c * e y * (e x)⁻¹)⁻¹)) :=
    IsTwistedSwap.mul_isDiagonal hconj ht
  have hscalar : (c * (c * e y * (e x)⁻¹)⁻¹) ^ 2 = 1 := by
    have hu : c * (c * e y * (e x)⁻¹)⁻¹ = e x * (e y)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv]
      calc
        c * (e x * ((e y)⁻¹ * c⁻¹)) = (c * c⁻¹) * (e x * (e y)⁻¹) := by ac_rfl
        _ = e x * (e y)⁻¹ := by rw [mul_inv_cancel, one_mul]
    rw [hu, mul_pow, he x, inv_pow, he y, inv_one, one_mul]
  have hpow : ((s * t) ^ 2) ^ 2 = 1 := by
    have hdiag' : IsDiagonal b ((s * t) ^ 2)
        (pairUnit p x y (c * (c * e y * (e x)⁻¹)⁻¹)) := by
      convert hdiag using 1
      rw [pow_two]
      group
    exact IsDiagonal.pow_two_eq_one hdiag' (pairUnit_pow_two_eq_one hscalar)
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  exact hpow

private lemma signChange_mul_isTwistedSwap_pow_four_eq_one
    {s t : U ≃ₗ[ZMod p] U} {i x y : Fin n} {c : (ZMod p)ˣ}
    (hs : IsDiagonal b s (fun k => if k = i then -1 else 1))
    (ht : IsTwistedSwap b t x y c) : (s * t) ^ 4 = 1 :=
  IsDiagonal.mul_isTwistedSwap_pow_four_eq_one hs
    (by intro k; by_cases hk : k = i <;> simp [hk]) ht

private lemma IsTwistedSwap.mul_pow_two_eq_one_of_same_pair
    {s t : U ≃ₗ[ZMod p] U} {x y : Fin n} {c d : (ZMod p)ˣ}
    (hs : IsTwistedSwap b s x y c) (ht : IsTwistedSwap b t x y d)
    (hd : (d * c⁻¹) ^ 2 = 1) : (s * t) ^ 2 = 1 :=
  IsDiagonal.pow_two_eq_one (IsTwistedSwap.mul_isDiagonal hs ht)
    (pairUnit_pow_two_eq_one hd)

private lemma IsTwistedSwap.mul_pow_two_eq_one_of_disjoint
    {s t : U ≃ₗ[ZMod p] U} {x y z w : Fin n} {c d : (ZMod p)ˣ}
    (hs : IsTwistedSwap b s x y c) (ht : IsTwistedSwap b t z w d)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) :
    (s * t) ^ 2 = 1 := by
  rw [pow_two]
  refine linearEquiv_eq_one_of_apply_basis_eq b ?_
  intro k
  simp only [LinearEquiv.mul_apply]
  by_cases hkx : k = x
  · subst k
    rw [ht.2.2.2 x hxz hxw, hs.2.1, map_smul, ht.2.2.2 y hyz hyw, map_smul, hs.2.2.1,
      smul_smul, Units.mul_inv, one_smul]
  · by_cases hky : k = y
    · subst k
      rw [ht.2.2.2 y hyz hyw, hs.2.2.1, map_smul, ht.2.2.2 x hxz hxw, map_smul, hs.2.1,
        smul_smul, Units.inv_mul, one_smul]
    · by_cases hkz : k = z
      · subst k
        rw [ht.2.1, map_smul, hs.2.2.2 w (Ne.symm hxw) (Ne.symm hyw), map_smul,
          ht.2.2.1, map_smul, map_smul, hs.2.2.2 z (Ne.symm hxz) (Ne.symm hyz), smul_smul,
          Units.mul_inv, one_smul]
      · by_cases hkw : k = w
        · subst k
          rw [ht.2.2.1, map_smul, hs.2.2.2 z (Ne.symm hxz) (Ne.symm hyz), map_smul,
            ht.2.1, map_smul, map_smul, hs.2.2.2 w (Ne.symm hxw) (Ne.symm hyw), smul_smul,
            Units.inv_mul, one_smul]
        · rw [ht.2.2.2 k hkz hkw, hs.2.2.2 k hkx hky, ht.2.2.2 k hkz hkw,
            hs.2.2.2 k hkx hky]

private lemma pow_two_ne_one_of_orderOf_eq_three {g : U ≃ₗ[ZMod p] U}
    (hord : orderOf g = 3) : g ^ 2 ≠ 1 := by
  intro h2
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at hdvd
  omega

private lemma pow_four_ne_one_of_orderOf_eq_three {g : U ≃ₗ[ZMod p] U}
    (hord : orderOf g = 3) : g ^ 4 ≠ 1 := by
  intro h4
  have hdvd : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  rw [hord] at hdvd
  omega

private lemma exists_isTwistedSwap_of_isTwistedSwap_mul_of_orderOf_eq_three
    {r₁ r₂ : U ≃ₗ[ZMod p] U} {x y z w : Fin n} {c d : (ZMod p)ˣ}
    (h₁ : IsTwistedSwap b r₁ x y c) (h₂ : IsTwistedSwap b r₂ z w d)
    (hord : orderOf (r₁ * r₂) = 3) :
    ∃ x y c, IsTwistedSwap b r₁ x y c ∧
      ((∃ z d, z ≠ x ∧ IsTwistedSwap b r₂ y z d) ∨
        ∃ d, IsTwistedSwap b r₂ x y d ∧ (d * c⁻¹) ^ 2 ≠ 1) := by
  classical
  by_cases hzx : z = x
  · subst z
    by_cases hwy : w = y
    · subst w
      refine ⟨x, y, c, h₁, Or.inr ?_⟩
      by_cases hdc : (d * c⁻¹) ^ 2 = 1
      · exact absurd (IsTwistedSwap.mul_pow_two_eq_one_of_same_pair h₁ h₂ hdc)
          (pow_two_ne_one_of_orderOf_eq_three hord)
      · exact ⟨d, h₂, hdc⟩
    · exact ⟨y, x, c⁻¹, h₁.symm, Or.inl ⟨w, d, hwy, h₂⟩⟩
  · by_cases hzy : z = y
    · subst z
      by_cases hwx : w = x
      · subst w
        have h₂' : IsTwistedSwap b r₂ x y d⁻¹ := h₂.symm
        refine ⟨x, y, c, h₁, Or.inr ?_⟩
        by_cases hdc : (d⁻¹ * c⁻¹) ^ 2 = 1
        · exact absurd (IsTwistedSwap.mul_pow_two_eq_one_of_same_pair h₁ h₂' hdc)
            (pow_two_ne_one_of_orderOf_eq_three hord)
        · exact ⟨d⁻¹, h₂', hdc⟩
      · exact ⟨x, y, c, h₁, Or.inl ⟨w, d, hwx, h₂⟩⟩
    · by_cases hwx : w = x
      · subst w
        exact ⟨y, x, c⁻¹, h₁.symm, Or.inl ⟨z, d⁻¹, hzy, h₂.symm⟩⟩
      · by_cases hwy : w = y
        · subst w
          exact ⟨x, y, c, h₁, Or.inl ⟨z, d⁻¹, hzx, h₂.symm⟩⟩
        · exact absurd (IsTwistedSwap.mul_pow_two_eq_one_of_disjoint h₁ h₂
            (Ne.symm hzx) (Ne.symm hwx) (Ne.symm hzy) (Ne.symm hwy))
            (pow_two_ne_one_of_orderOf_eq_three hord)

private lemma signChange_mul_signChange_pow_two_eq_one
    {s t : U ≃ₗ[ZMod p] U} {i j : Fin n}
    (hs : IsDiagonal b s (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1))
    (ht : IsDiagonal b t (fun k => if k = j then (-1 : (ZMod p)ˣ) else 1)) :
    (s * t) ^ 2 = 1 := by
  have he : ∀ k, ((fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) *
      (fun k => if k = j then (-1 : (ZMod p)ˣ) else 1)) k ^ 2 = 1 := by
    intro k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [Pi.mul_apply, hki, hkj]
  exact IsDiagonal.pow_two_eq_one (IsDiagonal.mul hs ht) he

theorem exists_isTwistedSwap_of_orderOf_eq_three [Fact p.Prime] (hp2 : p ≠ 2)
    {r₁ r₂ : U ≃ₗ[ZMod p] U} (h₁ : IsRefl p r₁) (h₂ : IsRefl p r₂)
    (hm₁ : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, r₁ (b i) = c i • b (σ i))
    (hm₂ : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, r₂ (b i) = c i • b (σ i))
    (hord : orderOf (r₁ * r₂) = 3) :
    ∃ x y c, IsTwistedSwap b r₁ x y c ∧
      ((∃ z d, z ≠ x ∧ IsTwistedSwap b r₂ y z d) ∨
        ∃ d, IsTwistedSwap b r₂ x y d ∧ (d * c⁻¹) ^ 2 ≠ 1) := by
  rcases isDiagonal_or_isTwistedSwap_of_isRefl hp2 h₁ hm₁ with ⟨i, hdiag₁⟩ | ⟨x, y, c, hswap₁⟩
  · rcases isDiagonal_or_isTwistedSwap_of_isRefl hp2 h₂ hm₂ with ⟨j, hdiag₂⟩ | ⟨z, w, d, hswap₂⟩
    · exact absurd (signChange_mul_signChange_pow_two_eq_one hdiag₁ hdiag₂)
        (pow_two_ne_one_of_orderOf_eq_three hord)
    · exact absurd (signChange_mul_isTwistedSwap_pow_four_eq_one hdiag₁ hswap₂)
        (pow_four_ne_one_of_orderOf_eq_three hord)
  · rcases isDiagonal_or_isTwistedSwap_of_isRefl hp2 h₂ hm₂ with ⟨j, hdiag₂⟩ | ⟨z, w, d, hswap₂⟩
    · have h4 : (r₂ * r₁) ^ 4 = 1 :=
        signChange_mul_isTwistedSwap_pow_four_eq_one hdiag₂ hswap₁
      have hinv : (r₁ * r₂)⁻¹ = r₂ * r₁ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h₁.1, inv_eq_of_mul_eq_one_right h₂.1]
      have hord' : orderOf (r₂ * r₁) = 3 := by
        rw [← hinv, orderOf_inv, hord]
      exact absurd h4 (pow_four_ne_one_of_orderOf_eq_three hord')
    · exact exists_isTwistedSwap_of_isTwistedSwap_mul_of_orderOf_eq_three hswap₁ hswap₂ hord

end CFSG.StandardType.ZS

end
