module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.Classical2.SLnSemilinearRigidity
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped MatrixGroups

@[expose] def UC22D4CentShape (ℓ q : ℕ) {G : Type*} [Group G] [Finite G] (C : Subgroup G) :
    Prop :=
  (∀ a ∈ C, ∀ b ∈ C, a * b = b * a) ∨ Odd (Nat.card C) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty ((⁅C, C⁆ : Subgroup G) ≃* SL(2, F))) ∨
    2 ≤ CFSG.Open.pRank ℓ C

variable {G : Type*} [Group G] [Finite G]

theorem uc22d4_le_pRank_of_sl2 {ℓ m : ℕ} (hℓ : ℓ.Prime) {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = ℓ ^ m) {L H : Subgroup G} (hLH : L ≤ H) (e : L ≃* SL(2, F)) :
    m ≤ CFSG.Open.pRank ℓ H := by
  by_cases hm : m = 0
  · subst hm
    exact Nat.zero_le _
  have hchar : CharP F ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (Nat.one_le_iff_ne_zero.2 hm) hF
  let h01 : (0 : Fin 2) ≠ 1 := by decide
  let φ : Multiplicative F →* SL(2, F) :=
    { toFun := fun x => Matrix.SpecialLinearGroup.transvection h01 x.toAdd
      map_one' := by
        change Matrix.SpecialLinearGroup.transvection h01 (0 : F) = 1
        exact Matrix.SpecialLinearGroup.transvection_coeff_zero h01
      map_mul' := fun x y => by
        rw [toAdd_mul, Matrix.SpecialLinearGroup.transvection_add] }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have hentry : (Matrix.SpecialLinearGroup.transvection h01 x.toAdd :
        Matrix (Fin 2) (Fin 2) F) 0 1 =
        (Matrix.SpecialLinearGroup.transvection h01 y.toAdd :
          Matrix (Fin 2) (Fin 2) F) 0 1 := by
      simpa [φ] using congrArg (fun u : SL(2, F) =>
        (u : Matrix (Fin 2) (Fin 2) F) 0 1) hxy
    simp [Matrix.SpecialLinearGroup.transvection_coe, h01] at hentry
    exact Multiplicative.toAdd.injective hentry
  let f : Multiplicative F →* G := L.subtype.comp (e.symm.toMonoidHom.comp φ)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : e.symm (φ x) = e.symm (φ y) := Subgroup.subtype_injective L hxy
    exact hφ_inj (e.symm.injective h1)
  have hpow : ∀ a : Multiplicative F, a ^ ℓ = 1 := by
    intro a
    rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
    have hzero : ℓ • a.toAdd = 0 := by
      rw [nsmul_eq_mul, CharP.cast_eq_zero F ℓ, zero_mul]
    rw [hzero, ofAdd_zero]
  have hA : Nat.card (Multiplicative F) = ℓ ^ m :=
    (Nat.card_congr Multiplicative.ofAdd).symm.trans hF
  refine CFSG.SectionRank.le_pRank_of_injective hℓ.one_lt
    (fun a b => mul_comm a b) hpow hA f hf ?_
  intro x hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hx
  exact hLH (by simp [f])

theorem uc22d4_le_pRank_of_sl3 {ℓ m : ℕ} (hℓ : ℓ.Prime) {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = ℓ ^ m) {L H : Subgroup G} (hLH : L ≤ H) (e : L ≃* SL(3, F)) :
    2 * m ≤ CFSG.Open.pRank ℓ H := by
  by_cases hm : m = 0
  · subst hm
    exact Nat.zero_le _
  have hchar : CharP F ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (Nat.one_le_iff_ne_zero.2 hm) hF
  let φFun : Multiplicative (F × F) → SL(3, F) := fun x =>
    ⟨!![1, 0, x.toAdd.1; 0, 1, x.toAdd.2; 0, 0, 1], by
      rw [Matrix.det_fin_three]
      simp⟩
  let φ : Multiplicative (F × F) →* SL(3, F) :=
    { toFun := φFun
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [φFun, Matrix.SpecialLinearGroup.coe_one]
      map_mul' := fun x y => by
        ext i j
        fin_cases i <;> fin_cases j <;>
          rw [Matrix.SpecialLinearGroup.coe_mul]
        all_goals simp [φFun, Matrix.mul_apply,
          Fin.sum_univ_three, toAdd_mul, add_comm] }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    change φFun x = φFun y at hxy
    have h02 : x.toAdd.1 = y.toAdd.1 := by
      have h := congrArg (fun u : SL(3, F) => (u : Matrix (Fin 3) (Fin 3) F) 0 2) hxy
      simpa [φFun, Matrix.SpecialLinearGroup.coe_mk] using h
    have h12 : x.toAdd.2 = y.toAdd.2 := by
      have h := congrArg (fun u : SL(3, F) => (u : Matrix (Fin 3) (Fin 3) F) 1 2) hxy
      simpa [φFun, Matrix.SpecialLinearGroup.coe_mk] using h
    have hpair : x.toAdd = y.toAdd := Prod.ext h02 h12
    exact Multiplicative.toAdd.injective hpair
  let f : Multiplicative (F × F) →* G := L.subtype.comp (e.symm.toMonoidHom.comp φ)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : e.symm (φ x) = e.symm (φ y) := Subgroup.subtype_injective L hxy
    exact hφ_inj (e.symm.injective h1)
  have hpow : ∀ a : Multiplicative (F × F), a ^ ℓ = 1 := by
    intro a
    rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
    have hzero : ℓ • a.toAdd = 0 := by
      rw [Prod.smul_def]
      ext <;> simp only [nsmul_eq_mul, CharP.cast_eq_zero F ℓ, zero_mul] <;> rfl
    rw [hzero, ofAdd_zero]
  have hcard : Nat.card (F × F) = ℓ ^ (2 * m) := by
    rw [Nat.card_prod, hF, ← pow_add, two_mul]
  have hA : Nat.card (Multiplicative (F × F)) = ℓ ^ (2 * m) :=
    (Nat.card_congr Multiplicative.ofAdd).symm.trans hcard
  refine CFSG.SectionRank.le_pRank_of_injective hℓ.one_lt
    (fun a b => mul_comm a b) hpow hA f hf ?_
  intro x hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hx
  exact hLH (by simp [f])

@[expose] def uc22d4_unit_X {Ω : Type*} [Field Ω] (a ab s c : Ω) :
    Matrix (Fin 3) (Fin 3) Ω :=
  !![1 + c, c * ab, -s; c * a, 1 - c, -s * a; s, s * ab, 1]

@[expose] def uc22d4_unit_Xbar {Ω : Type*} [Field Ω] (a ab s cb : Ω) :
    Matrix (Fin 3) (Fin 3) Ω :=
  !![1 + cb, cb * a, -s; cb * ab, 1 - cb, -s * ab; s, s * a, 1]

theorem uc22d4_unit_mul {Ω : Type*} [Field Ω] {a ab s c s' c' : Ω}
    (h : a * ab = -1) :
    uc22d4_unit_X a ab s c * uc22d4_unit_X a ab s' c' =
      uc22d4_unit_X a ab (s + s') (c + c' - s * s') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22d4_unit_X, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals
    first
    | linear_combination (c * c') * h
    | linear_combination (c * c' - s * s') * h
    | linear_combination (s * c') * h
    | linear_combination (-(c * s')) * h
    | linear_combination (-(s * s')) * h
    | ring

theorem uc22d4_unit_det {Ω : Type*} [Field Ω] {a ab s c : Ω} (h : a * ab = -1) :
    (uc22d4_unit_X a ab s c).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [uc22d4_unit_X]
  linear_combination (s ^ 2 - c * s ^ 2 - c ^ 2) * h

theorem uc22d4_unit_conj {Ω : Type*} [Field Ω] {a ab s c cb : Ω}
    (h : a * ab = -1) (hcb : cb = -c - s ^ 2) :
    Matrix.transpose (uc22d4_unit_Xbar a ab s cb) * uc22d4_unit_X a ab s c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22d4_unit_X, uc22d4_unit_Xbar, Matrix.mul_apply, Fin.sum_univ_three, hcb]
  all_goals
    first
    | linear_combination (-(s ^ 2 * c + c ^ 2)) * h
    | linear_combination (s ^ 3 + s * c) * h
    | linear_combination (s ^ 2 - c * s ^ 2 - c ^ 2) * h
    | linear_combination (-(s * c)) * h
    | linear_combination (s ^ 2) * h
    | ring

theorem uc22d4_unit_map_pow {Ω : Type*} [Field Ω] {q : ℕ} {a ab s c cb : Ω}
    {φ : Ω →+* Ω} (hφ : ∀ x : Ω, φ x = x ^ q)
    (hφs : φ s = s) (hφa : φ a = ab) (hφab : φ ab = a)
    (hφc : φ c = cb) (hφcb : φ cb = c) :
    (uc22d4_unit_X a ab s c).map (· ^ q) = uc22d4_unit_Xbar a ab s cb ∧
      (uc22d4_unit_Xbar a ab s cb).map (· ^ q) = uc22d4_unit_X a ab s c := by
  have hfun : (fun x : Ω => x ^ q) = ⇑φ := funext fun x => (hφ x).symm
  constructor
  · rw [hfun]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply, uc22d4_unit_X, uc22d4_unit_Xbar, map_add, map_sub, map_mul,
        map_neg, map_one, hφs, hφa, hφab, hφc]
  · rw [hfun]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply, uc22d4_unit_X, uc22d4_unit_Xbar, map_add, map_sub, map_mul,
        map_neg, map_one, hφs, hφa, hφab, hφcb]

theorem uc22d4_unit_zero {Ω : Type*} [Field Ω] {a ab : Ω} :
    uc22d4_unit_X a ab 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uc22d4_unit_X]

theorem uc22d4_unit_eq_one {Ω : Type*} [Field Ω] {a ab s c : Ω}
    (h : uc22d4_unit_X a ab s c = 1) : s = 0 ∧ c = 0 := by
  constructor
  · have h1 : (uc22d4_unit_X a ab s c) 2 0 = (1 : Matrix (Fin 3) (Fin 3) Ω) 2 0 := by rw [h]
    simpa [uc22d4_unit_X] using h1
  · have h1 : (uc22d4_unit_X a ab s c) 0 0 = (1 : Matrix (Fin 3) (Fin 3) Ω) 0 0 := by rw [h]
    have h2 : 1 + c = 1 := by simpa [uc22d4_unit_X] using h1
    linear_combination h2

theorem uc22d4_unit_c_add {Ω : Type*} [Field Ω] {x x' s s' c₀ : Ω}
    (h2 : (2 : Ω) ≠ 0) :
    (x * c₀ - s ^ 2 / 2) + (x' * c₀ - s' ^ 2 / 2) - s * s' =
      (x + x') * c₀ - (s + s') ^ 2 / 2 := by
  field_simp
  ring

theorem uc22d4_unit_phi_c {Ω : Type*} [Field Ω] {φ : Ω →+* Ω} {c₀ s x : Ω}
    (h2 : (2 : Ω) ≠ 0) (hφx : φ x = x) (hφs : φ s = s) (hφc0 : φ c₀ = -c₀)
    (hφ2 : φ (2 : Ω) = 2) :
    φ (x * c₀ - s ^ 2 / 2) = -(x * c₀ - s ^ 2 / 2) - s ^ 2 := by
  rw [map_sub, map_mul, map_div₀, map_pow, hφx, hφs, hφc0, hφ2]
  field_simp
  ring

theorem uc22d4_unit_phi_cb {Ω : Type*} [Field Ω] {φ : Ω →+* Ω} {c s : Ω}
    (hφc : φ c = -c - s ^ 2) (hφs : φ s = s) :
    φ (-c - s ^ 2) = c := by
  rw [map_sub, map_neg, map_pow, hφc, hφs]
  ring

theorem uc22d4_unit_mem {Ω : Type*} [Field Ω] {q : ℕ} {a ab s c cb : Ω}
    {φ : Ω →+* Ω} (hφ : ∀ x : Ω, φ x = x ^ q)
    (h1 : a * ab = -1) (hφs : φ s = s) (hφa : φ a = ab) (hφab : φ ab = a)
    (hφc : φ c = cb) (hφcb : φ cb = c) (hcb : cb = -c - s ^ 2)
    (hdet : IsUnit (uc22d4_unit_X a ab s c).det) :
    (Matrix.nonsingInvUnit (uc22d4_unit_X a ab s c) hdet : GL (Fin 3) Ω) ∈
      CFSG.RankThree.Classical2.unitarySet q 3 := by
  obtain ⟨hmap1, hmap2⟩ := uc22d4_unit_map_pow hφ hφs hφa hφab hφc hφcb
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · have hp1 : (uc22d4_unit_X a ab s c) i j ^ q = (uc22d4_unit_Xbar a ab s cb) i j := by
      simpa [Matrix.map_apply] using congrFun (congrFun hmap1 i) j
    have hp2 : (uc22d4_unit_Xbar a ab s cb) i j ^ q = (uc22d4_unit_X a ab s c) i j := by
      simpa [Matrix.map_apply] using congrFun (congrFun hmap2 i) j
    change (uc22d4_unit_X a ab s c) i j ^ q ^ 2 = (uc22d4_unit_X a ab s c) i j
    rw [pow_two, pow_mul, hp1, hp2]
  · change (uc22d4_unit_X a ab s c).det = 1
    exact uc22d4_unit_det h1
  · change Matrix.transpose ((uc22d4_unit_X a ab s c).map (· ^ q)) *
      (uc22d4_unit_X a ab s c) = 1
    rw [hmap1]
    exact uc22d4_unit_conj h1 hcb

theorem uc22d4_exists_injective_unitary {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharP Ω ℓ] (U : Subgroup (GL (Fin 3) Ω))
    (hU : (U : Set (GL (Fin 3) Ω)) = CFSG.RankThree.Classical2.unitarySet (ℓ ^ f) 3) :
    ∃ φ : Multiplicative (ZMod ℓ × ZMod ℓ) →* U, Function.Injective φ := by
  classical
  have hFact : Fact ℓ.Prime := ⟨hℓ⟩
  have hExpChar : ExpChar Ω ℓ := expChar_prime (R := Ω) ℓ
  have hℓ3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
  have hq3 : 3 ≤ ℓ ^ f := by
    have h1 : 3 ^ 1 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have h2 : 3 ^ f ≤ ℓ ^ f := Nat.pow_le_pow_left hℓ3 f
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ f := h1
      _ ≤ ℓ ^ f := h2
  have hq1 : 1 ≤ ℓ ^ f := le_trans (by norm_num) hq3
  have hqodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hqeven : Even (ℓ ^ f - 1) := Nat.Odd.sub_odd hqodd odd_one
  have h2 : (2 : Ω) ≠ 0 := by
    intro h
    have hdvd : ℓ ∣ 2 := (CharP.cast_eq_zero_iff Ω ℓ 2).1 (by simpa using h)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
    · exact hℓ.ne_one h'
    · exact hℓ2 h'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) (n := ℓ ^ f + 1) (by omega)
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) (n := ℓ ^ f - 1) (by omega)
  let ab : Ω := a ^ (ℓ ^ f)
  have h1 : a * ab = -1 := by
    show a * a ^ (ℓ ^ f) = -1
    rw [← pow_succ']
    exact ha
  have hc0q : c₀ ^ (ℓ ^ f) = -c₀ := by
    conv_lhs => rw [← Nat.sub_add_cancel hq1]
    rw [pow_succ, hc₀]
    ring
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : ℓ ^ f - 1 ≠ 0)] at hc₀
    exact (neg_ne_zero.mpr one_ne_zero) hc₀.symm
  have haa : a ^ (ℓ ^ f) ^ 2 = a := by
    have hqa : (ℓ ^ f) ^ 2 = (ℓ ^ f + 1) * (ℓ ^ f - 1) + 1 := by
      have hqsub : ℓ ^ f = (ℓ ^ f - 1) + 1 := (Nat.sub_add_cancel hq1).symm
      rw [hqsub]
      simp only [Nat.add_sub_cancel]
      ring
    calc a ^ (ℓ ^ f) ^ 2 = a ^ ((ℓ ^ f + 1) * (ℓ ^ f - 1) + 1) := by rw [hqa]
    _ = a ^ ((ℓ ^ f + 1) * (ℓ ^ f - 1)) * a := pow_succ _ _
    _ = (a ^ (ℓ ^ f + 1)) ^ (ℓ ^ f - 1) * a := by rw [pow_mul]
    _ = (-1) ^ (ℓ ^ f - 1) * a := by rw [ha]
    _ = 1 * a := by rw [Even.neg_one_pow hqeven]
    _ = a := one_mul a
  have habq : ab ^ (ℓ ^ f) = a := by
    show (a ^ (ℓ ^ f)) ^ (ℓ ^ f) = a
    rw [← pow_mul, ← pow_two]
    exact haa
  let ι : ZMod ℓ →+* Ω := ZMod.castHom (dvd_refl ℓ) Ω
  have hιinj : Function.Injective ι := ZMod.castHom_injective Ω
  have hιpow : ∀ m : ZMod ℓ, ι m ^ (ℓ ^ f) = ι m := by
    intro m
    rw [← map_pow]
    exact congrArg ι (ZMod.pow_card_pow m)
  let φ : Ω →+* Ω := iterateFrobenius Ω ℓ f
  have hφ : ∀ x : Ω, φ x = x ^ (ℓ ^ f) := fun x => iterateFrobenius_def ..
  have hι2 : ι (2 : ZMod ℓ) = (2 : Ω) := map_natCast ι 2
  have h2q : (2 : Ω) ^ (ℓ ^ f) = 2 := by
    rw [← hι2]
    exact hιpow 2
  have hφ2 : φ (2 : Ω) = 2 := by rw [hφ]; exact h2q
  have hφs : ∀ m : ZMod ℓ, φ (ι m) = ι m := fun m => by rw [hφ]; exact hιpow m
  have hφa : φ a = ab := hφ a
  have hφab : φ ab = a := by rw [hφ]; exact habq
  have hφc0 : φ c₀ = -c₀ := by rw [hφ]; exact hc0q
  have hdetu : ∀ p : ZMod ℓ × ZMod ℓ,
      IsUnit ((uc22d4_unit_X a ab (ι p.1) (ι p.2 * c₀ - (ι p.1) ^ 2 / 2)).det) := by
    rintro ⟨m, n⟩
    rw [uc22d4_unit_det h1]
    exact isUnit_one
  have hmem : ∀ p : ZMod ℓ × ZMod ℓ,
      (Matrix.nonsingInvUnit (uc22d4_unit_X a ab (ι p.1) (ι p.2 * c₀ - (ι p.1) ^ 2 / 2))
        (hdetu p) : GL (Fin 3) Ω) ∈
        CFSG.RankThree.Classical2.unitarySet (ℓ ^ f) 3 := by
    rintro ⟨m, n⟩
    have hφcm : φ (ι n * c₀ - (ι m) ^ 2 / 2) = -(ι n * c₀ - (ι m) ^ 2 / 2) - (ι m) ^ 2 :=
      uc22d4_unit_phi_c h2 (hφs n) (hφs m) hφc0 hφ2
    exact uc22d4_unit_mem hφ h1 (hφs m) hφa hφab hφcm
      (uc22d4_unit_phi_cb hφcm (hφs m)) rfl (hdetu (m, n))
  let F : Multiplicative (ZMod ℓ × ZMod ℓ) → U := fun x =>
    ⟨Matrix.nonsingInvUnit (uc22d4_unit_X a ab (ι x.toAdd.1)
      (ι x.toAdd.2 * c₀ - (ι x.toAdd.1) ^ 2 / 2)) (hdetu x.toAdd), by
      show (Matrix.nonsingInvUnit (uc22d4_unit_X a ab (ι x.toAdd.1)
        (ι x.toAdd.2 * c₀ - (ι x.toAdd.1) ^ 2 / 2)) (hdetu x.toAdd) :
          GL (Fin 3) Ω) ∈ (U : Set (GL (Fin 3) Ω))
      rw [hU]
      exact hmem x.toAdd⟩
  have hFone : F 1 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show uc22d4_unit_X a ab (ι (0 : ZMod ℓ))
      (ι (0 : ZMod ℓ) * c₀ - (ι (0 : ZMod ℓ)) ^ 2 / 2) = 1
    rw [map_zero, zero_mul, zero_pow (by norm_num), zero_div, sub_zero]
    exact uc22d4_unit_zero
  have hFmul : ∀ x y : Multiplicative (ZMod ℓ × ZMod ℓ), F (x * y) = F x * F y := by
    rintro ⟨m, n⟩ ⟨m', n'⟩
    apply Subtype.ext
    apply Units.ext
    have hcadd : (ι n * c₀ - (ι m) ^ 2 / 2) + (ι n' * c₀ - (ι m') ^ 2 / 2) -
        ι m * ι m' = ι (n + n') * c₀ - (ι (m + m')) ^ 2 / 2 := by
      rw [map_add, map_add]
      exact uc22d4_unit_c_add h2
    show uc22d4_unit_X a ab (ι (m + m')) (ι (n + n') * c₀ - (ι (m + m')) ^ 2 / 2) =
      uc22d4_unit_X a ab (ι m) (ι n * c₀ - (ι m) ^ 2 / 2) *
        uc22d4_unit_X a ab (ι m') (ι n' * c₀ - (ι m') ^ 2 / 2)
    rw [uc22d4_unit_mul h1, ← hcadd, map_add]
  refine ⟨{ toFun := F, map_one' := hFone, map_mul' := hFmul }, ?_⟩
  rw [injective_iff_map_eq_one]
  rintro ⟨m, n⟩ hx
  have hmat : uc22d4_unit_X a ab (ι m) (ι n * c₀ - (ι m) ^ 2 / 2) = 1 := by
    have h1' := congrArg (fun u : U => ((u : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω)) hx
    change uc22d4_unit_X a ab (ι m) (ι n * c₀ - (ι m) ^ 2 / 2) = 1 at h1'
    exact h1'
  obtain ⟨hs, hc⟩ := uc22d4_unit_eq_one hmat
  have hm : m = 0 := hιinj (by simpa using hs)
  have hnc : ι n * c₀ = 0 := by
    have hc' := hc
    rw [hs] at hc'
    simpa using hc'
  have hιn : ι n = 0 := by
    rcases mul_eq_zero.mp hnc with h | h
    · exact h
    · exact absurd h hc₀0
  have hn : n = 0 := hιinj (by simpa using hιn)
  subst hm
  subst hn
  rfl

theorem uc22d4_two_le_pRank_of_unitary {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharP Ω ℓ] (U : Subgroup (GL (Fin 3) Ω))
    (hU : (U : Set (GL (Fin 3) Ω)) = CFSG.RankThree.Classical2.unitarySet (ℓ ^ f) 3)
    {L H : Subgroup G} (hLH : L ≤ H) (e : L ≃* U) : 2 ≤ CFSG.Open.pRank ℓ H := by
  obtain ⟨φ, hφinj⟩ := uc22d4_exists_injective_unitary hℓ hℓ2 hf U hU
  have hNeZero : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hcomm : ∀ a b : Multiplicative (ZMod ℓ × ZMod ℓ), a * b = b * a :=
    fun a b => mul_comm a b
  have hpow : ∀ a : Multiplicative (ZMod ℓ × ZMod ℓ), a ^ ℓ = 1 := by
    intro a
    apply Multiplicative.ext
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
    apply Prod.ext <;> simp
  have hcard : Nat.card (Multiplicative (ZMod ℓ × ZMod ℓ)) = ℓ ^ 2 := by
    have h1 : Nat.card (Multiplicative (ZMod ℓ × ZMod ℓ)) = Nat.card (ZMod ℓ × ZMod ℓ) :=
      Nat.card_congr Multiplicative.toAdd
    rw [h1, Nat.card_prod]
    have h2 : Nat.card (ZMod ℓ) = ℓ := by rw [Nat.card_eq_fintype_card, ZMod.card]
    rw [h2, sq]
  let g : Multiplicative (ZMod ℓ × ZMod ℓ) →* G :=
    L.subtype.comp ((e.symm : U →* L).comp φ)
  have hginj : Function.Injective g :=
    L.subtype_injective.comp ((e.symm.injective).comp hφinj)
  have hgrange : g.range ≤ H := by
    rintro y ⟨x, rfl⟩
    exact hLH (e.symm (φ x)).2
  exact CFSG.SectionRank.le_pRank_of_injective hℓ.one_lt hcomm hpow hcard g hginj hgrange

theorem uc22d4_eq_commutator_of_sl2 {C L : Subgroup G} (hLC : L ≤ C) {F F' : Type*} [Field F]
    [Finite F] [Field F'] [Finite F'] (h4 : 4 ≤ Nat.card F) (hFF' : Nat.card F' = Nat.card F)
    (eC : (⁅C, C⁆ : Subgroup G) ≃* SL(2, F)) (eL : L ≃* SL(2, F')) : L = ⁅C, C⁆ := by
  have h4' : 4 ≤ Nat.card F' := by omega
  have hperf : Group.IsPerfect L := by
    have : Group.IsPerfect (SL(2, F')) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F' h4'
    exact Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hLL : ⁅L, L⁆ = L := Subgroup.commutator_eq_self
  have hLle : L ≤ ⁅C, C⁆ := by
    rw [← hLL]
    exact Subgroup.commutator_mono hLC hLC
  have hcardL : Nat.card L = Nat.card F' * (Nat.card F' ^ 2 - 1) := by
    let := Fintype.ofFinite F'
    have hq : 1 < Fintype.card F' := Fintype.one_lt_card
    rw [Nat.card_congr eL.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero,
      Fin.val_one, pow_zero, pow_one, Nat.card_eq_fintype_card,
      show Fintype.card F' ^ 2 - Fintype.card F' = Fintype.card F' * (Fintype.card F' - 1) by
        rw [Nat.mul_sub_one, sq],
      ← mul_assoc, Nat.mul_div_cancel _ (by omega), mul_comm]
  have hcardC : Nat.card (⁅C, C⁆ : Subgroup G) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    let := Fintype.ofFinite F
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    rw [Nat.card_congr eC.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero,
      Fin.val_one, pow_zero, pow_one, Nat.card_eq_fintype_card,
      show Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) by
        rw [Nat.mul_sub_one, sq],
      ← mul_assoc, Nat.mul_div_cancel _ (by omega), mul_comm]
  refine Subgroup.eq_of_le_of_card_ge hLle ?_
  rw [hcardL, hcardC, hFF']

private theorem uc22d4_tail_card_sl2 {L : Type*} [Group L] {F : Type*} [Field F] [Finite F]
    (e : L ≃* SL(2, F)) : Nat.card L = Nat.card F * (Nat.card F ^ 2 - 1) := by
  let := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, Nat.card_eq_fintype_card,
    show Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) by
      rw [Nat.mul_sub_one, sq],
    ← mul_assoc, Nat.mul_div_cancel _ (by omega), mul_comm]

theorem uc22d4_unique_sl2_or_rank_of_shape {ℓ q : ℕ} (hq : 4 ≤ q) {C : Subgroup G}
    (h : UC22D4CentShape ℓ q C) :
    (∀ L L' : Subgroup G, L ≤ C → L' ≤ C →
      ∀ (F F' : Type) [Field F] [Field F'] [Finite F] [Finite F'], Nat.card F = q →
        Nat.card F' = q → Nonempty (L ≃* SL(2, F)) → Nonempty (L' ≃* SL(2, F')) → L = L') ∨
      2 ≤ CFSG.Open.pRank ℓ C := by
  rcases h with hab | hodd | ⟨F₀, hFld₀, hFin₀, hF₀, ⟨eC⟩⟩ | hrk
  · left
    intro L L' hLC hL'C F F' _ _ _ _ hF hF' ⟨eL⟩ _
    exfalso
    have h4F : 4 ≤ Nat.card F := by omega
    have hperfL : Group.IsPerfect L := by
      have : Group.IsPerfect (SL(2, F)) :=
        CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4F
      exact Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
    have hLcomm : IsMulCommutative L :=
      IsMulCommutative.of_comm (fun a b => Subtype.ext (hab a (hLC a.2) b (hLC b.2)))
    have : Subsingleton L := Group.IsPerfect.subsingleton_of_isMulCommutative
    have h1 : Nat.card L = 1 := Nat.card_of_subsingleton 1
    have hcardL := uc22d4_tail_card_sl2 eL
    have h2 : 16 ≤ Nat.card F ^ 2 := by
      rw [sq]
      calc 16 = 4 * 4 := by norm_num
        _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul h4F h4F
    have h3 : 15 ≤ Nat.card F ^ 2 - 1 := by omega
    have hbig : 60 ≤ Nat.card L := by
      rw [hcardL]
      calc 60 = 4 * 15 := by norm_num
        _ ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h4F h3
    omega
  · left
    intro L L' hLC _ F F' _ _ _ _ hF _ ⟨eL⟩ _
    exfalso
    have hcardL := uc22d4_tail_card_sl2 eL
    have hev : Even (Nat.card L) := by
      rw [hcardL, Nat.even_mul]
      have h4F : 4 ≤ Nat.card F := by omega
      rcases Nat.even_or_odd (Nat.card F) with he | ho
      · exact Or.inl he
      · exact Or.inr (even_iff_two_dvd.mpr
          (dvd_trans (by norm_num : 2 ∣ 8) (Nat.eight_dvd_sq_sub_one_of_odd ho)))
    have h2C : 2 ∣ Nat.card C :=
      (even_iff_two_dvd.mp hev).trans (Subgroup.card_dvd_of_le hLC)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2C)
  · left
    let : Field F₀ := hFld₀
    let : Finite F₀ := hFin₀
    intro L L' hLC hL'C F F' _ _ _ _ hF hF' ⟨eL⟩ ⟨eL'⟩
    have h4F₀ : 4 ≤ Nat.card F₀ := by omega
    have hFF₀ : Nat.card F' = Nat.card F₀ := by omega
    have hFF₀' : Nat.card F = Nat.card F₀ := by omega
    exact (uc22d4_eq_commutator_of_sl2 (C := C) (L := L) (F := F₀) (F' := F)
      hLC h4F₀ hFF₀' eC eL).trans
      (uc22d4_eq_commutator_of_sl2 (C := C) (L := L') (F := F₀) (F' := F')
        hL'C h4F₀ hFF₀ eC eL').symm
  · right
    exact hrk

end CFSG.LocalAnalysis.UniquenessCase.UC22
