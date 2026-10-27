module

public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.RankThree.Classical.SteinbergBY

open Matrix CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

section Helpers

variable {Ω : Type*} [Field Ω]

local notation "M₃" => Matrix (Fin 3) (Fin 3) Ω

theorem scalar_three_eq_smul (c : Ω) : scalar (Fin 3) c = c • (1 : M₃) := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem conj_coe_eq_scalar_iff (h X : SL(3, Ω)) (c : Ω) :
    ((h * X * h⁻¹ : SL(3, Ω)) : M₃) = scalar (Fin 3) c ↔ (X : M₃) = scalar (Fin 3) c := by
  constructor
  · intro hX
    have h1 : X = h⁻¹ * (h * X * h⁻¹) * h := by group
    rw [h1, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hX,
      scalar_three_eq_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  · intro hX
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hX,
      scalar_three_eq_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_eq_smul_of_inv_mul {X X' : SL(3, Ω)} {c : Ω}
    (h : ((X⁻¹ * X' : SL(3, Ω)) : M₃) = scalar (Fin 3) c) : (X' : M₃) = c • (X : M₃) := by
  have h1 : X' = X * (X⁻¹ * X') := by group
  rw [h1, Matrix.SpecialLinearGroup.coe_mul, h, scalar_three_eq_smul, Matrix.mul_smul,
    Matrix.mul_one]

theorem inv_mul_coe_eq_scalar {X X' : SL(3, Ω)} {c : Ω} (h : (X' : M₃) = c • (X : M₃)) :
    ((X⁻¹ * X' : SL(3, Ω)) : M₃) = scalar (Fin 3) c := by
  rw [Matrix.SpecialLinearGroup.coe_mul, h, Matrix.mul_smul, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, scalar_three_eq_smul]

theorem sl_coe_ne_zero (X : SL(3, Ω)) : (X : M₃) ≠ 0 := by
  intro h
  have := X.2
  rw [h, Matrix.det_zero] at this
  exact zero_ne_one this

theorem smul_left_cancel_sl {X : SL(3, Ω)} {c c' : Ω} (h : c • (X : M₃) = c' • (X : M₃)) :
    c = c' := by
  by_contra hne
  have h1 : (c - c') • (X : M₃) = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact hne (sub_eq_zero.mp h2)
  · exact sl_coe_ne_zero X h2

@[expose] def scalarSL {R : Type*} [CommRing R] (c : R) (hc : c ^ 3 = 1) : SL(3, R) :=
  ⟨scalar (Fin 3) c, by
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hc]⟩

theorem coe_scalarSL {R : Type*} [CommRing R] (c : R) (hc : c ^ 3 = 1) :
    ((scalarSL c hc : SL(3, R)) : Matrix (Fin 3) (Fin 3) R) = scalar (Fin 3) c :=
  rfl

theorem natCard_rootsOfUnity_three_dvd : Nat.card (rootsOfUnity 3 Ω) ∣ 3 := by
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact (mem_rootsOfUnity 3 _).mp g.2

theorem card_map_mul_card_ker {G H : Type*} [Group G] [Group H] (φ : G →* H) (S : Subgroup G)
    (hS : φ.ker ≤ S) : Nat.card (S.map φ) * Nat.card φ.ker = Nat.card S := by
  have h1 := Subgroup.card_mul_index (φ.domRestrict S).ker
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv] at h1
  rw [← h1, mul_comm]

theorem pow_eq_self_of_three_dvd {q : ℕ} (hq : 1 ≤ q) (h3 : 3 ∣ q - 1) {c : Ω} (hc : c ^ 3 = 1) :
    c ^ q = c := by
  obtain ⟨m, hm⟩ := h3
  rw [show q = 3 * m + 1 by omega, pow_succ, pow_mul, hc, one_pow, one_mul]

theorem mul_pow_eq_one_of_not_three_dvd {q : ℕ} (h3 : ¬ 3 ∣ q - 1) {c : Ω} (hc : c ^ 3 = 1) :
    c * (c ^ (2 * (q - 1))) ^ (q - 1) = 1 := by
  have hmod : (1 + 2 * (q - 1) * (q - 1)) % 3 = 0 := by
    have : (q - 1) % 3 = 1 ∨ (q - 1) % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.add_mod, Nat.mul_mod, h]
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hmod
  rw [← pow_mul, ← pow_succ', add_comm, hm, pow_mul, hc, one_pow]

theorem commutatorElement_mul_center {G : Type*} [Group G] (a b : G) {s t : G}
    (hs : s ∈ Subgroup.center G) (ht : t ∈ Subgroup.center G) : ⁅a * s, b * t⁆ = ⁅a, b⁆ := by
  have h1 := Subgroup.mem_center_iff.mp hs b
  have h2 := Subgroup.mem_center_iff.mp ht a
  have h3 := Subgroup.mem_center_iff.mp ht s
  rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev, _root_.mul_inv_rev]
  calc a * s * (b * t) * (s⁻¹ * a⁻¹) * (t⁻¹ * b⁻¹)
      = a * (s * b) * t * s⁻¹ * a⁻¹ * t⁻¹ * b⁻¹ := by group
    _ = a * (b * s) * t * s⁻¹ * a⁻¹ * t⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * (s * t) * s⁻¹ * a⁻¹ * t⁻¹ * b⁻¹ := by group
    _ = a * b * (t * s) * s⁻¹ * a⁻¹ * t⁻¹ * b⁻¹ := by rw [h3]
    _ = a * b * t * a⁻¹ * t⁻¹ * b⁻¹ := by group
    _ = a * b * (t * a⁻¹) * t⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * t) * t⁻¹ * b⁻¹ := by
        rw [show t * a⁻¹ = a⁻¹ * t by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem scalarSL_mem_center {R : Type*} [CommRing R] (c : R) (hc : c ^ 3 = 1) :
    scalarSL c hc ∈ Subgroup.center SL(3, R) :=
  Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by rw [Fintype.card_fin]; exact hc, rfl⟩

theorem coe_mul_scalarSL (X : SL(3, Ω)) (c : Ω) (hc : c ^ 3 = 1) :
    ((X * scalarSL c hc : SL(3, Ω)) : M₃) = c • (X : M₃) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarSL, scalar_three_eq_smul, Matrix.mul_smul,
    Matrix.mul_one]

end Helpers

section Main

variable {Ω : Type} [Field Ω] {ℓ f : ℕ} {k : Type} [Field k] [Algebra k Ω] {Q : Type*} [Group Q]

local notation "M₃" => Matrix (Fin 3) (Fin 3) Ω

theorem exchanged_sl3_central_product_frobenius_full_fixed_layer (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω] (σ : Ω →+* Ω) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (μ : SL(3, Ω) × SL(3, Ω) →* Q) (hμ : Function.Surjective μ)
    (hμker : ∀ x : SL(3, Ω) × SL(3, Ω), μ x = 1 ↔ ∃ c : Ω, c ^ 3 = 1 ∧
      (x.1 : M₃) = scalar (Fin 3) c ∧ (x.2 : M₃) = scalar (Fin 3) c)
    (θ : Q ≃* Q) (a b : SL(3, Ω))
    (hθ : ∀ A B : SL(3, Ω), θ (μ (A, B)) =
      μ (a * SpecialLinearGroup.map σ B * a⁻¹, b * SpecialLinearGroup.map σ A * b⁻¹)) :
    ∃ k₂ : Subfield Ω, (∀ c : Ω, c ∈ k₂ ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧
    ∃ (h₁ h₂ : SL(3, Ω)) (ρ : SL(3, ↥k₂) →* Q),
      (∀ A : SL(3, ↥k₂), ρ A = μ (h₁ * SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * SpecialLinearGroup.map σ (SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹)) ∧
      ρ.range ≤ fixSubgroup θ ∧ (ρ.range.subgroupOf (fixSubgroup θ)).Normal ∧
      CFSG.IsQuasisimple ρ.range ∧
      (∀ A : SL(3, ↥k₂), ρ A = 1 ↔ ∃ c : k, c ^ 3 = 1 ∧
        ((SpecialLinearGroup.map k₂.subtype A : SL(3, Ω)) : M₃) =
          scalar (Fin 3) (algebraMap k Ω c)) ∧
      Nat.card ρ.ker = Nat.gcd 3 (ℓ ^ f - 1) ∧
      Nonempty (SL(3, ↥k₂) ⧸ ρ.ker ≃* ρ.range) ∧
      Nat.card (Subgroup.center ρ.range) =
        Nat.gcd 3 ((ℓ ^ f) ^ 2 - 1) / Nat.gcd 3 (ℓ ^ f - 1) ∧
      Finite (fixSubgroup θ) ∧
      (ρ.range.subgroupOf (fixSubgroup θ)).index ∣ Nat.gcd 3 (ℓ ^ f - 1) ∧
      commutator (fixSubgroup θ) = ρ.range.subgroupOf (fixSubgroup θ) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set q := ℓ ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hℓ.pos
  set F : Subfield Ω := (iterateFrobenius Ω ℓ (2 * f)).eqLocusField (RingHom.id Ω) with hFdef
  have hq2 : q ^ 2 = ℓ ^ (2 * f) := by rw [hq, ← pow_mul, mul_comm]
  have hF2 : ∀ c : Ω, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : Ω, c ∈ F ↔ c ^ q ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = q ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have hkq : ∀ c : k, c ^ q = c := fun c => by
    rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσσ : ∀ c, σ (σ c) = c ^ q ^ 2 := fun c => by rw [hσ, hσ, ← pow_mul, sq]
  set σS : SL(3, Ω) →* SL(3, Ω) := SpecialLinearGroup.map σ with hσS
  have hσS : ∀ X : SL(3, Ω), (σS X : M₃) = (X : M₃).map σ := fun X => rfl
  set ι : SL(3, F) →* SL(3, Ω) := SpecialLinearGroup.map F.subtype with hιdef
  have hι : ∀ A : SL(3, F), (ι A : M₃) = (A : Matrix (Fin 3) (Fin 3) F).map F.subtype :=
    fun A => rfl
  have hιinj : Function.Injective ι := specialLinearGroup_map_injective F.subtype.injective
  have hσσι : ∀ A : SL(3, F), σS (σS (ι A)) = ι A := by
    intro A
    apply Subtype.ext
    ext i j
    rw [hσS, Matrix.map_apply, hσS, Matrix.map_apply, hσσ, hι, Matrix.map_apply]
    exact (hF _).mp (A i j).2
  have hσσfix : ∀ X : SL(3, Ω), σS (σS X) = X → ∃ A : SL(3, F), ι A = X := by
    intro X hX
    refine exists_map_eq_of_forall_mem_range F.subtype.injective X fun i j => ?_
    have h1 := congrArg (fun Z : SL(3, Ω) => (Z : M₃) i j) hX
    simp only [hσS, Matrix.map_apply, hσσ] at h1
    exact ⟨⟨_, (hF _).mpr h1⟩, rfl⟩
  set F' : IntermediateField k Ω := F.toIntermediateField (fun x => by
    rw [hF, ← map_pow, pow_two, pow_mul, hkq, hkq]) with hF'def
  have : IsAlgClosure F' Ω :=
    ⟨IsAlgClosure.isAlgClosed k, Algebra.IsAlgebraic.tower_top (K := k) (A := Ω) F'⟩
  have : CharP F' ℓ := (RingHom.charP_iff_charP (algebraMap F' Ω) ℓ).mpr inferInstance
  have hF'card : Nat.card F' = ℓ ^ (2 * f) := by
    rw [← hq2, ← hFcard]
    rfl
  obtain ⟨-, hlang⟩ := matrix_frobenius_lang (K := F') (f := 2 * f) hℓ (by omega)
    hF'card (n := 3) (by norm_num) (SpecialLinearGroup.toGL (a * σS b))
  obtain ⟨H, hHdet, hH⟩ := hlang (a * σS b).2
  set Hs : SL(3, Ω) := ⟨H, hHdet⟩ with hHsdef
  have hc₀ : a * σS b = Hs⁻¹ * σS (σS Hs) := by
    apply Subtype.ext
    have e1 : ((a * σS b : SL(3, Ω)) : M₃) = (SpecialLinearGroup.toGL (a * σS b) : M₃) := rfl
    have hinv : ((Hs⁻¹ : SL(3, Ω)) : M₃) = ((H⁻¹ : GL (Fin 3) Ω) : M₃) := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.coe_units_inv, Matrix.inv_def, hHdet,
        Ring.inverse_one, one_smul]
    rw [e1, hH, Matrix.SpecialLinearGroup.coe_mul, hσS, hσS, Matrix.map_map, hinv]
    congr 1
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Function.comp_apply, hσσ, hq2]
  set h₁ : SL(3, Ω) := Hs⁻¹ with hh₁
  set h₂ : SL(3, Ω) := b * σS h₁ with hh₂
  have hah : a * σS h₂ = h₁ := by
    rw [hh₂, map_mul, ← mul_assoc, hc₀, mul_assoc, ← map_mul σS, ← map_mul σS, hh₁,
      mul_inv_cancel, map_one, map_one, mul_one]
  set ν : SL(3, Ω) × SL(3, Ω) →* Q :=
    μ.comp ((MulAut.conj h₁).toMonoidHom.prodMap (MulAut.conj h₂).toMonoidHom) with hνdef
  have hν : ∀ X Y, ν (X, Y) = μ (h₁ * X * h₁⁻¹, h₂ * Y * h₂⁻¹) := fun X Y => rfl
  have hνsurj : Function.Surjective ν := by
    intro x
    obtain ⟨⟨X, Y⟩, hXY⟩ := hμ x
    refine ⟨(h₁⁻¹ * X * h₁, h₂⁻¹ * Y * h₂), ?_⟩
    rw [hν, ← hXY]
    congr 1
    ext <;> simp only [] <;> group
  have hνker : ∀ X Y, ν (X, Y) = 1 ↔ ∃ c : Ω, c ^ 3 = 1 ∧ (X : M₃) = scalar (Fin 3) c ∧
      (Y : M₃) = scalar (Fin 3) c := by
    intro X Y
    rw [hν, hμker]
    simp only [conj_coe_eq_scalar_iff]
  have hνeq : ∀ X Y X' Y', ν (X, Y) = ν (X', Y') ↔ ∃ c : Ω, c ^ 3 = 1 ∧
      (X' : M₃) = c • (X : M₃) ∧ (Y' : M₃) = c • (Y : M₃) := by
    intro X Y X' Y'
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, hνker]
    constructor
    · rintro ⟨c, hc, h1, h2⟩
      exact ⟨c, hc, coe_eq_smul_of_inv_mul h1, coe_eq_smul_of_inv_mul h2⟩
    · rintro ⟨c, hc, h1, h2⟩
      exact ⟨c, hc, inv_mul_coe_eq_scalar h1, inv_mul_coe_eq_scalar h2⟩
  have hθν : ∀ X Y, θ (ν (X, Y)) = ν (σS Y, σS X) := by
    intro X Y
    have e1 : a * σS (h₂ * Y * h₂⁻¹) * a⁻¹ = (a * σS h₂) * σS Y * (a * σS h₂)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    have e2 : b * σS (h₁ * X * h₁⁻¹) * b⁻¹ = (b * σS h₁) * σS X * (b * σS h₁)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [hν, hθ, hν, e1, e2, hah]
  have hfixν : ∀ X Y, θ (ν (X, Y)) = ν (X, Y) ↔ ∃ c : Ω, c ^ 3 = 1 ∧
      (σS Y : M₃) = c • (X : M₃) ∧ (σS X : M₃) = c • (Y : M₃) := by
    intro X Y
    rw [hθν, eq_comm, hνeq]
  have hσsmul : ∀ (c : Ω) (X Y : SL(3, Ω)), (Y : M₃) = c • (X : M₃) →
      (σS Y : M₃) = σ c • (σS X : M₃) := by
    intro c X Y h
    rw [hσS, hσS, h]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  set ρ : SL(3, F) →* Q := ν.comp (ι.prod (σS.comp ι)) with hρdef
  have hρ : ∀ A, ρ A = ν (ι A, σS (ι A)) := fun A => rfl
  have hρfix : ∀ A, θ (ρ A) = ρ A := by
    intro A
    rw [hρ, hθν, hσσι]
  have hmemP : ∀ X Y, σS Y = X → σS X = Y → ν (X, Y) ∈ ρ.range := by
    intro X Y h1 h2
    have hX : σS (σS X) = X := by rw [h2, h1]
    obtain ⟨A, hA⟩ := hσσfix X hX
    exact ⟨A, by rw [hρ, hA, h2]⟩
  have hmemF : ∀ c : k, algebraMap k Ω c ∈ F := fun c =>
    (hF _).mpr (by rw [← map_pow, pow_two, pow_mul, hkq, hkq])
  have hρker : ∀ A : SL(3, F), ρ A = 1 ↔ ∃ c : k, c ^ 3 = 1 ∧
      (ι A : M₃) = scalar (Fin 3) (algebraMap k Ω c) := by
    intro A
    rw [hρ, hνker]
    constructor
    · rintro ⟨c, hc, h1, h2⟩
      rw [hσS, h1, scalar_map] at h2
      have hσc : σ c = c := by
        have := congrArg (fun M : M₃ => M 0 0) h2
        simpa [Matrix.scalar_apply] using this
      rw [hσ] at hσc
      obtain ⟨c', rfl⟩ := (mem_range_algebraMap_iff hℓ hf hk c).mpr hσc
      refine ⟨c', ?_, h1⟩
      apply (algebraMap k Ω).injective
      rw [map_pow, map_one, hc]
    · rintro ⟨c, hc, h1⟩
      refine ⟨algebraMap k Ω c, by rw [← map_pow, hc, map_one], h1, ?_⟩
      rw [hσS, h1, scalar_map, hσ, ← map_pow, hkq]
  have hker_le : ρ.ker ≤ Subgroup.center SL(3, F) := by
    intro A hA
    obtain ⟨c, hc, h1⟩ := (hρker A).mp hA
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨⟨_, hmemF c⟩, ?_, ?_⟩
    · apply Subtype.ext
      rw [Fintype.card_fin, SubmonoidClass.coe_pow, OneMemClass.coe_one, ← map_pow, hc, map_one]
    · have h2 : (scalar (Fin 3) (⟨_, hmemF c⟩ : F)).map F.subtype =
          (A : Matrix (Fin 3) (Fin 3) F).map F.subtype := by
        rw [scalar_map]
        exact h1.symm
      exact Matrix.map_injective F.subtype.injective h2
  have hkerCard : Nat.card ρ.ker = Nat.gcd 3 (q - 1) := by
    have hζ3 : ∀ ζ : rootsOfUnity 3 k, ((ζ : kˣ) : k) ^ 3 = 1 := fun ζ => by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ζ.2, Units.val_one]
    have hζF : ∀ ζ : rootsOfUnity 3 k, (⟨algebraMap k Ω ((ζ : kˣ) : k), hmemF _⟩ : F) ^ 3 = 1 :=
      fun ζ => Subtype.ext (by
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, ← map_pow, hζ3, map_one])
    have hmemker : ∀ ζ : rootsOfUnity 3 k, scalarSL _ (hζF ζ) ∈ ρ.ker := by
      intro ζ
      refine (hρker _).mpr ⟨_, hζ3 ζ, ?_⟩
      rw [hι, coe_scalarSL, scalar_map]
      rfl
    let toK : rootsOfUnity 3 k → ρ.ker := fun ζ => ⟨scalarSL _ (hζF ζ), hmemker ζ⟩
    have hbij : Function.Bijective toK := by
      constructor
      · intro ζ ζ' h
        have h1 := congrArg (fun A : ρ.ker => ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0) h
        simp only [toK, coe_scalarSL, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
        have h2 := congrArg Subtype.val h1
        exact Subtype.ext (Units.ext ((algebraMap k Ω).injective h2))
      · rintro ⟨A, hA⟩
        obtain ⟨c, hc, h1⟩ := (hρker A).mp hA
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_pow (by norm_num)] at hc
          exact zero_ne_one hc
        refine ⟨⟨Units.mk0 c hc0, (mem_rootsOfUnity 3 _).mpr (Units.ext (by
          rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc, Units.val_one]))⟩, ?_⟩
        apply Subtype.ext
        apply hιinj
        apply Subtype.ext
        rw [h1, hι, coe_scalarSL, scalar_map]
        rfl
    rw [← Nat.card_eq_of_bijective toK hbij, natCard_rootsOfUnity_eq_gcd, hk, Nat.gcd_comm]
  have : Fintype F := Fintype.ofFinite F
  have hQS : CFSG.IsQuasisimple SL(3, F) :=
    isQuasisimple_specialLinearGroup (K := F) (n := 3) (by norm_num)
  have hρne : ∃ A, ρ.rangeRestrict A ≠ 1 := by
    by_contra h
    push Not at h
    obtain ⟨-, -, x, y, hxy⟩ := hQS
    apply hxy
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    have hx1 : (x' : SL(3, F) ⧸ Subgroup.center SL(3, F)) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      apply hker_le
      rw [← MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]
      exact h x'
    rw [hx1, one_mul, mul_one]
  have hPQ : CFSG.IsQuasisimple ρ.range :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hQS ρ.rangeRestrict_surjective hρne
  have hker' : ρ.rangeRestrict.ker ≤ Subgroup.center SL(3, F) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker_le
  have hcen : Subgroup.center ρ.range = (Subgroup.center SL(3, F)).map ρ.rangeRestrict :=
    CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hQS
      ρ.rangeRestrict_surjective hker'
  have hcenSL : Nat.card (Subgroup.center SL(3, F)) = Nat.gcd 3 (q ^ 2 - 1) := by
    rw [Nat.card_congr
        (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
      Fintype.card_fin, natCard_rootsOfUnity_eq_gcd, hFcard, Nat.gcd_comm]
  have hd0 : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hcenCard : Nat.card (Subgroup.center ρ.range) =
      Nat.gcd 3 (q ^ 2 - 1) / Nat.gcd 3 (q - 1) := by
    have h := card_map_mul_card_ker ρ.rangeRestrict (Subgroup.center SL(3, F)) hker'
    rw [MonoidHom.ker_rangeRestrict, ← hcen, hkerCard, hcenSL] at h
    exact (Nat.div_eq_of_eq_mul_left hd0 h.symm).symm
  have hrep : ∀ x ∈ fixSubgroup θ, ∃ X Y : SL(3, Ω), ∃ c : Ω, ν (X, Y) = x ∧ c ^ 3 = 1 ∧
      (σS Y : M₃) = c • (X : M₃) ∧ (σS X : M₃) = c • (Y : M₃) := by
    intro x hx
    obtain ⟨⟨X, Y⟩, rfl⟩ := hνsurj x
    obtain ⟨c, hc, h1, h2⟩ := (hfixν X Y).mp hx
    exact ⟨X, Y, c, rfl, hc, h1, h2⟩
  have hσS_eq : ∀ (X Y : SL(3, Ω)) (c : Ω) (hc : c ^ 3 = 1), (σS Y : M₃) = c • (X : M₃) →
      σS Y = X * scalarSL c hc := fun X Y c hc h => Subtype.ext (by rw [coe_mul_scalarSL, h])
  have hcommP : ∀ x ∈ fixSubgroup θ, ∀ y ∈ fixSubgroup θ, ⁅x, y⁆ ∈ ρ.range := by
    intro x hx y hy
    obtain ⟨X₁, Y₁, c₁, rfl, hc₁, h₁₁, h₁₂⟩ := hrep x hx
    obtain ⟨X₂, Y₂, c₂, rfl, hc₂, h₂₁, h₂₂⟩ := hrep y hy
    rw [← map_commutatorElement]
    have hpair : ⁅(X₁, Y₁), (X₂, Y₂)⁆ = (⁅X₁, X₂⁆, ⁅Y₁, Y₂⁆) := rfl
    rw [hpair]
    apply hmemP
    · rw [map_commutatorElement, hσS_eq _ _ _ hc₁ h₁₁, hσS_eq _ _ _ hc₂ h₂₁,
        commutatorElement_mul_center _ _ (scalarSL_mem_center _ _) (scalarSL_mem_center _ _)]
    · rw [map_commutatorElement, hσS_eq _ _ _ hc₁ h₁₂, hσS_eq _ _ _ hc₂ h₂₂,
        commutatorElement_mul_center _ _ (scalarSL_mem_center _ _) (scalarSL_mem_center _ _)]
  have hPle : ρ.range ≤ fixSubgroup θ := by
    rintro _ ⟨A, rfl⟩
    exact hρfix A
  have hPn : (ρ.range.subgroupOf (fixSubgroup θ)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := mul_mem (hcommP g g.2 n n.2) hn
    have e : ((g * n * g⁻¹ : fixSubgroup θ) : Q) = ⁅(g : Q), (n : Q)⁆ * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact h
  have hcomm : commutator (fixSubgroup θ) = ρ.range.subgroupOf (fixSubgroup θ) := by
    apply le_antisymm
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [Subgroup.mem_subgroupOf]
      exact hcommP x x.2 y y.2
    · intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      have hperf : commutator ρ.range = ⊤ := hPQ.1.commutator_eq_top
      have hmem : (⟨z, hz⟩ : ρ.range) ∈ commutator ρ.range := hperf ▸ Subgroup.mem_top _
      have h1 := Subgroup.mem_map_of_mem (Subgroup.inclusion hPle) hmem
      rw [commutator_def, Subgroup.map_commutator] at h1
      have h2 := Subgroup.commutator_mono (le_top : Subgroup.map (Subgroup.inclusion hPle) ⊤ ≤ ⊤)
        (le_top : Subgroup.map (Subgroup.inclusion hPle) ⊤ ≤ ⊤) h1
      rw [← commutator_def] at h2
      exact h2
  have hindex : (ρ.range.subgroupOf (fixSubgroup θ)).index ∣ Nat.gcd 3 (q - 1) := by
    by_cases h3 : 3 ∣ q - 1
    · rw [Nat.gcd_eq_left h3]
      have hfixq : ∀ c : Ω, c ^ 3 = 1 → σ c = c := fun c hc => by
        rw [hσ]
        exact pow_eq_self_of_three_dvd hq1 h3 hc
      have hne0 : ∀ c : Ω, c ^ 3 = 1 → c ≠ 0 := by
        rintro c hc rfl
        rw [zero_pow (by norm_num)] at hc
        exact zero_ne_one hc
      have huniq : ∀ (X Y X' Y' : SL(3, Ω)) (c c' : Ω), ν (X, Y) = ν (X', Y') →
          (σS Y : M₃) = c • (X : M₃) → (σS Y' : M₃) = c' • (X' : M₃) → c = c' := by
        intro X Y X' Y' c c' hxy h h'
        obtain ⟨ν₀, hν₀, hX, hY⟩ := (hνeq X Y X' Y').mp hxy
        have h1 : (σS Y' : M₃) = σ ν₀ • (σS Y : M₃) := hσsmul ν₀ Y Y' hY
        rw [hfixq ν₀ hν₀, h, smul_smul, h', hX, smul_smul] at h1
        have h2 := smul_left_cancel_sl h1
        exact mul_left_cancel₀ (hne0 ν₀ hν₀) (by linear_combination -h2)
      choose Xf Yf cf hXY hc3 hcY hcX using fun x : fixSubgroup θ => hrep x x.2
      let δ : fixSubgroup θ →* Ωˣ :=
        { toFun := fun x => Units.mk0 (cf x) (hne0 _ (hc3 x))
          map_one' := by
            apply Units.ext
            rw [Units.val_mk0, Units.val_one]
            refine huniq (Xf 1) (Yf 1) 1 1 (cf 1) 1 ?_ (hcY 1) ?_
            · rw [hXY 1]
              exact (map_one ν).symm
            · rw [map_one, one_smul]
          map_mul' := fun x y => by
            apply Units.ext
            rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0]
            refine huniq (Xf (x * y)) (Yf (x * y)) (Xf x * Xf y) (Yf x * Yf y) (cf (x * y))
              (cf x * cf y) ?_ (hcY (x * y)) ?_
            · rw [hXY (x * y), Subgroup.coe_mul, ← hXY x, ← hXY y, ← map_mul]
              rfl
            · rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
                hcY x, hcY y, Matrix.smul_mul, Matrix.mul_smul, smul_smul] }
      have hδker : δ.ker = ρ.range.subgroupOf (fixSubgroup θ) := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro h
          have h1 : cf x = 1 := by
            have := congrArg Units.val h
            rwa [Units.val_one] at this
          have hY : σS (Yf x) = Xf x := Subtype.ext (by rw [hcY x, h1, one_smul])
          have hX : σS (Xf x) = Yf x := Subtype.ext (by rw [hcX x, h1, one_smul])
          rw [← hXY x]
          exact hmemP _ _ hY hX
        · rintro ⟨A, hA⟩
          apply Units.ext
          rw [Units.val_one]
          change cf x = 1
          refine huniq (Xf x) (Yf x) (ι A) (σS (ι A)) (cf x) 1 ?_ (hcY x) ?_
          · rw [hXY x, ← hA, hρ]
          · rw [hσσι, one_smul]
      have hδrange : δ.range ≤ rootsOfUnity 3 Ω := by
        rintro _ ⟨x, rfl⟩
        rw [mem_rootsOfUnity]
        apply Units.ext
        change (cf x) ^ 3 = 1
        exact hc3 x
      rw [← hδker, Subgroup.index_ker]
      exact (Subgroup.card_dvd_of_le hδrange).trans natCard_rootsOfUnity_three_dvd
    · have hall : ρ.range.subgroupOf (fixSubgroup θ) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_subgroupOf]
        obtain ⟨X, Y, c, hx, hc, h1, h2⟩ := hrep x x.2
        set ν₀ := c ^ (2 * (q - 1)) with hν₀def
        have hν₀ : ν₀ ^ 3 = 1 := by rw [hν₀def, ← pow_mul, mul_comm, pow_mul, hc, one_pow]
        have hcν : c * ν₀ ^ (q - 1) = 1 := mul_pow_eq_one_of_not_three_dvd h3 hc
        have hcν' : ν₀ ^ q * c = ν₀ := by
          calc ν₀ ^ q * c = (c * ν₀ ^ (q - 1)) * ν₀ := by
                rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hq1, mul_comm]
            _ = ν₀ := by rw [hcν, one_mul]
        have hx' : ν (X * scalarSL ν₀ hν₀, Y * scalarSL ν₀ hν₀) = x := by
          rw [← hx, eq_comm, hνeq]
          exact ⟨ν₀, hν₀, coe_mul_scalarSL _ _ _, coe_mul_scalarSL _ _ _⟩
        have hσsc : (σS (scalarSL ν₀ hν₀) : M₃) = ν₀ ^ q • (1 : M₃) := by
          rw [hσS, coe_scalarSL, scalar_map, hσ, scalar_three_eq_smul]
        rw [← hx']
        apply hmemP
        · apply Subtype.ext
          rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, h1, hσsc, coe_mul_scalarSL,
            Matrix.mul_smul, Matrix.mul_one, smul_smul, hcν']
        · apply Subtype.ext
          rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, h2, hσsc, coe_mul_scalarSL,
            Matrix.mul_smul, Matrix.mul_one, smul_smul, hcν']
      rw [hall, Subgroup.index_top]
      exact one_dvd _
  have hfin : Finite (fixSubgroup θ) := by
    have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
    have hPcard : Nat.card ρ.range ≠ 0 := Nat.card_pos.ne'
    have h := Subgroup.card_mul_index (ρ.range.subgroupOf (fixSubgroup θ))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv] at h
    have hidx : (ρ.range.subgroupOf (fixSubgroup θ)).index ≠ 0 := by
      intro h0
      rw [h0] at hindex
      exact absurd (Nat.eq_zero_of_zero_dvd hindex) hd0.ne'
    exact Nat.finite_of_card_ne_zero (by rw [← h]; exact mul_ne_zero hPcard hidx)
  exact ⟨F, hF, h₁, h₂, ρ, fun A => rfl, hPle, hPn, hPQ, hρker, hkerCard,
    ⟨QuotientGroup.quotientKerEquivRange ρ⟩, hcenCard, hfin, hindex, hcomm⟩

end Main

end CFSG.RankThree.Classical.SteinbergBY
