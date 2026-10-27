module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
public import CFSG.RankThree.Classical.SemilinearFixedBasis

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def fixedIn (X : Subgroup (GL (Fin 3) K)) (σ : GL (Fin 3) K →* GL (Fin 3) K) :
    Subgroup (GL (Fin 3) K) :=
  X ⊓ σ.eqLocus (MonoidHom.id _)

theorem mem_fixedIn {X : Subgroup (GL (Fin 3) K)} {σ : GL (Fin 3) K →* GL (Fin 3) K}
    {A : GL (Fin 3) K} : A ∈ fixedIn X σ ↔ A ∈ X ∧ σ A = A :=
  Iff.rfl

theorem ringAut_pow_apply {F : Type*} [Field F] {φ : F ≃+* F} {r : ℕ} (hφ : ∀ a, φ a = a ^ r)
    (k : ℕ) (a : F) : (φ ^ k) a = a ^ r ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [pow_succ, RingAut.mul_apply, ih, hφ, ← pow_mul, ← pow_succ']

theorem ringAut_apply_three {φ : K ≃+* K} (hφ3 : orderOf φ = 3) (c : K) : φ (φ (φ c)) = c := by
  have h := congrArg (fun e : K ≃+* K => e c) (pow_orderOf_eq_one φ)
  simp only [hφ3, RingAut.coe_pow, RingAut.one_apply] at h
  exact h

theorem exists_frob (hK : PiField π p f K) {f₀ : ℕ} (hf : f = 3 * f₀) :
    ∃ φ : K ≃+* K, (∀ c, φ c = c ^ piCard π (p ^ f₀)) ∧ orderOf φ = 3 := by
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  obtain ⟨k, hk0, hKn, hr⟩ : ∃ k, 0 < k ∧ Nat.card K = p ^ (3 * k) ∧
      piCard π (p ^ f₀) = p ^ k := by
    cases π
    · refine ⟨2 * f₀, by omega, ?_, ?_⟩
      · rw [hK.card, hf]
        change (p ^ (3 * f₀)) ^ 2 = p ^ (3 * (2 * f₀))
        ring
      · change (p ^ f₀) ^ 2 = p ^ (2 * f₀)
        ring
    · refine ⟨f₀, by omega, ?_, rfl⟩
      rw [hK.card, hf]
      rfl
  obtain ⟨σ, hσ, hord, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hK.prime (by omega) hKn
  refine ⟨σ ^ k, fun c => by rw [hr, ringAut_pow_apply hσ], ?_⟩
  rw [orderOf_pow_of_dvd hk0.ne' (by rw [hord]; exact dvd_mul_left k 3), hord,
    Nat.mul_div_cancel _ hk0]

theorem exists_fixedField (hK : PiField π p f K) {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K}
    (hφ3 : orderOf φ = 3) :
    ∃ K₀ : Subfield K, (∀ c, c ∈ K₀ ↔ φ c = c) ∧ Nat.card K₀ = piCard π (p ^ f₀) := by
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  obtain ⟨k, hk0, hKn, hr⟩ : ∃ k, 0 < k ∧ Nat.card K = p ^ (3 * k) ∧
      piCard π (p ^ f₀) = p ^ k := by
    cases π
    · refine ⟨2 * f₀, by omega, ?_, ?_⟩
      · rw [hK.card, hf]
        change (p ^ (3 * f₀)) ^ 2 = p ^ (3 * (2 * f₀))
        ring
      · change (p ^ f₀) ^ 2 = p ^ (2 * f₀)
        ring
    · refine ⟨f₀, by omega, ?_, rfl⟩
      rw [hK.card, hf]
      rfl
  obtain ⟨-, -, -, -, -, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality hK.prime (by omega) hKn
  obtain ⟨-, S, hS, hScard⟩ := hfix (Subgroup.zpowers φ)
  rw [Nat.card_zpowers, hφ3, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)] at hScard
  refine ⟨S, fun c => ?_, by rw [hScard, hr]⟩
  rw [← SetLike.mem_coe, hS, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h φ (Subgroup.mem_zpowers φ)
  · intro hc τ hτ
    have hfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hφ3]; norm_num)
    obtain ⟨m, rfl⟩ := hfin.mem_powers_iff_mem_zpowers.mpr hτ
    rw [RingAut.coe_pow]
    exact Function.iterate_fixed hc m

@[expose] noncomputable def frobGL (φ : K ≃+* K) : GL (Fin 3) K →* GL (Fin 3) K :=
  Units.map (φ : K →+* K).mapMatrix.toMonoidHom

theorem coe_frobGL (φ : K ≃+* K) (A : GL (Fin 3) K) :
    ((frobGL φ A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K).map φ :=
  rfl

theorem frobGL_three {φ : K ≃+* K} (hφ3 : orderOf φ = 3) (A : GL (Fin 3) K) :
    frobGL φ (frobGL φ (frobGL φ A)) = A := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL, coe_frobGL]
  ext i j
  simp only [Matrix.map_apply, ringAut_apply_three hφ3]

theorem frobGL_scalar (φ : K ≃+* K) (u : Kˣ) :
    frobGL φ (GeneralLinearGroup.scalar (Fin 3) u) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (φ : K →* K) u) := by
  apply Units.ext
  rw [coe_frobGL, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero φ)]
  rfl

theorem frobGL_mem_glPi (hK : PiField π p f K) (φ : K ≃+* K) {A : GL (Fin 3) K}
    (hA : A ∈ glPi π 3 (p ^ f) K) : frobGL φ A ∈ glPi π 3 (p ^ f) K := by
  cases π
  · have h := hK.unitary
    rw [mem_glPi_false h] at hA ⊢
    rw [coe_frobGL]
    have hc : ((A : Matrix (Fin 3) (Fin 3) K).map φ).map h.bar =
        ((A : Matrix (Fin 3) (Fin 3) K).map h.bar).map φ := by
      ext i j
      simp only [Matrix.map_apply, h.bar_apply, map_pow]
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, hA, Matrix.map_one _ (map_zero φ)
      (map_one φ)]
  · exact mem_glPi_true _ _

theorem frobGL_det (φ : K ≃+* K) (A : GL (Fin 3) K) :
    ((frobGL φ A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      φ (A : Matrix (Fin 3) (Fin 3) K).det := by
  rw [coe_frobGL]
  exact (RingHom.map_det (φ : K →+* K) _).symm

theorem frobGL_mem_slPi (hK : PiField π p f K) (φ : K ≃+* K) {A : GL (Fin 3) K}
    (hA : A ∈ slPi π 3 (p ^ f) K) : frobGL φ A ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [mem_slPi_iff hπ] at hA ⊢
  exact ⟨frobGL_mem_glPi hK φ hA.1, by rw [frobGL_det, hA.2, map_one]⟩

theorem exists_tau (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ τ : K, τ ^ 3 = 1 ∧ τ ≠ 1 := by
  have := hK.finite
  have h3 : 3 ∣ Nat.card K - 1 := dvd_trans (three_dvd_qSubPi hq) (qSubPi_dvd hK)
  have hcard : Nat.card (rootsOfUnity 3 K) = 3 := CFSG.LinearGroups.card_rootsOfUnity_of_dvd h3
  have : Nontrivial (rootsOfUnity 3 K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨t, ht⟩ := exists_ne (1 : rootsOfUnity 3 K)
  refine ⟨((t : Kˣ) : K), ?_, fun h => ht (Subtype.ext (Units.ext h))⟩
  have := congrArg Units.val ((mem_rootsOfUnity _ _).mp t.2)
  rwa [Units.val_pow_eq_pow_val, Units.val_one] at this

theorem pow_three_mod_three (n : ℕ) : n ^ 3 % 3 = n % 3 := by
  rw [Nat.pow_mod]
  have h : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize n % 3 = m at h ⊢
  interval_cases m <;> rfl

theorem modThree_of_cube {q₀ : ℕ} (h : ModThree π (q₀ ^ 3)) : ModThree π q₀ := by
  have h3 := pow_three_mod_three q₀
  cases π
  · change q₀ ^ 3 % 3 = 2 at h
    change q₀ % 3 = 2
    omega
  · change q₀ ^ 3 % 3 = 1 at h
    change q₀ % 3 = 1
    omega

theorem norm_exponent {q₀ : ℕ} (hq : ModThree π q₀) :
    ∃ j : ℕ, 1 + piCard π q₀ + piCard π q₀ ^ 2 =
      3 * (3 * (q₀ / 3) ^ 2 + 3 * (q₀ / 3) + 1) + j * qSubPi π (q₀ ^ 3) := by
  cases π
  · change q₀ % 3 = 2 at hq
    obtain ⟨t, rfl⟩ : ∃ t, q₀ = 3 * t + 2 := ⟨q₀ / 3, by omega⟩
    have ht : (3 * t + 2) / 3 = t := by omega
    refine ⟨3 * t + 2, ?_⟩
    change 1 + (3 * t + 2) ^ 2 + ((3 * t + 2) ^ 2) ^ 2 =
      _ + (3 * t + 2) * ((3 * t + 2) ^ 3 + 1)
    rw [ht]
    ring
  · change q₀ % 3 = 1 at hq
    obtain ⟨t, rfl⟩ : ∃ t, q₀ = 3 * t + 1 := ⟨q₀ / 3, by omega⟩
    have ht : (3 * t + 1) / 3 = t := by omega
    refine ⟨0, ?_⟩
    change 1 + (3 * t + 1) + (3 * t + 1) ^ 2 = _ + 0 * _
    rw [ht]
    ring

theorem pow_qSubPi_eq_one_of_fixed {q₀ : ℕ} (hq₀ : 1 ≤ q₀) {t : K} (ht0 : t ≠ 0)
    (hfix : t ^ piCard π q₀ = t) (ht : t ^ qSubPi π (q₀ ^ 3) = 1) : t ^ qSubPi π q₀ = 1 := by
  cases π
  · change t ^ (q₀ ^ 2) = t at hfix
    change t ^ (q₀ ^ 3 + 1) = 1 at ht
    change t ^ (q₀ + 1) = 1
    have h3 : t ^ q₀ ^ 3 = t ^ q₀ := by
      rw [show q₀ ^ 3 = q₀ ^ 2 * q₀ by ring, pow_mul, hfix]
    rw [pow_succ, h3, ← pow_succ] at ht
    exact ht
  · change t ^ q₀ = t at hfix
    change t ^ (q₀ - 1) = 1
    obtain ⟨k, rfl⟩ : ∃ k, q₀ = k + 1 := ⟨q₀ - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    rw [pow_succ] at hfix
    exact mul_right_cancel₀ ht0 (by rw [hfix, one_mul])

theorem exists_pow_eq_of_pow_div {G : Type*} [Group G] [IsCyclic G] [Finite G] {M : ℕ}
    (hM : M ∣ Nat.card G) {t : G} (ht : t ^ (Nat.card G / M) = 1) : ∃ s : G, s ^ M = t := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf γ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hγ t)
  obtain ⟨m, hm⟩ := hM
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hm
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have hdiv : Nat.card G / M = m := by rw [hm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hM0)]
  rw [hdiv, ← zpow_natCast, ← _root_.zpow_mul] at ht
  have h1 := orderOf_dvd_iff_zpow_eq_one.mpr ht
  rw [hord, hm] at h1
  push_cast at h1
  have hm0' : (m : ℤ) ≠ 0 := by exact_mod_cast hm0
  obtain ⟨i, rfl⟩ := (mul_dvd_mul_iff_right hm0').mp h1
  exact ⟨γ ^ i, by rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm]⟩

theorem exists_cocycle_eq_one (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hσ3 : ∀ A ∈ slPi π 3 (p ^ f) K,
      g * frobGL φ (g * frobGL φ (g * frobGL φ A * g⁻¹) * g⁻¹) * g⁻¹ = A) :
    ∃ s ∈ rootsOfUnity (qSubPi π (p ^ f)) K,
      g * GeneralLinearGroup.scalar (Fin 3) s *
          frobGL φ (g * GeneralLinearGroup.scalar (Fin 3) s) *
        frobGL φ (frobGL φ (g * GeneralLinearGroup.scalar (Fin 3) s)) = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hΦ3 := frobGL_three hφ3
  set c := g * frobGL φ g * frobGL φ (frobGL φ g) with hc
  have hcL : ∀ A ∈ slPi π 3 (p ^ f) K, c * A = A * c := by
    intro A hA
    have h := hσ3 A hA
    simp only [map_mul, map_inv, hΦ3] at h
    have h' : c * A * c⁻¹ = A := by
      rw [hc]
      convert h using 1
      group
    calc c * A = c * A * c⁻¹ * c := by group
      _ = A * c := by rw [h']
  obtain ⟨ζ, hζ⟩ := mem_statedScalars_of_commute hπ hq' hτ hτ1 hcL
  have hcH : c ∈ glPi π 3 (p ^ f) K :=
    mul_mem (mul_mem hg (frobGL_mem_glPi hK φ hg))
      (frobGL_mem_glPi hK φ (frobGL_mem_glPi hK φ hg))
  have hζT : ζ ∈ rootsOfUnity (qSubPi π (p ^ f)) K :=
    (scalar_mem_glPi_iff hK ζ).mp (hζ ▸ hcH)
  have hΦc : frobGL φ c = c := by
    have h1 : frobGL φ c = g⁻¹ * c * g := by
      rw [hc, map_mul, map_mul, hΦ3]
      group
    rw [h1, ← hζ, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g⁻¹).eq,
      inv_mul_cancel_right]
  have hφζ : (ζ : K) ^ piCard π (p ^ f₀) = ζ := by
    rw [← hφ]
    have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hΦc
    rw [← hζ, frobGL_scalar] at h1
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h1
  set q₀ := p ^ f₀ with hq₀def
  have hqq : p ^ f = q₀ ^ 3 := by rw [hf, pow_mul']
  have hq₀1 : 1 ≤ q₀ := Nat.one_le_pow _ _ hK.prime.pos
  have hq₀ : ModThree π q₀ := modThree_of_cube (hqq ▸ hq)
  set M := 3 * (3 * (q₀ / 3) ^ 2 + 3 * (q₀ / 3) + 1) with hMdef
  have hNM : qSubPi π (p ^ f) = qSubPi π q₀ * M := by rw [hqq, qSubPi_cube_eq hq₀]
  have hN0 : qSubPi π (p ^ f) ≠ 0 := qSubPi_ne_zero hK hq
  have hζ0 : qSubPi π q₀ ≠ 0 := fun h0 => hN0 (by rw [hNM, h0, zero_mul])
  have hM0 : 0 < M := by omega
  have hζq₀ : (ζ : K) ^ qSubPi π q₀ = 1 := by
    have hζN := congrArg Units.val ((mem_rootsOfUnity _ _).mp hζT)
    rw [Units.val_pow_eq_pow_val, Units.val_one, hqq] at hζN
    exact pow_qSubPi_eq_one_of_fixed hq₀1 ζ.ne_zero hφζ hζN
  have : NeZero (qSubPi π (p ^ f)) := ⟨hN0⟩
  have := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
  have hTcard := card_rootsOfUnity_qSubPi hK hq
  set t : rootsOfUnity (qSubPi π (p ^ f)) K := ⟨ζ⁻¹, inv_mem hζT⟩ with htdef
  have hexp : Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / M = qSubPi π q₀ := by
    rw [hTcard, hNM, Nat.mul_div_cancel _ hM0]
  have ht : t ^ (Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / M) = 1 := by
    rw [hexp]
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    change ζ⁻¹ ^ qSubPi π q₀ = 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow, hζq₀, inv_one,
      Units.val_one]
  obtain ⟨s, hs⟩ := exists_pow_eq_of_pow_div (by rw [hTcard, hNM]; exact dvd_mul_left M _) ht
  refine ⟨s, s.2, ?_⟩
  have hsM : ((s : Kˣ) : K) ^ M = (ζ : K)⁻¹ := by
    have := congrArg (fun u : rootsOfUnity (qSubPi π (p ^ f)) K => ((u : Kˣ) : K)) hs
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val] at this
    rw [this, htdef, Units.val_inv_eq_inv_val]
  have hsN : ((s : Kˣ) : K) ^ qSubPi π (p ^ f) = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).mp s.2)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hnorm : ((s : Kˣ) : K) * φ (s : Kˣ) * φ (φ (s : Kˣ)) = (ζ : K)⁻¹ := by
    obtain ⟨j, hj⟩ := norm_exponent hq₀
    rw [hφ (φ _), hφ]
    calc ((s : Kˣ) : K) * ((s : Kˣ) : K) ^ piCard π q₀ *
          (((s : Kˣ) : K) ^ piCard π q₀) ^ piCard π q₀ =
        ((s : Kˣ) : K) ^ (1 + piCard π q₀ + piCard π q₀ ^ 2) := by ring
      _ = ((s : Kˣ) : K) ^ M * (((s : Kˣ) : K) ^ qSubPi π (p ^ f)) ^ j := by
          rw [hj, ← hqq, pow_add, pow_mul, mul_comm j]
          ring
      _ = (ζ : K)⁻¹ := by rw [hsM, hsN, one_pow, mul_one]
  have hcM : (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map φ *
      ((g : Matrix (Fin 3) (Fin 3) K).map φ).map φ = (ζ : K) • 1 := by
    have := congrArg Units.val hζ
    rw [hc, Units.val_mul, Units.val_mul, coe_frobGL, coe_frobGL, coe_frobGL] at this
    rw [← this, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hgs : ((g * GeneralLinearGroup.scalar (Fin 3) (s : Kˣ) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((s : Kˣ) : K) • (g : Matrix (Fin 3) (Fin 3) K) := by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_frobGL, coe_frobGL, coe_frobGL, hgs,
    Matrix.map_smul' _ _ _ (fun x y => map_mul φ x y),
    Matrix.map_smul' _ _ _ (fun x y => map_mul φ x y)]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hcM, smul_smul, Units.val_one]
  have hinv : (ζ : K)⁻¹ * ζ = 1 := inv_mul_cancel₀ ζ.ne_zero
  convert one_smul K (1 : Matrix (Fin 3) (Fin 3) K) using 2
  linear_combination (ζ : K) * hnorm + hinv

@[expose] def frobVec (φ : K ≃+* K) (v : Fin 3 → K) : Fin 3 → K := fun i => φ (v i)

theorem frobVec_mulVec (φ : K ≃+* K) (M : Matrix (Fin 3) (Fin 3) K) (v : Fin 3 → K) :
    frobVec φ (M *ᵥ v) = M.map φ *ᵥ frobVec φ v := by
  funext i
  exact RingHom.map_mulVec (φ : K →+* K) M v i

theorem frobVec_three {φ : K ≃+* K} (hφ3 : orderOf φ = 3) (v : Fin 3 → K) :
    frobVec φ (frobVec φ (frobVec φ v)) = v := by
  funext i
  exact ringAut_apply_three hφ3 (v i)

theorem exists_lang (hK : PiField π p f K) {φ : K ≃+* K} (hφ3 : orderOf φ = 3)
    {g : GL (Fin 3) K} (hg : g * frobGL φ g * frobGL φ (frobGL φ g) = 1) :
    ∃ h : GL (Fin 3) K, g * frobGL φ h = h := by
  have := hK.finite
  obtain ⟨n, hn1, hKn⟩ : ∃ n, 1 ≤ n ∧ Nat.card K = p ^ n := by
    cases π
    · refine ⟨2 * f, by have := hK.one_le; omega, ?_⟩
      rw [hK.card]
      change (p ^ f) ^ 2 = _
      ring
    · exact ⟨f, hK.one_le, hK.card⟩
  set G := (g : Matrix (Fin 3) (Fin 3) K) with hGdef
  set Gi := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hGidef
  have hGGi : G * Gi = 1 := by rw [hGdef, hGidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hGdef, hGidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let a : (Fin 3 → K) ≃+ (Fin 3 → K) :=
    { toFun := fun v => G *ᵥ frobVec φ v
      invFun := fun w => frobVec φ.symm (Gi *ᵥ w)
      left_inv := fun v => by
        change frobVec φ.symm (Gi *ᵥ (G *ᵥ frobVec φ v)) = v
        rw [Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec]
        funext i
        exact φ.symm_apply_apply (v i)
      right_inv := fun w => by
        change G *ᵥ frobVec φ (frobVec φ.symm (Gi *ᵥ w)) = w
        have h1 : frobVec φ (frobVec φ.symm (Gi *ᵥ w)) = Gi *ᵥ w := by
          funext i
          exact φ.apply_symm_apply _
        rw [h1, Matrix.mulVec_mulVec, hGGi, Matrix.one_mulVec]
      map_add' := fun v w => by
        rw [← Matrix.mulVec_add]
        congr 1
        funext i
        exact map_add φ (v i) (w i) }
  have ha : ∀ (c : K) (v : Fin 3 → K), a (c • v) = φ c • a v := by
    intro c v
    change G *ᵥ frobVec φ (c • v) = φ c • (G *ᵥ frobVec φ v)
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    exact map_mul φ c (v i)
  have hgm : G * G.map φ * (G.map φ).map φ = 1 := by
    have := congrArg Units.val hg
    rwa [Units.val_mul, Units.val_mul, coe_frobGL, coe_frobGL, coe_frobGL, Units.val_one]
      at this
  have hah : ∀ v, (⇑a)^[3] v = v := by
    intro v
    change G *ᵥ frobVec φ (G *ᵥ frobVec φ (G *ᵥ frobVec φ v)) = v
    rw [frobVec_mulVec, frobVec_mulVec, frobVec_mulVec, frobVec_three hφ3,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgm, Matrix.one_mulVec]
  obtain ⟨-, -, -, -, b, hb, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis hK.prime hn1 hKn φ hφ3
      (Module.finrank_fin_fun K) a ha hah
  have hP : IsUnit (colMat fun i => b i) := isUnit_colMat b.linearIndependent
  refine ⟨hP.unit, Units.ext ?_⟩
  rw [Units.val_mul, coe_frobGL, IsUnit.unit_spec]
  have hmap : (colMat fun i => b i).map φ = colMat fun i => frobVec φ (b i) := by
    ext r j
    rfl
  rw [hmap]
  ext r j
  rw [mul_colMat_apply]
  exact congrFun (hb j) r

theorem exists_lang_unitary (hK : PiField false p f K) {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard false (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {g : GL (Fin 3) K} (hgH : g ∈ glPi false 3 (p ^ f) K) {h : GL (Fin 3) K}
    (hgh : g * frobGL φ h = h) :
    ∃ h' ∈ glPi false 3 (p ^ f) K, g * frobGL φ h' = h' := by
  have hU := hK.unitary
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.charP
  obtain ⟨K₀, hK₀, hK₀card⟩ := exists_fixedField hK hf hφ3
  have hK₀card' : Nat.card K₀ = (p ^ f₀) ^ 2 := hK₀card
  have hbar0 : ∀ c ∈ K₀, hU.bar c = c ^ p ^ f₀ := by
    intro c hc
    have h2 : c ^ (p ^ f₀) ^ 2 = c := by
      have := (hK₀ c).mp hc
      rwa [hφ] at this
    rw [hU.bar_apply, hf, pow_mul', show (p ^ f₀) ^ 3 = (p ^ f₀) ^ 2 * p ^ f₀ by ring, pow_mul,
      h2]
  have hφbar : ∀ c, φ (hU.bar c) = hU.bar (φ c) := fun c => by
    rw [hU.bar_apply, hU.bar_apply, map_pow]
  obtain ⟨Gram, hGram⟩ : ∃ G : Matrix (Fin 3) (Fin 3) K,
      G = ((h : Matrix (Fin 3) (Fin 3) K).map hU.bar)ᵀ * (h : Matrix (Fin 3) (Fin 3) K) :=
    ⟨_, rfl⟩
  have hhφ : (h : Matrix (Fin 3) (Fin 3) K).map φ =
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg Units.val hgh
    rw [Units.val_mul, coe_frobGL] at this
    calc (h : Matrix (Fin 3) (Fin 3) K).map φ =
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K).map φ) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      _ = _ := by rw [this]
  have hginv : ((((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map hU.bar)ᵀ *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
    (mem_glPi_false hU).mp (inv_mem hgH)
  have hGramφ : Gram.map φ = Gram := by
    have hc : ((h : Matrix (Fin 3) (Fin 3) K).map hU.bar).map φ =
        ((h : Matrix (Fin 3) (Fin 3) K).map φ).map hU.bar := by
      ext i j
      simp only [Matrix.map_apply, hφbar]
    rw [hGram, Matrix.map_mul, Matrix.transpose_map, hc, hhφ, Matrix.map_mul,
      Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (h : Matrix (Fin 3) (Fin 3) K),
      hginv, Matrix.one_mul]
  have hGramh : (Gram.map hU.bar)ᵀ = Gram := by
    rw [hGram, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.map_map,
      show ⇑hU.bar ∘ ⇑hU.bar = id from funext hU.bar_bar, Matrix.map_id]
  have hGramdet : Gram.det ≠ 0 := by
    rw [hGram, det_mul, det_transpose, show ((h : Matrix (Fin 3) (Fin 3) K).map hU.bar).det =
      hU.bar (h : Matrix (Fin 3) (Fin 3) K).det from (RingHom.map_det hU.bar _).symm]
    have hd : (h : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
    exact mul_ne_zero ((map_ne_zero hU.bar).mpr hd) hd
  have hGram0 : ∀ i j, Gram i j ∈ K₀ := fun i j =>
    (hK₀ _).mpr (congrFun (congrFun hGramφ i) j)
  let G₀ : Matrix (Fin 3) (Fin 3) K₀ := Matrix.of fun i j => ⟨Gram i j, hGram0 i j⟩
  have hG₀ : G₀.map K₀.subtype = Gram := by
    ext i j
    rfl
  have : Finite K₀ := Subtype.finite
  have : CharP K₀ p := inferInstance
  set σ₀ := CFSG.LieType.BorelTits.unitaryInvolution K₀ p f₀ with hσ₀def
  have hσ₀ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ₀ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK₀card'
  have hσ₀apply : ∀ c : K₀, ((σ₀ c : K₀) : K) = hU.bar c := fun c => by
    rw [hσ₀def, CFSG.LieType.BorelTits.unitaryInvolution_apply, hbar0 c c.2]
    rfl
  have hG₀h : CFSG.LieType.Universal.Unitary.conjTr σ₀ G₀ = G₀ := by
    ext i j
    rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.transpose_apply, Matrix.map_apply,
      hσ₀apply]
    exact congrFun (congrFun hGramh i) j
  have hG₀det : G₀.det ≠ 0 := by
    intro h0
    apply hGramdet
    rw [← hG₀, show (G₀.map K₀.subtype).det = K₀.subtype G₀.det from
      (RingHom.map_det K₀.subtype G₀).symm, h0, map_zero]
  obtain ⟨P₀, hP₀⟩ :=
    CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution hσ₀
      hG₀h hG₀det
  set P : GL (Fin 3) K := Units.map K₀.subtype.mapMatrix.toMonoidHom P₀ with hPdef
  have hPm : (P : Matrix (Fin 3) (Fin 3) K) = (P₀ : Matrix (Fin 3) (Fin 3) K₀).map K₀.subtype :=
    rfl
  refine ⟨h * P, ?_, ?_⟩
  · rw [mem_glPi_false hU, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, hPm]
    have hPbar : (((P₀ : Matrix (Fin 3) (Fin 3) K₀).map K₀.subtype).map hU.bar)ᵀ =
        (CFSG.LieType.Universal.Unitary.conjTr σ₀ (P₀ : Matrix (Fin 3) (Fin 3) K₀)).map
          K₀.subtype := by
      ext i j
      rw [CFSG.LieType.Universal.Unitary.conjTr]
      simp only [Matrix.transpose_apply, Matrix.map_apply, Subfield.coe_subtype]
      exact (hσ₀apply _).symm
    rw [hPbar, Matrix.mul_assoc, ← Matrix.mul_assoc ((h : Matrix (Fin 3) (Fin 3) K).map hU.bar)ᵀ,
      ← hGram, ← hG₀, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, hP₀,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · have hΦP : frobGL φ P = P := by
      apply Units.ext
      rw [coe_frobGL, hPm]
      ext i j
      exact (hK₀ _).mp (P₀ i j).2
    rw [map_mul, hΦP, ← mul_assoc, hgh]

theorem exists_lang_glPi (hK : PiField π p f K) {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {g : GL (Fin 3) K} (hgH : g ∈ glPi π 3 (p ^ f) K)
    (hg : g * frobGL φ g * frobGL φ (frobGL φ g) = 1) :
    ∃ h ∈ glPi π 3 (p ^ f) K, g * frobGL φ h = h := by
  obtain ⟨h₀, hh₀⟩ := exists_lang hK hφ3 hg
  cases π
  · exact exists_lang_unitary hK hf hφ hφ3 hgH hh₀
  · exact ⟨h₀, mem_glPi_true _ _, hh₀⟩

theorem exists_embedding_fixedIn (hK : PiField π p f K) {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    (K₀ : Type) [Field K₀] (hK₀ : PiField π p f₀ K₀) :
    ∃ ι : GL (Fin 3) K₀ →* GL (Fin 3) K, Function.Injective ι ∧
      (glPi π 3 (p ^ f₀) K₀).map ι = fixedIn (glPi π 3 (p ^ f) K) (frobGL φ) ∧
      (slPi π 3 (p ^ f₀) K₀).map ι = fixedIn (slPi π 3 (p ^ f) K) (frobGL φ) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hπ₀ : π = false → UnitaryFieldData p f₀ K₀ := fun h => by subst h; exact hK₀.unitary
  have := hK.finite
  have := hK₀.finite
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K₀
  obtain ⟨S, hS, hScard⟩ := exists_fixedField hK hf hφ3
  have : Fintype S := Fintype.ofFinite S
  have hcard : Fintype.card K₀ = Fintype.card S := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀.card, hScard]
  let e : K₀ ≃+* S := FiniteField.ringEquivOfCardEq hcard
  let j : K₀ →+* K := S.subtype.comp e.toRingHom
  have hjS : ∀ c, j c ∈ S := fun c => (e c).2
  have hjinj : Function.Injective j := fun a b hab => e.injective (Subtype.ext hab)
  have hjφ : ∀ c, φ (j c) = j c := fun c => (hS _).mp (hjS c)
  have hje : ∀ (x : K) (hx : x ∈ S), j (e.symm ⟨x, hx⟩) = x := fun x hx => by
    change ((e (e.symm ⟨x, hx⟩) : S) : K) = x
    rw [RingEquiv.apply_symm_apply]
  let ι : GL (Fin 3) K₀ →* GL (Fin 3) K := Units.map j.mapMatrix.toMonoidHom
  have hι : ∀ B : GL (Fin 3) K₀, ((ι B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K₀).map j := fun B => rfl
  have hιinj : Function.Injective ι := by
    intro B B' hBB'
    apply Units.ext
    apply Matrix.map_injective hjinj
    change ((ι B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((ι B' : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)
    rw [hBB']
  have hιfix : ∀ B, frobGL φ (ι B) = ι B := by
    intro B
    apply Units.ext
    rw [coe_frobGL, hι]
    ext i k
    exact hjφ _
  have hιH : ∀ B : GL (Fin 3) K₀, ι B ∈ glPi π 3 (p ^ f) K ↔ B ∈ glPi π 3 (p ^ f₀) K₀ := by
    intro B
    cases π
    · have hU := hK.unitary
      have hU₀ := hK₀.unitary
      rw [mem_glPi_false hU, mem_glPi_false hU₀, hι]
      have hbj : ∀ c, hU.bar (j c) = j (hU₀.bar c) := by
        intro c
        have h2 : (j c) ^ (p ^ f₀) ^ 2 = j c := by
          have := hjφ c
          rwa [hφ] at this
        rw [hU.bar_apply, hU₀.bar_apply, map_pow, hf, pow_mul',
          show (p ^ f₀) ^ 3 = (p ^ f₀) ^ 2 * p ^ f₀ by ring, pow_mul, h2]
      have hmap : ((B : Matrix (Fin 3) (Fin 3) K₀).map j).map hU.bar =
          ((B : Matrix (Fin 3) (Fin 3) K₀).map hU₀.bar).map j := by
        ext i k
        exact hbj _
      rw [hmap, ← Matrix.transpose_map, ← Matrix.map_mul]
      constructor
      · intro h1
        exact Matrix.map_injective hjinj (h1.trans (Matrix.map_one _ (map_zero j) (map_one j)).symm)
      · intro h1
        rw [h1, Matrix.map_one _ (map_zero j) (map_one j)]
    · exact ⟨fun _ => mem_glPi_true _ _, fun _ => mem_glPi_true _ _⟩
  have hιL : ∀ B : GL (Fin 3) K₀, ι B ∈ slPi π 3 (p ^ f) K ↔ B ∈ slPi π 3 (p ^ f₀) K₀ := by
    intro B
    rw [mem_slPi_iff hπ, mem_slPi_iff hπ₀, hιH, hι,
      show ((B : Matrix (Fin 3) (Fin 3) K₀).map j).det = j (B : Matrix (Fin 3) (Fin 3) K₀).det
        from (RingHom.map_det j _).symm]
    refine and_congr_right fun _ => ⟨fun h1 => hjinj (by rw [h1, map_one]), fun h1 => ?_⟩
    rw [h1, map_one]
  have hent : ∀ A : GL (Fin 3) K, frobGL φ A = A → ∀ i k,
      (A : Matrix (Fin 3) (Fin 3) K) i k ∈ S := by
    intro A hA i k
    apply (hS _).mpr
    have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) i k) hA
    simpa [coe_frobGL] using this
  have hsurj : ∀ A : GL (Fin 3) K, frobGL φ A = A → ∃ B, ι B = A := by
    intro A hA
    have hAinv : frobGL φ A⁻¹ = A⁻¹ := by rw [map_inv, hA]
    let pre : ∀ A : GL (Fin 3) K, frobGL φ A = A → Matrix (Fin 3) (Fin 3) K₀ :=
      fun A hA => Matrix.of fun i k => e.symm ⟨(A : Matrix (Fin 3) (Fin 3) K) i k, hent A hA i k⟩
    have hpre : ∀ A hA, (pre A hA).map j = (A : Matrix (Fin 3) (Fin 3) K) := by
      intro A hA
      ext i k
      exact hje _ _
    refine ⟨⟨pre A hA, pre A⁻¹ hAinv, ?_, ?_⟩, ?_⟩
    · apply Matrix.map_injective hjinj
      change (pre A hA * pre A⁻¹ hAinv).map j = (1 : Matrix (Fin 3) (Fin 3) K₀).map j
      rw [Matrix.map_mul, hpre A hA, hpre A⁻¹ hAinv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero j) (map_one j)]
    · apply Matrix.map_injective hjinj
      change (pre A⁻¹ hAinv * pre A hA).map j = (1 : Matrix (Fin 3) (Fin 3) K₀).map j
      rw [Matrix.map_mul, hpre A⁻¹ hAinv, hpre A hA, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero j) (map_one j)]
    · apply Units.ext
      exact hpre A hA
  have key : ∀ (X₀ : Subgroup (GL (Fin 3) K₀)) (X : Subgroup (GL (Fin 3) K)),
      (∀ B, ι B ∈ X ↔ B ∈ X₀) → X₀.map ι = fixedIn X (frobGL φ) := by
    intro X₀ X hX
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ⟨(hX B).mpr hB, hιfix B⟩
    · rintro ⟨hAX, hAφ⟩
      obtain ⟨B, rfl⟩ := hsurj A hAφ
      exact ⟨B, (hX B).mp hAX, rfl⟩
  exact ⟨ι, hιinj, key _ _ hιH, key _ _ hιL⟩

theorem map_conj_self {X : Subgroup (GL (Fin 3) K)} {h : GL (Fin 3) K} (hh : h ∈ X) :
    X.map (MulAut.conj h).toMonoidHom = X := by
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    exact mul_mem (mul_mem hh hA) (inv_mem hh)
  · intro A hA
    refine ⟨h⁻¹ * A * h, mul_mem (mul_mem (inv_mem hh) hA) hh, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem fixedIn_conj {σ Φ : GL (Fin 3) K →* GL (Fin 3) K} {h : GL (Fin 3) K}
    (hσ : ∀ A, σ A = h * Φ (h⁻¹ * A * h) * h⁻¹) {X : Subgroup (GL (Fin 3) K)}
    (hX : X.map (MulAut.conj h).toMonoidHom = X) :
    fixedIn X σ = (fixedIn X Φ).map (MulAut.conj h).toMonoidHom := by
  ext A
  constructor
  · rintro ⟨hAX, hσA⟩
    change σ A = A at hσA
    refine ⟨h⁻¹ * A * h, ⟨?_, ?_⟩, ?_⟩
    · rw [← hX] at hAX
      obtain ⟨B, hB, hBA⟩ := hAX
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hBA
      rw [← hBA]
      convert hB using 1
      group
    · change Φ (h⁻¹ * A * h) = h⁻¹ * A * h
      rw [hσ] at hσA
      calc Φ (h⁻¹ * A * h) = h⁻¹ * (h * Φ (h⁻¹ * A * h) * h⁻¹) * h := by group
        _ = h⁻¹ * A * h := by rw [hσA]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨B, ⟨hBX, hΦB⟩, rfl⟩
    change Φ B = B at hΦB
    refine ⟨?_, ?_⟩
    · rw [← hX]
      exact ⟨B, hBX, rfl⟩
    · change σ (h * B * h⁻¹) = h * B * h⁻¹
      rw [hσ]
      have : h⁻¹ * (h * B * h⁻¹) * h = B := by group
      rw [this, hΦB]

theorem rank3II_4_10_four (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (σ : GL (Fin 3) K →* GL (Fin 3) K)
    (hσ : ∀ A : GL (Fin 3) K, (σ A : Matrix (Fin 3) (Fin 3) K) =
      g * (A : Matrix (Fin 3) (Fin 3) K).map (· ^ piCard π (p ^ f₀)) * (g⁻¹ : GL (Fin 3) K))
    (hσ3 : ∀ A ∈ slPi π 3 (p ^ f) K, σ (σ (σ A)) = A)
    (K₀ : Type) [Field K₀] (hK₀ : PiField π p f₀ K₀) :
    Nonempty (↥(fixedIn (glPi π 3 (p ^ f) K) σ) ≃* ↥(glPi π 3 (p ^ f₀) K₀)) ∧
      (∀ A ∈ fixedIn (glPi π 3 (p ^ f) K) σ, ∃ l ∈ slPi π 3 (p ^ f) K,
        ∀ m ∈ slPi π 3 (p ^ f) K, A * m * A⁻¹ = l * m * l⁻¹) ∧
      Nonempty (↥(fixedIn (slPi π 3 (p ^ f) K) σ) ≃* ↥(slPi π 3 (p ^ f₀) K₀)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  have hσΦ : ∀ A, σ A = g * frobGL φ A * g⁻¹ := by
    intro A
    apply Units.ext
    rw [hσ, Units.val_mul, Units.val_mul, coe_frobGL]
    congr 2
    ext i k
    exact (hφ _).symm
  have hσ3' : ∀ A ∈ slPi π 3 (p ^ f) K,
      g * frobGL φ (g * frobGL φ (g * frobGL φ A * g⁻¹) * g⁻¹) * g⁻¹ = A := by
    intro A hA
    have := hσ3 A hA
    rwa [hσΦ, hσΦ, hσΦ] at this
  obtain ⟨s, hsT, hcoc⟩ := exists_cocycle_eq_one hK hq hf hφ hφ3 hg hσ3'
  have hg₁H : g * GeneralLinearGroup.scalar (Fin 3) s ∈ glPi π 3 (p ^ f) K :=
    mul_mem hg ((scalar_mem_glPi_iff hK s).mpr hsT)
  obtain ⟨h, hhH, hgh⟩ := exists_lang_glPi hK hf hφ hφ3 hg₁H hcoc
  have hσh : ∀ A, σ A = h * frobGL φ (h⁻¹ * A * h) * h⁻¹ := by
    intro A
    have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s (frobGL φ A)).eq
    have hg₁ : g * GeneralLinearGroup.scalar (Fin 3) s = h * (frobGL φ h)⁻¹ := by
      calc g * GeneralLinearGroup.scalar (Fin 3) s =
          g * GeneralLinearGroup.scalar (Fin 3) s * frobGL φ h * (frobGL φ h)⁻¹ := by group
        _ = h * (frobGL φ h)⁻¹ := by rw [hgh]
    calc σ A = g * frobGL φ A * g⁻¹ := hσΦ A
      _ = g * (frobGL φ A * GeneralLinearGroup.scalar (Fin 3) s) *
          (GeneralLinearGroup.scalar (Fin 3) s)⁻¹ * g⁻¹ := by group
      _ = (g * GeneralLinearGroup.scalar (Fin 3) s) * frobGL φ A *
          (g * GeneralLinearGroup.scalar (Fin 3) s)⁻¹ := by rw [hc]; group
      _ = h * frobGL φ (h⁻¹ * A * h) * h⁻¹ := by
          rw [hg₁, map_mul, map_mul, map_inv]
          group
  have hFH := fixedIn_conj hσh (map_conj_self hhH)
  have hFL := fixedIn_conj hσh (map_conj_slPi hπ hhH)
  obtain ⟨ι, hιinj, hιH, hιL⟩ := exists_embedding_fixedIn hK hf hφ hφ3 K₀ hK₀
  refine ⟨?_, ?_, ?_⟩
  · rw [hFH, ← hιH]
    exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj h).injective).symm.trans
      (Subgroup.equivMapOfInjective _ _ hιinj).symm⟩
  · rintro A ⟨hAH, hσA⟩
    change σ A = A at hσA
    have hdetφ : φ (A : Matrix (Fin 3) (Fin 3) K).det = (A : Matrix (Fin 3) (Fin 3) K).det := by
      have h1 := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K).det) hσA
      rw [hσΦ, Units.val_mul, Units.val_mul, det_mul, det_mul, frobGL_det] at h1
      have hg1 : (g : Matrix (Fin 3) (Fin 3) K).det *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
        rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
      linear_combination h1 - φ (A : Matrix (Fin 3) (Fin 3) K).det * hg1
    set q₀ := p ^ f₀ with hq₀def
    have hqq : p ^ f = q₀ ^ 3 := by rw [hf, pow_mul']
    have hq₀1 : 1 ≤ q₀ := Nat.one_le_pow _ _ hK.prime.pos
    have hq₀ : ModThree π q₀ := modThree_of_cube (hqq ▸ hq)
    have hdetT := det_mem_rootsOfUnity hK hAH
    have hdetN : (A : Matrix (Fin 3) (Fin 3) K).det ^ qSubPi π (q₀ ^ 3) = 1 := by
      have := congrArg Units.val ((mem_rootsOfUnity _ _).mp hdetT)
      rwa [Units.val_pow_eq_pow_val, Units.val_one, GeneralLinearGroup.val_det_apply, hqq] at this
    have hdet0 : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
    have hdetq₀ := pow_qSubPi_eq_one_of_fixed hq₀1 hdet0 (by rw [← hφ]; exact hdetφ) hdetN
    have hN0 : qSubPi π (p ^ f) ≠ 0 := qSubPi_ne_zero hK hq
    have : NeZero (qSubPi π (p ^ f)) := ⟨hN0⟩
    have := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
    have hTcard := card_rootsOfUnity_qSubPi hK hq
    set t : rootsOfUnity (qSubPi π (p ^ f)) K := ⟨GeneralLinearGroup.det A, hdetT⟩ with htdef
    have hexp : Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / 3 =
        qSubPi π q₀ * (3 * (q₀ / 3) ^ 2 + 3 * (q₀ / 3) + 1) := by
      rw [hTcard, hqq, qSubPi_cube_eq hq₀, ← mul_assoc, mul_comm (qSubPi π q₀) 3, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
    have ht : t ^ (Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / 3) = 1 := by
      rw [hexp, pow_mul]
      have : t ^ qSubPi π q₀ = 1 := by
        apply Subtype.ext
        apply Units.ext
        simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
          Units.val_one]
        change (GeneralLinearGroup.det A : K) ^ qSubPi π q₀ = 1
        rw [GeneralLinearGroup.val_det_apply]
        exact hdetq₀
      rw [this, one_pow]
    obtain ⟨ξ, hξ⟩ := exists_pow_three_eq (by rw [hTcard]; exact three_dvd_qSubPi hq) ht
    have hξ3 : ((ξ : Kˣ) : K) ^ 3 = (A : Matrix (Fin 3) (Fin 3) K).det := by
      have := congrArg (fun u : rootsOfUnity (qSubPi π (p ^ f)) K => ((u : Kˣ) : K)) hξ
      simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val] at this
      rw [this, htdef]
      rfl
    have hξZ := scalar_mem_zPi hK hq hτ hτ1 ξ.2
    have hξH : GeneralLinearGroup.scalar (Fin 3) (ξ : Kˣ) ∈ glPi π 3 (p ^ f) K :=
      (scalar_mem_glPi_iff hK _).mpr ξ.2
    rw [inducesInner_iff hπ hq' hτ hτ1 hAH]
    refine ⟨A * (GeneralLinearGroup.scalar (Fin 3) (ξ : Kˣ))⁻¹, ?_,
      GeneralLinearGroup.scalar (Fin 3) (ξ : Kˣ), hξZ, by group⟩
    rw [mem_slPi_iff hπ]
    refine ⟨mul_mem hAH (inv_mem hξH), ?_⟩
    rw [Units.val_mul, det_mul, ← map_inv, det_scalar, Units.val_inv_eq_inv_val, inv_pow, hξ3,
      mul_inv_cancel₀ hdet0]
  · rw [hFL, ← hιL]
    exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj h).injective).symm.trans
      (Subgroup.equivMapOfInjective _ _ hιinj).symm⟩

end CFSG.RankThree.PartTwo.Sec4
