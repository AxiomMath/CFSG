module

public import CFSG.Monster.CodeLattice
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.Monster

open Module

variable {C : Submodule (ZMod 2) (Fin 24 → ZMod 2)}

theorem dotProductBilin_nondegenerate :
    (dotProductBilin (ZMod 2) (ZMod 2) :
      LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · funext i
    have := hx (Pi.single i 1)
    simpa [dotProductBilin_apply_apply, dotProduct_single] using this
  · funext i
    have := hx (Pi.single i 1)
    simpa [dotProductBilin_apply_apply, single_dotProduct] using this

theorem finrank_eq_twelve_of_selfDual (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) :
    finrank (ZMod 2) C = 12 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2) := dotProductBilin (ZMod 2) (ZMod 2)
  have horth : B.orthogonal C = C := by
    ext x
    rw [LinearMap.BilinForm.mem_orthogonal_iff, hdual x]
    refine forall₂_congr fun y _ => ?_
    simp [B, dotProductBilin_apply_apply, dotProduct_comm]
  have h := LinearMap.BilinForm.finrank_orthogonal dotProductBilin_nondegenerate C
  rw [horth, finrank_fin_fun] at h
  have hle : finrank (ZMod 2) C ≤ 24 := by
    have := Submodule.finrank_le C
    rwa [finrank_fin_fun] at this
  omega

theorem card_eq_of_selfDual (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) :
    Nat.card C = 2 ^ 12 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← FiniteField.pow_finrank_eq_natCard 2 C, finrank_eq_twelve_of_selfDual hdual]

@[expose] def lift4 (t : ZMod 2) : ZMod 4 := (t.val : ZMod 4)

@[expose] def resid4 (m : ZMod 2) (d : Fin 24 → ZMod 2) : Fin 24 → ZMod 4 :=
  fun i => lift4 m + 2 * lift4 (d i)

theorem resid4_add (m m' : ZMod 2) (d d' : Fin 24 → ZMod 2) :
    resid4 m d + resid4 m' d' = resid4 (m + m') (d + d' + (m * m') • allOnes) := by
  funext i
  simp only [resid4, Pi.add_apply, Pi.smul_apply, smul_eq_mul, allOnes, mul_one]
  generalize d i = a
  generalize d' i = b
  revert m m' a b
  decide

theorem resid4_neg (m : ZMod 2) (d : Fin 24 → ZMod 2) :
    -resid4 m d = resid4 m (d + m • allOnes) := by
  funext i
  simp only [resid4, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, allOnes, mul_one]
  generalize d i = a
  revert m a
  decide

theorem resid4_inj {m m' : ZMod 2} {d d' : Fin 24 → ZMod 2} (h : resid4 m d = resid4 m' d') :
    m = m' ∧ d = d' := by
  have key : ∀ m m' a b : ZMod 2, lift4 m + 2 * lift4 a = lift4 m' + 2 * lift4 b →
      m = m' ∧ a = b := by decide
  refine ⟨(key m m' (d 0) (d' 0) (congrFun h 0)).1, funext fun i => ?_⟩
  exact (key m m' (d i) (d' i) (congrFun h i)).2

variable (C) in
@[expose] def resid4Subgroup (hΩ : allOnes ∈ C) : AddSubgroup (Fin 24 → ZMod 4) where
  carrier := {x | ∃ m : ZMod 2, ∃ d ∈ C, x = resid4 m d}
  zero_mem' := ⟨0, 0, C.zero_mem, by funext i; simp [resid4, lift4]⟩
  add_mem' := by
    rintro _ _ ⟨m, d, hd, rfl⟩ ⟨m', d', hd', rfl⟩
    exact ⟨m + m', _, C.add_mem (C.add_mem hd hd') (C.smul_mem _ hΩ), resid4_add m m' d d'⟩
  neg_mem' := by
    rintro _ ⟨m, d, hd, rfl⟩
    exact ⟨m, _, C.add_mem hd (C.smul_mem _ hΩ), resid4_neg m d⟩

theorem card_resid4Subgroup (hΩ : allOnes ∈ C) (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) :
    Nat.card (resid4Subgroup C hΩ) = 2 ^ 13 := by
  let f : ZMod 2 × C → resid4Subgroup C hΩ := fun p => ⟨resid4 p.1 p.2, p.1, p.2, p.2.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, ?_⟩
    · have h' := resid4_inj (congrArg Subtype.val h)
      exact Prod.ext h'.1 (Subtype.ext h'.2)
    · rintro ⟨_, m, d, hd, rfl⟩
      exact ⟨(m, ⟨d, hd⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_zmod,
    card_eq_of_selfDual hdual]
  norm_num

@[expose] def red4 : (Fin 24 → ℤ) →+ (Fin 24 → ZMod 4) :=
  (Int.castAddHom (ZMod 4)).compLeft (Fin 24)

theorem red4_apply (u : Fin 24 → ℤ) (i : Fin 24) : red4 u i = (u i : ZMod 4) := rfl

theorem red4_surjective : Function.Surjective red4 := by
  intro x
  refine ⟨fun i => (x i).val, funext fun i => ?_⟩
  simp [red4_apply]

variable (C) in
@[expose] def codeLatticeMod4 (hΩ : allOnes ∈ C) : AddSubgroup (Fin 24 → ℤ) :=
  (resid4Subgroup C hΩ).comap red4

theorem index_codeLatticeMod4 (hΩ : allOnes ∈ C) (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) :
    (codeLatticeMod4 C hΩ).index = 2 ^ 35 := by
  rw [codeLatticeMod4, AddSubgroup.index_comap_of_surjective _ red4_surjective]
  have h := (resid4Subgroup C hΩ).index_mul_card
  rw [card_resid4Subgroup hΩ hdual, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  have h' : (resid4Subgroup C hΩ).index * 2 ^ 13 = 2 ^ 35 * 2 ^ 13 := by rw [h]; norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem lift4_eq_cast_bitLift (t : ZMod 2) : lift4 t = ((bitLift t : ℤ) : ZMod 4) := by
  fin_cases t <;> rfl

theorem mem_codeLatticeMod4_iff (hΩ : allOnes ∈ C) (u : Fin 24 → ℤ) :
    u ∈ codeLatticeMod4 C hΩ ↔
      ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ d ∈ C, ∀ i, u i ≡ m + 2 * bitLift (d i) [ZMOD 4] := by
  constructor
  · rintro ⟨m, d, hd, h⟩
    refine ⟨bitLift m, bitLift_zero_or_one m, d, hd, fun i => ?_⟩
    have hi : (u i : ZMod 4) = ((bitLift m + 2 * bitLift (d i) : ℤ) : ZMod 4) := by
      have := congrFun h i
      rw [red4_apply] at this
      rw [this, resid4, lift4_eq_cast_bitLift, lift4_eq_cast_bitLift]
      push_cast
      rfl
    exact (ZMod.intCast_eq_intCast_iff _ _ 4).1 hi
  · rintro ⟨m, hm, d, hd, h⟩
    refine ⟨(m : ZMod 2), d, hd, funext fun i => ?_⟩
    rw [red4_apply, resid4, lift4_eq_cast_bitLift, (ZMod.intCast_eq_intCast_iff _ _ 4).2 (h i)]
    push_cast
    congr 1
    rcases hm with rfl | rfl <;> rfl

theorem codeLattice_le_mod4 (hΩ : allOnes ∈ C) :
    codeLatticeSubgroup hΩ ≤ codeLatticeMod4 C hΩ := by
  rintro u ⟨m, hm, d, hd, h, -⟩
  exact (mem_codeLatticeMod4_iff hΩ u).2 ⟨m, hm, d, hd, h⟩

private theorem sum_eq_of_modEq {u : Fin 24 → ℤ} {m : ℤ} {d : Fin 24 → ZMod 2}
    (h : ∀ i, u i ≡ m + 2 * bitLift (d i) [ZMOD 4]) :
    ∃ k : ℤ, ∑ i, u i = 24 * m + 2 * weight d + 4 * k := by
  refine ⟨∑ i, (u i - m - 2 * bitLift (d i)) / 4, ?_⟩
  have hk : ∀ i, u i = m + 2 * bitLift (d i) + 4 * ((u i - m - 2 * bitLift (d i)) / 4) := by
    intro i
    have := h i
    unfold Int.ModEq at this
    omega
  rw [Finset.sum_congr rfl (fun i _ => hk i)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, weight]
  ring

theorem sum_emod_four_of_mem_mod4 (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u : Fin 24 → ℤ} (hu : u ∈ codeLatticeMod4 C hΩ) : (∑ i, u i) % 4 = 0 := by
  obtain ⟨m, -, d, hd, h⟩ := (mem_codeLatticeMod4_iff hΩ u).1 hu
  obtain ⟨k, hk⟩ := sum_eq_of_modEq h
  have := hC4 d hd
  omega

theorem mem_codeLattice_iff_of_mem_mod4 (hΩ : allOnes ∈ C) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLatticeMod4 C hΩ) :
    u ∈ codeLattice C ↔ (∑ i, u i) % 8 = 4 * (u 0 % 2) := by
  obtain ⟨m, hm, d, hd, h⟩ := (mem_codeLatticeMod4_iff hΩ u).1 hu
  have hm0 : u 0 % 2 = m := by
    have := h 0
    unfold Int.ModEq at this
    rcases hm with rfl | rfl <;> omega
  constructor
  · rintro ⟨m₁, hm₁, d₁, -, h₁, hs⟩
    have hm₁0 : u 0 % 2 = m₁ := by
      have := h₁ 0
      unfold Int.ModEq at this
      rcases hm₁ with rfl | rfl <;> omega
    unfold Int.ModEq at hs
    rcases hm₁ with rfl | rfl <;> omega
  · intro hs
    refine ⟨m, hm, d, hd, h, ?_⟩
    unfold Int.ModEq
    rcases hm with rfl | rfl <;> omega

theorem four_single_mem_mod4 (hΩ : allOnes ∈ C) :
    (4 : ℤ) • (Pi.single 0 1 : Fin 24 → ℤ) ∈ codeLatticeMod4 C hΩ := by
  have : red4 ((4 : ℤ) • (Pi.single 0 1 : Fin 24 → ℤ)) = 0 := by
    funext i
    rw [red4_apply]
    by_cases hi : i = 0
    · subst hi; simp; decide
    · simp [hi]
  change red4 _ ∈ resid4Subgroup C hΩ
  rw [this]
  exact AddSubgroup.zero_mem _

theorem relIndex_codeLattice (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0) :
    (codeLatticeSubgroup hΩ).relIndex (codeLatticeMod4 C hΩ) = 2 := by
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_two_iff]
  refine ⟨⟨_, four_single_mem_mod4 hΩ⟩, fun b => ?_⟩
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add]
  have hb := b.2
  have hb4 := AddSubgroup.add_mem _ hb (four_single_mem_mod4 hΩ)
  show Xor ((b : Fin 24 → ℤ) + (4 : ℤ) • (Pi.single 0 1 : Fin 24 → ℤ) ∈ codeLattice C)
    ((b : Fin 24 → ℤ) ∈ codeLattice C)
  rw [mem_codeLattice_iff_of_mem_mod4 hΩ hb4, mem_codeLattice_iff_of_mem_mod4 hΩ hb]
  have hsum : ∑ i, ((b : Fin 24 → ℤ) + (4 : ℤ) • (Pi.single 0 1 : Fin 24 → ℤ)) i =
      ∑ i, (b : Fin 24 → ℤ) i + 4 := by
    simp [Finset.sum_add_distrib, Pi.single_apply]
  have h0 : ((b : Fin 24 → ℤ) + (4 : ℤ) • (Pi.single 0 1 : Fin 24 → ℤ)) 0 =
      (b : Fin 24 → ℤ) 0 + 4 := by simp
  rw [hsum, h0]
  have h4 := sum_emod_four_of_mem_mod4 hΩ hC4 hb
  by_cases hc : (∑ i, (b : Fin 24 → ℤ) i) % 8 = 4 * ((b : Fin 24 → ℤ) 0 % 2)
  · exact Or.inr ⟨hc, by omega⟩
  · exact Or.inl ⟨by omega, hc⟩

theorem index_codeLattice (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) :
    (codeLatticeSubgroup hΩ).index = 2 ^ 36 := by
  rw [← AddSubgroup.relIndex_mul_index (codeLattice_le_mod4 hΩ), relIndex_codeLattice hΩ hC4,
    index_codeLatticeMod4 hΩ hdual]
  norm_num

theorem nonempty_basis_codeLattice (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) :
    Nonempty (Basis (Fin 24) ℤ (codeLatticeSubgroup hΩ)) := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin 24))
    (codeLatticeSubgroup hΩ).toIntSubmodule
  have hn : n = 24 := by
    have h1 : finrank ℤ (codeLatticeSubgroup hΩ).toIntSubmodule = n := by
      rw [finrank_eq_card_basis b, Fintype.card_fin]
    have hfin : Finite ((Fin 24 → ℤ) ⧸ (codeLatticeSubgroup hΩ).toIntSubmodule) := by
      have h := index_codeLattice hΩ hC4 hdual
      rw [AddSubgroup.index] at h
      have h' : Nat.card ((Fin 24 → ℤ) ⧸ (codeLatticeSubgroup hΩ).toIntSubmodule) = 2 ^ 36 := h
      exact Nat.finite_of_card_ne_zero (by rw [h']; positivity)
    have h2 := (Submodule.finiteQuotient_iff _).1 hfin
    rw [finrank_fin_fun] at h2
    omega
  subst hn
  exact ⟨b⟩

theorem det_gram_codeLattice (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) (b : Basis (Fin 24) ℤ (codeLatticeSubgroup hΩ)) :
    (Matrix.of fun i j => codeForm (fun k => ((b i : Fin 24 → ℤ) k : ℚ))
      (fun k => ((b j : Fin 24 → ℤ) k : ℚ))).det = 1 := by
  classical
  have hidx := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 24)) (codeLatticeSubgroup hΩ) b
  rw [index_codeLattice hΩ hC4 hdual, Basis.det_apply] at hidx
  set A : Matrix (Fin 24) (Fin 24) ℤ := (Pi.basisFun ℤ (Fin 24)).toMatrix fun i => (b i : _)
    with hA
  have hAij : ∀ i j, A i j = (b j : Fin 24 → ℤ) i := by
    intro i j
    rw [hA, Basis.toMatrix_apply, Pi.basisFun_repr]
  have hgram : (Matrix.of fun i j => codeForm (fun k => ((b i : Fin 24 → ℤ) k : ℚ))
      (fun k => ((b j : Fin 24 → ℤ) k : ℚ))) =
      (8 : ℚ)⁻¹ • (Matrix.transpose (A.map (Int.castRingHom ℚ)) * A.map (Int.castRingHom ℚ)) := by
    ext i j
    simp only [Matrix.of_apply, codeForm, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.map_apply, hAij, eq_intCast, smul_eq_mul]
    ring
  have hdet : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) := by
    simpa using (RingHom.map_det (Int.castRingHom ℚ) A).symm
  rw [hgram, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, hdet, Fintype.card_fin]
  have hsq : (A.det : ℚ) * (A.det : ℚ) = (2 : ℚ) ^ 72 := by
    have h : (A.det.natAbs : ℤ) = 2 ^ 36 := by rw [← hidx]; norm_num
    have h2 : A.det * A.det = 2 ^ 72 := by
      rw [← Int.natAbs_mul_self' A.det, h]
      norm_num
    exact_mod_cast h2
  rw [hsq]
  norm_num

@[expose] def hInt (u v : Fin 24 → ℤ) : ℤ := (∑ i, u i * v i) / 8

theorem eight_mul_hInt (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    8 * hInt u v = ∑ i, u i * v i := by
  have := sum_mul_emod_eight hΩ hC4 hu hv
  unfold hInt
  omega

theorem hInt_comm (u v : Fin 24 → ℤ) : hInt u v = hInt v u := by
  simp only [hInt, mul_comm]

theorem hInt_add_left (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u u' v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hu' : u' ∈ codeLattice C)
    (hv : v ∈ codeLattice C) : hInt (u + u') v = hInt u v + hInt u' v := by
  have h1 := eight_mul_hInt hΩ hC4 (add_mem_codeLattice hΩ hu hu') hv
  have h2 := eight_mul_hInt hΩ hC4 hu hv
  have h3 := eight_mul_hInt hΩ hC4 hu' hv
  have e : ∑ i, (u + u') i * v i = ∑ i, u i * v i + ∑ i, u' i * v i := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  omega

theorem hInt_smul_left (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0) (c : ℤ)
    {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    hInt (c • u) v = c * hInt u v := by
  have hcu : c • u ∈ codeLattice C := (codeLatticeSubgroup hΩ).zsmul_mem hu c
  have h1 := eight_mul_hInt hΩ hC4 hcu hv
  have h2 := eight_mul_hInt hΩ hC4 hu hv
  have e : ∑ i, (c • u) i * v i = c * ∑ i, u i * v i := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [e, ← h2] at h1
  linarith

theorem two_dvd_hInt_self (hC4 : ∀ d ∈ C, weight d % 4 = 0) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice C) : 2 ∣ hInt u u := by
  have := sum_mul_self_emod_sixteen hC4 hu
  unfold hInt
  omega

theorem four_single_add_mem (i j : Fin 24) :
    (4 : ℤ) • ((Pi.single i 1 : Fin 24 → ℤ) + Pi.single j 1) ∈ codeLattice C := by
  refine ⟨0, .inl rfl, 0, C.zero_mem, fun k => ?_, ?_⟩
  · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply, bitLift, ZMod.val_zero,
      Nat.cast_zero, mul_zero, add_zero]
    exact Int.modEq_zero_iff_dvd.2 (Dvd.intro _ rfl)
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, ← Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true, mul_zero]
    exact Int.modEq_iff_dvd.2 ⟨-1, by ring⟩

theorem two_bitLift_mem (hC4 : ∀ d ∈ C, weight d % 4 = 0) {d : Fin 24 → ZMod 2} (hd : d ∈ C) :
    (fun i => 2 * bitLift (d i)) ∈ codeLattice C := by
  refine ⟨0, .inl rfl, d, hd, fun i => by simp, ?_⟩
  have h := hC4 d hd
  simp only [← Finset.mul_sum, mul_zero]
  unfold Int.ModEq
  unfold weight at h
  omega

theorem omega_sub_four_single_mem :
    ((fun _ => (1 : ℤ)) - (4 : ℤ) • (Pi.single 0 1 : Fin 24 → ℤ)) ∈ codeLattice C := by
  refine ⟨1, .inr rfl, 0, C.zero_mem, fun i => ?_, ?_⟩
  · by_cases hi : i = 0
    · subst hi
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Pi.zero_apply,
        bitLift, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero]
      exact Int.modEq_iff_dvd.2 ⟨1, by ring⟩
    · simp [hi, bitLift]
  · have hs : ∑ i, (((fun _ => (1 : ℤ)) - (4 : ℤ) • (Pi.single 0 1 : Fin 24 → ℤ)) :
        Fin 24 → ℤ) i = 20 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Finset.sum_pi_single', Finset.mem_univ, ite_true]
      norm_num
    rw [hs]
    decide

theorem mem_codeLattice_of_dual (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0)
    (hC4 : ∀ d ∈ C, weight d % 4 = 0) {w : Fin 24 → ℤ}
    (hw : ∀ v ∈ codeLattice C, (∑ i, w i * v i) % 8 = 0) : w ∈ codeLattice C := by
  have hpar : ∀ i, w i % 2 = w 0 % 2 := by
    intro i
    have h := hw _ (four_single_add_mem (C := C) i 0)
    have e : ∑ k, w k * (((4 : ℤ) • ((Pi.single i 1 : Fin 24 → ℤ) + Pi.single 0 1) :
        Fin 24 → ℤ) k) = 4 * (w i + w 0) := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      simp [Pi.single_apply]
      ring
    rw [e] at h
    omega
  set m : ℤ := w 0 % 2 with hm
  have hm01 : m = 0 ∨ m = 1 := by omega
  set y : Fin 24 → ℤ := fun i => (w i - m) / 2 with hy
  have hwy : ∀ i, w i = m + 2 * y i := by
    intro i
    have := hpar i
    simp only [hy]
    omega
  let d : Fin 24 → ZMod 2 := fun i => (y i : ZMod 2)
  have hbit : ∀ i, bitLift (d i) = y i % 2 := by
    intro i
    simp only [d, bitLift, ZMod.val_intCast]
    omega
  have hdC : d ∈ C := by
    rw [hdual]
    intro e he
    have h := hw _ (two_bitLift_mem hC4 he)
    have hwe := hC4 e he
    have e1 : ∑ i, w i * (2 * bitLift (e i)) =
        2 * m * weight e + 4 * ∑ i, y i * bitLift (e i) := by
      simp only [hwy, weight, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1] at h
    have h2 : (∑ i, y i * bitLift (e i)) % 2 = 0 := by
      unfold weight at hwe h
      rcases hm01 with h0 | h0 <;> rw [h0] at h <;> omega
    have : ((∑ i, y i * bitLift (e i) : ℤ) : ZMod 2) = d ⬝ᵥ e := by
      simp only [dotProduct, d, Int.cast_sum, Int.cast_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp [bitLift]
    rw [← this, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (Int.dvd_of_emod_eq_zero h2)]
  refine ⟨m, hm01, d, hdC, fun i => ?_, ?_⟩
  · rw [hwy i, hbit i]
    unfold Int.ModEq
    omega
  · have h := hw _ (omega_sub_four_single_mem (C := C))
    have e : ∑ i, w i * ((((fun _ => (1 : ℤ)) - (4 : ℤ) • (Pi.single 0 1 : Fin 24 → ℤ)) :
        Fin 24 → ℤ) i) = ∑ i, w i - 4 * w 0 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, mul_one,
        Finset.sum_sub_distrib]
      simp [Pi.single_apply]
      ring
    rw [e] at h
    unfold Int.ModEq
    have := hpar 0
    omega

theorem hInt_eq_codeForm (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    ((hInt u v : ℤ) : ℚ) = codeForm (fun i => (u i : ℚ)) (fun i => (v i : ℚ)) := by
  have h := eight_mul_hInt hΩ hC4 hu hv
  unfold codeForm
  have : (∑ i, (u i : ℚ) * (v i : ℚ)) = ((∑ i, u i * v i : ℤ) : ℚ) := by push_cast; rfl
  rw [this, ← h]
  push_cast
  ring

variable (C) in
abbrev codeLatticeModTwo (hΩ : allOnes ∈ C) : Type := ModN (codeLatticeSubgroup hΩ) 2

theorem finrank_codeLatticeModTwo (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) :
    finrank (ZMod 2) (codeLatticeModTwo C hΩ) = 24 := by
  obtain ⟨b⟩ := nonempty_basis_codeLattice hΩ hC4 hdual
  rw [finrank_eq_card_basis (ModN.basis (n := 2) b), Fintype.card_fin]

theorem mem_two_range_iff (hΩ : allOnes ∈ C) (x : codeLatticeSubgroup hΩ) :
    x ∈ LinearMap.range (LinearMap.lsmul ℤ (codeLatticeSubgroup hΩ) ((2 : ℕ) : ℤ)) ↔
      ∃ w : codeLatticeSubgroup hΩ, (2 : ℤ) • (w : Fin 24 → ℤ) = x := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Subtype.ext hw⟩

theorem hInt_add_two_smul (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u w : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hw : w ∈ codeLattice C) :
    hInt (u + (2 : ℤ) • w) (u + (2 : ℤ) • w) = hInt u u + 4 * hInt u w + 4 * hInt w w := by
  have h2w : (2 : ℤ) • w ∈ codeLattice C := (codeLatticeSubgroup hΩ).zsmul_mem hw 2
  have huw : u + (2 : ℤ) • w ∈ codeLattice C := add_mem_codeLattice hΩ hu h2w
  rw [hInt_add_left hΩ hC4 hu h2w huw, hInt_smul_left hΩ hC4 2 hw huw, hInt_comm u,
    hInt_comm w, hInt_add_left hΩ hC4 hu h2w hu, hInt_add_left hΩ hC4 hu h2w hw,
    hInt_smul_left hΩ hC4 2 hw hu, hInt_smul_left hΩ hC4 2 hw hw, hInt_comm w u]
  ring

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact .inl rfl
  · exact .inr rfl

variable (C) in
@[expose] def codeQuad (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0) :
    codeLatticeModTwo C hΩ → ZMod 2 :=
  Quotient.lift
    (s := (LinearMap.range (LinearMap.lsmul ℤ (codeLatticeSubgroup hΩ) ((2 : ℕ) : ℤ))).quotientRel)
    (fun u => ((hInt u u / 2 : ℤ) : ZMod 2)) (by
      intro u u' huu'
      have h := (Submodule.quotientRel_def _).1 huu'
      obtain ⟨w, hw⟩ := (mem_two_range_iff hΩ _).1 h
      have hu : (u : Fin 24 → ℤ) = u' + (2 : ℤ) • (w : Fin 24 → ℤ) := by
        rw [hw]
        simp
      rw [hu, hInt_add_two_smul hΩ hC4 u'.2 w.2]
      have he := two_dvd_hInt_self hC4 u'.2
      have : (hInt u' u' + 4 * hInt u' w + 4 * hInt w w) / 2 =
          hInt u' u' / 2 + 2 * (hInt u' w + hInt w w) := by omega
      rw [this]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero])

theorem codeQuad_mk (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (u : codeLatticeSubgroup hΩ) :
    codeQuad C hΩ hC4 (Submodule.Quotient.mk u) = ((hInt u u / 2 : ℤ) : ZMod 2) := rfl

theorem codeQuad_zero (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0) :
    codeQuad C hΩ hC4 0 = 0 := by
  rw [← Submodule.Quotient.mk_zero, codeQuad_mk]
  simp [hInt]

theorem polar_codeQuad_mk (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (u v : codeLatticeSubgroup hΩ) :
    QuadraticMap.polar (codeQuad C hΩ hC4) (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      ((hInt u v : ℤ) : ZMod 2) := by
  rw [QuadraticMap.polar, ← Submodule.Quotient.mk_add, codeQuad_mk, codeQuad_mk, codeQuad_mk]
  have huv : ((u + v : codeLatticeSubgroup hΩ) : Fin 24 → ℤ) = (u : Fin 24 → ℤ) + v := rfl
  rw [huv, hInt_add_left hΩ hC4 u.2 v.2 (add_mem_codeLattice hΩ u.2 v.2), hInt_comm u,
    hInt_comm v, hInt_add_left hΩ hC4 u.2 v.2 u.2, hInt_add_left hΩ hC4 u.2 v.2 v.2,
    hInt_comm v u]
  have hu := two_dvd_hInt_self hC4 u.2
  have hv := two_dvd_hInt_self hC4 v.2
  have : (hInt u u + hInt u v + (hInt u v + hInt v v)) / 2 =
      hInt u u / 2 + hInt v v / 2 + hInt u v := by omega
  rw [this]
  push_cast
  ring

variable (C) in
@[expose] noncomputable def codeQuadForm (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0) :
    QuadraticForm (ZMod 2) (codeLatticeModTwo C hΩ) :=
  QuadraticMap.ofPolar (codeQuad C hΩ hC4)
    (by
      intro a x
      rcases zmod_two_cases a with rfl | rfl
      · rw [zero_smul, codeQuad_zero, mul_zero, zero_smul]
      · rw [one_smul, mul_one, one_smul])
    (by
      intro x x' y
      induction x using Submodule.Quotient.induction_on with | H u => ?_
      induction x' using Submodule.Quotient.induction_on with | H u' => ?_
      induction y using Submodule.Quotient.induction_on with | H v => ?_
      rw [← Submodule.Quotient.mk_add, polar_codeQuad_mk, polar_codeQuad_mk, polar_codeQuad_mk]
      have : ((u + u' : codeLatticeSubgroup hΩ) : Fin 24 → ℤ) = (u : Fin 24 → ℤ) + u' := rfl
      rw [this, hInt_add_left hΩ hC4 u.2 u'.2 v.2]
      push_cast
      ring)
    (by
      intro a x y
      rcases zmod_two_cases a with rfl | rfl
      · rw [zero_smul, zero_smul, QuadraticMap.polar, zero_add, codeQuad_zero]
        ring
      · rw [one_smul, one_smul])

theorem codeQuadForm_mk (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (u : codeLatticeSubgroup hΩ) :
    codeQuadForm C hΩ hC4 (Submodule.Quotient.mk u) = ((hInt u u / 2 : ℤ) : ZMod 2) :=
  codeQuad_mk hΩ hC4 u

theorem polarBilin_codeQuadForm_mk (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (u v : codeLatticeSubgroup hΩ) :
    QuadraticMap.polarBilin (codeQuadForm C hΩ hC4) (Submodule.Quotient.mk u)
      (Submodule.Quotient.mk v) = ((hInt u v : ℤ) : ZMod 2) := by
  rw [QuadraticMap.polarBilin_apply_apply]
  exact polar_codeQuad_mk hΩ hC4 u v

theorem polarBilin_codeQuadForm_nondegenerate (hΩ : allOnes ∈ C)
    (hC4 : ∀ d ∈ C, weight d % 4 = 0) (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) :
    (QuadraticMap.polarBilin (codeQuadForm C hΩ hC4)).Nondegenerate := by
  have key : ∀ u : codeLatticeSubgroup hΩ,
      (∀ v : codeLatticeSubgroup hΩ, ((hInt u v : ℤ) : ZMod 2) = 0) →
      (Submodule.Quotient.mk u : codeLatticeModTwo C hΩ) = 0 := by
    intro u hu
    have hev : ∀ v ∈ codeLattice C, (∑ i, (u : Fin 24 → ℤ) i * v i) % 16 = 0 := by
      intro v hv
      have h1 := hu ⟨v, hv⟩
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
      have h2 := eight_mul_hInt hΩ hC4 u.2 hv
      push_cast at h1
      omega
    have hpar : ∀ i, (u : Fin 24 → ℤ) i % 2 = 0 := by
      intro i
      have h := hev _ (smul_eight_mem_codeLattice (C := C) (Pi.single i 1))
      have e : ∑ k, (u : Fin 24 → ℤ) k * ((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ)) k =
          8 * (u : Fin 24 → ℤ) i := by
        simp [Pi.single_apply]
        ring
      rw [e] at h
      omega
    set w : Fin 24 → ℤ := fun i => (u : Fin 24 → ℤ) i / 2 with hwdef
    have huw : (u : Fin 24 → ℤ) = (2 : ℤ) • w := by
      funext i
      have := hpar i
      simp only [Pi.smul_apply, smul_eq_mul, hwdef]
      omega
    have hwL : w ∈ codeLattice C := by
      refine mem_codeLattice_of_dual hdual hC4 fun v hv => ?_
      have h := hev v hv
      have e : ∑ i, (u : Fin 24 → ℤ) i * v i = 2 * ∑ i, w i * v i := by
        rw [huw, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [e] at h
      omega
    rw [Submodule.Quotient.mk_eq_zero, mem_two_range_iff]
    exact ⟨⟨w, hwL⟩, huw.symm⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · induction x using Submodule.Quotient.induction_on with | H u => ?_
    refine key u fun v => ?_
    have := hx (Submodule.Quotient.mk v)
    rwa [polarBilin_codeQuadForm_mk] at this
  · induction x using Submodule.Quotient.induction_on with | H u => ?_
    refine key u fun v => ?_
    have := hx (Submodule.Quotient.mk v)
    rwa [polarBilin_codeQuadForm_mk, hInt_comm] at this

theorem code_coordinate_even_unimodular_lattice (hΩ : allOnes ∈ C)
    (hC4 : ∀ d ∈ C, weight d % 4 = 0) (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0) :
    (∀ x : Fin 24 → ℤ, (8 : ℤ) • x ∈ codeLatticeSubgroup hΩ) ∧
    Nonempty (Basis (Fin 24) ℤ (codeLatticeSubgroup hΩ)) ∧
    (codeLatticeSubgroup hΩ).index = 2 ^ 36 ∧
    (∀ u ∈ codeLattice C, ∀ v ∈ codeLattice C,
      (∃ n : ℤ, codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 2 * n) ∧
        ∃ n : ℤ, codeForm (fun i => (u i : ℚ)) (fun i => (v i : ℚ)) = n) ∧
    (∀ b : Basis (Fin 24) ℤ (codeLatticeSubgroup hΩ),
      (Matrix.of fun i j => codeForm (fun k => ((b i : Fin 24 → ℤ) k : ℚ))
        (fun k => ((b j : Fin 24 → ℤ) k : ℚ))).det = 1) ∧
    finrank (ZMod 2) (codeLatticeModTwo C hΩ) = 24 ∧
    (∀ u : codeLatticeSubgroup hΩ, codeQuadForm C hΩ hC4 (Submodule.Quotient.mk u) =
      ((hInt u u / 2 : ℤ) : ZMod 2) ∧
      ((hInt u u : ℤ) : ℚ) = codeForm (fun i => ((u : Fin 24 → ℤ) i : ℚ))
        (fun i => ((u : Fin 24 → ℤ) i : ℚ))) ∧
    (∀ u v : codeLatticeSubgroup hΩ,
      QuadraticMap.polarBilin (codeQuadForm C hΩ hC4) (Submodule.Quotient.mk u)
        (Submodule.Quotient.mk v) = ((hInt u v : ℤ) : ZMod 2) ∧
      ((hInt u v : ℤ) : ℚ) = codeForm (fun i => ((u : Fin 24 → ℤ) i : ℚ))
        (fun i => ((v : Fin 24 → ℤ) i : ℚ))) ∧
    (QuadraticMap.polarBilin (codeQuadForm C hΩ hC4)).Nondegenerate :=
  ⟨fun x => smul_eight_mem_codeLattice x, nonempty_basis_codeLattice hΩ hC4 hdual,
    index_codeLattice hΩ hC4 hdual, fun _ hu _ hv => codeForm_even_integral hΩ hC4 hu hv,
    det_gram_codeLattice hΩ hC4 hdual, finrank_codeLatticeModTwo hΩ hC4 hdual,
    fun u => ⟨codeQuadForm_mk hΩ hC4 u, hInt_eq_codeForm hΩ hC4 u.2 u.2⟩,
    fun u v => ⟨polarBilin_codeQuadForm_mk hΩ hC4 u v, hInt_eq_codeForm hΩ hC4 u.2 v.2⟩,
    polarBilin_codeQuadForm_nondegenerate hΩ hC4 hdual⟩

end CFSG.Monster
