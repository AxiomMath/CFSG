module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp (InspPair)
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement

namespace InspEven

variable (K : Type*) [Field K]

noncomputable def stdPoint : ℙ K (Fin 2 → K) :=
  Projectivization.mk K (Pi.single 0 (1 : K)) (Pi.single_ne_zero_iff.2 one_ne_zero)

noncomputable def unipHom : Multiplicative K →* SL(2, K) where
  toFun c := SpecialLinearGroup.transvection zero_ne_one c.toAdd
  map_one' := by simp
  map_mul' c d := by rw [toAdd_mul, SpecialLinearGroup.transvection_add]

noncomputable def U0 : Subgroup SL(2, K) :=
  Subgroup.closure (Set.range fun c : K => SpecialLinearGroup.transvection zero_ne_one c)

theorem U0_eq_range : U0 K = (unipHom K).range := by
  apply le_antisymm
  · rw [show U0 K = Subgroup.closure (Set.range fun c : K =>
        SpecialLinearGroup.transvection zero_ne_one c) from rfl, Subgroup.closure_le]
    rintro x ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩
  · rintro x ⟨d, rfl⟩
    exact Subgroup.subset_closure ⟨Multiplicative.toAdd d, rfl⟩

theorem transvection_ne_one {c : K} (hc : c ≠ 0) :
    (SpecialLinearGroup.transvection zero_ne_one c : SL(2, K)) ≠ 1 := by
  intro h
  have h01 := congrFun (congrFun (congrArg (fun x : SL(2, K) =>
    (x : Matrix (Fin 2) (Fin 2) K)) h) 0) 1
  simp [SpecialLinearGroup.transvection_coe] at h01
  exact hc h01

theorem isPGroup_multiplicative [CharP K 2] : IsPGroup 2 (Multiplicative K) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  let c : K := Multiplicative.toAdd g
  have hg : Multiplicative.ofAdd c = g := rfl
  rw [← hg, pow_one, pow_two, ← ofAdd_add]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hcc : c + c = 0 := by rw [← two_mul, h2, zero_mul]
  rw [hcc, ofAdd_zero]

theorem isPGroup_U0 [CharP K 2] : IsPGroup 2 (U0 K) := by
  rw [U0_eq_range]
  exact IsPGroup.of_surjective (isPGroup_multiplicative K) (unipHom K).rangeRestrict
    (unipHom K).rangeRestrict_surjective

theorem isMulCommutative_U0 : IsMulCommutative (U0 K) := by
  apply Subgroup.isMulCommutative_closure
  rintro a ⟨c, rfl⟩ b ⟨d, rfl⟩ -
  rw [commute_iff_eq, ← SpecialLinearGroup.transvection_add,
    ← SpecialLinearGroup.transvection_add, add_comm]

theorem U0_ne_bot : U0 K ≠ ⊥ := by
  intro h
  have ht : SpecialLinearGroup.transvection zero_ne_one (1 : K) ∈ U0 K :=
    Subgroup.subset_closure ⟨1, rfl⟩
  rw [h] at ht
  exact transvection_ne_one K one_ne_zero (Subgroup.mem_bot.1 ht)

variable [CharP K 2]

theorem center_eq_bot : Subgroup.center SL(2, K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    rcases sq_eq_one_iff.1 hr with h | h
    · exact h
    · simpa [CharTwo.neg_eq] using h
  have hs : (Matrix.scalar (Fin 2) (1 : K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j; simp [Matrix.scalar_apply]
  rw [hr1, hs] at hrx
  exact Subtype.ext hrx.symm

theorem diag2_mul (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    diag2 a ha * diag2 b hb = diag2 (a * b) (mul_ne_zero ha hb) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diag2_coe, _root_.mul_inv_rev, mul_comm]

theorem diag2_pow (a : K) (ha : a ≠ 0) (k : ℕ) :
    (diag2 a ha) ^ k = diag2 (a ^ k) (pow_ne_zero k ha) := by
  induction k with
  | zero =>
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diag2_coe]
  | succ n ih =>
      rw [pow_succ, ih, diag2_mul]
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, diag2_coe, pow_succ, mul_comm, mul_assoc]

theorem diag2_ne_one {a : K} (ha : a ≠ 0) (ha1 : a ≠ 1) :
    diag2 a ha ≠ (1 : SL(2, K)) := by
  intro h
  have h00 := congrFun (congrFun (congrArg (fun x : SL(2, K) =>
    (x : Matrix (Fin 2) (Fin 2) K)) h) 0) 0
  simp [diag2_coe] at h00
  exact ha1 h00

theorem lambda_ne_zero (b : SL(2, K))
    (hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (b : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
  have hdet : (b : Matrix (Fin 2) (Fin 2) K) 0 0 * (b : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (b : Matrix (Fin 2) (Fin 2) K) 0 1 * (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := b.2
    rwa [Matrix.det_fin_two] at this
  rw [hb10, mul_zero, sub_zero] at hdet
  intro h
  rw [h, zero_mul] at hdet
  exact zero_ne_one hdet

theorem upper_decomp (b : SL(2, K))
    (hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    b = diag2 ((b : Matrix (Fin 2) (Fin 2) K) 0 0) (lambda_ne_zero K b hb10) *
      SpecialLinearGroup.transvection zero_ne_one
        (((b : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ * (b : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  have hlam := lambda_ne_zero K b hb10
  have hdet : (b : Matrix (Fin 2) (Fin 2) K) 0 0 * (b : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (b : Matrix (Fin 2) (Fin 2) K) 0 1 * (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := b.2
    rwa [Matrix.det_fin_two] at this
  have hmul : (b : Matrix (Fin 2) (Fin 2) K) 0 0 * (b : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [hb10, mul_zero, sub_zero] at hdet
    exact hdet
  have hB11 : (b : Matrix (Fin 2) (Fin 2) K) 1 1 =
      ((b : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, diag2_coe, SpecialLinearGroup.transvection_coe]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, diag2_coe, SpecialLinearGroup.transvection_coe]
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, diag2_coe, SpecialLinearGroup.transvection_coe,
      hb10]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, diag2_coe, SpecialLinearGroup.transvection_coe,
      hB11]

theorem upper_commutator (b : SL(2, K))
    (hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (c : K) :
    ⁅b, SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c⁆ =
      SpecialLinearGroup.transvection zero_ne_one
        ((((b : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2 - 1) * c) := by
  have hlam := lambda_ne_zero K b hb10
  have hdecomp := upper_decomp K b hb10
  conv_lhs => rw [hdecomp]
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hcomm : ⁅SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1)
      (((b : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ * (b : Matrix (Fin 2) (Fin 2) K) 0 1),
      SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm, ← SpecialLinearGroup.transvection_add,
      ← SpecialLinearGroup.transvection_add, add_comm]
  rw [hcomm, mul_one, mul_inv_cancel, one_mul,
    commutator_diag2_transvection ((b : Matrix (Fin 2) (Fin 2) K) 0 0) hlam c
      ((((b : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2 - 1) * c) (by ring)]

theorem upper_conj (b : SL(2, K))
    (hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (c : K) :
    b * SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c * b⁻¹ =
      SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1)
        ((((b : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2) * c) := by
  rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul, upper_commutator K b hb10 c,
    ← SpecialLinearGroup.transvection_add]
  congr 1
  ring

theorem inv_upper (b : SL(2, K))
    (hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ((b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  have hdet : (b : Matrix (Fin 2) (Fin 2) K) 0 0 * (b : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (b : Matrix (Fin 2) (Fin 2) K) 0 1 * (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := b.2
    rwa [Matrix.det_fin_two] at this
  have hmul' : (b : Matrix (Fin 2) (Fin 2) K) 0 0 * (b : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [hb10, mul_zero, sub_zero] at hdet
    exact hdet
  have h11 : (b : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := fun h => by
    rw [h, mul_zero] at hmul'
    exact zero_ne_one hmul'
  have hmul : (b : Matrix (Fin 2) (Fin 2) K) *
      ((b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    change ((b * b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [mul_inv_cancel]
    rfl
  have h10 := congrFun (congrFun hmul 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hb10, mul_zero, zero_mul, add_zero,
    zero_add, Matrix.one_apply, one_ne_zero, reduceIte] at h10
  rcases mul_eq_zero.mp h10 with h | h
  · exact absurd h h11
  · simpa only [SpecialLinearGroup.coe_inv] using h

theorem upper_conj_mem (b : SL(2, K))
    (hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) {x : SL(2, K)} (hx : x ∈ U0 K) :
    b * x * b⁻¹ ∈ U0 K := by
  revert hx
  refine Subgroup.closure_induction (p := fun x _ => b * x * b⁻¹ ∈ U0 K) ?_ ?_ ?_ ?_
  · rintro x ⟨c, rfl⟩
    rw [upper_conj K b hb10 c]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  · simp
  · rintro x y hx hy ihx ihy
    rw [show b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) by group]
    exact Subgroup.mul_mem _ ihx ihy
  · rintro x hx ihx
    rw [show b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ihx

theorem upper_mem_normalizer (b : SL(2, K))
    (hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    b ∈ Subgroup.normalizer (U0 K : Set SL(2, K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact upper_conj_mem K b hb10 hx
  · intro hx
    have hx' : b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ ∈ U0 K :=
      upper_conj_mem K b⁻¹ (inv_upper K b hb10) hx
    convert hx' using 1
    group

theorem lambda_sq_ne_one {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (b : SL(2, K))
    (hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (hbne : b ≠ 1) (hbr : b ^ r = 1) :
    (((b : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2) ≠ 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  intro hsq
  have hlam := lambda_ne_zero K b hb10
  have hdecomp := upper_decomp K b hb10
  have hlam1 : (b : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    rcases sq_eq_one_iff.1 hsq with h | h
    · exact h
    · simpa [CharTwo.neg_eq] using h
  have hdiag : diag2 ((b : Matrix (Fin 2) (Fin 2) K) 0 0) hlam = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe, hlam1]
  have hb2 : b ^ 2 = 1 := by
    rw [hdecomp, hdiag, one_mul, pow_two, ← SpecialLinearGroup.transvection_add]
    have h2 : ((b : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ * (b : Matrix (Fin 2) (Fin 2) K) 0 1 +
        ((b : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ * (b : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 :=
      CharTwo.add_self_eq_zero _
    rw [h2, SpecialLinearGroup.transvection_coeff_zero]
  have hord : orderOf b = r := orderOf_eq_prime hbr hbne
  have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 hb2
  rw [hord] at hdvd
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd)

end InspEven

namespace InspEven

open InspEven

theorem exists_card_sl (K : Type*) [Field K] [Finite K] [CharP K 2]
    (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (hrdvd : r ∣ Nat.card K - 1) :
    ∃ A : Subgroup SL(2, K), Nat.card A = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvd : r ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hrdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hxr : (x : K) ^ r = 1 := by
    have h := congrArg (fun y : Kˣ => (y : K)) (pow_orderOf_eq_one x)
    rw [hx] at h
    simpa using h
  have hxne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hr.ne_one hx.symm
  have hxK : (x : K) ≠ 0 := Units.ne_zero x
  have hxK1 : (x : K) ≠ 1 := fun h => hxne (Units.ext h)
  have hpow : (diag2 (x : K) hxK) ^ r = 1 := by
    rw [diag2_pow K (x : K) hxK r]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe, hxr]
  refine ⟨Subgroup.zpowers (diag2 (x : K) hxK), ?_⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hpow (diag2_ne_one K hxK hxK1)]

theorem insp_pair_sl (K : Type*) [Field K] [Finite K] [CharP K 2]
    (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (hrdvd : r ∣ Nat.card K - 1) :
    ∀ A : Subgroup SL(2, K), Nat.card A = r → ∃ U : Subgroup SL(2, K), InspPair 2 A U := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype K := Fintype.ofFinite K
  intro A hA
  haveI hAr : IsPGroup r A := IsPGroup.of_card (by rw [hA, pow_one])
  have hPcard : Nat.card (ℙ K (Fin 2 → K)) = Nat.card K + 1 := by
    rw [Projectivization.card_of_finrank_two (k := K) (V := Fin 2 → K)
      (by rw [Module.finrank_fin_fun])]
  have hKgt : 1 < Nat.card K := Finite.one_lt_card
  have hrndvd : ¬ r ∣ Nat.card (ℙ K (Fin 2 → K)) := by
    rw [hPcard]
    intro hdiv
    have h2 : r ∣ 2 := by
      have hsub := Nat.dvd_sub hdiv hrdvd
      convert hsub using 1
      omega
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  obtain ⟨p, hp⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card
    (hG := hAr) (α := ℙ K (Fin 2 → K)) hrndvd
  haveI : MulAction.IsPretransitive (SL(2, K)) (ℙ K (Fin 2 → K)) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := SL(2, K)) p (stdPoint K)
  let e : SL(2, K) ≃* SL(2, K) := MulAut.conj g
  let B : Subgroup SL(2, K) := A.map (e : SL(2, K) →* SL(2, K))
  have hBcard : Nat.card B = r := by
    rw [show B = A.map (e : SL(2, K) →* SL(2, K)) from rfl,
      Subgroup.card_map_of_injective e.injective, hA]
  have hBfix : ∀ b ∈ B, b • stdPoint K = stdPoint K := by
    intro b hb
    rw [show B = A.map (e : SL(2, K) →* SL(2, K)) from rfl] at hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
    change (MulAut.conj g a) • stdPoint K = stdPoint K
    rw [MulAut.conj_apply, mul_smul, mul_smul]
    have hainv : g⁻¹ • stdPoint K = p := by rw [← hg, inv_smul_smul]
    rw [hainv]
    have hap : a • p = p := by
      simpa using hp ⟨a, ha⟩
    rw [hap, hg]
  have hupper : ∀ b ∈ B, (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    intro b hb
    let e0 : Fin 2 → K := Pi.single (0 : Fin 2) (1 : K)
    have he0 : e0 ≠ 0 := by
      rw [show e0 = Pi.single (0 : Fin 2) (1 : K) from rfl]
      exact Pi.single_ne_zero_iff.2 one_ne_zero
    have hfix : b • stdPoint K = stdPoint K := hBfix b hb
    have hfix' : Projectivization.mk K (b • e0) ((smul_ne_zero_iff_ne b).mpr he0) =
        Projectivization.mk K e0 he0 := by
      simpa [stdPoint, e0, Projectivization.smul_mk] using hfix
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K (b • e0) e0 _ he0).1 hfix'
    have h0 : (b.1 *ᵥ e0 : Fin 2 → K) 1 = 0 :=
      (congrFun ha 1).symm.trans (by simp [e0])
    simpa [Matrix.mulVec, Fin.sum_univ_two, e0] using h0
  obtain ⟨bgen, hbgen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top B).1
    (isCyclic_of_prime_card (p := r) hBcard)
  let b0 : SL(2, K) := bgen
  have hbgenmem : bgen ∈ B := by rw [← hbgen]; exact Subgroup.mem_zpowers bgen
  have hb0mem : b0 ∈ B := by simpa [b0] using hbgenmem
  have hbgen_ne : bgen ≠ 1 := by
    intro h
    have hbot : B = ⊥ := by rw [← hbgen, h]; simp
    have hcard1 : Nat.card B = 1 := by rw [hbot]; simp
    have h2 : 2 ≤ r := hr.two_le
    omega
  have hb0ne : b0 ≠ 1 := by simpa [b0] using hbgen_ne
  have hb0r : b0 ^ r = 1 := by
    have h := pow_card_eq_one' (G := ↥B) (x := ⟨bgen, hbgenmem⟩)
    rw [hBcard] at h
    simpa [b0] using congrArg (fun y : ↥B => (y : SL(2, K))) h
  have hb0upper : (b0 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hupper b0 hb0mem
  have hlam2 : (((b0 : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2) ≠ 1 :=
    lambda_sq_ne_one K hr hr2 b0 hb0upper hb0ne hb0r
  have hInspB : InspPair 2 B (U0 K) := by
    refine ⟨isPGroup_U0 K, isMulCommutative_U0 K, U0_ne_bot K, ?_, ?_⟩
    · intro b hb
      exact upper_mem_normalizer K b (hupper b hb)
    · apply le_antisymm
      · rw [Subgroup.commutator_le]
        intro x hx y hy
        have hxN : x ∈ Subgroup.normalizer (U0 K : Set SL(2, K)) :=
          upper_mem_normalizer K x (hupper x hx)
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hxN y).1 hy)
          (Subgroup.inv_mem _ hy)
      · rw [show U0 K = Subgroup.closure (Set.range fun c : K =>
            SpecialLinearGroup.transvection zero_ne_one c) from rfl, Subgroup.closure_le]
        rintro x ⟨c, rfl⟩
        change SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c ∈
          ⁅B, U0 K⁆
        have hden : ((b0 : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2 - 1 ≠ 0 :=
          sub_ne_zero_of_ne hlam2
        have hc : (((b0 : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2 - 1) *
            (c / (((b0 : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2 - 1)) = c :=
          mul_div_cancel₀ c hden
        rw [← hc]
        rw [← upper_commutator K b0 hb0upper
          (c / (((b0 : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2 - 1))]
        exact Subgroup.commutator_mem_commutator hb0mem
          (Subgroup.subset_closure ⟨_, rfl⟩)
  refine ⟨(U0 K).map (e.symm : SL(2, K) →* SL(2, K)), ?_⟩
  have h := InspPair.map e.symm hInspB
  have hA' : B.map e.symm.toMonoidHom = A := by
    rw [show B = A.map e.toMonoidHom from rfl, Subgroup.map_map]
    rw [show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id (SL(2, K)) by
      ext x; simp, Subgroup.map_id]
  rw [hA'] at h
  exact h

end InspEven

theorem insp2L2_holds : Insp2L2 := by
  intro G _ _ n hL r hr hr2 hrdvd
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI hKc : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
    have hcenter := InspEven.center_eq_bot K
    have hinj : Function.Injective
        (QuotientGroup.mk' (Subgroup.center SL(2, K)) : SL(2, K) →* PSL(2, K)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hcenter
    let pslIso : SL(2, K) ≃* PSL(2, K) :=
      MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL(2, K)))
        ⟨hinj, QuotientGroup.mk'_surjective _⟩
    let e' : G ≃* SL(2, K) :=
      (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        K).symm).trans pslIso.symm
    refine ⟨?_, ?_⟩
    · obtain ⟨A, hA⟩ := InspEven.exists_card_sl K r hr hr2 (by rw [hK]; exact hrdvd)
      exact ⟨A.map e'.symm.toMonoidHom,
        by rw [Subgroup.card_map_of_injective e'.symm.injective, hA]⟩
    · intro A hA
      obtain ⟨U, hU⟩ := InspEven.insp_pair_sl K r hr hr2 (by rw [hK]; exact hrdvd)
        (A.map e'.toMonoidHom)
        (by rw [Subgroup.card_map_of_injective e'.injective, hA])
      refine ⟨U.map e'.symm.toMonoidHom, ?_⟩
      have h := InspPair.map e'.symm hU
      have hA' : (A.map e'.toMonoidHom).map e'.symm.toMonoidHom = A := by
        rw [Subgroup.map_map]
        have hcomp : e'.symm.toMonoidHom.comp e'.toMonoidHom = MonoidHom.id G := by
          ext x; simp
        rw [hcomp, Subgroup.map_id]
      rw [hA'] at h
      exact h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UCK
