module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Refine
import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
import CFSG.RankThree.PartTwo.Sec4.RonanK432R2
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowZ3FieldCore
import CFSG.RankThree.PartTwo.Sec4.Item424Res7ProofLin
import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofOuterLin
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalReal
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts

namespace L5Mod2

variable {K : Type} [Field K]

@[expose] def blk (A B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 5) (Fin 5) K :=
  !![A 0 0, A 0 1, 0, 0, 0;
     A 1 0, A 1 1, 0, 0, 0;
     0, 0, B 0 0, B 0 1, 0;
     0, 0, B 1 0, B 1 1, 0;
     0, 0, 0, 0, 1]

theorem blk_mul (A B A' B' : Matrix (Fin 2) (Fin 2) K) :
    blk A B * blk A' B' = blk (A * A') (B * B') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two]

theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.one_apply]

theorem det_blk (A B : Matrix (Fin 2) (Fin 2) K) : (blk A B).det = A.det * B.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp [blk, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem trace_blk_one (A : Matrix (Fin 2) (Fin 2) K) : (blk A 1).trace = A.trace + 3 := by
  simp [blk, Matrix.trace, Fin.sum_univ_five, Matrix.trace_fin_two] <;> ring

@[expose] def swapMat : Matrix (Fin 5) (Fin 5) K :=
  !![0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 0, 0, 1]

theorem det_swapMat : (swapMat : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  simp [swapMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem swapMat_mul_blk (A B : Matrix (Fin 2) (Fin 2) K) :
    swapMat * blk A B = blk B A * swapMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, blk, Matrix.mul_apply, Fin.sum_univ_five]

@[expose] def blkSL (A B : SL(2, K)) : SL(5, K) :=
  ⟨blk (A : Matrix (Fin 2) (Fin 2) K) B, by rw [det_blk, A.det_coe, B.det_coe, one_mul]⟩

@[expose] def blkHom : SL(2, K) × SL(2, K) →* SL(5, K) where
  toFun x := blkSL x.1 x.2
  map_one' := Subtype.ext (blk_one (K := K))
  map_mul' x y := Subtype.ext (blk_mul _ _ _ _).symm

@[expose] def swapSL : SL(5, K) := ⟨swapMat, det_swapMat⟩

theorem swapSL_conj (A B : SL(2, K)) : swapSL * blkSL A B * swapSL⁻¹ = blkSL B A := by
  rw [mul_inv_eq_iff_eq_mul]
  exact Subtype.ext (swapMat_mul_blk _ _)

@[expose] noncomputable def projCover5 : SL(5, K) →* projSL 5 K :=
  (Matrix.SpecialLinearGroup.toPGL : SL(5, K) →* Matrix.ProjGenLinGroup (Fin 5) K).codRestrict
    (projSL 5 K) fun x => by rw [KFacts.L34.projSL_eq_range_toPGL]; exact ⟨x, rfl⟩

theorem eq_one_of_toPGL_blkSL {A B : SL(2, K)}
    (h : Matrix.SpecialLinearGroup.toPGL (blkSL A B) = 1) : A = 1 ∧ B = 1 := by
  rw [← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker,
    Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, -, hr⟩ := h
  have e : ∀ i j, Matrix.scalar (Fin 5) r i j = blk (A : Matrix (Fin 2) (Fin 2) K) B i j :=
    fun i j => congrFun (congrFun hr i) j
  have hr1 : r = 1 := by simpa [blk] using e 4 4
  subst hr1
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [blk] using (e 0 0).symm
    · simpa [blk] using (e 0 1).symm
    · simpa [blk] using (e 1 0).symm
    · simpa [blk] using (e 1 1).symm
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [blk] using (e 2 2).symm
    · simpa [blk] using (e 2 3).symm
    · simpa [blk] using (e 3 2).symm
    · simpa [blk] using (e 3 3).symm

theorem blkHom_injective : Function.Injective ((projCover5 (K := K)).comp blkHom) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B⟩ h
  obtain ⟨rfl, rfl⟩ := eq_one_of_toPGL_blkSL (congrArg Subtype.val h)
  rfl

theorem exists_witness_prod {G S : Type} [Group G] [Group S] (φ : G × G →* S)
    (hφ : Function.Injective φ) (s : S) (hs : ∀ a b : G, s * φ (a, b) * s⁻¹ = φ (b, a))
    (hinv : ∀ a : G, a ^ 3 = 1 → a ≠ 1 → ∃ n : G, n * a * n⁻¹ = a⁻¹)
    {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : ((a, b) : G × G) ≠ 1) :
    ∃ g : S, (g * φ (a, b) * g⁻¹) * φ (a, b) = φ (a, b) * (g * φ (a, b) * g⁻¹) ∧
      g * φ (a, b) * g⁻¹ ∉ Subgroup.zpowers (φ (a, b)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ x y : G × G, φ y ∈ Subgroup.zpowers (φ x) → ∃ k : ℤ, x ^ k = y := by
    intro x y h
    rw [← MonoidHom.map_zpowers, Subgroup.mem_map_iff_mem hφ] at h
    exact Subgroup.mem_zpowers_iff.mp h
  by_cases ha1 : a = 1
  · subst ha1
    have hb1 : b ≠ 1 := fun h => hab (by rw [h]; rfl)
    refine ⟨s, ?_, ?_⟩
    · rw [hs, ← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    · rw [hs]
      intro h
      obtain ⟨k, hk⟩ := hmem _ _ h
      have := congrArg Prod.fst hk
      simp at this
      exact hb1 this.symm
  · by_cases hb1 : b = 1
    · subst hb1
      refine ⟨s, ?_, ?_⟩
      · rw [hs, ← map_mul, ← map_mul]
        congr 1
        ext <;> simp
      · rw [hs]
        intro h
        obtain ⟨k, hk⟩ := hmem _ _ h
        have := congrArg Prod.snd hk
        simp at this
        exact ha1 this.symm
    · obtain ⟨n, hn⟩ := hinv a ha ha1
      have e : φ (n, 1) * φ (a, b) * (φ (n, 1))⁻¹ = φ (a⁻¹, b) := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        ext
        · simpa using hn
        · simp
      refine ⟨φ (n, 1), ?_, ?_⟩
      · rw [e, ← map_mul, ← map_mul]
        congr 1
        ext <;> simp
      · rw [e]
        intro h
        obtain ⟨k, hk⟩ := hmem _ _ h
        have hk1 : a ^ k = a⁻¹ := by simpa using congrArg Prod.fst hk
        have hk2 : b ^ k = b := by simpa using congrArg Prod.snd hk
        have hoa : orderOf a = 3 := orderOf_eq_prime ha ha1
        have hob : orderOf b = 3 := orderOf_eq_prime hb hb1
        have d1 : ((3 : ℕ) : ℤ) ∣ k + 1 := by
          rw [← hoa]
          exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [_root_.zpow_add_one, hk1, inv_mul_cancel])
        have d2 : ((3 : ℕ) : ℤ) ∣ k - 1 := by
          rw [← hob]
          exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [_root_.zpow_sub_one, hk2, mul_inv_cancel])
        omega

theorem factorization_card_SL_five [Finite K] (hK : Nat.card K % 3 = 2) :
    (Nat.card SL(5, K)).factorization 3 = 2 * (Nat.card SL(2, K)).factorization 3 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
  set q := Nat.card K with hq
  have hq0 : 0 < q := Nat.card_pos
  have h25 : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
  have h22 : Finset.Icc 2 2 = {2} := by decide
  rw [h25, h22]
  simp only [Finset.prod_insert (show (2 : ℕ) ∉ ({3, 4, 5} : Finset ℕ) by decide),
    Finset.prod_insert (show (3 : ℕ) ∉ ({4, 5} : Finset ℕ) by decide),
    Finset.prod_insert (show (4 : ℕ) ∉ ({5} : Finset ℕ) by decide), Finset.prod_singleton]
  show (q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1))))).factorization 3 =
    2 * (q ^ 1 * (q ^ 2 - 1)).factorization 3
  rw [pow_one]
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq0
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq0
  have h4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [hq2, hq4]
    ring
  have hid : q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))) =
      (q * (q ^ 2 - 1)) ^ 2 * (q ^ 8 * (q ^ 2 + 1) * (q ^ 3 - 1) * (q ^ 5 - 1)) := by
    rw [h4]
    ring
  rw [hid]
  have hX : q * (q ^ 2 - 1) ≠ 0 := by
    have : 2 ≤ q := Finite.one_lt_card
    have : 4 ≤ q ^ 2 := by nlinarith
    exact Nat.mul_ne_zero hq0.ne' (by omega)
  have hR3 : ¬ 3 ∣ q ^ 8 * (q ^ 2 + 1) * (q ^ 3 - 1) * (q ^ 5 - 1) := by
    have a8 : q ^ 8 % 3 = 1 := by rw [Nat.pow_mod, hK]
    have a2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hK]
    have a3 : q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hK]
    have a5 : q ^ 5 % 3 = 2 := by rw [Nat.pow_mod, hK]
    have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq0
    have hq5 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq0
    generalize q ^ 8 = x8 at *
    generalize q ^ 2 = x2 at *
    generalize q ^ 3 = x3 at *
    generalize q ^ 5 = x5 at *
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h <;> omega
      · omega
    · omega
  have hR : q ^ 8 * (q ^ 2 + 1) * (q ^ 3 - 1) * (q ^ 5 - 1) ≠ 0 := fun h0 => hR3 (h0 ▸ dvd_zero 3)
  rw [Nat.factorization_mul (pow_ne_zero 2 hX) hR, Finsupp.add_apply, Nat.factorization_pow,
    Nat.factorization_eq_zero_of_not_dvd hR3]
  simp

theorem listRow_projSL_five_of_mod_two [Finite K] [Finite (projSL 5 K)]
    (hK : Nat.card K % 3 = 2) : ListRow (projSL 5 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : K) ≠ 0 := CFSG.ClassicalGroups.SLnThreeLocal.three_ne_zero_of_natCard_mod_three hK
  obtain ⟨T⟩ : Nonempty (Sylow 3 SL(2, K)) := inferInstance
  set φ : SL(2, K) × SL(2, K) →* projSL 5 K := (projCover5 (K := K)).comp blkHom with hφ
  have hinj : Function.Injective φ := blkHom_injective
  set a := (Nat.card SL(2, K)).factorization 3 with ha
  set Q : Subgroup (projSL 5 K) := ((T : Subgroup SL(2, K)).prod T).map φ with hQ
  have hQcard : Nat.card Q = 3 ^ (2 * a) := by
    rw [hQ, Subgroup.card_map_of_injective hinj, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
      Nat.card_prod, Sylow.card_eq_multiplicity, ← pow_add, two_mul]
  have hS : ¬ 3 ^ (2 * a + 1) ∣ Nat.card (projSL 5 K) := by
    intro h
    have h1 : 3 ^ (2 * a + 1) ∣ Nat.card SL(5, K) := h.trans (card_projSL_dvd 5 K)
    have hne : Nat.card SL(5, K) ≠ 0 := Nat.card_pos.ne'
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h1
    rw [factorization_card_SL_five hK] at this
    omega
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  refine not_weaklyClosed_of_sylow_witness (2 * a) Q hQcard hS (fun u hu huo => ?_) hz
  obtain ⟨⟨A, B⟩, -, rfl⟩ := Subgroup.mem_map.mp hu
  have hord : orderOf ((A, B) : SL(2, K) × SL(2, K)) = 3 := by
    rw [← orderOf_injective φ hinj]
    exact huo
  have h3AB : ((A, B) : SL(2, K) × SL(2, K)) ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hne : ((A, B) : SL(2, K) × SL(2, K)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  refine exists_witness_prod φ hinj (projCover5 swapSL) (fun A B => ?_)
    (fun A hA3 hA1 => Res424Seven.exists_conj_eq_inv_sl2 h3 hA3 hA1)
    (by simpa using congrArg Prod.fst h3AB) (by simpa using congrArg Prod.snd h3AB) hne
  simp only [hφ, MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ (swapSL_conj A B)

theorem map_trace_eq_of_fix (σ : K ≃+* K) (H : GL (Fin 5) K) {X : SL(5, K)} {N : ℕ}
    (hN : Nat.Coprime N 5) (hXN : X ^ N = 1)
    (h : (conjAut 5 K H * fieldAut 5 K σ * (conjAut 5 K H)⁻¹) (proj 5 K X) = proj 5 K X) :
    σ (X : Matrix (Fin 5) (Fin 5) K).trace = (X : Matrix (Fin 5) (Fin 5) K).trace := by
  obtain ⟨Y, hY⟩ : ∃ Y : SL(5, K), Y =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 5 K H⁻¹ X :=
    ⟨_, rfl⟩
  have hPY : ((conjAut 5 K H)⁻¹ : MulAut (projectiveSL 5 K)) (proj 5 K X) = proj 5 K Y := by
    rw [← map_inv, conjAut_proj, hY]
  have h1 : fieldAut 5 K σ (proj 5 K Y) = proj 5 K Y := by
    apply (conjAut 5 K H).injective
    rw [← hPY, MulAut.apply_inv_self]
    simpa only [MulAut.mul_apply] using h
  rw [fieldAut_proj, proj_eq_proj_iff] at h1
  obtain ⟨c, hc5, hc⟩ := mem_scalars.mp h1
  have hYN : Y ^ N = 1 := by rw [hY, ← map_pow, hXN, map_one]
  have hAN : (SpecialLinearGroup.map σ.toRingHom Y) ^ N = 1 := by rw [← map_pow, hYN, map_one]
  have hcomm : Commute (SpecialLinearGroup.map σ.toRingHom Y)
      ((SpecialLinearGroup.map σ.toRingHom Y)⁻¹ * Y) :=
    Subgroup.mem_center_iff.mp (scalars_le_center 5 K h1) _
  have hZN : ((SpecialLinearGroup.map σ.toRingHom Y)⁻¹ * Y) ^ N = 1 := by
    have e := congrArg (· ^ N) (mul_inv_cancel_left (SpecialLinearGroup.map σ.toRingHom Y) Y)
    simp only [hcomm.mul_pow, hAN, hYN, one_mul] at e
    exact e
  have hZ5 : ((SpecialLinearGroup.map σ.toRingHom Y)⁻¹ * Y) ^ 5 = 1 := by
    have e : ((((SpecialLinearGroup.map σ.toRingHom Y)⁻¹ * Y) ^ 5 : SL(5, K)) :
        Matrix (Fin 5) (Fin 5) K) = 1 := by
      change ((((SpecialLinearGroup.map σ.toRingHom Y)⁻¹ * Y : SL(5, K)) :
        Matrix (Fin 5) (Fin 5) K)) ^ 5 = 1
      rw [hc, ← map_pow, ← Units.val_pow_eq_pow_val, hc5, Units.val_one, map_one]
    exact Subtype.ext e
  have hAY : SpecialLinearGroup.map σ.toRingHom Y = Y :=
    inv_mul_eq_one.mp ((pow_eq_one_iff_of_coprime hN).mp ⟨hZN, hZ5⟩)
  have hmat : (Y : Matrix (Fin 5) (Fin 5) K).map σ = Y := by
    have := congrArg (fun g : SL(5, K) => (g : Matrix (Fin 5) (Fin 5) K)) hAY
    simpa [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using this
  have htr : (Y : Matrix (Fin 5) (Fin 5) K).trace = (X : Matrix (Fin 5) (Fin 5) K).trace := by
    rw [hY, coe_slConjugation, inv_inv, Matrix.trace_mul_cycle, Units.mul_inv, one_mul]
  rw [← htr, AddMonoidHom.map_trace, hmat]

theorem pow_sub_one_or_pow_add_one_eq_one {L : Type} [Field L] [Algebra K L] {p : ℕ}
    [Fact p.Prime] [CharP L p] (k : ℕ) (ζ : Lˣ) {s : K}
    (hrel : (ζ : L) ^ 2 - algebraMap K L s * ζ + 1 = 0) (hs : s ^ p ^ k = s) :
    ζ ^ (p ^ k - 1) = 1 ∨ ζ ^ (p ^ k + 1) = 1 := by
  have hp : p.Prime := Fact.out
  have hrel' := congrArg (iterateFrobenius L p k) hrel
  rw [map_add, map_sub, map_mul, map_pow, map_one, map_zero] at hrel'
  simp only [iterateFrobenius_def] at hrel'
  have hsL : algebraMap K L s ^ p ^ k = algebraMap K L s := by rw [← map_pow, hs]
  rw [hsL] at hrel'
  have hu : (ζ : L) * ((ζ⁻¹ : Lˣ) : L) = 1 := Units.mul_inv ζ
  have hprod : ((ζ : L) ^ p ^ k - ζ) * ((ζ : L) ^ p ^ k - ((ζ⁻¹ : Lˣ) : L)) = 0 := by
    linear_combination hrel' - (ζ : L) ^ p ^ k * ((ζ⁻¹ : Lˣ) : L) * hrel +
      ((ζ : L) ^ p ^ k * ((ζ : L) - algebraMap K L s) + 1) * hu
  rcases mul_eq_zero.mp hprod with h | h
  · left
    have h2 : ζ ^ p ^ k = ζ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact sub_eq_zero.mp h)
    rw [← Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos : 1 ≤ p ^ k), pow_succ] at h2
    exact mul_right_cancel (h2.trans (one_mul ζ).symm)
  · right
    have h2 : ζ ^ p ^ k = ζ⁻¹ :=
      Units.ext (by rw [Units.val_pow_eq_pow_val]; exact sub_eq_zero.mp h)
    rw [pow_succ, h2, inv_mul_cancel]

theorem exists_sl2_trace_pow_ne [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {k : ℕ}
    (hk : 1 ≤ k) (hK : Nat.card K = (p ^ k) ^ 3) (hmod : p ^ k % 3 = 2) :
    ∃ (j : ℕ) (t : SL(2, K)), t ^ (3 ^ j) = 1 ∧
      (t : Matrix (Fin 2) (Fin 2) K).trace ^ p ^ k ≠ (t : Matrix (Fin 2) (Fin 2) K).trace := by
  have hp : p.Prime := Fact.out
  have hq1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  have hq2 : 2 ≤ p ^ k := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hm0 : 0 < (p ^ k) ^ 2 - 1 := by
    have : 4 ≤ (p ^ k) ^ 2 := by nlinarith
    omega
  have hm3 : ((p ^ k) ^ 2 - 1) % 3 = 0 := by
    have : (p ^ k) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hmod]
    omega
  have hL : Nat.card (FiniteField.Extension K p 2) = ((p ^ k) ^ 2 - 1 + 1) ^ 3 := by
    rw [FiniteField.natCard_extension, hK, Nat.sub_add_cancel (by omega : 1 ≤ (p ^ k) ^ 2)]
    ring
  obtain ⟨ζ, hζ⟩ := Z3Field.exists_unit_orderOf_three_pow hL hm3 hm0
  obtain ⟨v, hv⟩ : ∃ v, v = padicValNat 3 ((p ^ k) ^ 2 - 1) := ⟨_, rfl⟩
  rw [← hv] at hζ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : FiniteField.Extension K p 2 →ₐ[K] Matrix (Fin 2) (Fin 2) K,
      Function.Injective ρ :=
    ⟨_, Algebra.leftMulMatrix_injective
      (Module.finBasisOfFinrankEq K _ (FiniteField.finrank_extension K p 2))⟩
  have hζN : ζ ^ (3 ^ (v + 1)) = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have htN : ρ (ζ : FiniteField.Extension K p 2) ^ (3 ^ (v + 1)) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hζN, Units.val_one, map_one]
  have hdet : (ρ (ζ : FiniteField.Extension K p 2)).det = 1 := by
    have h1 : (ρ (ζ : FiniteField.Extension K p 2)).det ^ (3 ^ (v + 1)) = 1 := by
      rw [← Matrix.det_pow, htN, Matrix.det_one]
    have h0 : (ρ (ζ : FiniteField.Extension K p 2)).det ≠ 0 := by
      intro h0
      have h' := congrArg Matrix.det (show ρ (ζ : FiniteField.Extension K p 2) *
          ρ ((ζ⁻¹ : (FiniteField.Extension K p 2)ˣ) : FiniteField.Extension K p 2) = 1 by
        rw [← map_mul, Units.mul_inv, map_one])
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h'
      exact zero_ne_one h'
    have := Fintype.ofFinite K
    have h2 : (ρ (ζ : FiniteField.Extension K p 2)).det ^ (Nat.card K - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ h0
    have hcop : Nat.Coprime (3 ^ (v + 1)) (Nat.card K - 1) := by
      refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
      have : (p ^ k) ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hmod]
      omega
    exact (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, h2⟩
  let t : SL(2, K) := ⟨ρ (ζ : FiniteField.Extension K p 2), hdet⟩
  have htN' : ((t ^ (3 ^ (v + 1)) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    change ρ (ζ : FiniteField.Extension K p 2) ^ (3 ^ (v + 1)) = 1
    exact htN
  refine ⟨v + 1, t, Subtype.ext htN', fun hs => ?_⟩
  change (ρ (ζ : FiniteField.Extension K p 2)).trace ^ p ^ k =
    (ρ (ζ : FiniteField.Extension K p 2)).trace at hs
  have hrel : (ζ : FiniteField.Extension K p 2) ^ 2 -
      algebraMap K _ (ρ (ζ : FiniteField.Extension K p 2)).trace * ζ + 1 = 0 := by
    apply hρ
    rw [map_zero, map_add, map_sub, map_mul, map_pow, AlgHom.commutes, map_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two, hdet, one_smul]
    abel
  haveI : CharP (FiniteField.Extension K p 2) p :=
    charP_of_injective_algebraMap (algebraMap K _).injective p
  rcases pow_sub_one_or_pow_add_one_eq_one k ζ hrel hs with h | h
  · have h3 := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at h3
    have : 3 ∣ p ^ k - 1 := (dvd_pow_self 3 (Nat.succ_ne_zero v)).trans h3
    omega
  · have h3 := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at h3
    have hfac : (p ^ k) ^ 2 - 1 = (p ^ k + 1) * (p ^ k - 1) := by
      have h4 : 1 ≤ (p ^ k) ^ 2 := by omega
      zify [hq1, h4]
      ring
    have := Z3Field.not_three_pow_succ_dvd hm0
    rw [← hv] at this
    exact this (h3.trans ⟨p ^ k - 1, hfac⟩)

theorem pow_eq_of_map_eq [Finite K] {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hK : Nat.card K = p ^ (3 * k)) {σ : K ≃+* K} (hσ : orderOf σ = 3) {s : K}
    (hs : σ s = s) : s ^ p ^ k = s := by
  obtain ⟨-, h1 | h1⟩ := eq_frobenius_pow_of_orderOf_eq_three hp (by omega) hK hσ
  · have e : 3 * k / 3 = k := by omega
    rw [h1 s, e] at hs
    exact hs
  · have e : 2 * (3 * k) / 3 = 2 * k := by omega
    have h2 : s ^ p ^ (2 * k) = s := by rw [← e, ← h1 s, hs]
    have := Fintype.ofFinite K
    have h3 : s ^ p ^ (3 * k) = s := by
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card s
    calc s ^ p ^ k = (s ^ p ^ (2 * k)) ^ p ^ k := by rw [h2]
      _ = s := by rw [← pow_mul, ← pow_add, show 2 * k + k = 3 * k by ring, h3]

theorem outerRow_projectiveSL_five_of_mod_two [Finite K] [Finite (projectiveSL 5 K)] {p e : ℕ}
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = p ^ e) (he : 1 ≤ e) (h2 : p ^ e % 3 = 2) :
    OuterRow (projectiveSL 5 K) := by
  have hp : p.Prime := Fact.out
  have h35 : ¬ (3 ∣ 5 ∧ 3 ∣ Nat.card K - 1) := fun h => absurd h.1 (by norm_num)
  by_cases h3e : 3 ∣ e
  · obtain ⟨k, rfl⟩ := h3e
    have hk : 1 ≤ k := by omega
    have hmod : p ^ k % 3 = 2 := by
      have h' : (p ^ k) ^ 3 % 3 = 2 := by rw [← pow_mul, mul_comm]; exact h2
      rw [Nat.pow_mod] at h'
      rcases (by omega : p ^ k % 3 = 0 ∨ p ^ k % 3 = 1 ∨ p ^ k % 3 = 2) with h0 | h0 | h0
      · rw [h0] at h'; norm_num at h'
      · rw [h0] at h'; norm_num at h'
      · exact h0
    have hK' : Nat.card K = (p ^ k) ^ 3 := by rw [hK, ← pow_mul, mul_comm]
    obtain ⟨j, t, htN, htr⟩ := exists_sl2_trace_pow_ne hk hK' hmod
    have hXN : blkSL t 1 ^ (3 ^ j) = 1 := by
      rw [show blkSL t 1 = blkHom (t, 1) from rfl, ← map_pow, Prod.pow_mk, htN, one_pow]
      exact map_one _
    have hR : IsPGroup 3 (Subgroup.zpowers (proj 5 K (blkSL t 1))) :=
      Z3Field.isPGroup_zpowers_of_pow_eq_one (by rw [← map_pow, hXN, map_one])
    have hZ : Subgroup.center (projectiveSL 5 K) = ⊥ :=
      CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)
    refine r2_outerRow hZ hR fun τ hτ hout hfix => ?_
    by_cases hD : τ ∈ linearAutGroup 5 K
    · exact hout (Sec21.Item223CensusProof.isInnerAut_of_mem_linearAutGroup_of_pow_three
        (by norm_num) h35 hD hτ)
    obtain ⟨σ, hσ, H, rfl⟩ := linear_order_three_field_descent (by norm_num) τ hτ hD
    have h1 := map_trace_eq_of_fix σ H (Nat.Coprime.pow_left _ (by norm_num)) hXN
      (hfix _ (Subgroup.mem_zpowers _))
    have h2' : ((blkSL t 1 : SL(5, K)) : Matrix (Fin 5) (Fin 5) K).trace =
        (t : Matrix (Fin 2) (Fin 2) K).trace + 3 :=
      trace_blk_one _
    rw [h2', map_add, map_ofNat, add_left_inj] at h1
    exact htr (pow_eq_of_map_eq hp hk hK hσ h1)
  · intro _ σ hσ hout _
    by_cases hD : σ ∈ linearAutGroup 5 K
    · exact hout (Sec21.Item223CensusProof.isInnerAut_of_mem_linearAutGroup_of_pow_three
        (by norm_num) h35 hD hσ)
    obtain ⟨τ, hτ, -⟩ := linear_order_three_field_descent (by norm_num) σ hσ hD
    exact h3e (eq_frobenius_pow_of_orderOf_eq_three hp he hK hτ).1

end L5Mod2

theorem listRowOf_projSL_five (p e : ℕ) [Fact p.Prime] (h : p ^ e % 3 = 2) :
    ListRowOf (projSL 5 (GaloisField p e)) := by
  intro S _ _ _ _ ⟨eS⟩
  have he : e ≠ 0 := by
    rintro rfl
    simp at h
  haveI : Finite (projSL 5 (GaloisField p e)) := Finite.of_equiv S eS.toEquiv
  have hK : Nat.card (GaloisField p e) % 3 = 2 := by
    rw [GaloisField.card p e he]
    exact h
  exact ListRow.of_mulEquiv eS.symm (L5Mod2.listRow_projSL_five_of_mod_two hK)

theorem outerRowOf_projSL_five (p e : ℕ) [Fact p.Prime] (h : p ^ e % 3 = 2) :
    OuterRowOf (projSL 5 (GaloisField p e)) := by
  intro S _ _ _ _ ⟨eS⟩
  have he : e ≠ 0 := by
    rintro rfl
    simp at h
  haveI : Finite (projSL 5 (GaloisField p e)) := Finite.of_equiv S eS.toEquiv
  haveI : Finite (projectiveSL 5 (GaloisField p e)) :=
    Finite.of_equiv _ (KFacts.L34.projSLEquivProjectiveSL 5 (GaloisField p e)).toEquiv
  exact OuterRow.of_mulEquiv (eS.trans (KFacts.L34.projSLEquivProjectiveSL 5 _)).symm
    (L5Mod2.outerRow_projectiveSL_five_of_mod_two (GaloisField.card p e he)
      (Nat.one_le_iff_ne_zero.mpr he) h)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
