module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Fam
public import CFSG.Quasithin.SteinbergCDUnitaryThreeSylowSixteen
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix

namespace AutM12Recog

theorem excl_of_orderOf_sixteen {K : Type} [Group K] [Finite K] {g : K} {k : ℕ} (hk : 4 ≤ k)
    (hg : orderOf g = 2 ^ k) : Excl K := by
  intro T _ _ hT Q n N hQN hcard hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hg])
  obtain ⟨Q', hgQ'⟩ := hgp.exists_le_sylow
  let y : ↥(Q' : Subgroup K) := ⟨g, hgQ' (Subgroup.mem_zpowers g)⟩
  let z : ↥(Q : Subgroup K) := Sylow.equiv Q' Q y
  have hz : orderOf z = 2 ^ k := by
    rw [MulEquiv.orderOf_eq]
    show orderOf y = 2 ^ k
    rw [← hg, ← Subgroup.orderOf_coe]
  have h8 : z ^ 8 = 1 := hT.pow_eight_eq_one (embed _ N hQN) (embed_injective _ N hQN) z
  have h3 := orderOf_dvd_of_pow_eq_one h8
  rw [hz] at h3
  have h16 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem exists_orderOf_two_pow {G : Type*} [Group G] {W : Subgroup G} (hW : IsPGroup 2 W) {x : G}
    (hx : x ∈ W) (h8 : x ^ 8 ≠ 1) : ∃ k : ℕ, 4 ≤ k ∧ orderOf x = 2 ^ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hW) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  refine ⟨k, ?_, hk⟩
  by_contra hlt
  apply h8
  rw [← orderOf_dvd_iff_pow_eq_one, hk]
  have : k ≤ 3 := by omega
  calc 2 ^ k ∣ 2 ^ 3 := pow_dvd_pow 2 this
    _ = 8 := by norm_num

theorem exists_orderOf_two_pow_mk {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]
    (hZ : ∀ z ∈ Z, z ^ 3 = 1) {x : G} {k : ℕ} (hk : 4 ≤ k) (hx : orderOf x = 2 ^ k) :
    ∃ j : ℕ, 4 ≤ j ∧ orderOf (QuotientGroup.mk x : G ⧸ Z) = 2 ^ j := by
  have hdvd : orderOf (QuotientGroup.mk x : G ⧸ Z) ∣ 2 ^ k := by
    rw [← hx]
    exact orderOf_map_dvd (QuotientGroup.mk' Z) x
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨j, ?_, hjeq⟩
  have h1 : x ^ orderOf (QuotientGroup.mk x : G ⧸ Z) ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  have h2 : x ^ (orderOf (QuotientGroup.mk x : G ⧸ Z) * 3) = 1 := by
    rw [pow_mul]
    exact hZ _ h1
  have h3 : 2 ^ k ∣ orderOf (QuotientGroup.mk x : G ⧸ Z) * 3 := by
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one h2
  have h4 : 2 ^ k ∣ orderOf (QuotientGroup.mk x : G ⧸ Z) :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right h3
  rw [hjeq] at h4
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h4
  omega

theorem ordProj_two_eq {n a m : ℕ} (hm : Odd m) (h : n = 2 ^ a * m) : ordProj[2] n = 2 ^ a := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  rw [h, Nat.ordProj_mul 2 (by positivity) hm0, Nat.ordProj_self_pow Nat.prime_two,
    CFSG.LieType.Steinberg.ordProj_two_of_odd hm, mul_one]

theorem ordProj_two_eq_two {n : ℕ} (hn : n % 4 = 2) : ordProj[2] n = 2 := by
  obtain ⟨k, hk⟩ : ∃ k, n = 2 ^ 1 * (2 * k + 1) := ⟨n / 4, by omega⟩
  rw [ordProj_two_eq (by exact ⟨k, rfl⟩) hk]
  norm_num

theorem sixteen_le_mul_of_sq_mul {i j : ℕ} (hj : 1 ≤ j)
    (h : 64 ≤ (2 ^ i) ^ 2 * 2 ^ j) : 16 ≤ 2 ^ i * 2 ^ j := by
  by_contra hlt
  have hlt' := not_le.mp hlt
  have h1 : 2 ^ (i + j) < 2 ^ 4 := by rw [pow_add]; omega
  have e : (2 ^ i) ^ 2 * 2 ^ j = 2 ^ (i * 2 + j) := by rw [← pow_mul, ← pow_add]
  have h2 : 2 ^ 6 ≤ 2 ^ (i * 2 + j) := by rw [← e]; omega
  have h3 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  omega

theorem eight_le_of_two_mul_sq {j : ℕ} (h : 64 ≤ 2 * (2 ^ j) ^ 2) : 8 ≤ 2 ^ j := by
  by_contra hlt
  have hlt' := not_le.mp hlt
  have : j < 3 := by
    by_contra hj
    have hj' := not_lt.mp hj
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj'
    omega
  interval_cases j <;> omega

theorem two_pow_le_two_of_dvd {n d : ℕ} (hd : d ∣ 3) (h : 2 ^ n ∣ 2 * d) : 2 ^ n ≤ 2 := by
  have hcop : Nat.Coprime (2 ^ n) d :=
    Nat.Coprime.pow_left _ (by
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with rfl | rfl <;> decide)
  exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right h)

section BlockMatrices

variable {K : Type} [Field K]

@[expose] def blk (A : Matrix (Fin 2) (Fin 2) K) (d : K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, d]

theorem blk_mul (A B : Matrix (Fin 2) (Fin 2) K) (d e : K) :
    blk A d * blk B e = blk (A * B) (d * e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem det_blk (A : Matrix (Fin 2) (Fin 2) K) (d : K) : (blk A d).det = A.det * d := by
  simp [blk, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem blk_inj {A B : Matrix (Fin 2) (Fin 2) K} {d e : K} (h : blk A d = blk B e) :
    A = B ∧ d = e := by
  refine ⟨?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h (Fin.castSucc i)) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;> simpa [blk] using this
  · simpa [blk] using congrFun (congrFun h 2) 2

end BlockMatrices

section LinearElement

variable {K : Type} [Field K] [Finite K]

theorem exists_quadratic_extension (hK : ringChar K ≠ 2) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), Module.finrank K L = 2 ∧ Module.Finite K L := by
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hK
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C c : Polynomial K) := by
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    exact hc ⟨b, by rw [← hb]; ring⟩
  have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C c : Polynomial K)) := ⟨hirr⟩
  refine ⟨AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C c), inferInstance, inferInstance, ?_,
    (AdjoinRoot.powerBasis hirr.ne_zero).finite⟩
  rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    Polynomial.natDegree_X_pow_sub_C]

theorem ringChar_ne_two (hodd : Odd (Nat.card K)) : ringChar K ≠ 2 := by
  intro h2
  have hp : CharP K 2 := by rw [← h2]; exact ringChar.charP K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have h : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rw [h] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)

theorem exists_specialLinear_three_orderOf (hodd : Odd (Nat.card K)) :
    ∃ (g : SpecialLinearGroup (Fin 3) K) (k : ℕ),
      orderOf g = 2 ^ k ∧ 2 ^ k = ordProj[2] (Nat.card K ^ 2 - 1) := by
  obtain ⟨L, hL, hAlg, hrank, hfin⟩ := exists_quadratic_extension (K := K) (ringChar_ne_two hodd)
  have : Finite L := Module.finite_of_finite K
  have hcardL : Nat.card L = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hrank]
  have hcardU : Nat.card Lˣ = Nat.card K ^ 2 - 1 := by rw [Nat.card_units, hcardL]
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Lˣ)
  have hN0 : Nat.card Lˣ ≠ 0 := Nat.card_pos.ne'
  have hdvd : ordProj[2] (Nat.card Lˣ) ∣ Nat.card Lˣ := Nat.ordProj_dvd _ _
  have hdiv0 : Nat.card Lˣ / ordProj[2] (Nat.card Lˣ) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd) (Nat.ordProj_pos _ _)).ne'
  let ζ : Lˣ := γ ^ (Nat.card Lˣ / ordProj[2] (Nat.card Lˣ))
  have hζ : orderOf ζ = ordProj[2] (Nat.card Lˣ) := by
    rw [orderOf_pow_of_dvd hdiv0 (by rw [hγ]; exact Nat.div_dvd_of_dvd hdvd), hγ,
      Nat.div_div_self hdvd hN0]
  let b : Module.Basis (Fin 2) K L := Module.finBasisOfFinrankEq K L hrank
  let M : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix b (ζ : L)
  let n : K := Algebra.norm K (ζ : L)
  have hn : n ≠ 0 := Algebra.norm_ne_zero_iff.mpr ζ.ne_zero
  have hdet : M.det = n := (Algebra.norm_eq_matrix_det b (ζ : L)).symm
  let g : SpecialLinearGroup (Fin 3) K :=
    ⟨blk M n⁻¹, by rw [det_blk, hdet, mul_inv_cancel₀ hn]⟩
  have hpow : ∀ j : ℕ, (g ^ j).1 = blk (M ^ j) (n⁻¹ ^ j) := by
    intro j
    induction j with
    | zero =>
      show (1 : Matrix (Fin 3) (Fin 3) K) = blk (M ^ 0) (n⁻¹ ^ 0)
      rw [pow_zero, pow_zero, blk_one]
    | succ j ih =>
      calc (g ^ (j + 1)).1 = (g ^ j * g).1 := by rw [pow_succ]
        _ = (g ^ j).1 * g.1 := rfl
        _ = blk (M ^ j) (n⁻¹ ^ j) * blk M n⁻¹ := by rw [ih]
        _ = blk (M ^ j * M) (n⁻¹ ^ j * n⁻¹) := blk_mul _ _ _ _
        _ = blk (M ^ (j + 1)) (n⁻¹ ^ (j + 1)) := by rw [pow_succ, pow_succ]
  have hgj : ∀ j : ℕ, g ^ j = 1 ↔ (ζ : L) ^ j = 1 := by
    intro j
    constructor
    · intro h
      have h0 : (1 : Matrix (Fin 3) (Fin 3) K) = blk (M ^ j) (n⁻¹ ^ j) := by
        rw [← hpow j, h]
        rfl
      rw [← blk_one] at h0
      have h2 := (blk_inj h0).1
      have h3 : Algebra.leftMulMatrix b ((ζ : L) ^ j) = Algebra.leftMulMatrix b 1 := by
        rw [map_pow, map_one]
        exact h2.symm
      exact Algebra.leftMulMatrix_injective b h3
    · intro h
      apply Subtype.ext
      have h1 : M ^ j = 1 := by rw [← map_pow, h, map_one]
      have h2 : n ^ j = 1 := by
        show (Algebra.norm K (ζ : L)) ^ j = 1
        rw [← map_pow, h, map_one]
      show (g ^ j).1 = 1
      rw [hpow, h1, inv_pow, h2, inv_one]
      exact blk_one
  have horder : orderOf g = orderOf ζ := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      rw [hgj]
      have := congrArg Units.val (pow_orderOf_eq_one ζ)
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    · apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact (hgj _).mp (pow_orderOf_eq_one g)
  refine ⟨g, (Nat.card Lˣ).factorization 2, ?_, ?_⟩
  · rw [horder, hζ]
  · rw [hcardU]

end LinearElement

section LinearThree

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_orderOf_two_pow_projectiveSL {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (h16 : 16 ≤ ordProj[2] (Nat.card K ^ 2 - 1)) :
    ∃ x : projectiveSL 3 K, ∃ j : ℕ, 4 ≤ j ∧ orderOf x = 2 ^ j := by
  obtain ⟨g, k, hg, hk⟩ := exists_specialLinear_three_orderOf hodd
  have hk4 : 4 ≤ k := by
    rw [← hk] at h16
    have : 2 ^ 4 ≤ 2 ^ k := by simpa using h16
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  obtain ⟨j, hj, hord⟩ := exists_orderOf_two_pow_mk (Z := scalars 3 K)
    (fun z hz => CFSG.Quasithin.SteinbergCD.pow_three_eq_one_of_mem_scalars hz) hk4 hg
  exact ⟨QuotientGroup.mk g, j, hj, hord⟩

theorem one_le_factorization_two {n : ℕ} (hn : n ≠ 0) (h2 : 2 ∣ n) : 1 ≤ n.factorization 2 :=
  Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn h2

theorem ordProj_two_sq_sub_one {p : ℕ} (hp : 1 < p) :
    ordProj[2] (p ^ 2 - 1) = ordProj[2] (p - 1) * ordProj[2] (p + 1) := by
  have e1 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hp
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [e1, Nat.ordProj_mul 2 (by omega) (by omega)]

theorem excl_psl_three_odd {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : StatedClassicalModel S .PSL 3 p 1) : Excl S := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hS := h
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hKodd : Odd (Nat.card K) := by rw [hK, pow_one]; exact hodd
  let e' : S ≃* projectiveSL 3 K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have hP : ordProj[2] (Nat.card S) = ordProj[2] (p - 1) ^ 2 * ordProj[2] (p + 1) := by
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Quasithin.SteinbergCD.ordProj_two_card_projectiveSL_three hKodd, hK, pow_one]
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (τ := .PSL) (Or.inl rfl) (n := 3) (ℓ := p) (f := 1) (by norm_num) hp le_rfl hS).1
  have hAut : ∀ n : ℕ, Nat.card S * 2 ^ n ∣ Nat.card (MulAut S) → 2 ^ n ≤ 2 := by
    intro n hn
    have h2 := (dvd_card_outer_of_dvd_card_mulAut hn).trans hout
    have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSL 3 (p ^ 1) ∣ 3 :=
      Nat.gcd_dvd_left _ _
    have h3 : 2 ^ n ∣ 2 * CFSG.RankThree.OuterOrder.determinantParameter .PSL 3 (p ^ 1) := by
      simpa using h2
    exact two_pow_le_two_of_dvd hd h3
  have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd hS0
  have hPa : ordProj[2] (Nat.card S) = 2 ^ a := ordProj_two_eq hm hcard
  by_cases ha : a ≤ 5
  · refine excl_of_aut_le (c := 2) ⟨m, hm, hcard⟩ (by omega) ?_ hAut
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (7 - a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  ·
    have h64 : 64 ≤ ordProj[2] (p - 1) ^ 2 * ordProj[2] (p + 1) := by
      rw [← hP, hPa]
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hj1 : 1 ≤ (p + 1).factorization 2 :=
      one_le_factorization_two (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩)
    have h16' : 16 ≤ ordProj[2] (p - 1) * ordProj[2] (p + 1) :=
      sixteen_le_mul_of_sq_mul hj1 h64
    have h16 : 16 ≤ ordProj[2] (Nat.card K ^ 2 - 1) := by
      rw [hK, pow_one, ordProj_two_sq_sub_one hp.one_lt]
      exact h16'
    obtain ⟨x, j, hj, hx⟩ := exists_orderOf_two_pow_projectiveSL hKodd h16
    exact excl_of_orderOf_sixteen (g := e'.symm x) hj (by rw [MulEquiv.orderOf_eq, hx])

end LinearThree

section UnitaryThree

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.SteinbergCD

variable {p : ℕ} {K : Type} [Field K]

theorem exists_orderOf_two_pow_unitaryPSU (h : UnitaryFieldData p 1 K) (hp2 : p ≠ 2)
    (h64 : 64 ≤ ordProj[2] (Nat.card (unitaryPSU h 3))) :
    ∃ x : unitaryPSU h 3, ∃ j : ℕ, 4 ≤ j ∧ orderOf x = 2 ^ j := by
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [det_one]; exact one_ne_zero
  obtain ⟨⟨P, hP⟩, -, -, -, h3, h1⟩ := odd_unitary_three_exact_coordinate_and_Sylow_models h hp2
    (bar_one_apply h) hdet (⊥ : Subgroup (SUgram h.bar (1 : Matrix (Fin 3) (Fin 3) K))) bot_le
  have hodd : Odd p := h.prime.odd_of_ne_two hp2
  have hP64 : 64 ≤ ordProj[2] (p - 1) * ordProj[2] (p + 1) ^ 2 := by
    rw [ordProj_two_card_unitaryPSU_three h hp2, pow_one] at h64
    exact h64
  have key : ∃ g : SUgram h.bar (1 : Matrix (Fin 3) (Fin 3) K), ∃ k : ℕ, 4 ≤ k ∧
      orderOf g = 2 ^ k := by
    have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
      rcases hodd with ⟨m, hm⟩
      omega
    rcases hmod with hq | hq
    ·
      obtain ⟨⟨z, hz⟩, ⟨M, hM⟩, hmodel⟩ := h1 (by rw [pow_one]; exact hq)
      obtain ⟨u, τ, -, -, hou, -⟩ := hmodel M hM z hz
      have hs : ordProj[2] (p + 1) = 2 := ordProj_two_eq_two (by omega)
      rw [hs] at hP64
      have hr : 16 ≤ ordProj[2] (p - 1) := by omega
      rw [pow_one] at hou
      refine ⟨u, (p - 1).factorization 2 + 1, ?_, ?_⟩
      · have : 2 ^ 4 ≤ 2 ^ (p - 1).factorization 2 := by simpa using hr
        have := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
        omega
      · rw [hou, pow_succ, mul_comm]
    ·
      obtain ⟨⟨l, hl, hlo⟩, hmodel⟩ := h3 (by rw [pow_one]; exact hq)
      obtain ⟨u, v, τ, -, -, -, hvu, huv, hou, hov, hτ2, -, -, hinj, -, hpg, -, -, -, -⟩ :=
        hmodel P hP l hl hlo
      have hr : ordProj[2] (p - 1) = 2 := ordProj_two_eq_two (by omega)
      rw [hr] at hP64
      have hs8 : 8 ≤ ordProj[2] (p + 1) := eight_le_of_two_mul_sq hP64
      rw [pow_one] at hou
      have hττ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left (by rw [← sq, hτ2])
      rw [hττ] at hvu
      have hg2 : (u * τ) * (u * τ) = u * v := by
        rw [hvu]
        group
      have hg8 : (u * τ) ^ 8 = u ^ 4 * v ^ 4 := by
        have : (u * τ) ^ 8 = ((u * τ) * (u * τ)) ^ 4 := by
          rw [← sq, ← pow_mul]
        rw [this, hg2, huv.mul_pow]
      have hne : (u * τ) ^ 8 ≠ 1 := by
        rw [hg8]
        intro h41
        have h4s : 4 < ordProj[2] (p ^ 1 + 1) := by rw [pow_one]; omega
        have := @hinj (⟨4, h4s⟩, ⟨4, h4s⟩, ⟨0, by norm_num⟩) (0, 0, 0) (by
          simp [h41])
        have h4 := congrArg (fun x : Fin (ordProj[2] (p ^ 1 + 1)) ×
          Fin (ordProj[2] (p ^ 1 + 1)) × Fin 2 => (x.1 : ℕ)) this
        simp at h4
      have hmem : u * τ ∈ Subgroup.closure {u, v, τ} :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      obtain ⟨k, hk, hk'⟩ := exists_orderOf_two_pow hpg hmem hne
      exact ⟨u * τ, k, hk, hk'⟩
  obtain ⟨g, k, hk, hg⟩ := key
  let e₀ := MulEquiv.subgroupCongr (SUgram_one_eq_unitarySU h)
  have hg' : orderOf (e₀ g) = 2 ^ k := by rw [MulEquiv.orderOf_eq, hg]
  obtain ⟨j, hj, hord⟩ := exists_orderOf_two_pow_mk (Z := unitaryScalars h 3)
    (fun z hz => pow_three_eq_one_of_mem_unitaryScalars h hz) hk hg'
  exact ⟨QuotientGroup.mk (e₀ g), j, hj, hord⟩

end UnitaryThree

theorem excl_psu_three_odd {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : StatedClassicalModel S .PSU 3 p 1) : Excl S := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hS := h
  obtain ⟨⟨-, -, hadm⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 K :=
    ⟨hp, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  let e' : S ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm
  have hP : ordProj[2] (Nat.card S) = ordProj[2] (p - 1) * ordProj[2] (p + 1) ^ 2 := by
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Quasithin.SteinbergCD.ordProj_two_card_unitaryPSU_three hU hp2, pow_one]
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (τ := .PSU) (Or.inr rfl) (n := 3) (ℓ := p) (f := 1) (by norm_num) hp le_rfl hS).1
  have hAut : ∀ n : ℕ, Nat.card S * 2 ^ n ∣ Nat.card (MulAut S) → 2 ^ n ≤ 2 := by
    intro n hn
    have h2 := (dvd_card_outer_of_dvd_card_mulAut hn).trans hout
    have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (p ^ 1) ∣ 3 :=
      Nat.gcd_dvd_left _ _
    have h3 : 2 ^ n ∣ 2 * CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (p ^ 1) := by
      simpa using h2
    exact two_pow_le_two_of_dvd hd h3
  have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd hS0
  have hPa : ordProj[2] (Nat.card S) = 2 ^ a := ordProj_two_eq hm hcard
  by_cases ha : a ≤ 5
  · refine excl_of_aut_le (c := 2) ⟨m, hm, hcard⟩ (by omega) ?_ hAut
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (7 - a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h64 : 64 ≤ ordProj[2] (Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3)) := by
      rw [← Nat.card_congr e'.toEquiv, hPa]
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨x, j, hj, hx⟩ := exists_orderOf_two_pow_unitaryPSU hU hp2 h64
    exact excl_of_orderOf_sixteen (g := e'.symm x) hj (by rw [MulEquiv.orderOf_eq, hx])

end AutM12Recog

end CFSG.Quasithin.F6
