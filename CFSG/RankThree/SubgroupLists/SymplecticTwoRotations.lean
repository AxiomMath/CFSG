module

public import CFSG.RankThree.SubgroupLists.SymplecticPlusBlock
public import CFSG.RankThree.SubgroupLists.SymplecticPartThreeBase
public import CFSG.RankThree.SubgroupLists.MitchellDickson
public import CFSG.RankThree.SubgroupLists.SymplecticSkewElations
public import Certificates.Certificate43
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Maximal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem exists_pow_eq_smul_add {X : Matrix V₄ V₄ K} {β : K}
    (hX : X * X = (2 * β) • X - 1) (k : ℕ) : ∃ a b : K, X ^ k = a • (1 : Matrix V₄ V₄ K) + b •
        X := by
  induction k with
  | zero => exact ⟨1, 0, by simp⟩
  | succ k ih =>
    obtain ⟨a, b, hab⟩ := ih
    refine ⟨-b, a + 2 * β * b, ?_⟩
    rw [pow_succ, hab, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, hX]
    module

theorem plusBlock_add (A B : Matrix V₄ V₄ K) : plusBlock (A + B) = plusBlock A + plusBlock B := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [plusBlock]

theorem plusBlock_smul (c : K) (A : Matrix V₄ V₄ K) : plusBlock (c • A) = c • plusBlock A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [plusBlock]

theorem plusBlock_sub (A B : Matrix V₄ V₄ K) : plusBlock (A - B) = plusBlock A - plusBlock B := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [plusBlock]

theorem plusBlock_pow (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K} (hM : M * tStdMat = tStdMat * M)
    (k : ℕ) : plusBlock (M ^ k) = plusBlock M ^ k := by
  induction k with
  | zero => simp [plusBlock_one]
  | succ k ih =>
    have hMk : M ^ k * tStdMat = tStdMat * M ^ k := (Commute.pow_left (hM : Commute M tStdMat) k).eq
    rw [pow_succ, plusBlock_mul h2 hMk hM, ih, pow_succ]

section Finite

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def plusImage (h2 : (2 : K) ≠ 0) (G : Subgroup (GL V₄ K)) :
    Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
  ((G.subgroupOf (stdCent K)).map (plusHom h2)).map
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))

@[expose] noncomputable def plusBar (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)} {x : GL V₄ K}
    (hxG : x ∈ G) (hxC : x ∈ stdCent K) : plusImage h2 G :=
  ⟨QuotientGroup.mk' _ (plusHom h2 ⟨x, hxC⟩),
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (show (⟨x, hxC⟩ : stdCent K) ∈
      G.subgroupOf (stdCent K) from hxG))⟩

theorem plusBar_mul (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)} {x y : GL V₄ K}
    (hxG : x ∈ G) (hxC : x ∈ stdCent K) (hyG : y ∈ G) (hyC : y ∈ stdCent K) :
    plusBar h2 hxG hxC * plusBar h2 hyG hyC = plusBar h2 (G.mul_mem hxG hyG) (mul_mem hxC hyC) := by
  apply Subtype.ext
  simp only [plusBar, Subgroup.coe_mul, ← map_mul]
  rfl

theorem plusBar_pow (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)} {x : GL V₄ K}
    (hxG : x ∈ G) (hxC : x ∈ stdCent K) (k : ℕ) :
    plusBar h2 hxG hxC ^ k = plusBar h2 (G.pow_mem hxG k) (pow_mem hxC k) := by
  apply Subtype.ext
  simp only [plusBar, SubgroupClass.coe_pow, ← map_pow]
  rfl

theorem plusBar_eq_one_iff (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)} {x : GL V₄ K}
    (hxG : x ∈ G) (hxC : x ∈ stdCent K) :
    plusBar h2 hxG hxC = 1 ↔ plusBlock (x : Matrix V₄ V₄ K) = 1 ∨
      plusBlock (x : Matrix V₄ V₄ K) = -1 := by
  have e1 : plusBar h2 hxG hxC = 1 ↔
      QuotientGroup.mk' (Subgroup.center SL(2, K)) (plusHom h2 ⟨x, hxC⟩) = 1 := by
    rw [Subtype.ext_iff]
    rfl
  rw [e1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hrx⟩
    have hx : Matrix.scalar (Fin 2) r = plusBlock (x : Matrix V₄ V₄ K) := by
      rw [hrx, coe_plusHom]
    have hr2 : (r - 1) * (r + 1) = 0 := by
      simp only [Fintype.card_fin] at hr
      linear_combination hr
    rcases mul_eq_zero.mp hr2 with h | h
    · left
      rw [← hx, show r = 1 by linear_combination h]
      simp
    · right
      rw [← hx, show r = -1 by linear_combination h]
      ext i j; fin_cases i <;> fin_cases j <;> simp
  · rintro (h | h)
    · refine ⟨1, by simp, ?_⟩
      rw [coe_plusHom, h]
      simp
    · refine ⟨-1, by simp, ?_⟩
      rw [coe_plusHom, h]
      ext i j; fin_cases i <;> fin_cases j <;> simp

variable (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
  (hneg : (-1 : GL V₄ K) ∈ G)
include hp2 hU0 hneg

theorem pow_eq_one_or_neg_of_plusBar {x : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ stdCent K)
    {β : K} (hx : (x : Matrix V₄ V₄ K) * x = (2 * β) • (x : Matrix V₄ V₄ K) - 1)
    (hx1 : x ≠ 1) (hxm : x ≠ -1) {k : ℕ}
    (hk : plusBar (two_ne_zero_of_charP hp2) hxG hxC ^ k = 1) : x ^ k = 1 ∨ x ^ k = -1 := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  have hxt := (mem_stdCent.mp hxC).2
  rw [plusBar_pow, plusBar_eq_one_iff] at hk
  simp only [Units.val_pow_eq_pow_val] at hk
  rw [plusBlock_pow h2 hxt] at hk
  obtain ⟨a, b, hab⟩ := exists_pow_eq_smul_add hx k
  have hpk : plusBlock (x : Matrix V₄ V₄ K) ^ k =
      a • (1 : Matrix (Fin 2) (Fin 2) K) + b • plusBlock (x : Matrix V₄ V₄ K) := by
    rw [← plusBlock_pow h2 hxt, hab, plusBlock_add, plusBlock_smul, plusBlock_smul, plusBlock_one]
  have hnsc : ∀ c : K, plusBlock (x : Matrix V₄ V₄ K) ≠ c • 1 := by
    intro c hc
    have hdet := det_plusBlock h2 (mem_stdCent.mp hxC).1 hxt
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    have hsq := congrArg plusBlock hx
    rw [plusBlock_mul h2 hxt hxt, plusBlock_sub, plusBlock_smul, plusBlock_one, hc] at hsq
    have hsq' := congrFun (congrFun hsq 0) 0
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hsq'
    have hβ : β = c := by
      have : (2 : K) * (β - c) = 0 := by linear_combination (-2 * β + c) * hdet - c * hsq'
      have := (mul_eq_zero.mp this).resolve_left h2
      linear_combination this
    have hc' : (c - 1) * (c + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp hc' with hc1 | hc1
    · apply hx1
      refine hU0 x hxG ?_
      rw [IsSqZero]
      have : ((x : Matrix V₄ V₄ K) - 1) * ((x : Matrix V₄ V₄ K) - 1) =
          (x : Matrix V₄ V₄ K) * x - (2 : K) • (x : Matrix V₄ V₄ K) + 1 := by
        rw [two_smul]; noncomm_ring
      rw [this, hx, hβ, show c = 1 by linear_combination hc1]
      simp only [mul_one]
      abel
    · apply hxm
      have hmG : -x ∈ G := by
        rw [show -x = -1 * x by simp]
        exact G.mul_mem hneg hxG
      have h1 := hU0 (-x) hmG (by
        rw [IsSqZero, Units.val_neg]
        have : (-(x : Matrix V₄ V₄ K) - 1) * (-(x : Matrix V₄ V₄ K) - 1) =
            (x : Matrix V₄ V₄ K) * x + (2 : K) • (x : Matrix V₄ V₄ K) + 1 := by
          rw [two_smul]; noncomm_ring
        rw [this, hx, hβ, show c = -1 by linear_combination hc1]
        simp only [mul_neg, mul_one, neg_smul]
        abel)
      rw [← neg_neg x, h1]
  have hcases : ∀ ε : K, plusBlock (x : Matrix V₄ V₄ K) ^ k = ε • 1 →
      (x : Matrix V₄ V₄ K) ^ k = ε • 1 := by
    intro ε hε
    rw [hpk] at hε
    by_cases hb : b = 0
    · rw [hb, zero_smul, add_zero] at hε
      have ha : a = ε := by
        have := congrFun (congrFun hε 0) 0
        simpa using this
      rw [hab, hb, zero_smul, add_zero, ha]
    · exfalso
      apply hnsc (b⁻¹ * (ε - a))
      have : b • plusBlock (x : Matrix V₄ V₄ K) = (ε - a) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [sub_smul, ← hε]; abel
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ hb, one_smul]
  rcases hk with hk | hk
  · left
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hcases 1 (by rw [hk, one_smul]), one_smul, Units.val_one]
  · right
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hcases (-1) (by rw [hk, neg_one_smul]), neg_one_smul,
      Units.val_neg, Units.val_one]

theorem not_dvd_card_plusImage : ¬ p ∣ Nat.card (plusImage (two_ne_zero_of_charP hp2) G) := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  intro hdvd
  set C := G.subgroupOf (stdCent K)
  have hC : ¬ p ∣ Nat.card C := by
    intro hpC
    have : Fact p.Prime := inferInstance
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hpC
    have hcG : ((c : stdCent K) : GL V₄ K) ∈ G := c.2
    have hct := (mem_stdCent.mp (c : stdCent K).2).2
    have hcomm : ((c : stdCent K) : GL V₄ K) * tStd = tStd * ((c : stdCent K) : GL V₄ K) :=
      Units.ext (by simpa [coe_tStd] using hct)
    have hord : orderOf ((c : stdCent K) : GL V₄ K) = p := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
    exact not_dvd_orderOf_of_commute hp2 hU0 (isNCInv_tStd h2) hcG hcomm (by rw [hord])
  apply hC
  refine dvd_trans hdvd (dvd_trans (Subgroup.card_map_dvd _ _) (Subgroup.card_map_dvd _ _))

theorem two_lt_orderOf_plusBar_of {x : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ stdCent K)
    {β : K} (hx : (x : Matrix V₄ V₄ K) * x = (2 * β) • (x : Matrix V₄ V₄ K) - 1) {m : ℕ}
    (hxm : ∀ k, 1 ≤ k → k < m → x ^ k ≠ 1 ∧ x ^ k ≠ -1) (hm : 2 ≤ m) :
    m ≤ orderOf (plusBar (two_ne_zero_of_charP hp2) hxG hxC) := by
  have hx1 := hxm 1 le_rfl (by omega)
  rw [pow_one] at hx1
  by_contra hlt
  push Not at hlt
  have hpos := orderOf_pos (plusBar (two_ne_zero_of_charP hp2) hxG hxC)
  have hk := pow_orderOf_eq_one (plusBar (two_ne_zero_of_charP hp2) hxG hxC)
  rcases pow_eq_one_or_neg_of_plusBar hp2 hU0 hneg hxG hxC hx hx1.1 hx1.2 hk with h | h
  · exact (hxm _ hpos hlt).1 h
  · exact (hxm _ hpos hlt).2 h

theorem plusBar_inv {x : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ stdCent K) :
    (plusBar (two_ne_zero_of_charP hp2) hxG hxC)⁻¹ =
      plusBar (two_ne_zero_of_charP hp2) (G.inv_mem hxG) (inv_mem hxC) := by
  apply Subtype.ext
  simp only [plusBar, InvMemClass.coe_inv, ← map_inv]
  rfl

omit hU0 hneg in
theorem card_eq_pow_of_finite : ∃ f : ℕ, Nat.card K = p ^ f := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem plusBlock_commutator_of_rotations {x y : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ stdCent K)
    (hyG : y ∈ G) (hyC : y ∈ stdCent K) {β γ : K}
    (hx : (x : Matrix V₄ V₄ K) * x = (2 * β) • (x : Matrix V₄ V₄ K) - 1)
    (hy : (y : Matrix V₄ V₄ K) * y = (2 * γ) • (y : Matrix V₄ V₄ K) - 1)
    (hx6 : ∀ k, 1 ≤ k → k < 6 → x ^ k ≠ 1 ∧ x ^ k ≠ -1)
    (hy3 : ∀ k, 1 ≤ k → k < 3 → y ^ k ≠ 1 ∧ y ^ k ≠ -1) :
    plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 ∨
      plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = -1 := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  obtain ⟨f, hF⟩ := card_eq_pow_of_finite (K := K) (p := p) hp2
  have hH := not_dvd_card_plusImage hp2 hU0 hneg
  have hxo := two_lt_orderOf_plusBar_of hp2 hU0 hneg hxG hxC hx hx6 (by norm_num)
  have hyo := two_lt_orderOf_plusBar_of hp2 hU0 hneg hyG hyC hy hy3 (by norm_num)
  have hcomm := commute_of_six_le_orderOf hF _ hH hxo (show 2 < orderOf (plusBar h2 hxG hxC) by
    omega) (show 2 < orderOf (plusBar h2 hyG hyC) by omega)
  have hcG : x * y * x⁻¹ * y⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)) (G.inv_mem hyG)
  have hcC : x * y * x⁻¹ * y⁻¹ ∈ stdCent K :=
    mul_mem (mul_mem (mul_mem hxC hyC) (inv_mem hxC)) (inv_mem hyC)
  refine (plusBar_eq_one_iff h2 hcG hcC).mp ?_
  have e : plusBar h2 hcG hcC = plusBar h2 hxG hxC * plusBar h2 hyG hyC *
      (plusBar h2 hxG hxC)⁻¹ * (plusBar h2 hyG hyC)⁻¹ := by
    rw [plusBar_inv hp2 hU0 hneg, plusBar_inv hp2 hU0 hneg, plusBar_mul, plusBar_mul, plusBar_mul]
  rw [e, hcomm]
  group

omit hp2 hU0 hneg in
theorem conj_hyps (k : GL V₄ K) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ K) ∈ G) :
    (∀ x ∈ G.map (MulAut.conj k).toMonoidHom, IsSqZero x → x = 1) ∧
      (-1 : GL V₄ K) ∈ G.map (MulAut.conj k).toMonoidHom := by
  constructor
  · intro x hx hsq
    rw [mem_map_conj] at hx
    have := hU0 _ hx (by
      have := isSqZero_conj hsq k⁻¹
      simpa [mul_assoc] using this)
    calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      _ = 1 := by rw [this]; group
  · rw [mem_map_conj]
    simpa using hneg

theorem minusBlock_commutator_of_rotations {x y : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ stdCent K)
    (hyG : y ∈ G) (hyC : y ∈ stdCent K) {β γ : K}
    (hx : (x : Matrix V₄ V₄ K) * x = (2 * β) • (x : Matrix V₄ V₄ K) - 1)
    (hy : (y : Matrix V₄ V₄ K) * y = (2 * γ) • (y : Matrix V₄ V₄ K) - 1)
    (hx6 : ∀ k, 1 ≤ k → k < 6 → x ^ k ≠ 1 ∧ x ^ k ≠ -1)
    (hy3 : ∀ k, 1 ≤ k → k < 3 → y ^ k ≠ 1 ∧ y ^ k ≠ -1) :
    minusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 ∨
      minusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = -1 := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  set σ : GL V₄ K := swapGL
  obtain ⟨hU0', hneg'⟩ := conj_hyps σ hU0 hneg
  have hσσ : σ⁻¹ = σ := swapGL_inv
  have hS : (swapMat : Matrix V₄ V₄ K) * swapMat = 1 := swapMat_mul_self
  have hs : (swapMat : Matrix V₄ V₄ K) * tStdMat = -(tStdMat * swapMat) := by
    have h := congrArg (· * (swapMat : Matrix V₄ V₄ K)) (swap_conj_tStdMat (K := K))
    simp only [Matrix.mul_assoc, hS, Matrix.mul_one, Matrix.neg_mul] at h
    exact h
  have hσm : ((σ : GL V₄ K) : Matrix V₄ V₄ K) = swapMat := coe_swapGL
  have hconjC : ∀ z ∈ stdCent K, σ * z * σ⁻¹ ∈ stdCent K := by
    intro z hz
    rw [mem_stdCent] at hz ⊢
    refine ⟨mul_mem (mul_mem swapGL_mem hz.1) (inv_mem swapGL_mem), ?_⟩
    rw [hσσ, Units.val_mul, Units.val_mul, hσm]
    have hz2 : (z : Matrix V₄ V₄ K) * tStdMat = tStdMat * (z : Matrix V₄ V₄ K) := hz.2
    calc (swapMat : Matrix V₄ V₄ K) * (z : Matrix V₄ V₄ K) * swapMat * tStdMat
        = swapMat * (z : Matrix V₄ V₄ K) * (swapMat * tStdMat) := by
          rw [Matrix.mul_assoc _ swapMat tStdMat]
      _ = -(swapMat * ((z : Matrix V₄ V₄ K) * tStdMat) * swapMat) := by
          rw [hs]
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(swapMat * (tStdMat * (z : Matrix V₄ V₄ K)) * swapMat) := by rw [hz2]
      _ = -((swapMat * tStdMat) * (z : Matrix V₄ V₄ K) * swapMat) := by
          simp only [Matrix.mul_assoc]
      _ = tStdMat * (swapMat * (z : Matrix V₄ V₄ K) * swapMat) := by
          rw [hs]
          simp only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have hrot : ∀ (z : GL V₄ K) (δ : K),
      (z : Matrix V₄ V₄ K) * z = (2 * δ) • (z : Matrix V₄ V₄ K) - 1 →
      ((σ * z * σ⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * ((σ * z * σ⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
        (2 * δ) • ((σ * z * σ⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1 := by
    intro z δ hz
    rw [hσσ, Units.val_mul, Units.val_mul, hσm]
    calc (swapMat : Matrix V₄ V₄ K) * (z : Matrix V₄ V₄ K) * swapMat *
          (swapMat * (z : Matrix V₄ V₄ K) * swapMat)
        = swapMat * ((z : Matrix V₄ V₄ K) * (z : Matrix V₄ V₄ K)) * swapMat := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (swapMat : Matrix V₄ V₄ K) swapMat, hS, Matrix.one_mul]
      _ = (2 * δ) • ((swapMat : Matrix V₄ V₄ K) * (z : Matrix V₄ V₄ K) * swapMat) - 1 := by
          rw [hz, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one, hS]
  have hpow : ∀ (z : GL V₄ K) (k : ℕ), (z ^ k ≠ 1 ∧ z ^ k ≠ -1) →
      ((σ * z * σ⁻¹) ^ k ≠ 1 ∧ (σ * z * σ⁻¹) ^ k ≠ -1) := by
    intro z k ⟨h1, h2'⟩
    have e : (σ * z * σ⁻¹) ^ k = σ * z ^ k * σ⁻¹ := by
      rw [show σ * z * σ⁻¹ = MulAut.conj σ z from rfl, ← map_pow]; rfl
    rw [e]
    constructor
    · intro h; apply h1
      calc z ^ k = σ⁻¹ * (σ * z ^ k * σ⁻¹) * σ := by group
        _ = 1 := by rw [h]; group
    · intro h; apply h2'
      calc z ^ k = σ⁻¹ * (σ * z ^ k * σ⁻¹) * σ := by group
        _ = -1 := by rw [h]; simp
  have hres := plusBlock_commutator_of_rotations hp2 hU0' hneg' (conj_mem_map_conj hxG)
    (hconjC x hxC) (conj_mem_map_conj hyG) (hconjC y hyC) (hrot x β hx) (hrot y γ hy)
    (fun k hk1 hk2 => hpow x k (hx6 k hk1 hk2)) (fun k hk1 hk2 => hpow y k (hy3 k hk1 hk2))
  have e : σ * x * σ⁻¹ * (σ * y * σ⁻¹) * (σ * x * σ⁻¹)⁻¹ * (σ * y * σ⁻¹)⁻¹ =
      σ * (x * y * x⁻¹ * y⁻¹) * σ⁻¹ := by group
  rw [e, hσσ, Units.val_mul, Units.val_mul, hσm] at hres
  rwa [plusBlock_swap_conj] at hres

theorem commute_of_rotations_tStd {x y : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ stdCent K)
    (hyG : y ∈ G) (hyC : y ∈ stdCent K) {β γ : K}
    (hx : (x : Matrix V₄ V₄ K) * x = (2 * β) • (x : Matrix V₄ V₄ K) - 1)
    (hy : (y : Matrix V₄ V₄ K) * y = (2 * γ) • (y : Matrix V₄ V₄ K) - 1)
    (hx6 : ∀ k, 1 ≤ k → k < 6 → x ^ k ≠ 1 ∧ x ^ k ≠ -1)
    (hy3 : ∀ k, 1 ≤ k → k < 3 → y ^ k ≠ 1 ∧ y ^ k ≠ -1) : x * y = y * x := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  have hp := plusBlock_commutator_of_rotations hp2 hU0 hneg hxG hxC hyG hyC hx hy hx6 hy3
  have hm := minusBlock_commutator_of_rotations hp2 hU0 hneg hxG hxC hyG hyC hx hy hx6 hy3
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcC : c ∈ stdCent K := mul_mem (mul_mem (mul_mem hxC hyC) (inv_mem hxC)) (inv_mem hyC)
  have hct := (mem_stdCent.mp hcC).2
  have hxt := (mem_stdCent.mp hxC).2
  obtain ⟨a, ha, ha2⟩ : ∃ a : K, plusBlock (c : Matrix V₄ V₄ K) = a • 1 ∧ a * a = 1 := by
    rcases hp with h | h
    · exact ⟨1, by rw [h, one_smul], by ring⟩
    · exact ⟨-1, by rw [h, neg_one_smul], by ring⟩
  obtain ⟨b, hb, hb2⟩ : ∃ b : K, minusBlock (c : Matrix V₄ V₄ K) = b • 1 ∧ b * b = 1 := by
    rcases hm with h | h
    · exact ⟨1, by rw [h, one_smul], by ring⟩
    · exact ⟨-1, by rw [h, neg_one_smul], by ring⟩
  have hcM := eq_of_blocks h2 hct ha hb
  have htt : tStdMat * tStdMat = (1 : Matrix V₄ V₄ K) := tStdMat_mul_self
  set α : K := (2 : K)⁻¹ * (a + b)
  set α' : K := (2 : K)⁻¹ * (a - b)
  have hcM' : (c : Matrix V₄ V₄ K) = α • (1 : Matrix V₄ V₄ K) + α' • tStdMat := by
    rw [hcM]
    simp only [α, α', smul_add, smul_sub, smul_smul, add_smul, sub_smul]
    module
  have hcx : c * x = x * c := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [hcM']
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hxt]
  have hcc : c * c = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_one]
    rw [hcM']
    have hexp : (α • (1 : Matrix V₄ V₄ K) + α' • tStdMat) * (α • 1 + α' • tStdMat) =
        (α * α + α' * α') • (1 : Matrix V₄ V₄ K) + (2 * (α * α')) • tStdMat := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, htt, smul_smul]
      module
    have e1 : α * α + α' * α' = 1 := by
      simp only [α, α']
      field_simp
      linear_combination 2 * ha2 + 2 * hb2
    have e2 : α * α' = 0 := by
      simp only [α, α']
      field_simp
      linear_combination ha2 - hb2
    rw [hexp, e1, e2, mul_zero, zero_smul, add_zero, one_smul]
  have hxxy : x * x * y = y * (x * x) := by
    have e : x * x * y * (x * x)⁻¹ * y⁻¹ = x * c * y * x⁻¹ * y⁻¹ := by
      rw [hc]; group
    have e2 : x * c * y * x⁻¹ * y⁻¹ = c * c := by
      rw [← hcx, hc]; group
    have : x * x * y * (x * x)⁻¹ * y⁻¹ = 1 := by rw [e, e2, hcc]
    calc x * x * y = x * x * y * (x * x)⁻¹ * y⁻¹ * (y * (x * x)) := by group
      _ = y * (x * x) := by rw [this, one_mul]
  have hβ : β ≠ 0 := by
    intro h0
    apply (hx6 2 (by norm_num) (by norm_num)).2
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_two, hx, h0, mul_zero, zero_smul, zero_sub, Units.val_neg,
      Units.val_one]
  apply Units.ext
  have hm' := congrArg (fun z : GL V₄ K => (z : Matrix V₄ V₄ K)) hxxy
  simp only [Units.val_mul] at hm'
  rw [hx, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one] at hm'
  have : (2 * β) • ((x : Matrix V₄ V₄ K) * y - (y : Matrix V₄ V₄ K) * x) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.mpr (by simpa using hm')
  rw [smul_eq_zero] at this
  rcases this with h | h
  · exact absurd ((mul_eq_zero.mp h).resolve_left h2) hβ
  · simp only [Units.val_mul]
    exact sub_eq_zero.mp h

omit hp2 hU0 hneg in
theorem conj_pow_ne {z : GL V₄ K} (k : GL V₄ K) {n : ℕ} (h : z ^ n ≠ 1 ∧ z ^ n ≠ -1) :
    (k * z * k⁻¹) ^ n ≠ 1 ∧ (k * z * k⁻¹) ^ n ≠ -1 := by
  have e : (k * z * k⁻¹) ^ n = k * z ^ n * k⁻¹ := by
    rw [show k * z * k⁻¹ = MulAut.conj k z from rfl, ← map_pow]; rfl
  rw [e]
  constructor
  · intro h'; apply h.1
    calc z ^ n = k⁻¹ * (k * z ^ n * k⁻¹) * k := by group
      _ = 1 := by rw [h']; group
  · intro h'; apply h.2
    calc z ^ n = k⁻¹ * (k * z ^ n * k⁻¹) * k := by group
      _ = -1 := by rw [h']; simp

omit hp2 hU0 hneg in
theorem conj_rotation {z : GL V₄ K} (k : GL V₄ K) {δ : K}
    (hz : (z : Matrix V₄ V₄ K) * z = (2 * δ) • (z : Matrix V₄ V₄ K) - 1) :
    ((k * z * k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (k * z * k⁻¹ : GL V₄ K) =
      (2 * δ) • ((k * z * k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1 := by
  have hkk : ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * k = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hkk' : (k : Matrix V₄ V₄ K) * ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  calc (k : Matrix V₄ V₄ K) * z * ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *
        ((k : Matrix V₄ V₄ K) * z * ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K))
      = (k : Matrix V₄ V₄ K) * ((z : Matrix V₄ V₄ K) * z) * ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) (k : Matrix V₄ V₄ K), hkk,
          Matrix.one_mul]
    _ = (2 * δ) • ((k : Matrix V₄ V₄ K) * z * ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) - 1 := by
        rw [hz, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          hkk']

theorem commute_of_rotations (hGS : G ≤ StatedSp 2 K) {u : GL V₄ K} (hu : IsNCInv u)
    {x y : GL V₄ K} (hxG : x ∈ G) (hyG : y ∈ G) (hxu : x * u = u * x) (hyu : y * u = u * y)
    {β γ : K} (hx : (x : Matrix V₄ V₄ K) * x = (2 * β) • (x : Matrix V₄ V₄ K) - 1)
    (hy : (y : Matrix V₄ V₄ K) * y = (2 * γ) • (y : Matrix V₄ V₄ K) - 1)
    (hx6 : ∀ k, 1 ≤ k → k < 6 → x ^ k ≠ 1 ∧ x ^ k ≠ -1)
    (hy3 : ∀ k, 1 ≤ k → k < 3 → y ^ k ≠ 1 ∧ y ^ k ≠ -1) : x * y = y * x := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  obtain ⟨h, hhS, hh⟩ := exists_conj_eq_tStd h2 hu
  set k := h⁻¹ with hk
  obtain ⟨hU0', hneg'⟩ := conj_hyps k hU0 hneg
  have htu : (tStd : GL V₄ K) = k * u * k⁻¹ := by rw [← hh, hk]; group
  have hC : ∀ z ∈ G, z * u = u * z → k * z * k⁻¹ ∈ stdCent K := by
    intro z hz hzu
    rw [mem_stdCent]
    refine ⟨mul_mem (mul_mem (inv_mem hhS) (hGS hz)) (by rw [hk, inv_inv]; exact hhS), ?_⟩
    have : k * z * k⁻¹ * tStd = tStd * (k * z * k⁻¹) := by
      rw [htu]
      calc k * z * k⁻¹ * (k * u * k⁻¹) = k * (z * u) * k⁻¹ := by group
        _ = k * (u * z) * k⁻¹ := by rw [hzu]
        _ = k * u * k⁻¹ * (k * z * k⁻¹) := by group
    have := congrArg (fun w : GL V₄ K => (w : Matrix V₄ V₄ K)) this
    simpa [coe_tStd] using this
  have hres := commute_of_rotations_tStd hp2 hU0' hneg' (conj_mem_map_conj hxG) (hC x hxG hxu)
    (conj_mem_map_conj hyG) (hC y hyG hyu) (conj_rotation k hx) (conj_rotation k hy)
    (fun n h1 h2' => conj_pow_ne k (hx6 n h1 h2')) (fun n h1 h2' => conj_pow_ne k (hy3 n h1 h2'))
  calc x * y = k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹)) * k := by group
    _ = k⁻¹ * ((k * y * k⁻¹) * (k * x * k⁻¹)) * k := by rw [hres]
    _ = y * x := by group

end Finite





end CFSG.RankThree.SubgroupLists
