module

public import CFSG.Quasithin.Background.G12FourHyp

public section

namespace CFSG.Quasithin.G11

open Matrix

theorem g12f_mem_normalizer_zpowers_iff {G : Type*} [Group G] {ω : G} (h3 : ω * ω * ω = 1)
    (h1 : ω ≠ 1) {g : G} :
    g ∈ Subgroup.normalizer (Subgroup.zpowers ω : Set G) ↔
      g * ω * g⁻¹ = ω ∨ g * ω * g⁻¹ = ω⁻¹ := by
  have hpow : ω ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, pow_succ, pow_two, h3]
  have hinv : ω⁻¹ = ω * ω := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, h3]
  constructor
  · intro hg
    have hm := (Subgroup.mem_normalizer_iff.1 hg ω).1 (Subgroup.mem_zpowers ω)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    rw [zpow_eq_zpow_emod k hpow] at hk
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h3' : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    obtain ⟨r, hr⟩ : ∃ r : ℕ, k % 3 = r := ⟨(k % 3).toNat, (Int.toNat_of_nonneg h0).symm⟩
    rw [hr] at hk h3'
    rw [zpow_natCast] at hk
    have hr3 : r < 3 := by omega
    interval_cases r
    · exfalso
      apply h1
      rw [pow_zero] at hk
      have : ω = g⁻¹ * (g * ω * g⁻¹) * g := by group
      rw [this, ← hk]
      group
    · left
      rw [← hk, pow_one]
    · right
      rw [← hk, hinv, pow_two]
  · intro h
    have hconj : ∀ k : ℤ, g * ω ^ k * g⁻¹ = (g * ω * g⁻¹) ^ k := fun k => (conj_zpow).symm
    have hconj' : g⁻¹ * ω * g = ω ∨ g⁻¹ * ω * g = ω⁻¹ := by
      rcases h with h | h
      · left
        calc g⁻¹ * ω * g = g⁻¹ * (g * ω * g⁻¹) * g := by rw [h]
          _ = ω := by group
      · right
        calc g⁻¹ * ω * g = (g⁻¹ * (g * ω * g⁻¹) * g)⁻¹ := by rw [h]; group
          _ = ω⁻¹ := by group
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [hconj]
      rcases h with h | h <;> rw [h]
      · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers ω) k
      · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers ω)) k
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      have e : x = (g⁻¹ * ω * g) ^ k := by
        rw [show g⁻¹ * ω * g = g⁻¹ * ω * g⁻¹⁻¹ by rw [inv_inv], conj_zpow, hk]
        group
      rw [e]
      rcases hconj' with h' | h' <;> rw [h']
      · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers ω) k
      · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers ω)) k

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def fourN : Subgroup (GLV FourV) :=
  Subgroup.normalizer (Subgroup.zpowers fourOm : Set (GLV FourV))

theorem fourOm_cube : fourOm * fourOm * fourOm = 1 := by
  refine LinearEquiv.ext fun x => ?_
  show fourOm (fourOm (fourOm x)) = x
  rw [fourOm_apply, fourOm_apply, fourOm_apply, mulVec_mulVec, mulVec_mulVec]
  revert x; decide

theorem fourOm_ne_one : fourOm ≠ 1 := by
  intro h
  have := congrArg (fun g : GLV FourV => g (fourBasisVec 0)) h
  change fourOm (fourBasisVec 0) = fourBasisVec 0 at this
  rw [fourOm_apply] at this
  revert this; decide

theorem fourOm_inv_apply' (x : FourV) : fourOm⁻¹ x = fourOmM *ᵥ (fourOmM *ᵥ x) := by
  rw [fourOm_inv_apply, mulVec_mulVec]

theorem mem_fourN_iff {g : GLV FourV} :
    g ∈ fourN ↔ (∀ x, g (fourOmM *ᵥ x) = fourOmM *ᵥ g x) ∨
      (∀ x, g (fourOmM *ᵥ x) = fourOmM *ᵥ (fourOmM *ᵥ g x)) := by
  rw [fourN, g12f_mem_normalizer_zpowers_iff fourOm_cube fourOm_ne_one, mul_inv_eq_iff_eq_mul,
    mul_inv_eq_iff_eq_mul]
  have e1 : (g * fourOm = fourOm * g) ↔ ∀ x, g (fourOmM *ᵥ x) = fourOmM *ᵥ g x := by
    constructor
    · intro h x
      have := congrArg (fun k : GLV FourV => k x) h
      change g (fourOm x) = fourOm (g x) at this
      rwa [fourOm_apply, fourOm_apply] at this
    · intro h
      refine LinearEquiv.ext fun x => ?_
      change g (fourOm x) = fourOm (g x)
      rw [fourOm_apply, fourOm_apply, h]
  have e2 : (g * fourOm = fourOm⁻¹ * g) ↔
      ∀ x, g (fourOmM *ᵥ x) = fourOmM *ᵥ (fourOmM *ᵥ g x) := by
    constructor
    · intro h x
      have := congrArg (fun k : GLV FourV => k x) h
      change g (fourOm x) = fourOm⁻¹ (g x) at this
      rwa [fourOm_apply, fourOm_inv_apply'] at this
    · intro h
      refine LinearEquiv.ext fun x => ?_
      change g (fourOm x) = fourOm⁻¹ (g x)
      rw [fourOm_apply, fourOm_inv_apply', h]
  rw [e1, e2]

theorem fourGen_mem_fourN (k : Fin 4) : fourGen k ∈ fourN := by
  rw [fourN, g12f_mem_normalizer_zpowers_iff fourOm_cube fourOm_ne_one]
  exact fourSemi_gen k

theorem fourM0_le_fourN : fourM0 ≤ fourN :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact fourGen_mem_fourN k)

theorem fourNorm_not_tv {w : FourV} (hw : w ≠ 0) : radE fourB w 0 1 ∉ fourN := by
  have hB := isSymplectic_fourB
  rw [mem_fourN_iff]
  simp only [radE_one_apply hB, fourB_apply]
  revert hw w
  decide

theorem fourNorm_not_tvProd : radE fourB (fourBasisVec 3) 0 1 * radE fourB (fourBasisVec 1) 0 1 ∉ fourN := by
  have hB := isSymplectic_fourB
  rw [mem_fourN_iff]
  have e : ∀ x, (radE fourB (fourBasisVec 3) 0 1 * radE fourB (fourBasisVec 1) 0 1) x =
      radE fourB (fourBasisVec 3) 0 1 (radE fourB (fourBasisVec 1) 0 1 x) := fun _ => rfl
  simp only [e, radE_one_apply hB, fourB_apply]
  decide

@[expose] def fourQf (qv : Fin 4 → ZMod 2) (x : FourV) : ZMod 2 :=
  x 0 * qv 0 + x 1 * qv 1 + x 2 * qv 2 + x 3 * qv 3 + x 0 * x 2 + x 1 * x 3

theorem fourQ_eq {q : FourV → ZMod 2} (hq : ∀ x y, q (x + y) = q x + q y + fourB x y)
    (x : FourV) : q x = fourQf (fun i => q (fourBasisVec i)) x := by
  have hq0 : q 0 = 0 := by
    have h := hq 0 0
    simp only [add_zero, map_zero] at h
    have h2 := g12_add_self (q 0)
    rw [← h] at h2
    exact h2
  have hsm : ∀ (c : ZMod 2) (y : FourV), q (c • y) = c * q y := by
    intro c y
    rcases g12_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul, hq0, zero_mul]
    · rw [one_smul, one_mul]
  have hx : x = x 0 • fourBasisVec 0 + x 1 • fourBasisVec 1 + x 2 • fourBasisVec 2 + x 3 • fourBasisVec 3 := by
    funext i
    fin_cases i <;> simp [fourBasisVec]
  rw [hx, hq, hq, hq, hsm, hsm, hsm, hsm]
  simp only [fourQf, fourB_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, fourBasisVec]
  simp
  ring

@[expose] def fourQW (qv : Fin 4 → ZMod 2) : FourV × FourV :=
  (if qv 0 = 0 then (if qv 1 = 0 then (if qv 2 = 0 then (if qv 3 = 0 then (![0, 0, 0, 1], ![0, 0, 1, 0]) else (![0, 1, 0, 0], ![1, 0, 0, 0])) else (if qv 3 = 0 then (![0, 1, 0, 0], ![0, 0, 1, 0]) else (![0, 1, 0, 0], ![0, 0, 1, 0]))) else (if qv 2 = 0 then (if qv 3 = 0 then (![0, 0, 0, 1], ![0, 0, 1, 0]) else (![0, 0, 1, 0], ![0, 1, 0, 0])) else (if qv 3 = 0 then (![0, 1, 0, 1], ![0, 0, 1, 0]) else (![0, 0, 1, 1], ![1, 1, 0, 0])))) else (if qv 1 = 0 then (if qv 2 = 0 then (if qv 3 = 0 then (![0, 0, 0, 1], ![0, 0, 1, 0]) else (![0, 1, 0, 1], ![1, 0, 0, 0])) else (if qv 3 = 0 then (![0, 0, 0, 1], ![1, 0, 0, 0]) else (![0, 0, 1, 1], ![1, 1, 0, 0]))) else (if qv 2 = 0 then (if qv 3 = 0 then (![0, 0, 0, 1], ![0, 0, 1, 0]) else (![0, 0, 1, 0], ![0, 1, 0, 0])) else (if qv 3 = 0 then (![0, 0, 0, 1], ![1, 0, 0, 0]) else (![0, 1, 1, 0], ![0, 0, 1, 0])))))

theorem fourQW_spec : ∀ qv : Fin 4 → ZMod 2, (fourQW qv).1 ≠ 0 ∧
    fourQf qv (fourQW qv).1 = 0 ∧ fourB (fourQW qv).1 (fourQW qv).2 = 0 ∧
    ¬ ((∀ x : FourV, fourOmM *ᵥ x + fourB (fourOmM *ᵥ x) (fourQW qv).1 • (fourQW qv).2 +
        (fourB (fourOmM *ᵥ x) (fourQW qv).2 + fourQf qv (fourQW qv).2 *
          fourB (fourOmM *ᵥ x) (fourQW qv).1) • (fourQW qv).1 =
        fourOmM *ᵥ (x + fourB x (fourQW qv).1 • (fourQW qv).2 +
          (fourB x (fourQW qv).2 + fourQf qv (fourQW qv).2 * fourB x (fourQW qv).1) •
            (fourQW qv).1)) ∨
      (∀ x : FourV, fourOmM *ᵥ x + fourB (fourOmM *ᵥ x) (fourQW qv).1 • (fourQW qv).2 +
        (fourB (fourOmM *ᵥ x) (fourQW qv).2 + fourQf qv (fourQW qv).2 *
          fourB (fourOmM *ᵥ x) (fourQW qv).1) • (fourQW qv).1 =
        fourOmM *ᵥ (fourOmM *ᵥ (x + fourB x (fourQW qv).1 • (fourQW qv).2 +
          (fourB x (fourQW qv).2 + fourQf qv (fourQW qv).2 * fourB x (fourQW qv).1) •
            (fourQW qv).1)))) := by
  simp only [fourB_apply]
  decide

theorem fourNorm_not_omega {q : FourV → ZMod 2}
    (hq : ∀ x y, q (x + y) = q x + q y + fourB x y) :
    ∃ w a, w ≠ 0 ∧ q w = 0 ∧ fourB w a = 0 ∧ radE fourB w a (q a) ∉ fourN := by
  have hB := isSymplectic_fourB
  obtain ⟨h1, h2, h3, h4⟩ := fourQW_spec (fun i => q (fourBasisVec i))
  refine ⟨_, _, h1, by rw [fourQ_eq hq]; exact h2, h3, ?_⟩
  rw [mem_fourN_iff]
  simp only [radE_apply hB h3]
  rw [fourQ_eq hq ((fourQW fun i => q (fourBasisVec i)).2)]
  exact h4

theorem fourNorm_inf_sp_le {g : GLV FourV} (hg : g ∈ fourN) (hs : g ∈ spSub fourB) :
    g ∈ fourM0 :=
  g12f_mem_fourM0_aux (Γ := fourN ⊓ spSub fourB) inf_le_right
    (fun h => fourNorm_not_tv (by decide) h.1) ⟨fourGen_mem_fourN 0, fourGen_mem_spSub 0⟩
    ⟨fourGen_mem_fourN 1, fourGen_mem_spSub 1⟩ (le_inf fourM0_le_fourN fourM0_le_spSub) ⟨hg, hs⟩

theorem fourM0_card : Nat.card fourM0 = 120 := by
  rw [Nat.card_congr fourRhoEquiv.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

@[expose] def fourJ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem fourB_eq_dot : ∀ x y : FourV, fourB x y = x ⬝ᵥ (fourJ *ᵥ y) := by
  simp only [fourB_apply]
  decide

theorem fourGram_mem_spSub {g : GLV FourV} {P : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hg : ∀ x, g x = P *ᵥ x) (hP : Pᵀ * fourJ * P = fourJ) : g ∈ spSub fourB := by
  intro x y
  rw [hg, hg, fourB_eq_dot, fourB_eq_dot, dotProduct_comm, dotProduct_mulVec,
    ← mulVec_transpose, dotProduct_comm, mulVec_mulVec, mulVec_mulVec, hP]

theorem fourV_linear_apply (g : GLV FourV) (x : FourV) :
    g x = x 0 • g (fourBasisVec 0) + x 1 • g (fourBasisVec 1) + x 2 • g (fourBasisVec 2) + x 3 • g (fourBasisVec 3) := by
  have hx : x = x 0 • fourBasisVec 0 + x 1 • fourBasisVec 1 + x 2 • fourBasisVec 2 + x 3 • fourBasisVec 3 := by
    funext i
    fin_cases i <;> simp [fourBasisVec]
  conv_lhs => rw [hx]
  simp only [map_add, map_smul]

@[expose] def fourCols (c : Fin 4 → FourV) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => c j i

theorem fourCols_mulVec (c : Fin 4 → FourV) (x : FourV) :
    fourCols c *ᵥ x = x 0 • c 0 + x 1 • c 1 + x 2 • c 2 + x 3 • c 3 := by
  funext i
  simp only [fourCols, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

@[expose] def fourOmPow : Fin 3 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![1, fourOmM, fourOmM * fourOmM]

@[expose] def fourNM (ε : Bool) (z : FourV) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fourCols ![fourBasisVec 0, if ε then fourBasisVec 1 else fourBasisVec 0 + fourBasisVec 1,
    if ε then fourOmM *ᵥ z else fourOmM *ᵥ (fourOmM *ᵥ z), z]

theorem fourNM_spec : ∀ ε : Bool, ∀ z : FourV, z ≠ 0 → z ≠ fourBasisVec 0 → z ≠ fourBasisVec 1 → z ≠ fourBasisVec 0 + fourBasisVec 1 →
    ∃ j : Fin 3, (fourNM ε z * fourOmPow j)ᵀ * fourJ * (fourNM ε z * fourOmPow j) = fourJ := by
  decide

theorem fourOm_pow_apply (j : Fin 3) (x : FourV) :
    (fourOm ^ (j : ℕ)) x = fourOmPow j *ᵥ x := by
  fin_cases j
  · show x = (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x
    rw [one_mulVec]
  · show (fourOm ^ 1) x = fourOmM *ᵥ x
    rw [pow_one, fourOm_apply]
  · show (fourOm ^ 2) x = (fourOmM * fourOmM) *ᵥ x
    rw [pow_two, ← mulVec_mulVec]
    show fourOm (fourOm x) = _
    rw [fourOm_apply, fourOm_apply]

theorem fourNorm_exists_pow_mem_sp {n : GLV FourV} (hn : n ∈ fourN) :
    ∃ j : ℕ, j < 3 ∧ n * fourOm ^ j ∈ spSub fourB := by
  have hw0 : n (fourBasisVec 0) ≠ 0 := (LinearEquiv.map_ne_zero_iff n).2 (by decide)
  obtain ⟨s, hsM, hs⟩ : ∃ s ∈ fourM0, s (fourBasisVec 0) = n (fourBasisVec 0) :=
    ⟨fourWord (fourSW (n (fourBasisVec 0))), fourWord_mem fourGen_mem _, by
      rw [fourWord_apply]; exact fourSW_spec _ hw0⟩
  obtain ⟨m, hmN, hm0, rfl⟩ : ∃ m ∈ fourN, m (fourBasisVec 0) = fourBasisVec 0 ∧ s * m = n := by
    refine ⟨s⁻¹ * n, fourN.mul_mem (fourN.inv_mem (fourM0_le_fourN hsM)) hn, ?_, by group⟩
    show s.symm (n (fourBasisVec 0)) = fourBasisVec 0
    rw [← hs, LinearEquiv.symm_apply_apply]
  have W1 : fourOmM *ᵥ fourBasisVec 1 = fourBasisVec 0 := by decide
  have W3 : fourOmM *ᵥ fourBasisVec 3 = fourBasisVec 2 := by decide
  have WW : ∀ y : FourV, fourOmM *ᵥ (fourOmM *ᵥ (fourOmM *ᵥ y)) = y := by decide
  have hz0 : m (fourBasisVec 3) ≠ 0 := (LinearEquiv.map_ne_zero_iff m).2 (by decide)
  have hz1 : m (fourBasisVec 3) ≠ fourBasisVec 0 := fun e => absurd (m.injective (e.trans hm0.symm)) (by decide)
  obtain ⟨ε, hm1, hm2⟩ : ∃ ε : Bool, m (fourBasisVec 1) = (if ε then fourBasisVec 1 else fourBasisVec 0 + fourBasisVec 1) ∧
      m (fourBasisVec 2) = (if ε then fourOmM *ᵥ m (fourBasisVec 3) else fourOmM *ᵥ (fourOmM *ᵥ m (fourBasisVec 3))) := by
    rcases mem_fourN_iff.1 hmN with hc | hc
    · refine ⟨true, ?_, ?_⟩
      · have h := hc (fourBasisVec 1)
        rw [W1, hm0] at h
        have := congrArg (fun y => fourOmM *ᵥ (fourOmM *ᵥ y)) h
        simp only [WW] at this
        rw [← this]
        decide
      · have h := hc (fourBasisVec 3)
        rw [W3] at h
        exact h
    · refine ⟨false, ?_, ?_⟩
      · have h := hc (fourBasisVec 1)
        rw [W1, hm0] at h
        have := congrArg (fun y => fourOmM *ᵥ y) h
        simp only [WW] at this
        rw [← this]
        decide
      · have h := hc (fourBasisVec 3)
        rw [W3] at h
        exact h
  have hm01 : m (fourBasisVec 0 + fourBasisVec 1) = fourBasisVec 0 + (if ε then fourBasisVec 1 else fourBasisVec 0 + fourBasisVec 1) := by
    rw [map_add, hm0, hm1]
  have hz2 : m (fourBasisVec 3) ≠ fourBasisVec 1 := by
    intro e
    cases ε
    · have h' : m (fourBasisVec 3) = m (fourBasisVec 0 + fourBasisVec 1) := by
        rw [hm01, e]; decide
      exact absurd (m.injective h') (by decide)
    · exact absurd (m.injective (e.trans hm1.symm)) (by decide)
  have hz3 : m (fourBasisVec 3) ≠ fourBasisVec 0 + fourBasisVec 1 := by
    intro e
    cases ε
    · exact absurd (m.injective (e.trans hm1.symm)) (by decide)
    · have h' : m (fourBasisVec 3) = m (fourBasisVec 0 + fourBasisVec 1) := by
        rw [hm01, e]; rfl
      exact absurd (m.injective h') (by decide)
  obtain ⟨j, hj⟩ := fourNM_spec ε (m (fourBasisVec 3)) hz0 hz1 hz2 hz3
  refine ⟨j, j.2, ?_⟩
  rw [mul_assoc]
  refine (spSub fourB).mul_mem (fourM0_le_spSub hsM) (fourGram_mem_spSub (fun x => ?_) hj)
  show m ((fourOm ^ (j : ℕ)) x) = _
  rw [fourOm_pow_apply, ← mulVec_mulVec, fourNM, fourCols_mulVec, fourV_linear_apply m, hm0,
    hm1, hm2]
  cases ε <;> rfl

end NoInst

end CFSG.Quasithin.G11
