module

public import CFSG.Quasithin.Background.RonanH44Sig

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem smul_mem_commV_sig (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {c : Fq n K}
    {v w : HMod n K} (hv : v ∈ commV (Subgroup.zpowers (sig n K)))
    (h : mat w = scalF n K c • mat v) : w ∈ commV (Subgroup.zpowers (sig n K)) := by
  obtain ⟨hdiag, hF⟩ := (mem_commV_sig hn hK).1 hv
  refine (mem_commV_sig hn hK).2 ⟨fun i => ?_, fun i j => ?_⟩
  · rw [h, Matrix.smul_apply, hdiag i, smul_zero]
  · rw [h, Matrix.smul_apply, smul_eq_mul, map_mul, bar_scalF, hF i j]

theorem smul_mem_fixV_sig (hK : Nat.card K = (2 ^ n) ^ 2) {c : Fq n K}
    {v w : HMod n K} (hv : v ∈ fixV (Subgroup.zpowers (sig n K)))
    (h : mat w = scalF n K c • mat v) : w ∈ fixV (Subgroup.zpowers (sig n K)) := by
  rw [mem_fixV_sig hK] at hv ⊢
  intro i j
  rw [h, Matrix.smul_apply, smul_eq_mul, map_mul, bar_scalF, hv i j]

theorem smul_mem_bot {c : K} {v w : HMod n K} (hv : v ∈ (⊥ : Subgroup (HMod n K)))
    (h : mat w = c • mat v) : w ∈ (⊥ : Subgroup (HMod n K)) := by
  rw [Subgroup.mem_bot] at hv ⊢
  apply mat_injective
  rw [mat_one, h, hv, mat_one, smul_zero]

theorem rho_smul_compat (hK : Nat.card K = (2 ^ n) ^ 2) (g : SL(3, K)) {c : K}
    {v w : HMod n K} (h : mat w = c • mat v) :
    mat (rho hK g w) = c • mat (rho hK g v) := by
  rw [mat_rho, mat_rho, h, tw_smul]

theorem mem_frobFixed_of_bar {x : K} (hx : bar n x = x) : x ∈ frobFixed (barR n K) :=
  CFSG.Quasithin.SteinbergCB.mem_frobFixed.2 hx

theorem trace_mem_Fq (hK : Nat.card K = (2 ^ n) ^ 2) (x : K) :
    x + bar n x ∈ frobFixed (barR n K) :=
  mem_frobFixed_of_bar (by rw [map_add, bar_bar hK]; exact add_comm _ _)

theorem vec3_eq_zero_iff (x y z : Fq n K) :
    (![x, y, z] : Fin 3 → Fq n K) = 0 ↔ x = 0 ∧ y = 0 ∧ z = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    funext i
    fin_cases i <;> rfl

theorem vec3_triple_eq_zero_iff (p : Fq n K × Fq n K × Fq n K) :
    (![p.1, p.2.1, p.2.2] : Fin 3 → Fq n K) = 0 ↔ p = 0 := by
  obtain ⟨a, b, c⟩ := p
  rw [Prod.mk_eq_zero, Prod.mk_eq_zero]
  exact vec3_eq_zero_iff a b c

theorem commVEquiv_zero (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    commVEquiv hn hK 0 = 1 := by
  apply Subtype.ext
  apply mat_injective
  change sigAltMat 0 = 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigAltMat]

theorem commVEquiv_add (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (a b : Fq n K × Fq n K × Fq n K) :
    commVEquiv hn hK (a + b) = commVEquiv hn hK a * commVEquiv hn hK b := by
  apply Subtype.ext
  apply mat_injective
  change sigAltMat (a + b) = sigAltMat a + sigAltMat b
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigAltMat]

theorem commVEquiv_symm_mul (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (u v : ↥(commV (Subgroup.zpowers (sig n K)))) :
    (commVEquiv hn hK).symm (u * v) = (commVEquiv hn hK).symm u + (commVEquiv hn hK).symm v := by
  rw [Equiv.symm_apply_eq, commVEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem mat_commV_eq (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (u : ↥(commV (Subgroup.zpowers (sig n K)))) :
    mat (u : HMod n K) = sigAltMat ((commVEquiv hn hK).symm u) := by
  obtain ⟨p, rfl⟩ := (commVEquiv hn hK).surjective u
  rw [Equiv.symm_apply_apply]
  rfl

theorem sigAltMat_smul_eq (c : Fq n K) (p q : Fq n K × Fq n K × Fq n K)
    (h : sigAltMat q = scalF n K c • sigAltMat p) : q = c • p := by
  obtain ⟨q1, q2, q3⟩ := q
  obtain ⟨p1, p2, p3⟩ := p
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h12 := congrFun (congrFun h 1) 2
  simp [sigAltMat, scalF_apply] at h01 h02 h12
  have e1 : q1 = c * p1 := Subtype.ext (by simpa using h01)
  have e2 : q2 = c * p2 := Subtype.ext (by simpa using h02)
  have e3 : q3 = c * p3 := Subtype.ext (by simpa using h12)
  rw [e1, e2, e3]
  rfl

@[expose] noncomputable def commCoord (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ↥(commV (Subgroup.zpowers (sig n K))) →* Multiplicative (Fin 3 → Fq n K) where
  toFun u := Multiplicative.ofAdd
    (![((commVEquiv hn hK).symm u).1, ((commVEquiv hn hK).symm u).2.1,
      ((commVEquiv hn hK).symm u).2.2] : Fin 3 → Fq n K)
  map_one' := by
    try dsimp only
    rw [ofAdd_eq_one, vec3_triple_eq_zero_iff]
    exact (Equiv.symm_apply_eq _).2 (commVEquiv_zero hn hK).symm
  map_mul' u v := by
    try dsimp only
    rw [← ofAdd_add, commVEquiv_symm_mul]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem commCoord_apply (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (u : ↥(commV (Subgroup.zpowers (sig n K)))) :
    commCoord hn hK u = Multiplicative.ofAdd
      (![((commVEquiv hn hK).symm u).1, ((commVEquiv hn hK).symm u).2.1,
        ((commVEquiv hn hK).symm u).2.2] : Fin 3 → Fq n K) :=
  rfl

@[expose] noncomputable def fixDiag (hK : Nat.card K = (2 ^ n) ^ 2) :
    ↥(fixV (Subgroup.zpowers (sig n K))) →* Multiplicative (Fin 3 → Fq n K) where
  toFun u := Multiplicative.ofAdd
    (![⟨mat u.1 0 0, mem_frobFixed_of_bar ((mem_fixV_sig hK).1 u.2 0 0)⟩,
      ⟨mat u.1 1 1, mem_frobFixed_of_bar ((mem_fixV_sig hK).1 u.2 1 1)⟩,
      ⟨mat u.1 2 2, mem_frobFixed_of_bar ((mem_fixV_sig hK).1 u.2 2 2)⟩] : Fin 3 → Fq n K)
  map_one' := by
    try dsimp only
    rw [ofAdd_eq_one]
    funext i
    apply Subtype.ext
    fin_cases i <;> simp [mat_one]
  map_mul' u v := by
    try dsimp only
    rw [← ofAdd_add]
    congr 1
    funext i
    apply Subtype.ext
    fin_cases i <;> simp [mat_mul]

theorem fixDiag_apply (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(fixV (Subgroup.zpowers (sig n K)))) :
    fixDiag hK u = Multiplicative.ofAdd
      (![⟨mat u.1 0 0, mem_frobFixed_of_bar ((mem_fixV_sig hK).1 u.2 0 0)⟩,
        ⟨mat u.1 1 1, mem_frobFixed_of_bar ((mem_fixV_sig hK).1 u.2 1 1)⟩,
        ⟨mat u.1 2 2, mem_frobFixed_of_bar ((mem_fixV_sig hK).1 u.2 2 2)⟩] : Fin 3 → Fq n K) :=
  rfl

theorem fixDiag_eq_one_iff (hK : Nat.card K = (2 ^ n) ^ 2)
    (u : ↥(fixV (Subgroup.zpowers (sig n K)))) :
    fixDiag hK u = 1 ↔ ∀ i : Fin 3, mat (u : HMod n K) i i = 0 := by
  rw [fixDiag_apply, ofAdd_eq_one]
  constructor
  · intro h i
    fin_cases i
    · simpa using congrArg Subtype.val (congrFun h 0)
    · simpa using congrArg Subtype.val (congrFun h 1)
    · simpa using congrArg Subtype.val (congrFun h 2)
  · intro h
    funext i
    apply Subtype.ext
    fin_cases i <;> simp [h]

@[expose] def diagFq (a b c : Fq n K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![(a : K), (b : K), (c : K)]

theorem diagFq_herm (a b c : Fq n K) : (conjM n (diagFq a b c))ᵀ = diagFq a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagFq, conjM, bar_val_fq]

@[expose] noncomputable def traceMat (n : ℕ) (z₀ z₁ z₂ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, z₀, z₁; bar n z₀, 0, z₂; bar n z₁, bar n z₂, 0]

theorem traceMat_01 (n : ℕ) (z₀ z₁ z₂ : K) : traceMat n z₀ z₁ z₂ 0 1 = z₀ := rfl

theorem traceMat_02 (n : ℕ) (z₀ z₁ z₂ : K) : traceMat n z₀ z₁ z₂ 0 2 = z₁ := rfl

theorem traceMat_12 (n : ℕ) (z₀ z₁ z₂ : K) : traceMat n z₀ z₁ z₂ 1 2 = z₂ := rfl

theorem traceMat_herm (hK : Nat.card K = (2 ^ n) ^ 2) (z₀ z₁ z₂ : K) :
    (conjM n (traceMat n z₀ z₁ z₂))ᵀ = traceMat n z₀ z₁ z₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceMat, conjM, bar_bar hK]

theorem trace_mul_eq {ω : K} (hω : ω + bar n ω = 1) (t : Fq n K) :
    (t : K) * ω + bar n ((t : K) * ω) = (t : K) := by
  rw [map_mul, bar_val_fq, ← mul_add, hω, mul_one]

theorem bar_eq_of_trace_zero {x : K} (h : x + bar n x = 0) : bar n x = x := by
  rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]

theorem bar_fixed_of_trace (X : HMod n K)
    (h01 : mat X 0 1 + bar n (mat X 0 1) = 0) (h02 : mat X 0 2 + bar n (mat X 0 2) = 0)
    (h12 : mat X 1 2 + bar n (mat X 1 2) = 0) (i j : Fin 3) :
    bar n (mat X i j) = mat X i j := by
  have e01 := bar_eq_of_trace_zero h01
  have e02 := bar_eq_of_trace_zero h02
  have e12 := bar_eq_of_trace_zero h12
  have f10 : mat X 1 0 = mat X 0 1 := by rw [← herm_apply X 1 0, e01]
  have f20 : mat X 2 0 = mat X 0 2 := by rw [← herm_apply X 2 0, e02]
  have f21 : mat X 2 1 = mat X 1 2 := by rw [← herm_apply X 2 1, e12]
  fin_cases i <;> fin_cases j <;> first
    | exact herm_apply X _ _
    | exact e01
    | exact e02
    | exact e12
    | exact (congrArg (bar n) f10).trans (e01.trans f10.symm)
    | exact (congrArg (bar n) f20).trans (e02.trans f20.symm)
    | exact (congrArg (bar n) f21).trans (e12.trans f21.symm)

@[expose] noncomputable def topTrace (hK : Nat.card K = (2 ^ n) ^ 2) :
    ↥(⊤ : Subgroup (HMod n K)) →* Multiplicative (Fin 3 → Fq n K) where
  toFun u := Multiplicative.ofAdd
    (![⟨mat u.1 0 1 + bar n (mat u.1 0 1), trace_mem_Fq hK _⟩,
      ⟨mat u.1 0 2 + bar n (mat u.1 0 2), trace_mem_Fq hK _⟩,
      ⟨mat u.1 1 2 + bar n (mat u.1 1 2), trace_mem_Fq hK _⟩] : Fin 3 → Fq n K)
  map_one' := by
    try dsimp only
    rw [ofAdd_eq_one]
    funext i
    apply Subtype.ext
    fin_cases i <;> simp [mat_one]
  map_mul' u v := by
    try dsimp only
    rw [← ofAdd_add]
    congr 1
    funext i
    apply Subtype.ext
    fin_cases i <;> simp [mat_mul] <;> ring

theorem topTrace_apply (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(⊤ : Subgroup (HMod n K))) :
    topTrace hK u = Multiplicative.ofAdd
      (![⟨mat u.1 0 1 + bar n (mat u.1 0 1), trace_mem_Fq hK _⟩,
        ⟨mat u.1 0 2 + bar n (mat u.1 0 2), trace_mem_Fq hK _⟩,
        ⟨mat u.1 1 2 + bar n (mat u.1 1 2), trace_mem_Fq hK _⟩] : Fin 3 → Fq n K) :=
  rfl

theorem exists_top_trace (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (t : Fin 3 → Fq n K) :
    ∃ X : HMod n K, mat X 0 1 + bar n (mat X 0 1) = (t 0 : K) ∧
      mat X 0 2 + bar n (mat X 0 2) = (t 1 : K) ∧
      mat X 1 2 + bar n (mat X 1 2) = (t 2 : K) := by
  obtain ⟨ω, hω⟩ := exists_trace_one hn hK
  have hH := traceMat_herm hK ((t 0 : K) * ω) ((t 1 : K) * ω) ((t 2 : K) * ω)
  refine ⟨mkH _ hH, ?_, ?_, ?_⟩
  · rw [mat_mkH, traceMat_01]
    exact trace_mul_eq hω _
  · rw [mat_mkH, traceMat_02]
    exact trace_mul_eq hω _
  · rw [mat_mkH, traceMat_12]
    exact trace_mul_eq hω _

theorem sec_comm (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ β : ↥(commV (Subgroup.zpowers (sig n K))) →* Multiplicative (Fin 3 → Fq n K),
      Function.Surjective β ∧
      (∀ u : ↥(commV (Subgroup.zpowers (sig n K))),
        β u = 1 ↔ (u : HMod n K) ∈ (⊥ : Subgroup (HMod n K))) ∧
      (∀ (c : Fq n K) (v w : ↥(commV (Subgroup.zpowers (sig n K)))),
        mat (w : HMod n K) = scalF n K c • mat (v : HMod n K) →
        Multiplicative.toAdd (β w) = c • Multiplicative.toAdd (β v)) := by
  refine ⟨commCoord hn hK, ?_, ?_, ?_⟩
  · intro t
    refine ⟨commVEquiv hn hK (Multiplicative.toAdd t 0, Multiplicative.toAdd t 1,
      Multiplicative.toAdd t 2), ?_⟩
    rw [commCoord_apply, Equiv.symm_apply_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    funext i
    fin_cases i <;> rfl
  · intro u
    rw [Subgroup.mem_bot, commCoord_apply, ofAdd_eq_one, vec3_triple_eq_zero_iff,
      Equiv.symm_apply_eq, commVEquiv_zero hn hK]
    exact Subtype.ext_iff
  · intro c v w h
    rw [commCoord_apply, commCoord_apply, toAdd_ofAdd, toAdd_ofAdd]
    rw [mat_commV_eq hn hK, mat_commV_eq hn hK] at h
    rw [sigAltMat_smul_eq c _ _ h]
    funext i
    fin_cases i <;> rfl

theorem sec_fix (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ β : ↥(fixV (Subgroup.zpowers (sig n K))) →* Multiplicative (Fin 3 → Fq n K),
      Function.Surjective β ∧
      (∀ u : ↥(fixV (Subgroup.zpowers (sig n K))),
        β u = 1 ↔ (u : HMod n K) ∈ commV (Subgroup.zpowers (sig n K))) ∧
      (∀ (c : Fq n K) (v w : ↥(fixV (Subgroup.zpowers (sig n K)))),
        mat (w : HMod n K) = scalF n K c • mat (v : HMod n K) →
        Multiplicative.toAdd (β w) = c • Multiplicative.toAdd (β v)) := by
  refine ⟨fixDiag hK, ?_, ?_, ?_⟩
  · intro t
    have hH := diagFq_herm (Multiplicative.toAdd t 0) (Multiplicative.toAdd t 1)
      (Multiplicative.toAdd t 2)
    refine ⟨⟨mkH _ hH, (mem_fixV_sig hK).2 ?_⟩, ?_⟩
    · intro i j
      rw [mat_mkH]
      fin_cases i <;> fin_cases j <;> simp [diagFq, bar_val_fq]
    · rw [fixDiag_apply]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      funext i
      apply Subtype.ext
      fin_cases i <;> simp [diagFq, mat_mkH]
  · intro u
    rw [mem_commV_sig hn hK, fixDiag_eq_one_iff]
    exact ⟨fun h => ⟨h, (mem_fixV_sig hK).1 u.2⟩, fun h => h.1⟩
  · intro c v w h
    have hw : ∀ i j, mat (w : HMod n K) i j = scalF n K c * mat (v : HMod n K) i j :=
      fun i j => by rw [h, Matrix.smul_apply, smul_eq_mul]
    rw [fixDiag_apply, fixDiag_apply, toAdd_ofAdd, toAdd_ofAdd]
    funext i
    apply Subtype.ext
    fin_cases i <;> simp [hw, scalF_apply]

theorem sec_top (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ β : ↥(⊤ : Subgroup (HMod n K)) →* Multiplicative (Fin 3 → Fq n K),
      Function.Surjective β ∧
      (∀ u : ↥(⊤ : Subgroup (HMod n K)),
        β u = 1 ↔ (u : HMod n K) ∈ fixV (Subgroup.zpowers (sig n K))) ∧
      (∀ (c : Fq n K) (v w : ↥(⊤ : Subgroup (HMod n K))),
        mat (w : HMod n K) = scalF n K c • mat (v : HMod n K) →
        Multiplicative.toAdd (β w) = c • Multiplicative.toAdd (β v)) := by
  refine ⟨topTrace hK, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨X, h01, h02, h12⟩ := exists_top_trace hn hK (Multiplicative.toAdd t)
    refine ⟨⟨X, Subgroup.mem_top _⟩, ?_⟩
    rw [topTrace_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    funext i
    apply Subtype.ext
    fin_cases i
    · exact h01
    · exact h02
    · exact h12
  · intro u
    rw [mem_fixV_sig hK, topTrace_apply, ofAdd_eq_one]
    constructor
    · intro h
      have e01 : mat u.1 0 1 + bar n (mat u.1 0 1) = 0 := congrArg Subtype.val (congrFun h 0)
      have e02 : mat u.1 0 2 + bar n (mat u.1 0 2) = 0 := congrArg Subtype.val (congrFun h 1)
      have e12 : mat u.1 1 2 + bar n (mat u.1 1 2) = 0 := congrArg Subtype.val (congrFun h 2)
      exact fun i j => bar_fixed_of_trace u.1 e01 e02 e12 i j
    · intro h
      funext i
      apply Subtype.ext
      fin_cases i <;> simp [h, CharTwo.add_self_eq_zero]
  · intro c v w h
    rw [topTrace_apply, topTrace_apply, toAdd_ofAdd, toAdd_ofAdd]
    have hw : ∀ i j, mat (w : HMod n K) i j = scalF n K c * mat (v : HMod n K) i j :=
      fun i j => by rw [h, Matrix.smul_apply, smul_eq_mul]
    funext i
    apply Subtype.ext
    fin_cases i <;> simp [hw, map_mul, bar_val_fq, scalF_apply, mul_add]

end CFSG.Quasithin.RonanH44
