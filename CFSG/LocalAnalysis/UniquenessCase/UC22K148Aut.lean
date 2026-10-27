module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Lie
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.QuasithinUnique.Setup CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open Matrix

variable {G : Type} [Group G]

@[expose] def InducesInnerOn (L : Subgroup G) (b : G) : Prop :=
  ∃ l ∈ L, ∀ x ∈ L, b * x * b⁻¹ = l * x * l⁻¹

namespace AutAux

@[expose] noncomputable def condHom (L : Subgroup G) : ↥(Subgroup.normalizer (L : Set G)) →* MulAut ↥L where
  toFun b :=
    { toFun := fun x => ⟨(b : G) * x * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp b.2 x).mp x.2⟩
      invFun := fun x => ⟨(b : G)⁻¹ * x * b, by
        have h := (Subgroup.mem_normalizer_iff.mp (inv_mem b.2) x).mp x.2
        simpa using h⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a c => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext x; simp
  map_mul' b c := by ext x; simp [mul_assoc]

theorem condHom_apply (L : Subgroup G) (b : ↥(Subgroup.normalizer (L : Set G))) (x : ↥L) :
    ((condHom L b x : ↥L) : G) = (b : G) * x * (b : G)⁻¹ := rfl

theorem inducesInnerOn_of_mem_inner {L : Subgroup G} {M : Type} [Group M] (e : ↥L ≃* M)
    {b : ↥(Subgroup.normalizer (L : Set G))} (h : MulAut.congr e (condHom L b) ∈ inner M) :
    InducesInnerOn L b := by
  obtain ⟨m, hm⟩ := h
  refine ⟨((e.symm m : ↥L) : G), (e.symm m).2, fun x hx => ?_⟩
  have h1 := congrArg (fun φ : MulAut M => e.symm (φ (e ⟨x, hx⟩))) hm
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    map_mul, map_inv] at h1
  have h2 := congrArg Subtype.val h1
  exact h2.symm

theorem minorAut_pow_two_mul {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : minorAut K ^ (2 * n) = 1 := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := X7b.exists_frobenius_data hn hK
  have h1 := (exceptionalAut_structure hn hFr hord hzp).1
  apply (X7b.autCongr K).injective
  rw [map_one, X7b.autCongr_pow, X7b.autCongr_minorAut, ← h1]
  exact pow_orderOf_eq_one _

theorem center_eq_bot_of_equiv_antiSp {M : Type} [Group M] {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : M ≃* antiSp K) : Subgroup.center M = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have h1 : MulAut.conj (e z) = MulAut.conj (1 : antiSp K) := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨y', rfl⟩ := e.surjective y
    have h3 : z * y' * z⁻¹ = y' := by rw [← Subgroup.mem_center_iff.mp hz y', mul_inv_cancel_right]
    calc (MulAut.conj (e z)) (e y') = e (z * y' * z⁻¹) := by
          rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
      _ = e y' := by rw [h3]
      _ = (MulAut.conj (1 : antiSp K)) (e y') := by rw [MulAut.conj_apply]; simp
  exact e.map_eq_one_iff.mp (X7b.conj_injective h1)

theorem isInnDiagFieldAut_conj_mul_pow_even {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (h : antiSp K) (k : ℕ) :
    CFSG.ASVolI.ChA.IsInnDiagFieldAut (antiSp K) (MulAut.conj h * minorAut K ^ (2 * k)) := by
  obtain ⟨Fr, hFr, -, -⟩ := X7b.exists_frobenius_data hn hK
  refine ⟨MulAut.conj h, minorAut K ^ (2 * k), Or.inl ⟨h, rfl⟩, ?_, rfl⟩
  refine Or.inr (Or.inr (Or.inr (Or.inl
    ⟨n, K, inferInstance, inferInstance, X7b.antiProjEquiv K, Fr ^ k, hK, ?_⟩)))
  have hα : MulAut.congr (X7b.antiProjEquiv K) (minorAut K ^ (2 * k)) = fieldAut 2 K (Fr ^ k) := by
    change X7b.autCongr K (minorAut K ^ (2 * k)) = _
    rw [X7b.autCongr_pow, X7b.autCongr_minorAut, pow_mul, exceptionalAut_sq hFr, ← map_pow]
  rw [hα]
  intro g
  exact ⟨fieldSp 2 K (Fr ^ k) g, rfl, rfl⟩

section S0

variable {K : Type} [Field K]

@[expose] def s0Mat : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1]

@[expose] def s0MatInv : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]

variable [CharP K 2]

theorem s0Mat_mul_s0MatInv : (s0Mat : Matrix (Fin 4) (Fin 4) K) * s0MatInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s0Mat, s0MatInv, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

theorem s0MatInv_mul_s0Mat : (s0MatInv : Matrix (Fin 4) (Fin 4) K) * s0Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s0Mat, s0MatInv, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

theorem s0Mat_mul_self : (s0Mat : Matrix (Fin 4) (Fin 4) K) * s0Mat = s0MatInv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s0Mat, s0MatInv, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

variable (K) in
@[expose] def s0GL : GL (Fin 4) K :=
  ⟨s0Mat, s0MatInv, s0Mat_mul_s0MatInv, s0MatInv_mul_s0Mat⟩

theorem glMat_s0GL : glMat (s0GL K) = s0Mat := rfl

theorem s0GL_mem : s0GL K ∈ antiSp K := by
  rw [mem_antiSp]
  ext k l
  rw [transpose_mul_minorJ_mul_apply]
  fin_cases k <;> fin_cases l <;>
    simp [glMat_s0GL, s0Mat, minorJ_apply, CharTwo.add_self_eq_zero]

variable (K) in
@[expose] def s0 : antiSp K :=
  ⟨s0GL K, s0GL_mem⟩

theorem glMat_s0 : glMat (s0 K : GL (Fin 4) K) = s0Mat := rfl

theorem s0_pow_three : (s0 K) ^ 3 = 1 := by
  rw [pow_three]
  refine Subtype.ext (Units.ext ?_)
  change s0Mat * (s0Mat * s0Mat) = (1 : Matrix (Fin 4) (Fin 4) K)
  rw [s0Mat_mul_self, s0Mat_mul_s0MatInv]

theorem s0_ne_one : s0 K ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : antiSp K => (glMat (x : GL (Fin 4) K)) 0 0) h
  simp [glMat_s0, s0Mat] at h1

theorem orderOf_s0 : orderOf (s0 K) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime s0_pow_three s0_ne_one

theorem s0Mat_mulVec (v : Fin 4 → K) :
    (s0Mat : Matrix (Fin 4) (Fin 4) K) *ᵥ v = ![v 3, v 1, v 2, v 0 + v 3] := by
  ext i
  fin_cases i <;> simp [s0Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem fix_s0 {v : Fin 4 → K} (hv : (s0Mat : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v) :
    v 0 = 0 ∧ v 3 = 0 := by
  rw [s0Mat_mulVec] at hv
  have h0 : v 3 = v 0 := congrFun hv 0
  have h3 : v 0 + v 3 = v 3 := congrFun hv 3
  have h4 : v 0 = 0 := by linear_combination h3
  exact ⟨h4, h0.trans h4⟩

theorem card_fix_s0 :
    Nat.card {v : Fin 4 → K // (s0Mat : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v} = Nat.card K ^ 2 := by
  let f : {v : Fin 4 → K // (s0Mat : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v} ≃ K × K :=
    { toFun := fun v => (v.1 1, v.1 2)
      invFun := fun p => ⟨![0, p.1, p.2, 0], by
        rw [s0Mat_mulVec]
        ext i
        fin_cases i <;> simp⟩
      left_inv := fun v => by
        obtain ⟨h0, h3⟩ := fix_s0 v.2
        refine Subtype.ext (funext fun i => ?_)
        fin_cases i <;> simp [h0, h3]
      right_inv := fun p => rfl }
  rw [Nat.card_congr f, Nat.card_prod, sq]

theorem minorMap_s0Mat : minorMap (s0Mat : Matrix (Fin 4) (Fin 4) K) =
    !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1] := by
  ext A B
  fin_cases A <;> fin_cases B <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, s0Mat,
      CharTwo.sub_eq_add, CharTwo.neg_eq]

theorem minorMap_s0Mat_mulVec (v : Fin 4 → K) :
    minorMap (s0Mat : Matrix (Fin 4) (Fin 4) K) *ᵥ v = ![v 2, v 3, v 0 + v 2, v 1 + v 3] := by
  rw [minorMap_s0Mat]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem fix_minorMap_s0Mat {v : Fin 4 → K}
    (hv : minorMap (s0Mat : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v) : v = 0 := by
  rw [minorMap_s0Mat_mulVec] at hv
  have h0 : v 2 = v 0 := congrFun hv 0
  have h1 : v 3 = v 1 := congrFun hv 1
  have h2 : v 0 + v 2 = v 2 := congrFun hv 2
  have h3 : v 1 + v 3 = v 3 := congrFun hv 3
  have e0 : v 0 = 0 := by linear_combination h2
  have e1 : v 1 = 0 := by linear_combination h3
  have e2 : v 2 = 0 := h0.trans e0
  have e3 : v 3 = 0 := h1.trans e1
  funext i
  fin_cases i <;> simp [e0, e1, e2, e3]

theorem card_fix_minorMap_s0Mat :
    Nat.card {v : Fin 4 → K // minorMap (s0Mat : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, Matrix.mulVec_zero _⟩⟩⟩
  exact Subtype.ext ((fix_minorMap_s0Mat a.2).trans (fix_minorMap_s0Mat b.2).symm)

@[expose] def mulVecEquiv (P : GL (Fin 4) K) : (Fin 4 → K) ≃ (Fin 4 → K) where
  toFun v := glMat P *ᵥ v
  invFun v := glMat P⁻¹ *ᵥ v
  left_inv v := by
    show glMat P⁻¹ *ᵥ (glMat P *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, P.inv_mul, Matrix.one_mulVec]
  right_inv v := by
    show glMat P *ᵥ (glMat P⁻¹ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, P.mul_inv, Matrix.one_mulVec]

theorem card_fix_conj (P M : GL (Fin 4) K) :
    Nat.card {v : Fin 4 → K // glMat (P * M * P⁻¹) *ᵥ v = v} =
      Nat.card {v : Fin 4 → K // glMat M *ᵥ v = v} := by
  refine Nat.card_congr ((mulVecEquiv P⁻¹).subtypeEquiv fun v => ?_)
  have h1 : glMat (P * M * P⁻¹) *ᵥ v = glMat P *ᵥ (glMat M *ᵥ (glMat P⁻¹ *ᵥ v)) := by
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h2 : v = glMat P *ᵥ (glMat P⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, P.mul_inv, Matrix.one_mulVec]
  show glMat (P * M * P⁻¹) *ᵥ v = v ↔ glMat M *ᵥ (glMat P⁻¹ *ᵥ v) = glMat P⁻¹ *ᵥ v
  rw [h1]
  constructor
  · intro h
    apply (mulVecEquiv P).injective
    show glMat P *ᵥ (glMat M *ᵥ (glMat P⁻¹ *ᵥ v)) = glMat P *ᵥ (glMat P⁻¹ *ᵥ v)
    rw [h, ← h2]
  · intro h
    rw [h, ← h2]

variable [Finite K]

theorem minorAut_sq_s0 : (minorAut K ^ 2) (s0 K) = s0 K := by
  rw [sq, MulAut.mul_apply]
  change minorHom K (minorHom K (s0 K)) = _
  rw [minorHom_minorHom]
  refine Subtype.ext (Units.ext ?_)
  change glMat (frobHom K (s0 K) : GL (Fin 4) K) = s0Mat
  rw [glMat_frobHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [glMat_s0, s0Mat]

theorem minorAut_pow_two_mul_s0 (k : ℕ) : (minorAut K ^ (2 * k)) (s0 K) = s0 K := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, MulAut.mul_apply, ih, minorAut_sq_s0]

theorem minorAut_pow_two_mul_add_one_s0 (k : ℕ) :
    (minorAut K ^ (2 * k + 1)) (s0 K) = minorAut K (s0 K) := by
  rw [pow_succ', MulAut.mul_apply, minorAut_pow_two_mul_s0]

theorem card_fix_pow_s0 (m : ℕ) :
    Nat.card {v : Fin 4 → K // glMat ((minorAut K ^ m) (s0 K) : GL (Fin 4) K) *ᵥ v = v} =
      if Even m then Nat.card K ^ 2 else 1 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [minorAut_pow_two_mul_s0, if_pos (even_two_mul k), glMat_s0]
    exact card_fix_s0
  · rw [minorAut_pow_two_mul_add_one_s0, if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)),
      glMat_minorAut, glMat_s0]
    exact card_fix_minorMap_s0Mat

theorem card_fix_ne_aux {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (i : ℕ) (h : antiSp K) {j : ℕ}
    (hj : Odd j) :
    Nat.card {v : Fin 4 → K // glMat ((minorAut K ^ i) (s0 K) : GL (Fin 4) K) *ᵥ v = v} ≠
      Nat.card {v : Fin 4 → K //
        glMat ((minorAut K ^ i) ((MulAut.conj h * minorAut K ^ j) (s0 K)) : GL (Fin 4) K) *ᵥ v = v} := by
  obtain ⟨k, rfl⟩ := hj
  have h1 : (MulAut.conj h * minorAut K ^ (2 * k + 1)) (s0 K) = h * minorAut K (s0 K) * h⁻¹ := by
    rw [MulAut.mul_apply, minorAut_pow_two_mul_add_one_s0, MulAut.conj_apply]
  have h2 : (minorAut K ^ i) (minorAut K (s0 K)) = (minorAut K ^ (i + 1)) (s0 K) := by
    rw [pow_succ, MulAut.mul_apply]
  rw [h1, map_mul, map_mul, map_inv, h2, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    card_fix_conj, card_fix_pow_s0, card_fix_pow_s0]
  have hK1 : 1 < Nat.card K := by
    rw [hK]
    exact Nat.one_lt_two_pow (by omega)
  have hK2 : Nat.card K ^ 2 ≠ 1 := (Nat.one_lt_pow two_ne_zero hK1).ne'
  rcases Nat.even_or_odd i with hev | hodd
  · rw [if_pos hev, if_neg (by simpa [Nat.even_add_one] using hev)]
    exact hK2
  · rw [if_neg (Nat.not_even_iff_odd.mpr hodd), if_pos (by simpa [Nat.even_add_one] using hodd)]
    exact hK2.symm

end S0

end AutAux

open AutAux in
theorem inducesInnerOn_trichotomy {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* antiSp K) {b₁ b₂ : G}
    (h₁ : b₁ ∈ Subgroup.normalizer (L : Set G)) (h₂ : b₂ ∈ Subgroup.normalizer (L : Set G))
    (hb₁ : b₁ * b₁ = 1) (hb₂ : b₂ * b₂ = 1) :
    InducesInnerOn L b₁ ∨ InducesInnerOn L b₂ ∨ InducesInnerOn L (b₁ * b₂) := by
  classical
  let B₁ : ↥(Subgroup.normalizer (L : Set G)) := ⟨b₁, h₁⟩
  let B₂ : ↥(Subgroup.normalizer (L : Set G)) := ⟨b₂, h₂⟩
  let a : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (antiSp K) :=
    (MulAut.congr e).toMonoidHom.comp (condHom L)
  have haB : ∀ B, a B = MulAut.congr e (condHom L B) := fun B => rfl
  have hB₁ : a B₁ * a B₁ = 1 := by
    rw [← map_mul, show B₁ * B₁ = 1 from Subtype.ext hb₁, map_one]
  have hB₂ : a B₂ * a B₂ = 1 := by
    rw [← map_mul, show B₂ * B₂ = 1 from Subtype.ext hb₂, map_one]
  by_cases c₁ : a B₁ ∈ inner (antiSp K)
  · exact Or.inl (inducesInnerOn_of_mem_inner e (haB B₁ ▸ c₁))
  by_cases c₂ : a B₂ ∈ inner (antiSp K)
  · exact Or.inr (Or.inl (inducesInnerOn_of_mem_inner e (haB B₂ ▸ c₂)))
  refine Or.inr (Or.inr ?_)
  obtain ⟨g₁, hg₁⟩ := X7b.outer_involution_form hn hK (a B₁) hB₁ c₁
  obtain ⟨g₂, hg₂⟩ := X7b.outer_involution_form hn hK (a B₂) hB₂ c₂
  have hρ := minorAut_pow_two_mul hn hK
  have key : a (B₁ * B₂) ∈ inner (antiSp K) := by
    rw [map_mul, hg₁, hg₂]
    refine ⟨g₁ * (minorAut K ^ n) g₂, ?_⟩
    rw [map_mul, X7b.conj_apply_eq']
    calc MulAut.conj g₁ * (minorAut K ^ n * MulAut.conj g₂ * (minorAut K ^ n)⁻¹)
        = MulAut.conj g₁ * (minorAut K ^ n * MulAut.conj g₂ * (minorAut K ^ n)⁻¹) *
            (minorAut K ^ n * minorAut K ^ n) := by
          rw [← pow_add, ← two_mul, hρ, mul_one]
      _ = MulAut.conj g₁ * minorAut K ^ n * (MulAut.conj g₂ * minorAut K ^ n) := by group
  exact inducesInnerOn_of_mem_inner e (haB (B₁ * B₂) ▸ key)

open AutAux in
theorem exists_card_fix_ne_of_diagram {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* antiSp K) (i : ℕ) {g : G}
    (hg : ActsNontrivOnDiagramIn L g) :
    ∃ s s' : ↥L, orderOf s = 3 ∧ (s' : G) = g * s * g⁻¹ ∧
      Nat.card {v : Fin 4 → K // glMat ((minorAut K ^ i) (e s)) *ᵥ v = v} ≠
        Nat.card {v : Fin 4 → K // glMat ((minorAut K ^ i) (e s')) *ᵥ v = v} := by
  classical
  obtain ⟨hgN, θ, hθ, hnot⟩ := hg
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv_antiSp e
  let κ : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hκ : ∀ x : ↥L, κ.symm x = QuotientGroup.mk x := fun x => by
    apply κ.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  let ε : ↥L ⧸ Subgroup.center ↥L ≃* antiSp K := κ.trans e
  have hθ' : ∀ x x' : ↥L, (x' : G) = g * x * g⁻¹ → MulAut.congr ε θ (e x) = e x' := by
    intro x x' hx
    have h0 : MulAut.congr ε θ (e x) = ε (θ (ε.symm (e x))) := rfl
    have h1 : ε.symm (e x) = QuotientGroup.mk x := by
      rw [MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply, hκ]
    rw [h0, h1, hθ x x' hx]
    show e (κ (QuotientGroup.mk x')) = e x'
    rw [← hκ x', MulEquiv.apply_symm_apply]
  obtain ⟨h, j, -, hj⟩ := X7b.aut_eq_conj_mul_pow hn1 hK (MulAut.congr ε θ)
  rcases Nat.even_or_odd j with hev | hodd
  · exfalso
    obtain ⟨k, hk⟩ := hev
    apply hnot
    rw [← uc22p22wi_isInnDiagFieldAut_congr ε θ, hj, hk, ← two_mul]
    exact isInnDiagFieldAut_conj_mul_pow_even hn1 hK h k
  · let s : ↥L := e.symm (s0 K)
    let s' : ↥L := ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN s).mp s.2⟩
    have hs : e s = s0 K := e.apply_symm_apply _
    have hs' : e s' = (MulAut.conj h * minorAut K ^ j) (s0 K) := by
      rw [← hj, ← hs]
      exact (hθ' s s' rfl).symm
    refine ⟨s, s', (MulEquiv.orderOf_eq e.symm _).trans orderOf_s0, rfl, ?_⟩
    rw [hs, hs']
    exact card_fix_ne_aux hn1 hK i h hodd

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
