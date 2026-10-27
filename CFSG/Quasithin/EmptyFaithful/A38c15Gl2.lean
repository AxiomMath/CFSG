module

public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Quasithin.EmptyFaithful.A38c15Line

public section

namespace CFSG.Quasithin.A38c15

open Matrix CFSG.RankThree.SubgroupLists
open scoped commutatorElement

section Trace

variable {K : Type*} [Field K]

theorem pow_five_fin_two (X : Matrix (Fin 2) (Fin 2) K) (t : K) (h : X * X = t • X - 1) :
    X ^ 5 = (t ^ 4 - 3 * t ^ 2 + 1) • X - (t ^ 3 - 2 * t) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h3 : X ^ 3 = (t ^ 2 - 1) • X - t • (1 : Matrix (Fin 2) (Fin 2) K) := by
    calc X ^ 3 = X * (X * X) := by rw [pow_succ', pow_two]
      _ = X * (t • X - 1) := by rw [h]
      _ = t • (X * X) - X := by rw [mul_sub, mul_smul_comm, mul_one]
      _ = t • (t • X - 1) - X := by rw [h]
      _ = (t ^ 2 - 1) • X - t • 1 := by module
  have h4 : X ^ 4 = (t ^ 3 - 2 * t) • X - (t ^ 2 - 1) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    calc X ^ 4 = X * X ^ 3 := by rw [pow_succ']
      _ = X * ((t ^ 2 - 1) • X - t • 1) := by rw [h3]
      _ = (t ^ 2 - 1) • (X * X) - t • X := by
          rw [mul_sub, mul_smul_comm, mul_smul_comm, mul_one]
      _ = (t ^ 2 - 1) • (t • X - 1) - t • X := by rw [h]
      _ = (t ^ 3 - 2 * t) • X - (t ^ 2 - 1) • 1 := by module
  calc X ^ 5 = X * X ^ 4 := by rw [pow_succ']
    _ = X * ((t ^ 3 - 2 * t) • X - (t ^ 2 - 1) • 1) := by rw [h4]
    _ = (t ^ 3 - 2 * t) • (X * X) - (t ^ 2 - 1) • X := by
        rw [mul_sub, mul_smul_comm, mul_smul_comm, mul_one]
    _ = (t ^ 3 - 2 * t) • (t • X - 1) - (t ^ 2 - 1) • X := by rw [h]
    _ = (t ^ 4 - 3 * t ^ 2 + 1) • X - (t ^ 3 - 2 * t) • 1 := by module

theorem trace_sq_add_trace_sub_one {X : Matrix (Fin 2) (Fin 2) K} (hX : X.det = 1)
    (h5 : X ^ 5 = 1) (h1 : X ≠ 1) : X.trace ^ 2 + X.trace - 1 = 0 := by
  set t := X.trace with ht
  have hsq : X * X = t • X - 1 := by
    rw [mul_self_fin_two, hX, one_smul]
  have hp := pow_five_fin_two X t hsq
  rw [h5] at hp
  have hA : (t ^ 4 - 3 * t ^ 2 + 1) • X = (1 + (t ^ 3 - 2 * t)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have : (t ^ 4 - 3 * t ^ 2 + 1) • X = 1 + (t ^ 3 - 2 * t) • (1 : Matrix (Fin 2) (Fin 2) K) :=
      sub_eq_iff_eq_add.mp hp.symm
    rw [this, add_smul, one_smul]
  have hA0 : t ^ 4 - 3 * t ^ 2 + 1 = 0 := by
    by_contra hne
    apply h1
    have hX' : X = ((t ^ 4 - 3 * t ^ 2 + 1)⁻¹ * (1 + (t ^ 3 - 2 * t))) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [mul_smul, ← hA, smul_smul, inv_mul_cancel₀ hne, one_smul]
    set c := (t ^ 4 - 3 * t ^ 2 + 1)⁻¹ * (1 + (t ^ 3 - 2 * t)) with hc
    have hdet : c ^ 2 = 1 := by
      have := congrArg Matrix.det hX'
      rw [hX] at this
      simpa [Matrix.det_smul, sq] using this.symm
    have h5c : c ^ 5 = 1 := by
      have := congrArg (fun M => M ^ 5) hX'
      simp only [h5, smul_pow, one_pow] at this
      have h' := congrFun (congrFun this 0) 0
      simpa using h'.symm
    have hc1 : c = 1 := by
      have h' : c ^ 5 = c * (c ^ 2) ^ 2 := by ring
      rw [h', hdet] at h5c
      simpa using h5c
    rw [hX', hc1, one_smul]
  have hB : 1 + (t ^ 3 - 2 * t) = 0 := by
    rw [hA0, zero_smul] at hA
    have h' := congrFun (congrFun hA 0) 0
    simp at h'
    exact h'.symm
  by_contra hne
  have h3 : (t - 1) * (t ^ 2 + t - 1) = 0 := by linear_combination hB
  have h4 : (t ^ 2 + t - 1) * (t ^ 2 - t - 1) = 0 := by linear_combination hA0
  have ht1 : t - 1 = 0 := (mul_eq_zero.mp h3).resolve_right hne
  have ht2 : t ^ 2 - t - 1 = 0 := (mul_eq_zero.mp h4).resolve_left hne
  have : t = 1 := by linear_combination ht1
  rw [this] at ht2
  norm_num at ht2

theorem trace_ne_trace_sq {X : Matrix (Fin 2) (Fin 2) K} (h5K : (5 : K) ≠ 0) (hX : X.det = 1)
    (h5 : X ^ 5 = 1) (h1 : X ≠ 1) : X.trace ≠ (X ^ 2).trace := by
  intro hEq
  have h := trace_sq_add_trace_sub_one hX h5 h1
  have hsq : X * X = X.trace • X - 1 := by rw [mul_self_fin_two, hX, one_smul]
  have htr2 : (X ^ 2).trace = X.trace ^ 2 - 2 := by
    rw [pow_two, hsq, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp [sq]
  rw [htr2] at hEq
  set t := X.trace with ht
  have h3 : 2 * t + 1 = 0 := by linear_combination h + hEq
  apply h5K
  linear_combination (2 * t + 1) * h3 - 4 * h

theorem exists_eq_add_smul_of_commute {X M : Matrix (Fin 2) (Fin 2) K}
    (hX : ∀ c : K, X ≠ Matrix.scalar (Fin 2) c) (hc : M * X = X * M) :
    ∃ a b : K, M = a • (1 : Matrix (Fin 2) (Fin 2) K) + b • X := by
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases h10 : X 1 0 = 0
  · by_cases h01 : X 0 1 = 0
    ·
      have h00 : X 0 0 - X 1 1 ≠ 0 := by
        intro h
        apply hX (X 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h10, h01, sub_eq_zero.mp h]
      have hb : (M 0 0 - M 1 1) / (X 0 0 - X 1 1) * (X 0 0 - X 1 1) = M 0 0 - M 1 1 :=
        div_mul_cancel₀ _ h00
      have hM01 : M 0 1 = 0 := by
        have : M 0 1 * (X 0 0 - X 1 1) = 0 := by
          linear_combination (-1 : K) * e01 + (M 0 0 - M 1 1) * h01
        exact (mul_eq_zero.mp this).resolve_right h00
      have hM10 : M 1 0 = 0 := by
        have : M 1 0 * (X 0 0 - X 1 1) = 0 := by
          linear_combination e10 + (M 0 0 - M 1 1) * h10
        exact (mul_eq_zero.mp this).resolve_right h00
      refine ⟨M 1 1 - (M 0 0 - M 1 1) / (X 0 0 - X 1 1) * X 1 1,
        (M 0 0 - M 1 1) / (X 0 0 - X 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one]
        linear_combination (-1 : K) * hb
      · simp [hM01, h01]
      · simp [hM10, h10]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one]
        ring
    ·
      have hb : (M 0 1 / X 0 1) * X 0 1 = M 0 1 := div_mul_cancel₀ _ h01
      refine ⟨M 1 1 - (M 0 1 / X 0 1) * X 1 1, M 0 1 / X 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one]
        apply mul_right_cancel₀ h01
        linear_combination e01 + (X 1 1 - X 0 0) * hb
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul, mul_zero, zero_add]
        exact hb.symm
      · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_zero, zero_add]
        apply mul_right_cancel₀ h01
        linear_combination (-1 : K) * e00 - X 1 0 * hb
      · simp only [Fin.mk_one, Fin.isValue, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one]
        ring
  ·
    have hb : (M 1 0 / X 1 0) * X 1 0 = M 1 0 := div_mul_cancel₀ _ h10
    refine ⟨M 1 1 - (M 1 0 / X 1 0) * X 1 1, M 1 0 / X 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one]
      apply mul_right_cancel₀ h10
      linear_combination (-1 : K) * e10 + (X 1 1 - X 0 0) * hb
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul, mul_zero, zero_add]
      apply mul_right_cancel₀ h10
      linear_combination e00 - X 0 1 * hb
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_zero, zero_add]
      exact hb.symm
    · simp only [Fin.mk_one, Fin.isValue, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one]
      ring

end Trace

section Schur

variable {K : Type*} [Field K]

theorem scalar_fin_two_eq_smul_one (c : K) :
    Matrix.scalar (Fin 2) c = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem not_scalar_of_order_five {x₀ : GL (Fin 2) K}
    (hdet : (x₀ : Matrix (Fin 2) (Fin 2) K).det = 1) (h5 : x₀ ^ 5 = 1) (h1 : x₀ ≠ 1) :
    ∀ c : K, (x₀ : Matrix (Fin 2) (Fin 2) K) ≠ Matrix.scalar (Fin 2) c := by
  intro c hc
  rw [scalar_fin_two_eq_smul_one] at hc
  have hc2 : c ^ 2 = 1 := by
    have := congrArg Matrix.det hc
    rw [hdet] at this
    simpa [Matrix.det_smul, sq] using this.symm
  have hc5 : c ^ 5 = 1 := by
    have hX5 : (x₀ : Matrix (Fin 2) (Fin 2) K) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h5, Units.val_one]
    rw [hc, smul_pow, one_pow] at hX5
    have h' := congrFun (congrFun hX5 0) 0
    simpa using h'
  have hc1 : c = 1 := by
    have h' : c ^ 5 = c * (c ^ 2) ^ 2 := by ring
    rw [h', hc2] at hc5
    simpa using hc5
  apply h1
  apply Units.ext
  rw [hc, hc1, one_smul, Units.val_one]

theorem scalar_of_commute_pair {x₀ h₀ : GL (Fin 2) K}
    (hdet : (x₀ : Matrix (Fin 2) (Fin 2) K).det = 1) (h5 : x₀ ^ 5 = 1) (h1 : x₀ ≠ 1)
    (hconj : h₀ * x₀ * h₀⁻¹ = x₀ ^ 4) {M : Matrix (Fin 2) (Fin 2) K}
    (hx : (x₀ : Matrix (Fin 2) (Fin 2) K) * M = M * x₀)
    (hh : (h₀ : Matrix (Fin 2) (Fin 2) K) * M = M * h₀) :
    ∃ c : K, M = Matrix.scalar (Fin 2) c := by
  obtain ⟨a, b, hM⟩ := exists_eq_add_smul_of_commute (not_scalar_of_order_five hdet h5 h1) hx.symm
  have hb : b = 0 := by
    by_contra hb0
    have hx4 : x₀ ^ 4 ≠ x₀ := by
      intro h4
      apply h1
      have h3 : x₀ ^ 3 = 1 := by
        have : x₀ * x₀ ^ 3 = x₀ * 1 := by rw [← pow_succ', mul_one]; exact h4
        exact mul_left_cancel this
      have h2 : x₀ ^ 2 = 1 := by
        have : x₀ ^ 3 * x₀ ^ 2 = x₀ ^ 3 * 1 := by rw [← pow_add, mul_one, h3]; exact h5
        exact mul_left_cancel this
      calc x₀ = x₀ ^ 3 := by rw [pow_succ, h2, one_mul]
        _ = 1 := h3
    have hHX : (h₀ : Matrix (Fin 2) (Fin 2) K) * x₀ = (x₀ : Matrix (Fin 2) (Fin 2) K) ^ 4 * h₀ := by
      have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) * h₀) hconj
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this
      simpa [mul_assoc] using this
    have e1 : b • ((x₀ : Matrix (Fin 2) (Fin 2) K) * h₀) = b • ((h₀ : Matrix (Fin 2) (Fin 2) K) * x₀) := by
      have := hh
      rw [hM] at this
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at this
      have h' := add_left_cancel this
      exact h'.symm
    rw [hHX, ← sub_eq_zero, ← smul_sub, ← sub_mul] at e1
    rcases smul_eq_zero.mp e1 with h0 | h0
    · exact hb0 h0
    · have hXX : (x₀ : Matrix (Fin 2) (Fin 2) K) = (x₀ : Matrix (Fin 2) (Fin 2) K) ^ 4 := by
        have h' := congrArg (fun N => N * ((h₀⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h0
        simp only [zero_mul, Matrix.mul_assoc] at h'
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at h'
        exact sub_eq_zero.mp h'
      apply hx4
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact hXX.symm
  exact ⟨a, by rw [hM, hb, zero_smul, add_zero, scalar_fin_two_eq_smul_one]⟩

end Schur

section A5

open Equiv

@[expose] def c5 : alternatingGroup (Fin 5) :=
  ⟨finRotate 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def inv5 : alternatingGroup (Fin 5) :=
  ⟨swap 1 4 * swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def sq5 : Perm (Fin 5) := swap 1 2 * swap 2 4 * swap 4 3

theorem inv5_conj : inv5 * c5 * inv5⁻¹ = c5 ^ 4 := Subtype.ext (by decide)

theorem sq5_conj : sq5 * (c5 : Perm (Fin 5)) * sq5⁻¹ = (c5 : Perm (Fin 5)) ^ 2 := by decide

theorem sign_sq5 : Perm.sign sq5 = -1 := by decide

theorem c5_pow_five : c5 ^ 5 = 1 := Subtype.ext (by decide)

theorem c5_ne_one : c5 ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  revert this
  decide

theorem commutator_mul_mul_of_central {G : Type*} [Group G] {x₁ x₂ w₁ w₂ : G}
    (c1 : ∀ g : G, g * w₁ = w₁ * g) (c2 : ∀ g : G, g * w₂ = w₂ * g) :
    ⁅x₁ * w₁, x₂ * w₂⁆ = ⁅x₁, x₂⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x₁ * w₁ * (x₂ * w₂) * (x₁ * w₁)⁻¹ * (x₂ * w₂)⁻¹
      = x₁ * (w₁ * x₂) * w₂ * w₁⁻¹ * x₁⁻¹ * w₂⁻¹ * x₂⁻¹ := by group
    _ = x₁ * (x₂ * w₁) * w₂ * w₁⁻¹ * x₁⁻¹ * w₂⁻¹ * x₂⁻¹ := by rw [c1 x₂]
    _ = x₁ * x₂ * (w₁ * w₂ * w₁⁻¹) * x₁⁻¹ * w₂⁻¹ * x₂⁻¹ := by group
    _ = x₁ * x₂ * (w₂ * w₁ * w₁⁻¹) * x₁⁻¹ * w₂⁻¹ * x₂⁻¹ := by rw [c1 w₂]
    _ = x₁ * x₂ * (w₂ * x₁⁻¹) * w₂⁻¹ * x₂⁻¹ := by group
    _ = x₁ * x₂ * (x₁⁻¹ * w₂) * w₂⁻¹ * x₂⁻¹ := by rw [c2 x₁⁻¹]
    _ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ := by group

end A5

section Normalizer

open Equiv

variable {K : Type} [Field K]

theorem exists_eq_mul_scalar_of_normalizes_sl25 (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (Y : Subgroup (GL (Fin 2) K)) (hperf : ⁅Y, Y⁆ = Y)
    (hdet : ∀ y ∈ Y, (y : Matrix (Fin 2) (Fin 2) K).det = 1)
    (hcen : ∀ y : Y, y ∈ Subgroup.center ↥Y ↔
      (y : GL (Fin 2) K) = 1 ∨ (y : GL (Fin 2) K) = -1)
    (φ : (↥Y ⧸ Subgroup.center ↥Y) ≃* alternatingGroup (Fin 5))
    {g : GL (Fin 2) K} (hg : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y) (hg' : ∀ x ∈ Y, g⁻¹ * x * g ∈ Y) :
    ∃ y ∈ Y, ∃ c : K, (g : Matrix (Fin 2) (Fin 2) K) =
      (y : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) c := by
  classical
  have hneg : (-1 : GL (Fin 2) K) ≠ 1 := by
    intro h
    have := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at this
    exact h2 (by linear_combination -this)
  have hnegc : ∀ x : GL (Fin 2) K, x * (-1 : GL (Fin 2) K) = (-1 : GL (Fin 2) K) * x := fun x => by
    simp
  let α : ↥Y ≃* ↥Y :=
    { toFun := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, hg' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hαapply : ∀ x : ↥Y, ((α x : ↥Y) : GL (Fin 2) K) = g * x * g⁻¹ := fun x => rfl
  have hαc : (Subgroup.center ↥Y).map α.toMonoidHom = Subgroup.center ↥Y :=
    Subgroup.map_center_eq α
  let ᾱ : (↥Y ⧸ Subgroup.center ↥Y) ≃* (↥Y ⧸ Subgroup.center ↥Y) :=
    QuotientGroup.congr _ _ α hαc
  let α' : MulAut (alternatingGroup (Fin 5)) := (φ.symm.trans ᾱ).trans φ
  let Φ : ↥Y →* alternatingGroup (Fin 5) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Y))
  have hΦs : Function.Surjective Φ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hΦα : ∀ y : ↥Y, Φ (α y) = α' (Φ y) := by
    intro y
    have h1 : ᾱ (QuotientGroup.mk y) = QuotientGroup.mk (α y) :=
      QuotientGroup.congr_mk _ _ α hαc y
    show φ (QuotientGroup.mk (α y)) = φ (ᾱ (φ.symm (φ (QuotientGroup.mk y))))
    rw [φ.symm_apply_apply, h1]
  have hΦeq : ∀ y z : ↥Y, Φ y = Φ z → ∃ ε : GL (Fin 2) K, (ε = 1 ∨ ε = -1) ∧
      (z : GL (Fin 2) K) = (y : GL (Fin 2) K) * ε := by
    intro y z hyz
    have h1 : (y⁻¹ * z) ∈ Subgroup.center ↥Y := by
      have : φ (QuotientGroup.mk (y⁻¹ * z)) = 1 := by
        have h' : Φ (y⁻¹ * z) = 1 := by rw [map_mul, map_inv, hyz, inv_mul_cancel]
        exact h'
      rw [map_eq_one_iff φ φ.injective] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    obtain ⟨ε, hε, hεeq⟩ : ∃ ε : GL (Fin 2) K, (ε = 1 ∨ ε = -1) ∧
        ((y⁻¹ * z : ↥Y) : GL (Fin 2) K) = ε := ⟨_, (hcen _).mp h1, rfl⟩
    refine ⟨ε, hε, ?_⟩
    rw [← hεeq]
    simp
  have hlift5 : ∀ u v : ↥Y, Φ u = Φ v → (u : GL (Fin 2) K) ^ 5 = 1 → (v : GL (Fin 2) K) ^ 5 = 1 →
      (u : GL (Fin 2) K) = v := by
    intro u v huv hu hv
    obtain ⟨ε, hε, hεeq⟩ := hΦeq u v huv
    rcases hε with rfl | rfl
    · simpa using hεeq.symm
    · exfalso
      have h' : ((v : GL (Fin 2) K)) ^ 5 = (u : GL (Fin 2) K) ^ 5 * (-1) ^ 5 := by
        rw [hεeq]
        exact (Commute.mul_pow (Commute.symm (Commute.neg_one_left _)) 5)
      rw [hv, hu, Odd.neg_one_pow (by decide)] at h'
      exact hneg (by simpa using h'.symm)
  obtain ⟨π, hπ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
      (by norm_num)).2 α'
  have key : ∀ y : alternatingGroup (Fin 5),
      ((α' y : alternatingGroup (Fin 5)) : Perm (Fin 5)) = π * y * π⁻¹ := by
    intro y
    rw [← hπ, MulAut.conjNormal_apply]
  obtain ⟨y₀, hy₀⟩ := hΦs c5
  let x₀ : ↥Y := y₀ ^ 6
  have hx₀Φ : Φ x₀ = c5 := by
    simp only [x₀, map_pow, hy₀]
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, c5_pow_five, one_mul]
  have hy010 : (y₀ : GL (Fin 2) K) ^ 10 = 1 := by
    have h1 : Φ (y₀ ^ 5) = Φ 1 := by rw [map_pow, hy₀, c5_pow_five, map_one]
    obtain ⟨ε, hε, hεeq⟩ := hΦeq _ _ h1
    have h2 : (y₀ : GL (Fin 2) K) ^ 5 * ε = 1 := by
      have := hεeq.symm
      simpa using this
    rcases hε with rfl | rfl
    · have : (y₀ : GL (Fin 2) K) ^ 5 = 1 := by simpa using h2
      calc (y₀ : GL (Fin 2) K) ^ 10 = ((y₀ : GL (Fin 2) K) ^ 5) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [this, one_pow]
    · have : (y₀ : GL (Fin 2) K) ^ 5 = -1 := by
        have h3 := congrArg (fun z => z * (-1 : GL (Fin 2) K)) h2
        simpa using h3
      calc (y₀ : GL (Fin 2) K) ^ 10 = ((y₀ : GL (Fin 2) K) ^ 5) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [this]; simp
  have hx₀pow : (x₀ : GL (Fin 2) K) ^ 5 = 1 := by
    have : (x₀ : GL (Fin 2) K) = (y₀ : GL (Fin 2) K) ^ 6 := rfl
    rw [this, ← pow_mul, show 6 * 5 = 10 * 3 by norm_num, pow_mul, hy010, one_pow]
  have hx₀det : ((x₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := hdet _ x₀.2
  have hx₀ne : (x₀ : GL (Fin 2) K) ≠ 1 := by
    intro h
    have : x₀ = 1 := Subtype.ext h
    have h' : Φ x₀ = 1 := by rw [this, map_one]
    rw [hx₀Φ] at h'
    exact c5_ne_one h'
  have hx₀ne' : ((x₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h =>
    hx₀ne (Units.ext (by simpa using h))
  have hx₀pow' : ((x₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx₀pow, Units.val_one]
  clear_value x₀
  have hπeven : Perm.sign π = 1 := by
    by_contra hodd
    have hπ1 : Perm.sign π = -1 := (Int.units_eq_one_or _).resolve_left hodd
    set σ : alternatingGroup (Fin 5) := ⟨π * sq5⁻¹, Equiv.Perm.mem_alternatingGroup.mpr
      (by rw [Perm.sign_mul, Perm.sign_inv, hπ1, sign_sq5]; rfl)⟩ with hσ
    have hc : α' c5 = σ * c5 ^ 2 * σ⁻¹ := by
      apply Subtype.ext
      rw [key, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hσ,
        ← sq5_conj]
      simp only
      group
    obtain ⟨s, hs⟩ := hΦs σ
    have hΦu : Φ (α x₀) = Φ (s * x₀ ^ 2 * s⁻¹) := by
      rw [hΦα, hx₀Φ, hc, map_mul, map_mul, map_inv, map_pow, hs, hx₀Φ]
    have hαx5 : ((α x₀ : ↥Y) : GL (Fin 2) K) ^ 5 = 1 := by
      rw [hαapply, conj_pow, hx₀pow, mul_one, mul_inv_cancel]
    have hux5 : ((s * x₀ ^ 2 * s⁻¹ : ↥Y) : GL (Fin 2) K) ^ 5 = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      rw [conj_pow, ← pow_mul, mul_comm 2 5, pow_mul, hx₀pow, one_pow, mul_one, mul_inv_cancel]
    have heq := hlift5 _ _ hΦu hαx5 hux5
    have htr : ((x₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace =
        (((x₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2).trace := by
      calc ((x₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace
          = (((g * x₀ * g⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K).trace := by
            rw [Units.val_mul, Units.val_mul, Matrix.trace_units_conj]
        _ = ((((s * x₀ ^ 2 * s⁻¹ : ↥Y)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace := by
            rw [← hαapply, heq]
        _ = (((x₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2).trace := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, Units.val_mul,
              Units.val_pow_eq_pow_val]
            rw [Matrix.trace_units_conj]
    exact trace_ne_trace_sq h5 hx₀det hx₀pow' hx₀ne' htr
  set π' : alternatingGroup (Fin 5) :=
    ⟨π, Equiv.Perm.mem_alternatingGroup.mpr hπeven⟩ with hπ'
  obtain ⟨h, hh⟩ := hΦs π'
  have hΦconj : ∀ y : ↥Y, Φ (h * y * h⁻¹) = Φ (α y) := by
    intro y
    rw [map_mul, map_mul, map_inv, hh, hΦα]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, key]
  have hgε : ∀ y : ↥Y, ∃ ε : GL (Fin 2) K, (ε = 1 ∨ ε = -1) ∧
      g * (y : GL (Fin 2) K) * g⁻¹ = (h : GL (Fin 2) K) * y * (h : GL (Fin 2) K)⁻¹ * ε := by
    intro y
    obtain ⟨ε, hε, hεeq⟩ := hΦeq _ _ (hΦconj y)
    refine ⟨ε, hε, ?_⟩
    rw [← hαapply]
    simpa using hεeq
  have hεc : ∀ ε : GL (Fin 2) K, (ε = 1 ∨ ε = -1) → ∀ z : GL (Fin 2) K, z * ε = ε * z := by
    intro ε hε z
    rcases hε with rfl | rfl
    · simp
    · exact hnegc z
  set g' : GL (Fin 2) K := (h : GL (Fin 2) K)⁻¹ * g with hg'def
  have hcentral : ∀ y : ↥Y, ∃ ε : GL (Fin 2) K, (ε = 1 ∨ ε = -1) ∧
      g' * (y : GL (Fin 2) K) * g'⁻¹ = y * ε := by
    intro y
    obtain ⟨ε, hε, hεeq⟩ := hgε y
    refine ⟨ε, hε, ?_⟩
    calc g' * (y : GL (Fin 2) K) * g'⁻¹
        = (h : GL (Fin 2) K)⁻¹ * (g * (y : GL (Fin 2) K) * g⁻¹) * h := by
          simp only [hg'def]
          group
      _ = (h : GL (Fin 2) K)⁻¹ * ((h : GL (Fin 2) K) * y * (h : GL (Fin 2) K)⁻¹ * ε) * h := by
          rw [hεeq]
      _ = (y : GL (Fin 2) K) * ((h : GL (Fin 2) K)⁻¹ * ε * h) := by group
      _ = y * ε := by
          rw [hεc ε hε (h : GL (Fin 2) K)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hcomm : ∀ a ∈ Y, ∀ b ∈ Y, ⁅a, b⁆ ∈ Subgroup.centralizer ({g'} : Set (GL (Fin 2) K)) := by
    intro a ha b hb
    obtain ⟨εa, hεa, hea⟩ := hcentral ⟨a, ha⟩
    obtain ⟨εb, hεb, heb⟩ := hcentral ⟨b, hb⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g' * ⁅a, b⁆ * g'⁻¹ = ⁅a, b⁆ := by
      have : g' * ⁅a, b⁆ * g'⁻¹ = ⁅g' * a * g'⁻¹, g' * b * g'⁻¹⁆ :=
        map_commutatorElement (MulAut.conj g') a b
      rw [this]
      have hea' : g' * a * g'⁻¹ = a * εa := hea
      have heb' : g' * b * g'⁻¹ = b * εb := heb
      rw [hea', heb']
      exact commutator_mul_mul_of_central (hεc εa hεa) (hεc εb hεb)
    calc ⁅a, b⁆ * g' = (g' * ⁅a, b⁆ * g'⁻¹) * g' := by rw [h1]
      _ = g' * ⁅a, b⁆ := by group
  have hYc : ∀ y ∈ Y, g' * y = y * g' := by
    have h1 : ⁅Y, Y⁆ ≤ Subgroup.centralizer ({g'} : Set (GL (Fin 2) K)) :=
      Subgroup.commutator_le.mpr hcomm
    rw [hperf] at h1
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h1 hy)).symm
  obtain ⟨h₀, hh₀⟩ := hΦs inv5
  have hconj : (h₀ : GL (Fin 2) K) * x₀ * (h₀ : GL (Fin 2) K)⁻¹ = (x₀ : GL (Fin 2) K) ^ 4 := by
    have hΦ' : Φ (h₀ * x₀ * h₀⁻¹) = Φ (x₀ ^ 4) := by
      rw [map_mul, map_mul, map_inv, map_pow, hh₀, hx₀Φ, inv5_conj]
    have hu5 : ((h₀ * x₀ * h₀⁻¹ : ↥Y) : GL (Fin 2) K) ^ 5 = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [conj_pow, hx₀pow, mul_one, mul_inv_cancel]
    have hv5 : ((x₀ ^ 4 : ↥Y) : GL (Fin 2) K) ^ 5 = 1 := by
      simp only [Subgroup.coe_pow]
      rw [← pow_mul, mul_comm 4 5, pow_mul, hx₀pow, one_pow]
    have := hlift5 _ _ hΦ' hu5 hv5
    simpa using this
  have hx : ((x₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (g' : Matrix (Fin 2) (Fin 2) K) =
      (g' : Matrix (Fin 2) (Fin 2) K) * (x₀ : GL (Fin 2) K) := by
    rw [← Units.val_mul, ← Units.val_mul, ← hYc x₀ x₀.2]
  have hhm : ((h₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (g' : Matrix (Fin 2) (Fin 2) K) =
      (g' : Matrix (Fin 2) (Fin 2) K) * (h₀ : GL (Fin 2) K) := by
    rw [← Units.val_mul, ← Units.val_mul, ← hYc h₀ h₀.2]
  obtain ⟨c, hc⟩ := scalar_of_commute_pair hx₀det hx₀pow hx₀ne hconj hx hhm
  refine ⟨(h : GL (Fin 2) K), h.2, c, ?_⟩
  have hgg : g = (h : GL (Fin 2) K) * g' := by simp [hg'def]
  rw [hgg, Units.val_mul, hc]

end Normalizer

section Assembly

open Equiv CFSG.Quasithin

theorem eight_dvd_card_pgl2 {F : Type} [Field F] [Finite F] {p : ℕ} (hF : Nat.card F = p)
    (hp : Odd p) (hp1 : 1 < p) : 8 ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) := by
  have := Fintype.ofFinite F
  obtain ⟨m, rfl⟩ := hp
  have hm : 1 ≤ m := by omega
  have hq : Fintype.card F = 2 * m + 1 := by rw [← Nat.card_eq_fintype_card, hF]
  have hGL : Nat.card (GL (Fin 2) F) = 4 * m * (m + 1) * ((2 * m + 1) * (2 * m)) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, hq]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    rw [Nat.sub_eq_of_eq_add (show (2 * m + 1) ^ 2 = 4 * m * (m + 1) + 1 by ring),
      Nat.sub_eq_of_eq_add (show (2 * m + 1) ^ 2 = (2 * m + 1) * (2 * m) + (2 * m + 1) by ring)]
  have hZ : Nat.card (Subgroup.center (GL (Fin 2) F)) = 2 * m := by
    have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        Fˣ →* GL (Fin 2) F) :=
      fun a b hab => by
        have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hab
        exact Units.ext (by simpa using this)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hF]
    omega
  have h := (Subgroup.center (GL (Fin 2) F)).card_mul_index
  rw [hZ, hGL] at h
  have hP : Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) = 4 * m * (m + 1) * (2 * m + 1) := by
    change (Subgroup.center (GL (Fin 2) F)).index = _
    have h2 : 2 * m * (Subgroup.center (GL (Fin 2) F)).index =
        2 * m * (4 * m * (m + 1) * (2 * m + 1)) := by
      rw [h]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  rw [hP]
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self m
  exact ⟨j * (2 * m + 1), by rw [show 4 * m * (m + 1) * (2 * m + 1) =
    4 * (m * (m + 1)) * (2 * m + 1) by ring, hj]; ring⟩

theorem card_alt_five_fin : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem gl2OddIndex : GL2OddIndex := by
  intro p _ hp2 M hodd hns g hdg
  classical
  have hpp : p.Prime := Fact.out
  have hpodd : Odd p := hpp.odd_of_ne_two hp2
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  set Q : Subgroup (GL (Fin 2) (ZMod p)) := perfectCore M with hQdef
  have hQperf : ⁅Q, Q⁆ = Q := perfectCore_perfect M
  have hQM : Q ≤ M := perfectCore_le M
  have hQne : Q ≠ ⊥ := fun h => hns ((isSolvable_iff_perfectCore_eq_bot M).mpr h)
  have : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.mpr hQperf
  obtain ⟨-, hcen, -, -, hdiv, hndiv⟩ :=
    CFSG.SectionRank.Ccomm.perfect_prime_linear_recognition hp2 Q hQne
  by_cases hpQ : p ∣ Nat.card Q
  · have hQeq := (hdiv hpQ).1
    have hgQ : g ∈ Q := by
      rw [hQeq]
      exact ⟨⟨(g : Matrix (Fin 2) (Fin 2) (ZMod p)), hdg⟩, Units.ext rfl⟩
    exact hQM hgQ
  · exfalso
    obtain ⟨eP⟩ := hndiv hpQ
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨eA⟩ := (CFSG.LinearGroups.five_field_linear_two_alternating_five_model (ZMod 5) (by simp)).1
    let φ : (↥Q ⧸ Subgroup.center ↥Q) ≃* alternatingGroup (Fin 5) := eP.trans eA
    have hcard : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 60 := by
      rw [Nat.card_congr φ.toEquiv, card_alt_five_fin]
    have h5 : (5 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_five).mp h'
      apply hpQ
      have h60 : 60 ∣ Nat.card Q := hcard ▸ Subgroup.card_quotient_dvd_card _
      have h5dvd : (5 : ℕ) ∣ Nat.card Q := (show 5 ∣ 60 by norm_num).trans h60
      rwa [← hp5] at h5dvd
    have hdet : ∀ y ∈ Q, (y : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := fun y hy =>
      CFSG.SectionRank.Ccomm.det_eq_one_of_perfect Q hy
    have hnorm : ∀ g' ∈ M, ∃ y ∈ Q, ∃ c : ZMod p,
        (g' : Matrix (Fin 2) (Fin 2) (ZMod p)) =
          (y : Matrix (Fin 2) (Fin 2) (ZMod p)) * Matrix.scalar (Fin 2) c := by
      intro g' hg'
      refine exists_eq_mul_scalar_of_normalizes_sl25 h2 h5 Q hQperf hdet hcen φ ?_ ?_
      · intro x hx
        exact (perfectCore_normal M).conj_mem ⟨x, hQM hx⟩ hx ⟨g', hg'⟩
      · intro x hx
        have := (perfectCore_normal M).conj_mem ⟨x, hQM hx⟩ hx ⟨g'⁻¹, M.inv_mem hg'⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
    let π : GL (Fin 2) (ZMod p) →* Matrix.ProjGenLinGroup (Fin 2) (ZMod p) :=
      Matrix.ProjGenLinGroup.mk
    have hπM : M.map π ≤ Q.map π := by
      rintro _ ⟨g', hg', rfl⟩
      obtain ⟨y, hy, c, hc⟩ := hnorm g' hg'
      refine ⟨y, hy, ?_⟩
      have hz : (y : GL (Fin 2) (ZMod p))⁻¹ * g' ∈ Subgroup.center (GL (Fin 2) (ZMod p)) := by
        rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
        refine ⟨c, ?_⟩
        rw [Units.val_mul, hc, ← mul_assoc, Units.inv_mul, one_mul]
      have h1 : π ((y : GL (Fin 2) (ZMod p))⁻¹ * g') = 1 :=
        Matrix.ProjGenLinGroup.mk_eq_one.mpr hz
      rw [map_mul, map_inv] at h1
      exact inv_mul_eq_one.mp h1
    have hidx : Odd (M.map π).index :=
      Odd.of_dvd_nat hodd (Subgroup.index_map_dvd M Matrix.ProjGenLinGroup.mk_surjective)
    have hidx' : Odd (Q.map π).index := Odd.of_dvd_nat hidx (Subgroup.index_dvd_of_le hπM)
    have hQ60 : Nat.card (Q.map π) ∣ 60 := by
      let ψ : ↥Q →* Matrix.ProjGenLinGroup (Fin 2) (ZMod p) := π.comp Q.subtype
      have hψ1 : ∀ z ∈ Subgroup.center ↥Q, ψ z = 1 := by
        intro z hz
        have hz' := (hcen z).mp hz
        show π (z : GL (Fin 2) (ZMod p)) = 1
        rcases hz' with h | h
        · rw [h, map_one]
        · rw [h]
          refine Matrix.ProjGenLinGroup.mk_eq_one.mpr ?_
          rw [Subgroup.mem_center_iff]
          intro x
          simp
      let ψr : ↥Q →* ψ.range := ψ.rangeRestrict
      have hψr : ∀ z ∈ Subgroup.center ↥Q, ψr z = 1 := fun z hz => Subtype.ext (hψ1 z hz)
      let ψ' : (↥Q ⧸ Subgroup.center ↥Q) →* ψ.range :=
        QuotientGroup.lift (Subgroup.center ↥Q) ψr hψr
      have hsurj : Function.Surjective ψ' := by
        intro r
        obtain ⟨q, hq⟩ := ψ.rangeRestrict_surjective r
        exact ⟨QuotientGroup.mk q, hq⟩
      have hdvd : Nat.card ψ.range ∣ Nat.card (↥Q ⧸ Subgroup.center ↥Q) :=
        Subgroup.card_dvd_of_surjective hsurj
      have hrange : ψ.range = Q.map π := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [hrange, hcard] at hdvd
      exact hdvd
    have h8 : 8 ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 2) (ZMod p)) :=
      eight_dvd_card_pgl2 (Nat.card_zmod p) hpodd hpp.one_lt
    have hcm : Nat.card (Q.map π) * (Q.map π).index =
        Nat.card (Matrix.ProjGenLinGroup (Fin 2) (ZMod p)) := Subgroup.card_mul_index _
    have hcop : Nat.Coprime 8 (Q.map π).index := by
      have := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hidx')
      simpa using this
    have h8' : 8 ∣ Nat.card (Q.map π) := by
      rw [← hcm] at h8
      exact hcop.dvd_of_dvd_mul_right h8
    have := h8'.trans hQ60
    omega

end Assembly

end CFSG.Quasithin.A38c15
