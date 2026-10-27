module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix

variable {K : Type} [Field K]

variable (K) in
@[expose] def symAdd : AddSubgroup (Matrix (Fin 2) (Fin 2) K) where
  carrier := {C | Cᵀ = C}
  zero_mem' := transpose_zero
  add_mem' {C D} hC hD := by
    change (C + D)ᵀ = C + D
    rw [transpose_add, hC, hD]
  neg_mem' {C} hC := by
    change (-C)ᵀ = -C
    rw [transpose_neg, hC]

@[expose] def levAct (g : GL (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K where
  toFun C := (g : Matrix (Fin 2) (Fin 2) K) * C * (g : Matrix (Fin 2) (Fin 2) K)ᵀ
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' C D := by rw [Matrix.mul_add, Matrix.add_mul]

private lemma transpose_symm (a b c : K) :
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![a, b; b, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma entry_symm {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) : S 1 0 = S 0 1 := by
  have h := congrFun (congrFun hS 0) 1
  simpa [Matrix.transpose_apply] using h

private lemma eq_of_symm {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    S = !![S 0 0, S 0 1; S 0 1, S 1 1] := by
  nth_rw 1 [Matrix.eta_fin_two S]
  rw [entry_symm hS]

private lemma levAct_transpose {g : GL (Fin 2) K} {C : Matrix (Fin 2) (Fin 2) K}
    (hC : Cᵀ = C) : (levAct g C)ᵀ = levAct g C := by
  simp only [levAct, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hC,
    Matrix.mul_assoc]

private lemma levAct_mul (g h : GL (Fin 2) K) :
    levAct (g * h) = (levAct g).comp (levAct h) := by
  ext C
  simp only [levAct, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.comp_apply,
    Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

private lemma levAct_one : levAct (K := K) (1 : GL (Fin 2) K) = AddMonoidHom.id _ := by
  ext C
  rw [levAct, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.id_apply]
  simp

private lemma mem_map_levAct {H : AddSubgroup (Matrix (Fin 2) (Fin 2) K)} {g : GL (Fin 2) K}
    {S : Matrix (Fin 2) (Fin 2) K} :
    S ∈ H.map (levAct g) ↔ levAct (K := K) g⁻¹ S ∈ H := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← AddMonoidHom.comp_apply, ← levAct_mul, inv_mul_cancel, levAct_one,
      AddMonoidHom.id_apply]
    exact hx
  · intro h
    exact ⟨_, h, by
      rw [← AddMonoidHom.comp_apply, ← levAct_mul, mul_inv_cancel, levAct_one,
        AddMonoidHom.id_apply]⟩

private def glOf (u u' : Matrix (Fin 2) (Fin 2) K) (hu : u * u' = 1) (hu' : u' * u = 1) :
    GL (Fin 2) K := ⟨u, u', hu, hu'⟩

private lemma coe_glOf_inv {u u' : Matrix (Fin 2) (Fin 2) K} (hu : u * u' = 1)
    (hu' : u' * u = 1) :
    (((glOf u u' hu hu')⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = u' := by
  simp [glOf, Units.inv_mk]

private noncomputable def traHom (p : ℕ) [Algebra (ZMod p) K]
    (T : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K →+ ZMod p where
  toFun S := Algebra.trace (ZMod p) K (Matrix.trace (T * S))
  map_zero' := by simp
  map_add' S S' := by simp [Matrix.mul_add, Matrix.trace_add]

private lemma traHom_apply (p : ℕ) [Algebra (ZMod p) K] (T S : Matrix (Fin 2) (Fin 2) K) :
    traHom p T S = Algebra.trace (ZMod p) K (Matrix.trace (T * S)) := rfl

private lemma traHom_sub_smul (p : ℕ) [Algebra (ZMod p) K]
    (X Y : Matrix (Fin 2) (Fin 2) K) (c : ZMod p) (S : Matrix (Fin 2) (Fin 2) K) :
    traHom p (X - c • Y) S = traHom p X S - c • traHom p Y S := by
  rw [traHom_apply, traHom_apply, traHom_apply]
  have h1 : (X - c • Y) * S = X * S - c • (Y * S) := by
    rw [Matrix.sub_mul, Matrix.smul_mul]
  rw [h1, Matrix.trace_sub, Matrix.trace_smul, map_sub, map_smul]

private lemma trace_mul_eq {T S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    Matrix.trace (T * S) =
      T 0 0 * S 0 0 + T 0 1 * S 0 1 + T 1 0 * S 0 1 + T 1 1 * S 1 1 := by
  have h10 : S 1 0 = S 0 1 := entry_symm hS
  rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, h10]
  ring

private lemma eq_zero_of_trace_mul_eq_zero {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K]
    [Algebra (ZMod p) K] {a : K} (h : ∀ y : K, Algebra.trace (ZMod p) K (a * y) = 0) :
    a = 0 :=
  (traceForm_nondegenerate (ZMod p) K).1 a (fun y => by
    rw [Algebra.traceForm_apply]
    exact h y)

private lemma trace_mul_diag_left (T : Matrix (Fin 2) (Fin 2) K) (y : K) :
    Matrix.trace (T * (!![y, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K)) = T 0 0 * y := by
  rw [trace_mul_eq (transpose_symm y 0 0)]
  simp

private lemma trace_mul_diag_right (T : Matrix (Fin 2) (Fin 2) K) (y : K) :
    Matrix.trace (T * (!![0, 0; 0, y] : Matrix (Fin 2) (Fin 2) K)) = T 1 1 * y := by
  rw [trace_mul_eq (transpose_symm 0 0 y)]
  simp

private lemma trace_mul_offdiag {T : Matrix (Fin 2) (Fin 2) K} (hT : Tᵀ = T) (y : K) :
    Matrix.trace (T * (!![0, y; y, 0] : Matrix (Fin 2) (Fin 2) K)) = 2 * (T 0 1 * y) := by
  rw [trace_mul_eq (transpose_symm 0 y 0), entry_symm hT]
  simp
  ring

private lemma eq_zero_of_traHom_symm {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K]
    [Algebra (ZMod p) K] (h2 : (2 : K) ≠ 0) {T : Matrix (Fin 2) (Fin 2) K} (hT : Tᵀ = T)
    (h : ∀ S, Sᵀ = S → traHom p T S = 0) : T = 0 := by
  have h00 : T 0 0 = 0 := by
    refine eq_zero_of_trace_mul_eq_zero (p := p) (fun y => ?_)
    have hy := h !![y, 0; 0, 0] (transpose_symm y 0 0)
    rw [traHom_apply, trace_mul_diag_left] at hy
    exact hy
  have h11 : T 1 1 = 0 := by
    refine eq_zero_of_trace_mul_eq_zero (p := p) (fun y => ?_)
    have hy := h !![0, 0; 0, y] (transpose_symm 0 0 y)
    rw [traHom_apply, trace_mul_diag_right] at hy
    exact hy
  have hT10 : T 1 0 = T 0 1 := entry_symm hT
  have h01 : T 0 1 = 0 := by
    have h2a : (2 : K) * T 0 1 = 0 := by
      refine eq_zero_of_trace_mul_eq_zero (p := p) (fun y => ?_)
      have hy := h !![0, y; y, 0] (transpose_symm 0 y 0)
      rw [traHom_apply, trace_mul_offdiag hT] at hy
      rwa [← mul_assoc] at hy
    rcases mul_eq_zero.mp h2a with h | h
    · exact absurd h h2
    · exact h
  rw [Matrix.eta_fin_two T, h00, h11, hT10, h01]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma exists_trace_mul_eq {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K]
    [Algebra (ZMod p) K] (φ : K →+ ZMod p) :
    ∃ a : K, ∀ t : K, φ t = Algebra.trace (ZMod p) K (a * t) := by
  refine ⟨((Algebra.traceForm (ZMod p) K).toDual
    (traceForm_nondegenerate (ZMod p) K)).symm (φ.toZModLinearMap p), fun t => ?_⟩
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm (ZMod p) K)
    (hB := traceForm_nondegenerate (ZMod p) K) (φ.toZModLinearMap p) t
  rw [Algebra.traceForm_apply] at h
  exact h.symm

private lemma trace_pivot_eq {t₁ t₂ t₃ : K} (h2 : (2 : K) ≠ 0)
    {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    Matrix.trace ((!![t₁, t₂ / 2; t₂ / 2, t₃] : Matrix (Fin 2) (Fin 2) K) * S) =
      t₁ * S 0 0 + t₂ * S 0 1 + t₃ * S 1 1 := by
  rw [trace_mul_eq hS]
  have h00 : (!![t₁, t₂ / 2; t₂ / 2, t₃] : Matrix (Fin 2) (Fin 2) K) 0 0 = t₁ := by simp
  have h01 : (!![t₁, t₂ / 2; t₂ / 2, t₃] : Matrix (Fin 2) (Fin 2) K) 0 1 = t₂ / 2 := by simp
  have h10 : (!![t₁, t₂ / 2; t₂ / 2, t₃] : Matrix (Fin 2) (Fin 2) K) 1 0 = t₂ / 2 := by simp
  have h11 : (!![t₁, t₂ / 2; t₂ / 2, t₃] : Matrix (Fin 2) (Fin 2) K) 1 1 = t₃ := by simp
  rw [h00, h01, h10, h11]
  have hc : 2 * (t₂ / 2) = t₂ := mul_div_cancel₀ t₂ h2
  linear_combination (S 0 1) * hc

private lemma exists_traHom_of_relIndex {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K]
    [Algebra (ZMod p) K] (h2 : (2 : K) ≠ 0) {H₀ : AddSubgroup (Matrix (Fin 2) (Fin 2) K)}
    (hH₀ : H₀ ≤ symAdd K) (hidx : H₀.relIndex (symAdd K) = p) :
    ∃ T : Matrix (Fin 2) (Fin 2) K, Tᵀ = T ∧ T ≠ 0 ∧
      ∀ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S → (S ∈ H₀ ↔ traHom p T S = 0) := by
  classical
  let N : AddSubgroup ↥(symAdd K) := AddSubgroup.comap (AddSubgroup.subtype (symAdd K)) H₀
  have hNcard : Nat.card N = Nat.card H₀ := by
    refine Nat.card_congr ?_
    exact { toFun := fun x => ⟨x.1.1, x.2⟩
            invFun := fun h => ⟨⟨h.1, hH₀ h.2⟩, h.2⟩
            left_inv := fun x => rfl
            right_inv := fun h => rfl }
  have hmul : p * Nat.card H₀ = Nat.card ↥(symAdd K) := by
    have h := AddSubgroup.relIndex_mul_card H₀ (symAdd K)
    rw [hidx, inf_eq_left.mpr hH₀] at h
    exact h
  have hidxN : N.index = p := by
    have h := AddSubgroup.index_mul_card N
    rw [hNcard] at h
    have h' : N.index * Nat.card ↥H₀ = p * Nat.card ↥H₀ := by rw [h, hmul]
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥H₀)) h'
  have hcardq : Nat.card (↥(symAdd K) ⧸ N) = p := by
    rw [← AddSubgroup.index_eq_card, hidxN]
  let e : (↥(symAdd K) ⧸ N) ≃+ ZMod p :=
    addEquivOfPrimeCardEq hcardq (by rw [Nat.card_eq_fintype_card, ZMod.card])
  let φ : ↥(symAdd K) →+ ZMod p := e.toAddMonoidHom.comp (QuotientAddGroup.mk' N)
  have hφ : ∀ x : ↥(symAdd K), φ x = 0 ↔ (x : Matrix (Fin 2) (Fin 2) K) ∈ H₀ := by
    intro x
    show e (QuotientAddGroup.mk' N x) = 0 ↔ _
    rw [AddEquiv.map_eq_zero_iff, ← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
    rfl
  let s₁ : K →+ ↥(symAdd K) :=
    { toFun := fun x => ⟨!![x, 0; 0, 0], transpose_symm x 0 0⟩
      map_zero' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_add' := fun x y => by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp }
  let s₂ : K →+ ↥(symAdd K) :=
    { toFun := fun x => ⟨!![0, x; x, 0], transpose_symm 0 x 0⟩
      map_zero' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_add' := fun x y => by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp }
  let s₃ : K →+ ↥(symAdd K) :=
    { toFun := fun x => ⟨!![0, 0; 0, x], transpose_symm 0 0 x⟩
      map_zero' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_add' := fun x y => by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp }
  obtain ⟨t₁, ht₁⟩ := exists_trace_mul_eq (p := p) (φ.comp s₁)
  obtain ⟨t₂, ht₂⟩ := exists_trace_mul_eq (p := p) (φ.comp s₂)
  obtain ⟨t₃, ht₃⟩ := exists_trace_mul_eq (p := p) (φ.comp s₃)
  have hchar : ∀ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S →
      (S ∈ H₀ ↔ traHom p !![t₁, t₂ / 2; t₂ / 2, t₃] S = 0) := by
    intro S hS
    have hSS : (⟨S, hS⟩ : ↥(symAdd K)) = s₁ (S 0 0) + s₂ (S 0 1) + s₃ (S 1 1) := by
      apply Subtype.ext
      show S = !![S 0 0, 0; 0, 0] + !![0, S 0 1; S 0 1, 0] + !![0, 0; 0, S 1 1]
      rw [eq_of_symm hS]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hval : φ (⟨S, hS⟩ : ↥(symAdd K)) =
        Algebra.trace (ZMod p) K (t₁ * S 0 0) + Algebra.trace (ZMod p) K (t₂ * S 0 1) +
          Algebra.trace (ZMod p) K (t₃ * S 1 1) := by
      have e1 : ∀ x : K, φ (s₁ x) = Algebra.trace (ZMod p) K (t₁ * x) := fun x => ht₁ x
      have e2 : ∀ x : K, φ (s₂ x) = Algebra.trace (ZMod p) K (t₂ * x) := fun x => ht₂ x
      have e3 : ∀ x : K, φ (s₃ x) = Algebra.trace (ZMod p) K (t₃ * x) := fun x => ht₃ x
      rw [hSS, map_add, map_add, e1, e2, e3]
    have h1 : (S ∈ H₀) ↔ (φ (⟨S, hS⟩ : ↥(symAdd K)) = 0) := by
      have h := hφ (⟨S, hS⟩ : ↥(symAdd K))
      simpa using h.symm
    rw [h1, hval, traHom_apply, trace_pivot_eq h2 hS, map_add, map_add]
  refine ⟨!![t₁, t₂ / 2; t₂ / 2, t₃], transpose_symm t₁ (t₂ / 2) t₃, ?_, hchar⟩
  intro hT0
  have hle : symAdd K ≤ H₀ := by
    intro S hS
    rw [hchar S hS, hT0, traHom_apply]
    simp
  have h1 : H₀.relIndex (symAdd K) = 1 := by
    have h := AddSubgroup.relIndex_mul_card H₀ (symAdd K)
    rw [inf_eq_right.mpr hle] at h
    have h' : H₀.relIndex (symAdd K) * Nat.card ↥(symAdd K) = 1 * Nat.card ↥(symAdd K) := by
      rw [h, one_mul]
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(symAdd K))) h'
  have h2p : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

private lemma two_ne_zero_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] :
    (2 : K) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := hp.two_le
  omega

private lemma exists_trace_sq_mul_add_ne_zero {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K]
    [Algebra (ZMod p) K] (h2 : (2 : K) ≠ 0) (h4 : 4 < Nat.card K) {α β : K} (hα : α ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ Algebra.trace (ZMod p) K (α * c ^ 2 + β) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have key : ∀ c d : K, c ≠ 0 → d ≠ 0 → c + d ≠ 0 →
      Algebra.trace (ZMod p) K (2 * (α * c * d)) = Algebra.trace (ZMod p) K β := by
    intro c d hc hd hcd
    have h1 := hcon (c + d) hcd
    have h2' := hcon c hc
    have h3' := hcon d hd
    have he : 2 * (α * c * d) =
        (α * (c + d) ^ 2 + β - (α * c ^ 2 + β) - (α * d ^ 2 + β)) + β := by ring
    rw [he, map_add, map_sub, map_sub, h1, h2', h3']
    ring
  have main : ∀ x : K, Algebra.trace (ZMod p) K (2 * α * x) = 0 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · obtain ⟨c, hc⟩ : ∃ c : K, c ∉ (Set.range ![0, -x, -1, -x - 1] : Set K) := by
        by_contra hc
        push Not at hc
        have hsub : (Set.range ![0, -x, -1, -x - 1] : Set K) = Set.univ :=
          Set.eq_univ_of_forall hc
        have hcard : (Set.range ![0, -x, -1, -x - 1] : Set K).ncard ≤ 4 := by
          have h1 : (Set.range ![0, -x, -1, -x - 1] : Set K) =
              (![0, -x, -1, -x - 1] : Fin 4 → K) '' Set.univ := by rw [Set.image_univ]
          rw [h1]
          calc ((![0, -x, -1, -x - 1] : Fin 4 → K) '' Set.univ).ncard
              ≤ (Set.univ : Set (Fin 4)).ncard := Set.ncard_image_le
            _ = 4 := by rw [Set.ncard_univ]; simp
        rw [hsub, Set.ncard_univ] at hcard
        omega
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hc (Set.mem_range_self (⟨0, by norm_num⟩ : Fin 4))
      have hcx : c ≠ -x := by
        rintro rfl
        exact hc (Set.mem_range_self (⟨1, by norm_num⟩ : Fin 4))
      have hc1 : c ≠ -1 := by
        rintro rfl
        exact hc (Set.mem_range_self (⟨2, by norm_num⟩ : Fin 4))
      have hc1x : c ≠ -x - 1 := by
        rintro rfl
        exact hc (Set.mem_range_self (⟨3, by norm_num⟩ : Fin 4))
      have hd1 : c + x ≠ 0 := by
        intro h
        exact hcx (by linear_combination h)
      have hd2 : c + 1 ≠ 0 := by
        intro h
        exact hc1 (by linear_combination h)
      have hd3 : c + 1 + x ≠ 0 := by
        intro h
        exact hc1x (by linear_combination h)
      have e1 := key c x hc0 hx hd1
      have e2 := key (c + 1) x hd2 hx hd3
      have hsub : Algebra.trace (ZMod p) K (2 * (α * (c + 1) * x)) -
          Algebra.trace (ZMod p) K (2 * (α * c * x)) = 0 := by rw [e2, e1]; ring
      rw [← map_sub, show 2 * (α * (c + 1) * x) - 2 * (α * c * x) = 2 * α * x by ring] at hsub
      exact hsub
  have h2a : 2 * α = 0 := by
    refine eq_zero_of_trace_mul_eq_zero (p := p) (fun y => ?_)
    exact main y
  rcases mul_eq_zero.mp h2a with h | h
  · exact h2 h
  · exact hα h

private lemma mem_map_levAct_traHom {p : ℕ} [Algebra (ZMod p) K]
    {H : AddSubgroup (Matrix (Fin 2) (Fin 2) K)} {T : Matrix (Fin 2) (Fin 2) K}
    (hH : ∀ S, Sᵀ = S → (S ∈ H ↔ traHom p T S = 0)) (g : GL (Fin 2) K)
    {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    S ∈ H.map (levAct g) ↔ traHom p
      ((((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ) * T *
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) S = 0 := by
  rw [mem_map_levAct, hH _ (levAct_transpose hS), traHom_apply, traHom_apply]
  have htr : ∀ (A u S : Matrix (Fin 2) (Fin 2) K),
      Matrix.trace (A * (u * S * uᵀ)) = Matrix.trace (uᵀ * A * u * S) := by
    intro A u S
    have e1 : A * (u * S * uᵀ) = (A * u * S) * uᵀ := by simp only [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm (A * u * S) uᵀ]
    simp only [Matrix.mul_assoc]
  rw [levAct, AddMonoidHom.coe_mk, ZeroHom.coe_mk, htr]

private lemma dot_quad {S₀ : Matrix (Fin 2) (Fin 2) K} (hS₀ : S₀ᵀ = S₀) (ρ : K) :
    (![1, ρ] : Fin 2 → K) ⬝ᵥ (S₀ *ᵥ ![1, ρ]) =
      S₀ 0 0 + 2 * ρ * S₀ 0 1 + ρ ^ 2 * S₀ 1 1 := by
  have h10 : S₀ 1 0 = S₀ 0 1 := entry_symm hS₀
  simp only [dotProduct, mulVec, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, h10]
  ring

private lemma quad_form_ne_zero {S₀ : Matrix (Fin 2) (Fin 2) K} (hS₀ : S₀ᵀ = S₀)
    (haniso : ∀ v : Fin 2 → K, v ≠ 0 → v ⬝ᵥ (S₀ *ᵥ v) ≠ 0) (ρ : K) :
    S₀ 0 0 + 2 * ρ * S₀ 0 1 + ρ ^ 2 * S₀ 1 1 ≠ 0 := by
  have hv : (![1, ρ] : Fin 2 → K) ≠ 0 := by
    intro h
    have h0 : (1 : K) = 0 := by simpa using congrFun h 0
    exact one_ne_zero h0
  have h := haniso ![1, ρ] hv
  rwa [dot_quad hS₀] at h

private lemma conj_tri_pivot {T : Matrix (Fin 2) (Fin 2) K} (hT : Tᵀ = T) (hT0 : T 0 0 ≠ 0)
    (ρ c : K) :
    (!![c, ρ * c - T 0 1 / T 0 0; 0, 1] : Matrix (Fin 2) (Fin 2) K)ᵀ * T *
        !![c, ρ * c - T 0 1 / T 0 0; 0, 1] =
      !![c ^ 2 * T 0 0, ρ * c ^ 2 * T 0 0; ρ * c ^ 2 * T 0 0,
        ρ ^ 2 * c ^ 2 * T 0 0 + T.det / T 0 0] := by
  have h10 : T 1 0 = T 0 1 := entry_symm hT
  have hdet : T.det = T 0 0 * T 1 1 - T 0 1 * T 0 1 := by
    rw [Matrix.det_fin_two, h10]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hdet] <;>
    field_simp <;> ring

private lemma trace_conj_pivot {S₀ : Matrix (Fin 2) (Fin 2) K} (hS₀ : S₀ᵀ = S₀)
    {γ δ : K} (ρ c : K) :
    Matrix.trace (!![c ^ 2 * γ, ρ * c ^ 2 * γ; ρ * c ^ 2 * γ,
        ρ ^ 2 * c ^ 2 * γ + δ] * S₀) =
      γ * (S₀ 0 0 + 2 * ρ * S₀ 0 1 + ρ ^ 2 * S₀ 1 1) * c ^ 2 + δ * S₀ 1 1 := by
  rw [trace_mul_eq hS₀]
  have h00 : (!![c ^ 2 * γ, ρ * c ^ 2 * γ; ρ * c ^ 2 * γ, ρ ^ 2 * c ^ 2 * γ + δ] :
      Matrix (Fin 2) (Fin 2) K) 0 0 = c ^ 2 * γ := by simp
  have h01 : (!![c ^ 2 * γ, ρ * c ^ 2 * γ; ρ * c ^ 2 * γ, ρ ^ 2 * c ^ 2 * γ + δ] :
      Matrix (Fin 2) (Fin 2) K) 0 1 = ρ * c ^ 2 * γ := by simp
  have h10 : (!![c ^ 2 * γ, ρ * c ^ 2 * γ; ρ * c ^ 2 * γ, ρ ^ 2 * c ^ 2 * γ + δ] :
      Matrix (Fin 2) (Fin 2) K) 1 0 = ρ * c ^ 2 * γ := by simp
  have h11 : (!![c ^ 2 * γ, ρ * c ^ 2 * γ; ρ * c ^ 2 * γ, ρ ^ 2 * c ^ 2 * γ + δ] :
      Matrix (Fin 2) (Fin 2) K) 1 1 = ρ ^ 2 * c ^ 2 * γ + δ := by simp
  rw [h00, h01, h10, h11]
  ring

private lemma exists_smul_eq_of_ker_eq {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    {f f' : V →+ ZMod p} (hf : f ≠ 0) (h : ∀ x, f x = 0 ↔ f' x = 0) :
    ∃ lam : ZMod p, lam ≠ 0 ∧ ∀ x, f' x = lam * f x := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf (AddMonoidHom.ext fun x => by simpa using hc x)
  have key : ∀ x : V, f' x = (f' y / f y) * f x := by
    intro x
    have hz : f ((f x).val • y - (f y).val • x) = 0 := by
      simp only [map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
      ring
    have hz' := (h _).mp hz
    simp only [map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val] at hz'
    rw [div_mul_eq_mul_div, eq_div_iff hy]
    linear_combination -hz'
  refine ⟨f' y / f y, ?_, key⟩
  intro h0
  have : f' y = 0 := by rw [key y, h0, zero_mul]
  exact hy ((h y).mpr this)

private lemma conj_swap_entry (T : Matrix (Fin 2) (Fin 2) K) :
    ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)ᵀ * T *
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)) 0 0 = T 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma conj_shear_entry {T : Matrix (Fin 2) (Fin 2) K} (hT : Tᵀ = T) :
    ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K)ᵀ * T *
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K)) 0 0 = T 0 0 + 2 * T 0 1 + T 1 1 := by
  have h10 : T 1 0 = T 0 1 := entry_symm hT
  simp [Matrix.mul_apply, Fin.sum_univ_two, h10]
  ring

private lemma count_of_pivot {p e : ℕ} [Fact p.Prime] [CharP K p] [Finite K]
    [Algebra (ZMod p) K] (h2 : (2 : K) ≠ 0) (h4 : 4 < Nat.card K) (hK : Nat.card K = p ^ e)
    {S₀ : Matrix (Fin 2) (Fin 2) K} (hS₀ : S₀ᵀ = S₀)
    (haniso : ∀ v : Fin 2 → K, v ≠ 0 → v ⬝ᵥ (S₀ *ᵥ v) ≠ 0)
    {T : Matrix (Fin 2) (Fin 2) K} (hT : Tᵀ = T) (hT0 : T 0 0 ≠ 0)
    {H : AddSubgroup (Matrix (Fin 2) (Fin 2) K)}
    (hH : ∀ S, Sᵀ = S → (S ∈ H ↔ traHom p T S = 0)) :
    p ^ e ≤ {H' : AddSubgroup (Matrix (Fin 2) (Fin 2) K) |
      S₀ ∉ H' ∧ ∃ g : GL (Fin 2) K, H' = H.map (levAct g)}.ncard := by
  classical
  have hQ : ∀ ρ : K, S₀ 0 0 + 2 * ρ * S₀ 0 1 + ρ ^ 2 * S₀ 1 1 ≠ 0 :=
    quad_form_ne_zero hS₀ haniso
  have hex : ∀ ρ : K, ∃ c : K, c ≠ 0 ∧ Algebra.trace (ZMod p) K
      (T 0 0 * (S₀ 0 0 + 2 * ρ * S₀ 0 1 + ρ ^ 2 * S₀ 1 1) * c ^ 2 +
        T.det / T 0 0 * S₀ 1 1) ≠ 0 := by
    intro ρ
    exact exists_trace_sq_mul_add_ne_zero h2 h4 (mul_ne_zero hT0 (hQ ρ))
  let c : K → K := fun ρ => Classical.choose (hex ρ)
  have hc : ∀ ρ, c ρ ≠ 0 := fun ρ => (Classical.choose_spec (hex ρ)).1
  have hct : ∀ ρ, Algebra.trace (ZMod p) K
      (T 0 0 * (S₀ 0 0 + 2 * ρ * S₀ 0 1 + ρ ^ 2 * S₀ 1 1) * c ρ ^ 2 +
        T.det / T 0 0 * S₀ 1 1) ≠ 0 := fun ρ => (Classical.choose_spec (hex ρ)).2
  let mv : K → Matrix (Fin 2) (Fin 2) K :=
    fun ρ => !![(c ρ)⁻¹, -(ρ * c ρ - T 0 1 / T 0 0) * (c ρ)⁻¹; 0, 1]
  let mu : K → Matrix (Fin 2) (Fin 2) K := fun ρ => !![c ρ, ρ * c ρ - T 0 1 / T 0 0; 0, 1]
  have hmul : ∀ ρ, mv ρ * mu ρ = 1 := by
    intro ρ
    have hcρ : c ρ ≠ 0 := hc ρ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mv, mu, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      field_simp <;> ring
  have hmul' : ∀ ρ, mu ρ * mv ρ = 1 := by
    intro ρ
    have hcρ : c ρ ≠ 0 := hc ρ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mv, mu, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      field_simp <;> ring
  let g : K → GL (Fin 2) K := fun ρ => glOf (mv ρ) (mu ρ) (hmul ρ) (hmul' ρ)
  let Hf : K → AddSubgroup (Matrix (Fin 2) (Fin 2) K) := fun ρ => H.map (levAct (g ρ))
  let M : K → Matrix (Fin 2) (Fin 2) K := fun ρ => !![c ρ ^ 2 * T 0 0, ρ * c ρ ^ 2 * T 0 0;
    ρ * c ρ ^ 2 * T 0 0, ρ ^ 2 * c ρ ^ 2 * T 0 0 + T.det / T 0 0]
  have hMsym : ∀ ρ, (M ρ)ᵀ = M ρ := fun ρ => transpose_symm _ _ _
  have hcoe : ∀ ρ, (((g ρ)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = mu ρ :=
    fun ρ => coe_glOf_inv (hmul ρ) (hmul' ρ)
  have hT'' : ∀ ρ, (mu ρ)ᵀ * T * mu ρ = M ρ := by
    intro ρ
    exact conj_tri_pivot hT hT0 ρ (c ρ)
  have hmem : ∀ (ρ : K) (S : Matrix (Fin 2) (Fin 2) K), Sᵀ = S →
      (S ∈ Hf ρ ↔ traHom p (M ρ) S = 0) := by
    intro ρ S hS
    show S ∈ H.map (levAct (g ρ)) ↔ _
    rw [mem_map_levAct_traHom hH (g ρ) hS, hcoe ρ, hT'' ρ]
  have hnot : ∀ ρ, S₀ ∉ Hf ρ := by
    intro ρ
    rw [hmem ρ S₀ hS₀, traHom_apply, trace_conj_pivot hS₀ ρ (c ρ)]
    exact hct ρ
  have hfker : ∀ (ρ : K) (x : ↥(symAdd K)),
      (traHom p (M ρ)).comp (AddSubgroup.subtype (symAdd K)) x = 0 ↔
        (x : Matrix (Fin 2) (Fin 2) K) ∈ Hf ρ := by
    intro ρ x
    rw [AddMonoidHom.comp_apply, hmem ρ _ x.2]
    rfl
  have hinj : Function.Injective Hf := by
    intro ρ ρ' hρ
    have hker : ∀ x : ↥(symAdd K), ((traHom p (M ρ)).comp
        (AddSubgroup.subtype (symAdd K))) x = 0 ↔
        ((traHom p (M ρ')).comp (AddSubgroup.subtype (symAdd K))) x = 0 := by
      intro x
      rw [hfker ρ x, hfker ρ' x, hρ]
    have hfne : (traHom p (M ρ)).comp (AddSubgroup.subtype (symAdd K)) ≠ 0 := by
      intro hzero
      have hz : ∀ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S → traHom p (M ρ) S = 0 := by
        intro S hS
        have := congrArg (fun (φ : ↥(symAdd K) →+ ZMod p) => φ ⟨S, hS⟩) hzero
        simpa using this
      have hzero' := eq_zero_of_traHom_symm h2 (hMsym ρ) hz
      have h00 : c ρ ^ 2 * T 0 0 = 0 := by
        have := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N 0 0) hzero'
        simpa [M] using this
      exact mul_ne_zero (pow_ne_zero 2 (hc ρ)) hT0 h00
    obtain ⟨lam, hlam, hlam_eq⟩ := exists_smul_eq_of_ker_eq hfne hker
    have hTeq : M ρ' = lam • M ρ := by
      have h0 : M ρ' - lam • M ρ = 0 := by
        refine eq_zero_of_traHom_symm h2 ?_ ?_
        · rw [Matrix.transpose_sub, Matrix.transpose_smul, hMsym, hMsym]
        · intro S hS
          rw [traHom_sub_smul]
          change ((traHom p (M ρ')).comp (AddSubgroup.subtype (symAdd K))) ⟨S, hS⟩ -
            lam • ((traHom p (M ρ)).comp (AddSubgroup.subtype (symAdd K))) ⟨S, hS⟩ = 0
          rw [hlam_eq ⟨S, hS⟩, smul_eq_mul]
          ring
      exact sub_eq_zero.mp h0
    have e00 : c ρ' ^ 2 * T 0 0 = (algebraMap (ZMod p) K lam) * (c ρ ^ 2 * T 0 0) := by
      have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N 0 0) hTeq
      simpa [M, Matrix.smul_apply, Algebra.smul_def] using h
    have e01 : ρ' * c ρ' ^ 2 * T 0 0 = (algebraMap (ZMod p) K lam) * (ρ * c ρ ^ 2 * T 0 0) := by
      have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N 0 1) hTeq
      simpa [M, Matrix.smul_apply, Algebra.smul_def] using h
    have hcT : c ρ' ^ 2 * T 0 0 ≠ 0 := mul_ne_zero (pow_ne_zero 2 (hc ρ')) hT0
    have hz : (ρ' - ρ) * (c ρ' ^ 2 * T 0 0) = 0 := by
      linear_combination e01 - ρ * e00
    rcases mul_eq_zero.mp hz with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hcT
  have hsub : Set.range Hf ⊆ {H' : AddSubgroup (Matrix (Fin 2) (Fin 2) K) |
      S₀ ∉ H' ∧ ∃ g : GL (Fin 2) K, H' = H.map (levAct g)} := by
    rintro H' ⟨ρ, rfl⟩
    exact ⟨hnot ρ, g ρ, rfl⟩
  have hcard : (Set.range Hf).ncard = p ^ e := by
    rw [Set.ncard_range_of_injective hinj, ← hK]
  calc p ^ e = (Set.range Hf).ncard := hcard.symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem le_ncard_levAct [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) {S₀ : Matrix (Fin 2) (Fin 2) K} (hS₀ : S₀ᵀ = S₀)
    (haniso : ∀ v : Fin 2 → K, v ≠ 0 → v ⬝ᵥ (S₀ *ᵥ v) ≠ 0)
    {H₀ : AddSubgroup (Matrix (Fin 2) (Fin 2) K)} (hH₀ : H₀ ≤ symAdd K)
    (hidx : H₀.relIndex (symAdd K) = p) :
    p ^ e ≤ {H : AddSubgroup (Matrix (Fin 2) (Fin 2) K) |
      S₀ ∉ H ∧ ∃ g : GL (Fin 2) K, H = H₀.map (levAct g)}.ncard := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ne_two hp hp2
  have h3' : 3 < Nat.card K := by rw [hK]; exact h3
  have h4 : 4 < Nat.card K := by
    have hodd : Odd (Nat.card K) := by
      rw [hK]
      exact Odd.pow (hp.odd_of_ne_two hp2)
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨T, hT, hTne, hchar⟩ := exists_traHom_of_relIndex h2 hH₀ hidx
  by_cases hT0 : T 0 0 = 0
  · obtain ⟨g, hg⟩ : ∃ g : GL (Fin 2) K,
        ((((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ) * T *
          ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 ≠ 0 := by
      by_cases h11 : T 1 1 = 0
      · have h01 : T 0 1 ≠ 0 := by
          intro h
          apply hTne
          rw [Matrix.eta_fin_two T, hT0, h11, entry_symm hT, h]
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
        refine ⟨glOf !![1, 0; -1, 1] !![1, 0; 1, 1] ?_ ?_, ?_⟩
        · ext i j
          fin_cases i <;> fin_cases j <;>
            simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
              Matrix.head_cons, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
              Matrix.one_apply]
          all_goals norm_num
        · ext i j
          fin_cases i <;> fin_cases j <;>
            simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
              Matrix.head_cons, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
              Matrix.one_apply]
          all_goals norm_num
        · rw [coe_glOf_inv, conj_shear_entry hT, hT0, h11, zero_add, add_zero]
          exact mul_ne_zero h2 h01
      · refine ⟨glOf !![0, 1; 1, 0] !![0, 1; 1, 0] ?_ ?_, ?_⟩
        · ext i j
          fin_cases i <;> fin_cases j <;>
            simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
              Matrix.head_cons, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
              Matrix.one_apply]
          all_goals norm_num
        · ext i j
          fin_cases i <;> fin_cases j <;>
            simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
              Matrix.head_cons, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
              Matrix.one_apply]
          all_goals norm_num
        · rw [coe_glOf_inv, conj_swap_entry]
          exact h11
    let T' : Matrix (Fin 2) (Fin 2) K :=
      (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ) * T *
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    have hT'0 : T' 0 0 ≠ 0 := hg
    have hT'sym : T'ᵀ = T' := by
      simp only [T', Matrix.transpose_mul, Matrix.transpose_transpose, hT, Matrix.mul_assoc]
    have hT'char : ∀ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S →
        (S ∈ H₀.map (levAct g) ↔ traHom p T' S = 0) :=
      fun S hS => mem_map_levAct_traHom hchar g hS
    have hcount := count_of_pivot h2 h4 hK hS₀ haniso hT'sym hT'0 hT'char
    refine le_trans hcount (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro H' ⟨hS₀', g', rfl⟩
    exact ⟨hS₀', g' * g, by rw [AddSubgroup.map_map, levAct_mul]⟩
  · exact count_of_pivot h2 h4 hK hS₀ haniso hT hT0 hchar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
