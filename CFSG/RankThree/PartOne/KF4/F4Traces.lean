module

public import CFSG.RankThree.PartOne.KF4.Strings
public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Chevalley



theorem rootExponents_F4_long (i : Fin Tag.F4.rank) (hi : i = f4Index 0 ∨ i = f4Index 1) :
    (rootExponents .F4 i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents .F4 i).count (-2) = 1 ∧
      (rootExponents .F4 i).count (-1) = 14 ∧ (rootExponents .F4 i).count 0 = 18 ∧
      (rootExponents .F4 i).count 1 = 14 ∧ (rootExponents .F4 i).count 2 = 1 := by
  rcases hi with rfl | rfl <;> decide +kernel

theorem rootExponents_F4_short (i : Fin Tag.F4.rank) (hi : i = f4Index 2 ∨ i = f4Index 3) :
    (rootExponents .F4 i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents .F4 i).count (-2) = 7 ∧
      (rootExponents .F4 i).count (-1) = 8 ∧ (rootExponents .F4 i).count 0 = 18 ∧
      (rootExponents .F4 i).count 1 = 8 ∧ (rootExponents .F4 i).count 2 = 7 := by
  rcases hi with rfl | rfl <;> decide +kernel

section Counts

variable {τ : Tag} {L : Type} [Field L]

theorem sum_torusEigen_of_counts' (i : Fin τ.rank) (c : Lˣ) {a b m : ℕ}
    (h : (rootExponents τ i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents τ i).count (-2) = a ∧
      (rootExponents τ i).count (-1) = b ∧ (rootExponents τ i).count 0 = m ∧
      (rootExponents τ i).count 1 = b ∧ (rootExponents τ i).count 2 = a) :
    ∑ b' : Label τ, torusEigen i c b' =
      a * (((c : L) + (c⁻¹ : Lˣ)) ^ 2 - 2) + b * ((c : L) + (c⁻¹ : Lˣ)) + (τ.rank + m) := by
  obtain ⟨hset, h2, h1, h0, h1', h2'⟩ := h
  rw [sum_torusEigen, sum_isRoot_eq_rootExponents i (fun n => ((c ^ n : Lˣ) : L)),
    list_sum_map_eq_of_toFinset _ _ hset, h2, h1, h0, h1', h2']
  simp only [Units.val_zpow_eq_zpow_val, nsmul_eq_mul, zpow_zero, Units.val_one, mul_one]
  have hc : (c : L) ≠ 0 := c.ne_zero
  rw [Units.val_inv_eq_inv_val]
  have e1 : ((c : L) ^ (-2 : ℤ)) = ((c : L) ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
  have e2 : ((c : L) ^ (-1 : ℤ)) = (c : L)⁻¹ := by rw [zpow_neg, zpow_one]
  rw [e1, e2, zpow_one, zpow_ofNat]
  field_simp
  ring

theorem trace_simpleRootSL2_HSL_mul_uSL' (i : Fin τ.rank) (c : Lˣ) (s : L) {a b m : ℕ}
    (h : (rootExponents τ i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents τ i).count (-2) = a ∧
      (rootExponents τ i).count (-1) = b ∧ (rootExponents τ i).count 0 = m ∧
      (rootExponents τ i).count 1 = b ∧ (rootExponents τ i).count 2 = a) :
    LinearMap.trace L (RootModule τ L)
        (simpleRootSL2 τ L i (HSL c * uSL s) : Module.End L (RootModule τ L)) =
      a * (((c : L) + (c⁻¹ : Lˣ)) ^ 2 - 2) + b * ((c : L) + (c⁻¹ : Lˣ)) + (τ.rank + m) := by
  rw [map_mul, simpleRootSL2_HSL, simpleRootSL2_uSL, Units.val_mul,
    trace_torusElt_mul_of_isUpperUnitriangular i c (isUpperUnitriangular_xUnit i s),
    sum_torusEigen_of_counts' i c h]

theorem trace_simpleRootSL2_of_counts' {k : Type} [Field k] (i : Fin τ.rank) {a b m : ℕ}
    (h : (rootExponents τ i).toFinset = {-2, -1, 0, 1, 2} ∧ (rootExponents τ i).count (-2) = a ∧
      (rootExponents τ i).count (-1) = b ∧ (rootExponents τ i).count 0 = m ∧
      (rootExponents τ i).count 1 = b ∧ (rootExponents τ i).count 2 = a) (A : SL2 k) :
    LinearMap.trace k (RootModule τ k) (simpleRootSL2 τ k i A : Module.End k (RootModule τ k)) =
      a * ((A : Matrix (Fin 2) (Fin 2) k).trace ^ 2 - 2) +
        b * (A : Matrix (Fin 2) (Fin 2) k).trace + (τ.rank + m) := by
  set L := AlgebraicClosure k
  set f : k →+* L := algebraMap k L
  apply f.injective
  rw [← trace_baseChangeGL, baseChangeGL_simpleRootSL2]
  set A' := Matrix.SpecialLinearGroup.map f A
  obtain ⟨Q, hQ⟩ := exists_conj_lower_eq_zero_of_isAlgClosed A'
  set B := Q⁻¹ * A' * Q with hB
  have hA' : A' = Q * B * Q⁻¹ := by rw [hB]; group
  have hBe := eq_HSL_mul_uSL hQ
  set u := Units.mk0 _ (SL2_apply_zero_zero_ne_zero hQ)
  set s := (B : Matrix (Fin 2) (Fin 2) L) 0 1 / (B : Matrix (Fin 2) (Fin 2) L) 0 0
  have htr : f (A : Matrix (Fin 2) (Fin 2) k).trace = (u : L) + (u⁻¹ : Lˣ) := by
    have h1 : f (A : Matrix (Fin 2) (Fin 2) k).trace = (A' : Matrix (Fin 2) (Fin 2) L).trace := by
      simp [A', Matrix.trace_fin_two]
    have h2 : (A' : Matrix (Fin 2) (Fin 2) L).trace = (B : Matrix (Fin 2) (Fin 2) L).trace := by
      rw [hA', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, one_mul]
    rw [h1, h2, hBe, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two]
    simp [coe_HSL, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hA', map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, LinearMap.trace_conj, hBe,
    trace_simpleRootSL2_HSL_mul_uSL' i u s h]
  simp only [map_add, map_mul, map_sub, map_pow, map_natCast, map_ofNat, htr]

end Counts

section Closure

theorem closure_range_quad_nat {k : Type*} [Field k] [Finite k] (a₀ b₀ z₀ : ℕ)
    (hcase : (a₀ : k) ≠ 0 ∨ (b₀ : k) ≠ 0)
    (h2 : ringChar k = 2 → (a₀ : k) ≠ 0 → (b₀ : k) = 0) :
    Subfield.closure (Set.range fun t : k => (a₀ : k) * t ^ 2 + b₀ * t + z₀) = ⊤ := by
  rcases eq_or_ne (a₀ : k) 0 with ha | ha
  · have hb : (b₀ : k) ≠ 0 := hcase.resolve_left (not_not.2 ha)
    rw [eq_top_iff]
    intro y _
    refine Subfield.subset_closure ⟨(y - z₀) / b₀, ?_⟩
    simp only [ha, zero_mul, zero_add]
    field_simp
    ring
  · set F := Subfield.closure (Set.range fun t : k => (a₀ : k) * t ^ 2 + b₀ * t + z₀) with hF
    have haF : (a₀ : k) ∈ F := natCast_mem F a₀
    have hQ : Subfield.closure (Set.range fun t : k =>
        t ^ 2 + ((b₀ : k) / a₀) * t + ((z₀ : k) / a₀)) = ⊤ :=
      closure_range_quadratic_eq_top _ _ (fun h => by rw [h2 h ha, zero_div])
    rw [eq_top_iff, ← hQ, Subfield.closure_le]
    rintro _ ⟨t, rfl⟩
    beta_reduce
    have e : t ^ 2 + ((b₀ : k) / a₀) * t + ((z₀ : k) / a₀) =
        (a₀ : k)⁻¹ * ((a₀ : k) * t ^ 2 + b₀ * t + z₀) := by
      field_simp
    rw [e]
    exact F.mul_mem (F.inv_mem haF) (Subfield.subset_closure ⟨t, rfl⟩)

variable {τ : Tag}

theorem closure_traces_of_formula (i : Fin τ.rank) (a₀ b₀ z₀ : ℕ)
    (hform : ∀ (M : Type) [Field M] (A : SL2 M),
      LinearMap.trace M (RootModule τ M) (simpleRootSL2 τ M i A : Module.End M (RootModule τ M)) =
        (a₀ : M) * (A : Matrix (Fin 2) (Fin 2) M).trace ^ 2 +
          (b₀ : M) * (A : Matrix (Fin 2) (Fin 2) M).trace + (z₀ : M))
    (k : Type) [Field k] [Finite k] (hcase : (a₀ : k) ≠ 0 ∨ (b₀ : k) ≠ 0)
    (h2 : ringChar k = 2 → (a₀ : k) ≠ 0 → (b₀ : k) = 0)
    (M : Type) [Field M] [Algebra k M] (P : GL (Fin 2) M) (g : ModGL τ M) :
    Subfield.closure {x : M | ∃ A : SL2 k, x = LinearMap.trace M (RootModule τ M)
      ((g * simpleRootSL2 τ M i (conjGL P (Matrix.SpecialLinearGroup.map (algebraMap k M) A)) *
        g⁻¹ : ModGL τ M) : Module.End M (RootModule τ M))} = (algebraMap k M).fieldRange := by
  set f : k →+* M := algebraMap k M
  have hval : ∀ A : SL2 k, LinearMap.trace M (RootModule τ M)
      ((g * simpleRootSL2 τ M i (conjGL P (Matrix.SpecialLinearGroup.map f A)) *
        g⁻¹ : ModGL τ M) : Module.End M (RootModule τ M)) =
      f ((a₀ : k) * (A : Matrix (Fin 2) (Fin 2) k).trace ^ 2 +
        (b₀ : k) * (A : Matrix (Fin 2) (Fin 2) k).trace + (z₀ : k)) := by
    intro A
    rw [Units.val_mul, Units.val_mul, LinearMap.trace_conj, hform M, trace_conjGL]
    have htr : ((Matrix.SpecialLinearGroup.map f A : SL2 M) : Matrix (Fin 2) (Fin 2) M).trace =
        f (A : Matrix (Fin 2) (Fin 2) k).trace := by
      simp [Matrix.trace_fin_two]
    rw [htr]
    simp only [map_add, map_mul, map_pow, map_natCast]
  have hS : {x : M | ∃ A : SL2 k, x = LinearMap.trace M (RootModule τ M)
      ((g * simpleRootSL2 τ M i (conjGL P (Matrix.SpecialLinearGroup.map f A)) *
        g⁻¹ : ModGL τ M) : Module.End M (RootModule τ M))} =
      f '' Set.range fun t : k => (a₀ : k) * t ^ 2 + b₀ * t + z₀ := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, (hval A).symm⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      refine ⟨companionSL t, ?_⟩
      rw [hval, trace_companionSL]
  rw [hS, ← RingHom.map_field_closure, closure_range_quad_nat a₀ b₀ z₀ hcase h2,
    RingHom.fieldRange_eq_map]

end Closure

section F4

theorem trace_simpleRootSL2_F4_long (i : Fin Tag.F4.rank) (hi : i = f4Index 0 ∨ i = f4Index 1)
    {k : Type} [Field k] (A : SL2 k) :
    LinearMap.trace k (RootModule .F4 k) (simpleRootSL2 .F4 k i A : Module.End k (RootModule .F4 k))
      = ((1 : ℕ) : k) * (A : Matrix (Fin 2) (Fin 2) k).trace ^ 2 +
        ((14 : ℕ) : k) * (A : Matrix (Fin 2) (Fin 2) k).trace + ((20 : ℕ) : k) := by
  rw [trace_simpleRootSL2_of_counts' (a := 1) (b := 14) (m := 18) i (rootExponents_F4_long i hi) A]
  have : ((Tag.F4.rank : ℕ) : k) = 4 := by norm_num [Tag.rank]
  rw [this]
  push_cast
  ring

theorem trace_simpleRootSL2_F4_short (i : Fin Tag.F4.rank) (hi : i = f4Index 2 ∨ i = f4Index 3)
    {k : Type} [Field k] (A : SL2 k) :
    LinearMap.trace k (RootModule .F4 k) (simpleRootSL2 .F4 k i A : Module.End k (RootModule .F4 k))
      = ((7 : ℕ) : k) * (A : Matrix (Fin 2) (Fin 2) k).trace ^ 2 +
        ((8 : ℕ) : k) * (A : Matrix (Fin 2) (Fin 2) k).trace + ((8 : ℕ) : k) := by
  rw [trace_simpleRootSL2_of_counts' (a := 7) (b := 8) (m := 18) i (rootExponents_F4_short i hi) A]
  have : ((Tag.F4.rank : ℕ) : k) = 4 := by norm_num [Tag.rank]
  rw [this]
  push_cast
  ring

theorem closure_trace_F4_long (i : Fin Tag.F4.rank) (hi : i = f4Index 0 ∨ i = f4Index 1)
    (k : Type) [Field k] [Finite k] (M : Type) [Field M] [Algebra k M] (P : GL (Fin 2) M)
    (g : ModGL Tag.F4 M) :
    Subfield.closure {x : M | ∃ A : SL2 k, x = LinearMap.trace M (RootModule .F4 M)
      ((g * simpleRootSL2 .F4 M i (conjGL P (Matrix.SpecialLinearGroup.map (algebraMap k M) A)) *
        g⁻¹ : ModGL .F4 M) : Module.End M (RootModule .F4 M))} =
      (algebraMap k M).fieldRange :=
  closure_traces_of_formula i 1 14 20 (fun M _ A => trace_simpleRootSL2_F4_long i hi A) k
    (Or.inl (by simp)) (fun h2 _ => by
      have : CharP k 2 := ringChar.of_eq h2
      rw [show ((14 : ℕ) : k) = ((2 * 7 : ℕ) : k) by norm_num, Nat.cast_mul, Nat.cast_two,
        CharTwo.two_eq_zero, zero_mul]) M P g

theorem closure_trace_F4_short (i : Fin Tag.F4.rank) (hi : i = f4Index 2 ∨ i = f4Index 3)
    (k : Type) [Field k] [Finite k] (M : Type) [Field M] [Algebra k M] (P : GL (Fin 2) M)
    (g : ModGL Tag.F4 M) :
    Subfield.closure {x : M | ∃ A : SL2 k, x = LinearMap.trace M (RootModule .F4 M)
      ((g * simpleRootSL2 .F4 M i (conjGL P (Matrix.SpecialLinearGroup.map (algebraMap k M) A)) *
        g⁻¹ : ModGL .F4 M) : Module.End M (RootModule .F4 M))} =
      (algebraMap k M).fieldRange := by
  refine closure_traces_of_formula i 7 8 8 (fun M _ A => trace_simpleRootSL2_F4_short i hi A) k
    ?_ (fun h2 _ => ?_) M P g
  · by_cases h7 : ((7 : ℕ) : k) = 0
    · right
      intro h8
      have h1 : ((8 : ℕ) : k) = ((7 : ℕ) : k) + 1 := by norm_num
      rw [h1, h7, zero_add] at h8
      exact one_ne_zero h8
    · exact Or.inl h7
  · have : CharP k 2 := ringChar.of_eq h2
    rw [show ((8 : ℕ) : k) = ((2 * 4 : ℕ) : k) by norm_num, Nat.cast_mul, Nat.cast_two,
      CharTwo.two_eq_zero, zero_mul]

end F4

end CFSG.RankThree.PartOne.KF4
