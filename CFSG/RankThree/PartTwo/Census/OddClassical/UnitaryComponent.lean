module

public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearComponent
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] {m : ℕ}

theorem diagBlock_apply_inr {k : ℕ} (X : Matrix (Fin k) (Fin k) K) (Y : Matrix (Fin m) (Fin m) K)
    (i j : Fin m) :
    diagBlock X Y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = Y i j := by
  rw [diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    fromBlocks_apply₂₂]

theorem diagBlock_apply_inl {k : ℕ} (X : Matrix (Fin k) (Fin k) K) (Y : Matrix (Fin m) (Fin m) K)
    (i j : Fin k) :
    diagBlock X Y (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = X i j := by
  rw [diagBlock, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    fromBlocks_apply₁₁]

theorem blockGL_mem_unitarySU (h : UnitaryFieldData p f K) {X : GL (Fin 2) K}
    (hX : X ∈ unitarySU p f K 2) : blockGL K 2 m X ∈ unitarySU p f K (2 + m) := by
  rw [mem_unitarySU_iff h] at hX ⊢
  rw [det_blockGL, coe_blockGL_eq_diagBlock, diagBlock_map, diagBlock_transpose, diagBlock_mul,
    Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.mul_one, hX.2, diagBlock_one]
  exact ⟨hX.1, rfl⟩

@[expose] noncomputable def unitaryBlock (h : UnitaryFieldData p f K) (m : ℕ) :
    unitarySU p f K 2 →* unitarySU p f K (2 + m) :=
  ((blockGL K 2 m).comp (unitarySU p f K 2).subtype).codRestrict _
    fun X => blockGL_mem_unitarySU h X.2

theorem coe_unitaryBlock (h : UnitaryFieldData p f K) (X : unitarySU p f K 2) :
    (((unitaryBlock h m X : unitarySU p f K (2 + m)) : GL (Fin (2 + m)) K) :
      Matrix (Fin (2 + m)) (Fin (2 + m)) K) =
      diagBlock ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 :=
  rfl

theorem unitaryBlock_injective (h : UnitaryFieldData p f K) :
    Function.Injective (unitaryBlock h m) := by
  intro X Y hXY
  have h' := congrArg (fun g : unitarySU p f K (2 + m) => ((g : GL (Fin (2 + m)) K) :
    Matrix (Fin (2 + m)) (Fin (2 + m)) K)) hXY
  simp only [coe_unitaryBlock] at h'
  exact Subtype.ext (Units.ext (diagBlock_injective h').1)

theorem neg_one_mem_unitarySU (h : UnitaryFieldData p f K) :
    (-1 : GL (Fin 2) K) ∈ unitarySU p f K 2 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [Units.val_neg, Units.val_one, det_neg, det_one, Fintype.card_fin]
    norm_num
  · rw [Units.val_neg, Units.val_one, Matrix.map_neg _ (map_neg _),
      Matrix.map_one _ (map_zero _) (map_one _), transpose_neg, transpose_one, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, Matrix.one_mul]

@[expose] noncomputable def unitaryBlockInvolution (h : UnitaryFieldData p f K) (m : ℕ) :
    unitarySU p f K (2 + m) :=
  unitaryBlock h m ⟨-1, neg_one_mem_unitarySU h⟩

theorem coe_unitaryBlockInvolution (h : UnitaryFieldData p f K) :
    (((unitaryBlockInvolution h m : unitarySU p f K (2 + m)) : GL (Fin (2 + m)) K) :
      Matrix (Fin (2 + m)) (Fin (2 + m)) K) = diagBlock (-1) 1 := by
  rw [unitaryBlockInvolution, coe_unitaryBlock]
  simp

theorem unitaryBlockInvolution_sq (h : UnitaryFieldData p f K) :
    unitaryBlockInvolution h m ^ 2 = 1 := by
  have h1 : (⟨-1, neg_one_mem_unitarySU h⟩ : unitarySU p f K 2) ^ 2 = 1 := by
    apply Subtype.ext
    change ((-1 : GL (Fin 2) K)) ^ 2 = 1
    rw [neg_one_sq]
  rw [unitaryBlockInvolution, ← map_pow, h1, map_one]

theorem unitaryBlockInvolution_not_mem (h : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0)
    (hm : 1 ≤ m) : unitaryBlockInvolution h m ∉ unitaryScalars h (2 + m) := by
  intro ht
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp ht
  have hc' := congrArg Units.val hc
  rw [GeneralLinearGroup.coe_scalar] at hc'
  change (((unitaryBlockInvolution h m : unitarySU p f K (2 + m)) : GL (Fin (2 + m)) K) :
    Matrix (Fin (2 + m)) (Fin (2 + m)) K) = _ at hc'
  rw [coe_unitaryBlockInvolution] at hc'
  have e0 := congrFun (congrFun hc' (finSumFinEquiv (Sum.inl 0))) (finSumFinEquiv (Sum.inl 0))
  have e1 := congrFun (congrFun hc' (finSumFinEquiv (Sum.inr ⟨0, by omega⟩)))
    (finSumFinEquiv (Sum.inr ⟨0, by omega⟩))
  rw [diagBlock_apply_inl, scalar_apply_finSumFinEquiv] at e0
  rw [diagBlock_apply_inr, scalar_apply_finSumFinEquiv] at e1
  simp at e0 e1
  apply h2
  linear_combination e1 - e0

theorem conj_mem_range_unitaryBlock (h : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0)
    {g : unitarySU p f K (2 + m)}
    (hg : g * unitaryBlockInvolution h m = unitaryBlockInvolution h m * g)
    (X : unitarySU p f K 2) :
    g * unitaryBlock h m X * g⁻¹ ∈ (unitaryBlock h m).range := by
  have hcomm : ∀ x : unitarySU p f K (2 + m), x * unitaryBlockInvolution h m =
      unitaryBlockInvolution h m * x → ∃ A D, ((x : GL (Fin (2 + m)) K) :
        Matrix (Fin (2 + m)) (Fin (2 + m)) K) = diagBlock A D := fun x hx =>
    eq_diagBlock_of_comm h2 (by
      have := congrArg (fun y : unitarySU p f K (2 + m) => ((y : GL (Fin (2 + m)) K) :
        Matrix (Fin (2 + m)) (Fin (2 + m)) K)) hx
      simpa only [Subgroup.coe_mul, Units.val_mul, coe_unitaryBlockInvolution] using this)
  have hg' : g⁻¹ * unitaryBlockInvolution h m = unitaryBlockInvolution h m * g⁻¹ :=
    (Commute.inv_left hg).eq
  obtain ⟨A, D, hAD⟩ := hcomm g hg
  obtain ⟨A', D', hAD'⟩ := hcomm g⁻¹ hg'
  have hone : diagBlock (A * A') (D * D') = diagBlock 1 1 := by
    rw [← diagBlock_mul, ← hAD, ← hAD', diagBlock_one, ← Units.val_mul, ← Subgroup.coe_mul,
      mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  have hone' : diagBlock (A' * A) (D' * D) = diagBlock 1 1 := by
    rw [← diagBlock_mul, ← hAD, ← hAD', diagBlock_one, ← Units.val_mul, ← Subgroup.coe_mul,
      inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  obtain ⟨hA, hD⟩ := diagBlock_injective hone
  obtain ⟨hA', -⟩ := diagBlock_injective hone'
  have hunit : ∀ x : unitarySU p f K (2 + m), ∀ A D, ((x : GL (Fin (2 + m)) K) :
      Matrix (Fin (2 + m)) (Fin (2 + m)) K) = diagBlock A D → (A.map h.bar)ᵀ * A = 1 := by
    intro x A D hx
    have hx2 := ((mem_unitarySU_iff h).mp x.2).2
    rw [hx, diagBlock_map, diagBlock_transpose, diagBlock_mul, ← diagBlock_one] at hx2
    exact (diagBlock_injective hx2).1
  have hAu := hunit g A D hAD
  have hA'u := hunit g⁻¹ A' D' hAD'
  set Xm := ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  obtain ⟨hXdet, hXu⟩ := (mem_unitarySU_iff h).mp X.2
  have hdet : (A * Xm * A').det = 1 := by
    rw [det_mul, det_mul, hXdet, mul_one, ← det_mul, hA, det_one]
  set Y : GL (Fin 2) K :=
    GeneralLinearGroup.mkOfDetNeZero (A * Xm * A') (by rw [hdet]; exact one_ne_zero)
  have hYcoe : (Y : Matrix (Fin 2) (Fin 2) K) = A * Xm * A' := rfl
  have hY : Y ∈ unitarySU p f K 2 := by
    rw [mem_unitarySU_iff h, hYcoe]
    refine ⟨hdet, ?_⟩
    rw [Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul]
    calc (A'.map h.bar)ᵀ * ((Xm.map h.bar)ᵀ * (A.map h.bar)ᵀ) * (A * Xm * A')
        = (A'.map h.bar)ᵀ * ((Xm.map h.bar)ᵀ * ((A.map h.bar)ᵀ * A) * Xm) * A' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAu, Matrix.mul_one, hXu, Matrix.mul_one, hA'u]
  refine ⟨⟨Y, hY⟩, Subtype.ext (Units.ext ?_)⟩
  rw [coe_unitaryBlock]
  change diagBlock (A * Xm * A') 1 = ((g : GL (Fin (2 + m)) K) :
      Matrix (Fin (2 + m)) (Fin (2 + m)) K) * diagBlock Xm 1 *
    (((g⁻¹ : unitarySU p f K (2 + m)) : GL (Fin (2 + m)) K) :
      Matrix (Fin (2 + m)) (Fin (2 + m)) K)
  rw [hAD, hAD', diagBlock_mul, diagBlock_mul, Matrix.mul_one, hD]

theorem nonempty_sl2_mulEquiv_unitarySU_two [Finite K] (h : UnitaryFieldData p f K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (SL(2, F) ≃* unitarySU p f K 2) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 2
  refine ⟨CFSG.LieType.Steinberg.fixedSubfield K p f, inferInstance, inferInstance,
    CFSG.LieType.Steinberg.card_fixedSubfield hK, ⟨?_⟩⟩
  exact ((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
    (CFSG.LieType.Universal.Unitary.conjEquiv P hP)).trans
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 2))

theorem not_isCharTwoType_unitaryPSU_block [Finite K] (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hm : 1 ≤ m) : ¬ IsCharTwoType (unitaryPSU h (2 + m)) := by
  have h2 := two_ne_zero_of_unitaryFieldData h hp2
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := nonempty_sl2_mulEquiv_unitarySU_two h
  set φ := (unitaryBlock h m).comp ψ.toMonoidHom
  have hφ : Function.Injective φ := (unitaryBlock_injective h).comp ψ.injective
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.Prime.odd_of_ne_two h.prime hp2).pow
  have hrange : φ.range = (unitaryBlock h m).range := by
    ext x
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨ψ B, rfl⟩
    · rintro ⟨X, rfl⟩
      exact ⟨ψ.symm X, by simp [φ]⟩
  refine not_isCharTwoType_of_sl2_component _ (unitaryScalars_le_center h _)
    (unitaryBlockInvolution_not_mem h h2 hm)
    (by rw [unitaryBlockInvolution_sq]; exact Subgroup.one_mem _) (J := φ.range)
    ?_ ?_ ?_ (by rw [hF]; omega) hodd (MonoidHom.ofInjective hφ).symm
  · rw [hrange]
    rintro _ ⟨X, rfl⟩
    rw [unitaryBlockInvolution, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (X : GL (Fin 2) K) * (-1) = (-1) * X
    rw [mul_neg_one, neg_one_mul]
  · rw [hrange]
    rintro g hg _ ⟨X, rfl⟩
    exact conj_mem_range_unitaryBlock h h2 hg X
  · rw [eq_bot_iff, hrange]
    rintro _ hx
    obtain ⟨⟨X, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨c, -, -, hcX⟩ := mem_unitaryScalars.mp hc
    have hc' := congrArg Units.val hcX
    rw [GeneralLinearGroup.coe_scalar] at hc'
    change (((unitaryBlock h m X : unitarySU p f K (2 + m)) : GL (Fin (2 + m)) K) :
      Matrix (Fin (2 + m)) (Fin (2 + m)) K) = _ at hc'
    rw [coe_unitaryBlock] at hc'
    have e1 := congrFun (congrFun hc' (finSumFinEquiv (Sum.inr ⟨0, by omega⟩)))
      (finSumFinEquiv (Sum.inr ⟨0, by omega⟩))
    rw [diagBlock_apply_inr, scalar_apply_finSumFinEquiv] at e1
    simp only [ite_true, one_apply_eq] at e1
    rw [← e1, map_one, ← diagBlock_one] at hc'
    have hX1 : X = 1 := Subtype.ext (Units.ext (diagBlock_injective hc').1)
    rw [hX1, map_one]
    exact Subgroup.one_mem _

theorem excluded433_twistedA_two_odd (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.p ≠ 2) (h5 : 5 ≤ q.card) :
    Excluded433 (.lie ⟨.twistedA 2 q, hv⟩) := by
  intro G _ _ hG e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have he : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  have h := unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩) _
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 2 q, hv⟩)
  refine hG.false_of_not_isCharTwoType
    ((e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)).trans
      (unitaryPSUEquiv h (n := 2 + 1) (by omega)).symm)
    (not_isCharTwoType_unitaryPSU_block h (by rw [hc]; exact hq) ?_ le_rfl)
  rw [hc, he]
  simpa only [TauCeti.PrimePower.card_def] using h5

theorem excluded433_twistedA_three_odd_of_five_le (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.p ≠ 2) (h5 : 5 ≤ q.card) :
    Excluded433 (.lie ⟨.twistedA 3 q, hv⟩) := by
  intro G _ _ hG e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 3 q
  have he : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 3 q
  have h := unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩) _
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 3 q, hv⟩)
  refine hG.false_of_not_isCharTwoType
    ((e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)).trans
      (unitaryPSUEquiv h (n := 2 + 2) (by omega)).symm)
    (not_isCharTwoType_unitaryPSU_block h (by rw [hc]; exact hq) ?_ (by norm_num))
  rw [hc, he]
  simpa only [TauCeti.PrimePower.card_def] using h5

end CFSG.RankThree.PartTwo.Census
