module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsAlpha
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsIso
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartGroup

public section

namespace CFSG.StandardType

namespace SUFacts

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.SeitzReduction.UnitaryPilot (IsPairRadical isPairRadical_one)

section Pattern

variable (F : Type) [Field F]

@[expose] def radW : Submodule F (Fin 6 → F) := Submodule.span F {Pi.single 5 1}

@[expose] def radL : Submodule F (Fin 6 → F) where
  carrier := {v | v 0 = 0}
  add_mem' {a b} ha hb := by
    change a 0 + b 0 = 0
    rw [show a 0 = 0 from ha, show b 0 = 0 from hb, add_zero]
  zero_mem' := rfl
  smul_mem' c v hv := by
    change c * v 0 = 0
    rw [show v 0 = 0 from hv, mul_zero]

variable {F}

theorem mem_radL {v : Fin 6 → F} : v ∈ radL F ↔ v 0 = 0 := Iff.rfl

theorem mem_radW {v : Fin 6 → F} : v ∈ radW F ↔ ∃ c : F, c • Pi.single 5 1 = v :=
  Submodule.mem_span_singleton

theorem entries_of_isPairRadical {M : Matrix (Fin 6) (Fin 6) F}
    (hM : IsPairRadical (radW F) (radL F) M) :
    (∀ i, M i 5 = (1 : Matrix (Fin 6) (Fin 6) F) i 5) ∧
    (∀ j, M 0 j = (1 : Matrix (Fin 6) (Fin 6) F) 0 j) ∧
    (∀ i j, i ≠ 5 → j ≠ 0 → M i j = (1 : Matrix (Fin 6) (Fin 6) F) i j) := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun i => ?_, fun j => ?_, fun i j hi hj => ?_⟩
  · have := congrFun (h1 _ (Submodule.mem_span_singleton_self _)) i
    rw [mulVec_single_one, col_apply, Pi.single_apply] at this
    rw [this, one_apply]
  · have := h3 (Pi.single j 1)
    rw [mem_radL, Pi.sub_apply, mulVec_single_one, col_apply, Pi.single_apply,
      sub_eq_zero] at this
    rw [this, one_apply]
  · have hj' : Pi.single j (1 : F) ∈ radL F := by
      rw [mem_radL, Pi.single_apply, ite_eq_right (Ne.symm hj)]
    obtain ⟨c, hc⟩ := mem_radW.mp (h2 _ hj')
    have := congrFun hc i
    rw [Pi.smul_apply, Pi.single_apply, ite_eq_right hi, smul_zero, Pi.sub_apply, mulVec_single_one,
      col_apply, Pi.single_apply, eq_comm, sub_eq_zero] at this
    rw [this, one_apply]

theorem isPairRadical_of_entries {M : Matrix (Fin 6) (Fin 6) F}
    (h5 : ∀ i, M i 5 = (1 : Matrix (Fin 6) (Fin 6) F) i 5)
    (h0 : ∀ j, M 0 j = (1 : Matrix (Fin 6) (Fin 6) F) 0 j)
    (hm : ∀ i j, i ≠ 5 → j ≠ 0 → M i j = (1 : Matrix (Fin 6) (Fin 6) F) i j) :
    IsPairRadical (radW F) (radL F) M := by
  have hcol : M *ᵥ Pi.single 5 1 = Pi.single 5 1 := by
    ext i
    rw [mulVec_single_one, col_apply, h5 i, one_apply, Pi.single_apply]
  refine ⟨fun w hw => ?_, fun v hv => ?_, fun v => ?_⟩
  · obtain ⟨c, rfl⟩ := mem_radW.mp hw
    rw [mulVec_smul, hcol]
  · rw [mem_radL] at hv
    have key : ∀ i, i ≠ 5 → (M *ᵥ v) i = v i := by
      intro i hi
      have : (M *ᵥ v) i = ((1 : Matrix (Fin 6) (Fin 6) F) *ᵥ v) i := by
        simp only [mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = 0
        · subst hj
          rw [hv, mul_zero, mul_zero]
        · rw [hm i j hi hj]
      rw [this, one_mulVec]
    refine mem_radW.mpr ⟨(M *ᵥ v - v) 5, ?_⟩
    ext i
    rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hi : i = 5
    · rw [ite_eq_left hi, mul_one, hi]
    · rw [ite_eq_right hi, mul_zero, Pi.sub_apply, key i hi, sub_self]
  · rw [mem_radL, Pi.sub_apply, sub_eq_zero]
    have : (M *ᵥ v) 0 = ((1 : Matrix (Fin 6) (Fin 6) F) *ᵥ v) 0 := by
      simp only [mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by rw [h0 j]
    rw [this, one_mulVec]

theorem mat_eq_of_mulVec {A B : Matrix (Fin 6) (Fin 6) F} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rwa [mulVec_single_one, mulVec_single_one, col_apply, col_apply] at this

theorem ggInvUNil_six_one_mulVec (v : Fin 6 → F) :
    ggInvUNil 6 1 F *ᵥ v = v 0 • Pi.single 5 1 := by
  ext a
  rw [mulVec, dotProduct, Finset.sum_eq_single (0 : Fin 6)]
  · rw [ggInvUNil_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases ha : a = 5
    · subst ha
      rw [ite_eq_left (by decide), ite_eq_left rfl, one_mul, mul_one]
    · rw [ite_eq_right (fun h => ha (Fin.ext (by have := h.2.1; simp at this; omega))),
        ite_eq_right ha, zero_mul, mul_zero]
  · intro b _ hb
    rw [ggInvUNil_apply, ite_eq_right (fun h => hb (Fin.ext (by have := h.1; omega))), zero_mul]
  · simp

theorem ggInvUMatrix_six_one_mulVec (v : Fin 6 → F) :
    ggInvUMatrix 6 1 F *ᵥ v = v + v 0 • Pi.single 5 1 := by
  rw [ggInvUMatrix, add_mulVec, one_mulVec, ggInvUNil_six_one_mulVec]

theorem ggInvUMatrix_six_one_sub_mem (v : Fin 6 → F) :
    ggInvUMatrix 6 1 F *ᵥ v - v ∈ radW F := by
  rw [ggInvUMatrix_six_one_mulVec, add_sub_cancel_left]
  exact mem_radW.mpr ⟨v 0, rfl⟩

theorem ggInvUMatrix_six_one_mulVec_eq_iff (v : Fin 6 → F) :
    ggInvUMatrix 6 1 F *ᵥ v = v ↔ v ∈ radL F := by
  rw [ggInvUMatrix_six_one_mulVec, add_eq_left, mem_radL]
  constructor
  · intro h
    have := congrFun h 5
    simpa using this
  · intro h
    rw [h, zero_smul]

end Pattern

section Group

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] def rootRad : Subgroup (SU σ 6) where
  carrier := {g | IsPairRadical (radW F) (radL F) ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)}
  one_mem' := isPairRadical_one _ _
  mul_mem' hg hg' := IsPairRadical.mul hg hg'
  inv_mem' {g} hg := IsPairRadical.of_mul_eq_one hg (g : GL (Fin 6) F).val_inv
    (g : GL (Fin 6) F).inv_val

variable {σ}

theorem pow_four_eq_one_of_mem_rootRad [CharP F 2] {g : SU σ 6} (hg : g ∈ rootRad σ) :
    g ^ 4 = 1 :=
  Subtype.ext (Units.ext (by
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.pow_four_eq_one_of_sub_one_pow_three
      (IsPairRadical.sub_one_pow_three hg)))

variable (σ) in
theorem isPGroup_rootRad [CharP F 2] : IsPGroup 2 (rootRad σ) := fun g =>
  ⟨2, Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact pow_four_eq_one_of_mem_rootRad g.2)⟩

theorem commute_ggInvSU_of_mem_rootRad [CharP F 2] {g : SU σ 6} (hg : g ∈ rootRad σ) :
    g * ggInvSU σ 6 1 = ggInvSU σ 6 1 * g := by
  obtain ⟨h1, -, h3⟩ := hg
  apply Subtype.ext
  apply Units.ext
  change ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      (((ggInvSU σ 6 1 : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
    (((ggInvSU σ 6 1 : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  rw [coe_ggInvSU σ (by norm_num)]
  refine mat_eq_of_mulVec fun v => ?_
  set G := ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  rw [← mulVec_mulVec, ← mulVec_mulVec, ggInvUMatrix_six_one_mulVec,
    ggInvUMatrix_six_one_mulVec, mulVec_add, mulVec_smul,
    h1 _ (Submodule.mem_span_singleton_self _)]
  have h0 : (G *ᵥ v) 0 = v 0 := by
    have := h3 v
    rw [mem_radL, Pi.sub_apply, sub_eq_zero] at this
    exact this
  rw [h0]

theorem mulVec_mem_of_commute [CharP F 2] {c : SU σ 6}
    (hc : c * ggInvSU σ 6 1 = ggInvSU σ 6 1 * c) :
    (∀ w ∈ radW F, ((c : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ w ∈ radW F) ∧
      ∀ v ∈ radL F, ((c : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ v ∈ radL F := by
  set C := ((c : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have hm : C * ggInvUMatrix 6 1 F = ggInvUMatrix 6 1 F * C := by
    have := congrArg (fun x : SU σ 6 => ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hc
    simp only [Subgroup.coe_mul, Units.val_mul, coe_ggInvSU σ (show 2 * 1 ≤ 6 by norm_num)]
      at this
    exact this
  have hv : ∀ v, ggInvUMatrix 6 1 F *ᵥ (C *ᵥ v) = C *ᵥ (ggInvUMatrix 6 1 F *ᵥ v) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec, hm]
  refine ⟨fun w hw => ?_, fun v hv' => ?_⟩
  · obtain ⟨a, rfl⟩ := mem_radW.mp hw
    rw [mulVec_smul]
    refine Submodule.smul_mem _ a ?_
    have he : Pi.single 5 (1 : F) = ggInvUMatrix 6 1 F *ᵥ Pi.single 0 1 - Pi.single 0 1 := by
      rw [ggInvUMatrix_six_one_mulVec, add_sub_cancel_left, Pi.single_eq_same, one_smul]
    rw [he, mulVec_sub, ← hv]
    exact ggInvUMatrix_six_one_sub_mem _
  · rw [← ggInvUMatrix_six_one_mulVec_eq_iff] at hv' ⊢
    rw [hv, hv']

theorem conj_mem_rootRad [CharP F 2] {c x : SU σ 6}
    (hc : c * ggInvSU σ 6 1 = ggInvSU σ 6 1 * c) (hx : x ∈ rootRad σ) :
    c * x * c⁻¹ ∈ rootRad σ := by
  have hc' : c⁻¹ * ggInvSU σ 6 1 = ggInvSU σ 6 1 * c⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨hgW, hgL⟩ := mulVec_mem_of_commute hc
  obtain ⟨hgW', hgL'⟩ := mulVec_mem_of_commute hc'
  obtain ⟨h1, h2, h3⟩ := hx
  set G := ((c : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  set G' := (((c⁻¹ : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  set X := ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have hinv : ∀ v, G *ᵥ (G' *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, show G * G' = (((c * c⁻¹ : SU σ 6) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) by simp only [Subgroup.coe_mul, Units.val_mul, G, G'],
      mul_inv_cancel, OneMemClass.coe_one, Units.val_one, one_mulVec]
  have hexp : ∀ v, (((c * x * c⁻¹ : SU σ 6) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) *ᵥ v = G *ᵥ (X *ᵥ (G' *ᵥ v)) := fun v => by
    simp only [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec, G, X, G', mul_assoc]
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v => ?_⟩
  · rw [hexp, h1 _ (hgW' v hv), hinv]
  · rw [hexp]
    have := hgW _ (h2 _ (hgL' v hv))
    rwa [mulVec_sub, hinv] at this
  · rw [hexp]
    have := hgL _ (h3 (G' *ᵥ v))
    rwa [mulVec_sub, hinv] at this

end Group

section Entries

variable {F : Type} [Field F]

@[expose] def midIdx (k : Fin 4) : Fin 6 := k.castSucc.succ

theorem val_midIdx (k : Fin 4) : (midIdx k : ℕ) = k + 1 := rfl

theorem midIdx_ne_zero (k : Fin 4) : midIdx k ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [val_midIdx] at this
  simp at this

theorem midIdx_ne_five (k : Fin 4) : midIdx k ≠ 5 := by
  intro h
  have h1 := congrArg Fin.val h
  rw [val_midIdx] at h1
  have := k.isLt
  simp at h1
  omega

theorem midIdx_injective : Function.Injective midIdx := by
  intro k l h
  have := congrArg Fin.val h
  rw [val_midIdx, val_midIdx] at this
  exact Fin.ext (by omega)

theorem rev_midIdx (k : Fin 4) : Fin.rev (midIdx k) = midIdx (Fin.rev k) := by
  ext
  rw [Fin.val_rev, val_midIdx, val_midIdx, Fin.val_rev]
  have := k.isLt
  omega

theorem sum_fin_six_mid {M : Type*} [AddCommMonoid M] (f : Fin 6 → M) :
    ∑ c, f c = f 0 + ∑ k : Fin 4, f (midIdx k) + f 5 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, add_assoc]
  rfl

@[expose] def radVec (M : Matrix (Fin 6) (Fin 6) F) : Fin 4 → F := fun k => M (midIdx k) 0

theorem radVec_mul {M M' : Matrix (Fin 6) (Fin 6) F} (hM : IsPairRadical (radW F) (radL F) M)
    (hM' : IsPairRadical (radW F) (radL F) M') : radVec (M * M') = radVec M + radVec M' := by
  obtain ⟨-, -, hm⟩ := entries_of_isPairRadical hM
  obtain ⟨-, h0', -⟩ := entries_of_isPairRadical hM'
  funext k
  rw [radVec, Pi.add_apply, radVec, radVec, mul_apply, Finset.sum_eq_add_of_mem 0 (midIdx k)
    (Finset.mem_univ _) (Finset.mem_univ _) (midIdx_ne_zero k).symm]
  · rw [h0' 0, one_apply_eq, mul_one, hm _ _ (midIdx_ne_five k) (midIdx_ne_zero k),
      one_apply_eq, one_mul]
  · intro c _ hc
    rw [hm _ _ (midIdx_ne_five k) hc.1, one_apply_ne (Ne.symm hc.2), zero_mul]

variable (σ : F ≃+* F)

theorem conjTr_antidiag_mul_apply (A : Matrix (Fin 6) (Fin 6) F) (i j : Fin 6) :
    (conjTr σ A * antidiag 6 * A : Matrix (Fin 6) (Fin 6) F) i j =
      ∑ b, σ (A (Fin.rev b) i) * A b j := by
  rw [mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [mul_apply, Finset.sum_eq_single (Fin.rev b)]
  · rw [antidiag, of_apply, Fin.rev_rev, ite_eq_left rfl, mul_one]
    rfl
  · intro a _ ha
    rw [antidiag, of_apply, ite_eq_right (fun h => ha (by rw [h, Fin.rev_rev])), mul_zero]
  · simp

variable {σ}

theorem entry_five_mid [CharP F 2] {M : Matrix (Fin 6) (Fin 6) F}
    (hM : IsPairRadical (radW F) (radL F) M)
    (hU : conjTr σ M * antidiag 6 * M = antidiag 6) (k : Fin 4) :
    M 5 (midIdx k) = σ (radVec M (Fin.rev k)) := by
  obtain ⟨-, h0, hm⟩ := entries_of_isPairRadical hM
  have h := congrFun (congrFun hU 0) (midIdx k)
  rw [conjTr_antidiag_mul_apply, sum_fin_six_mid, antidiag, of_apply,
    ite_eq_right (fun h' => midIdx_ne_five k (by rw [h']; rfl))] at h
  rw [h0 (midIdx k), one_apply_ne (midIdx_ne_zero k).symm, mul_zero, zero_add,
    show Fin.rev (5 : Fin 6) = 0 from rfl, h0 0, one_apply_eq, map_one, one_mul] at h
  rw [Finset.sum_eq_single k] at h
  · rw [hm _ _ (midIdx_ne_five k) (midIdx_ne_zero k), one_apply_eq, mul_one, rev_midIdx] at h
    rw [radVec]
    linear_combination h - (CharTwo.two_eq_zero (R := F)) * σ (M (midIdx (Fin.rev k)) 0)
  · intro l _ hl
    rw [hm _ _ (midIdx_ne_five l) (midIdx_ne_zero k),
      one_apply_ne (fun h' => hl (midIdx_injective h')), mul_zero]
  · simp

theorem entry_five_zero [CharP F 2] {M : Matrix (Fin 6) (Fin 6) F}
    (hM : IsPairRadical (radW F) (radL F) M)
    (hU : conjTr σ M * antidiag 6 * M = antidiag 6) :
    M 5 0 + σ (M 5 0) = radB σ (radVec M) (radVec M) := by
  obtain ⟨-, h0, -⟩ := entries_of_isPairRadical hM
  have h := congrFun (congrFun hU 0) 0
  rw [conjTr_antidiag_mul_apply, sum_fin_six_mid, antidiag, of_apply,
    ite_eq_right (by decide)] at h
  rw [show Fin.rev (0 : Fin 6) = 5 from rfl, show Fin.rev (5 : Fin 6) = 0 from rfl, h0 0,
    one_apply_eq, mul_one, map_one, one_mul] at h
  have hs : ∑ k : Fin 4, σ (M (Fin.rev (midIdx k)) 0) * M (midIdx k) 0 =
      radB σ (radVec M) (radVec M) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rev_midIdx]
    rfl
  rw [hs] at h
  linear_combination h - (CharTwo.two_eq_zero (R := F)) * radB σ (radVec M) (radVec M)

theorem mul_entry_five_zero [CharP F 2] {M M' : Matrix (Fin 6) (Fin 6) F}
    (hM : IsPairRadical (radW F) (radL F) M) (hU : conjTr σ M * antidiag 6 * M = antidiag 6)
    (hM' : IsPairRadical (radW F) (radL F) M') :
    (M * M') 5 0 = M 5 0 + M' 5 0 + radB σ (radVec M) (radVec M') := by
  obtain ⟨h5, -, -⟩ := entries_of_isPairRadical hM
  obtain ⟨-, h0', -⟩ := entries_of_isPairRadical hM'
  rw [mul_apply, sum_fin_six_mid, h0' 0, one_apply_eq, mul_one, h5 5, one_apply_eq, one_mul]
  have hs : ∑ k : Fin 4, M 5 (midIdx k) * M' (midIdx k) 0 = radB σ (radVec M) (radVec M') := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [entry_five_mid hM hU k]
    rfl
  rw [hs]
  ring

theorem radB_swap (hσ : ∀ c, σ (σ c) = c) (x y : Fin 4 → F) :
    radB σ y x = σ (radB σ x y) := by
  rw [radB, radB, map_sum]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, map_mul, hσ]
  ring

theorem radB_fixed_of_commute [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {M M' : Matrix (Fin 6) (Fin 6) F}
    (hM : IsPairRadical (radW F) (radL F) M) (hU : conjTr σ M * antidiag 6 * M = antidiag 6)
    (hM' : IsPairRadical (radW F) (radL F) M') (hU' : conjTr σ M' * antidiag 6 * M' = antidiag 6)
    (hc : M * M' = M' * M) :
    σ (radB σ (radVec M) (radVec M')) = radB σ (radVec M) (radVec M') := by
  have h1 := mul_entry_five_zero hM hU hM'
  have h2 := mul_entry_five_zero hM' hU' hM
  rw [hc, h2, add_comm (M' 5 0)] at h1
  rw [← radB_swap hσ]
  exact add_left_cancel h1

theorem exists_midIdx_eq {j : Fin 6} (h0 : j ≠ 0) (h5 : j ≠ 5) : ∃ k, midIdx k = j := by
  have h0' : (j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
  have h5' : (j : ℕ) ≠ 5 := fun h => h5 (Fin.ext h)
  have := j.isLt
  exact ⟨⟨(j : ℕ) - 1, by omega⟩, Fin.ext (by rw [val_midIdx]; simp only; omega)⟩

theorem eq_of_radVec_eq_zero [CharP F 2] {M M' : Matrix (Fin 6) (Fin 6) F}
    (hM : IsPairRadical (radW F) (radL F) M) (hU : conjTr σ M * antidiag 6 * M = antidiag 6)
    (hM' : IsPairRadical (radW F) (radL F) M') (hU' : conjTr σ M' * antidiag 6 * M' = antidiag 6)
    (hv : radVec M = 0) (hv' : radVec M' = 0) (h50 : M 5 0 = M' 5 0) : M = M' := by
  obtain ⟨h5, h0, hm⟩ := entries_of_isPairRadical hM
  obtain ⟨h5', h0', hm'⟩ := entries_of_isPairRadical hM'
  ext i j
  by_cases hj5 : j = 5
  · subst hj5; rw [h5, h5']
  by_cases hi0 : i = 0
  · subst hi0; rw [h0, h0']
  by_cases hi5 : i = 5
  · subst hi5
    by_cases hj0 : j = 0
    · subst hj0; exact h50
    · obtain ⟨k, rfl⟩ := exists_midIdx_eq hj0 hj5
      rw [entry_five_mid hM hU, entry_five_mid hM' hU', hv, hv']
  · by_cases hj0 : j = 0
    · subst hj0
      obtain ⟨k, rfl⟩ := exists_midIdx_eq hi0 hi5
      have e1 := congrFun hv k
      have e2 := congrFun hv' k
      rw [radVec] at e1 e2
      rw [Pi.zero_apply] at e1 e2
      rw [e1, e2]
    · rw [hm i j hi5 hj0, hm' i j hi5 hj0]

end Entries

section Count

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem midIdx_ne_rev (k : Fin 4) : midIdx k ≠ Fin.rev (midIdx k) := by
  intro h
  have h1 := congrArg Fin.val h
  rw [Fin.val_rev, val_midIdx] at h1
  have := k.isLt
  omega

variable (σ) in
theorem isPairRadical_rootMatrix (k : Fin 4) (c : F) :
    IsPairRadical (radW F) (radL F) (rootMatrix σ (midIdx k) 0 c) := by
  have hr : Fin.rev (0 : Fin 6) = 5 := rfl
  have hk5 : Fin.rev (midIdx k) ≠ 5 := by rw [rev_midIdx]; exact midIdx_ne_five _
  refine isPairRadical_of_entries (fun i => ?_) (fun j => ?_) (fun i j hi hj => ?_)
  · rw [rootMatrix, Matrix.sub_apply, Matrix.add_apply, single_apply, single_apply, hr,
      ite_eq_right (fun h => absurd h.2 (by decide)), ite_eq_right (fun h => hk5 h.2), add_zero,
      sub_zero]
  · rw [rootMatrix, Matrix.sub_apply, Matrix.add_apply, single_apply, single_apply, hr,
      ite_eq_right (fun h => midIdx_ne_zero k h.1), ite_eq_right (fun h => absurd h.1 (by decide)),
      add_zero, sub_zero]
  · rw [rootMatrix, Matrix.sub_apply, Matrix.add_apply, single_apply, single_apply, hr,
      ite_eq_right (fun h => hj h.2.symm), ite_eq_right (fun h => hi h.1.symm), add_zero, sub_zero]

variable (σ) in
theorem radVec_rootMatrix (k : Fin 4) (c : F) :
    radVec (rootMatrix σ (midIdx k) 0 c) = Pi.single k c := by
  funext l
  have h2 : ¬ (Fin.rev (0 : Fin 6) = midIdx l ∧ Fin.rev (midIdx k) = 0) :=
    fun h => midIdx_ne_five l h.1.symm
  rw [radVec, rootMatrix, Matrix.sub_apply, Matrix.add_apply, single_apply, single_apply,
    ite_eq_right h2, sub_zero, one_apply_ne (midIdx_ne_zero l), zero_add, Pi.single_apply]
  by_cases hl : l = k
  · subst hl; rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl]
  · rw [ite_eq_right (fun h => hl (midIdx_injective h.1).symm), ite_eq_right hl]

theorem radVec_one : radVec (1 : Matrix (Fin 6) (Fin 6) F) = 0 := by
  funext k
  rw [radVec, one_apply_ne (midIdx_ne_zero k), Pi.zero_apply]

theorem isPairRadical_longRootMatrix (d : F) :
    IsPairRadical (radW F) (radL F) (longRootMatrix (5 : Fin 6) d) := by
  have hr : Fin.rev (5 : Fin 6) = 0 := rfl
  refine isPairRadical_of_entries (fun i => ?_) (fun j => ?_) (fun i j hi hj => ?_)
  · rw [longRootMatrix, Matrix.add_apply, single_apply, hr, ite_eq_right (fun h => absurd h.2 (by decide)),
      add_zero]
  · rw [longRootMatrix, Matrix.add_apply, single_apply, ite_eq_right (fun h => absurd h.1 (by decide)),
      add_zero]
  · rw [longRootMatrix, Matrix.add_apply, single_apply, ite_eq_right (fun h => hi h.1.symm), add_zero]

theorem radVec_longRootMatrix (d : F) : radVec (longRootMatrix (5 : Fin 6) d) = 0 := by
  funext l
  rw [radVec, longRootMatrix, Matrix.add_apply, single_apply, one_apply_ne (midIdx_ne_zero l), zero_add,
    ite_eq_right (fun h => midIdx_ne_five l h.1.symm), Pi.zero_apply]

theorem longRootMatrix_five_zero (d : F) : longRootMatrix (5 : Fin 6) d 5 0 = d := by
  rw [longRootMatrix, Matrix.add_apply, single_apply, one_apply_ne (by decide), zero_add,
    ite_eq_left ⟨rfl, rfl⟩]

variable (σ) in
@[expose] noncomputable def radHom : rootRad σ →* Multiplicative (Fin 4 → F) where
  toFun g := Multiplicative.ofAdd (radVec (((g : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))
  map_one' := by
    change Multiplicative.ofAdd (radVec (1 : Matrix (Fin 6) (Fin 6) F)) = Multiplicative.ofAdd 0
    rw [radVec_one]
  map_mul' g g' := by
    change Multiplicative.ofAdd (radVec ((((g : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      (((g' : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))) = _
    rw [radVec_mul g.2 g'.2]
    rfl

theorem radHom_apply (g : rootRad σ) :
    radHom σ g = Multiplicative.ofAdd
      (radVec (((g : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) := rfl

end Count

section Card

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

@[expose] noncomputable def rootElt (hσ : ∀ c, σ (σ c) = c) (k : Fin 4) (c : F) : rootRad σ :=
  ⟨rootHom σ hσ (midIdx_ne_zero k) (midIdx_ne_rev k) (by decide) (Multiplicative.ofAdd c),
    isPairRadical_rootMatrix σ k c⟩

omit [CharP F 2] in
theorem radHom_rootElt (hσ : ∀ c, σ (σ c) = c) (k : Fin 4) (c : F) :
    radHom σ (rootElt hσ k c) = Multiplicative.ofAdd (Pi.single k c) := by
  rw [radHom_apply]
  exact congrArg Multiplicative.ofAdd (radVec_rootMatrix σ k c)

@[expose] noncomputable def longElt (d : traceZero σ) : rootRad σ :=
  ⟨longRootHom σ (by decide : (5 : Fin 6) ≠ Fin.rev 5) (Multiplicative.ofAdd d),
    isPairRadical_longRootMatrix (d : F)⟩

omit [CharP F 2] in
theorem matrix_longElt (d : traceZero σ) :
    ((((longElt d : rootRad σ) : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      longRootMatrix (5 : Fin 6) (d : F) := rfl

omit [CharP F 2] in
theorem card_rootRad_ge [Finite F] (hσ : ∀ c, σ (σ c) = c) :
    Nat.card F ^ 4 * Nat.card (traceZero σ) ≤ Nat.card (rootRad σ) := by
  have hrange : (radHom σ).range = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.ofAdd v = x := ⟨Multiplicative.toAdd x, rfl⟩
    refine ⟨rootElt hσ 0 (v 0) * rootElt hσ 1 (v 1) * rootElt hσ 2 (v 2) * rootElt hσ 3 (v 3), ?_⟩
    rw [map_mul, map_mul, map_mul, radHom_rootElt, radHom_rootElt, radHom_rootElt, radHom_rootElt,
      ← ofAdd_add, ← ofAdd_add, ← ofAdd_add]
    congr 1
    funext k
    fin_cases k <;> simp
  have hker : Nat.card (traceZero σ) ≤ Nat.card (radHom σ).ker := by
    refine Nat.card_le_card_of_injective (fun d => ⟨longElt d, ?_⟩) ?_
    · rw [MonoidHom.mem_ker, radHom_apply, matrix_longElt, radVec_longRootMatrix]
      rfl
    · intro d d' h
      have := congrArg (fun g : (radHom σ).ker =>
        ((((g : rootRad σ) : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) 5 0) h
      simp only [matrix_longElt, longRootMatrix_five_zero] at this
      exact Subtype.ext this
  have hsplit := Subgroup.card_ker_mul_card_range (radHom σ)
  rw [hrange, Subgroup.card_top] at hsplit
  have hM : Nat.card (Multiplicative (Fin 4 → F)) = Nat.card F ^ 4 := by
    rw [show Nat.card (Multiplicative (Fin 4 → F)) = Nat.card (Fin 4 → F) from rfl, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
  rw [hM] at hsplit
  rw [← hsplit, mul_comm]
  exact Nat.mul_le_mul_right _ hker

theorem card_le_of_abelian_rootRad [Finite F] (hσ : ∀ c, σ (σ c) = c) {θ : F} (hθ : σ θ ≠ θ)
    {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : Nat.card (traceZero σ) = q)
    {A : Subgroup (SU σ 6)} (hA : A ≤ rootRad σ) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ q ^ 5 := by
  set φ : A →* Multiplicative (Fin 4 → F) := (radHom σ).comp (Subgroup.inclusion hA) with hφ
  have hφapp : ∀ g : A, φ g = Multiplicative.ofAdd
      (radVec ((((g : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))) := fun g => rfl
  have hvec : ∀ g ∈ φ.ker, radVec ((((g : SU σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) =
      0 := by
    intro g hg
    rw [MonoidHom.mem_ker, hφapp] at hg
    exact congrArg Multiplicative.toAdd hg
  have hker : Nat.card φ.ker ≤ q := by
    rw [← hq]
    refine Nat.card_le_card_of_injective (fun g => ⟨((((g : A) : SU σ 6) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) 5 0, ?_⟩) ?_
    · have h := entry_five_zero (hA (g : A).2) ((g : A) : SU σ 6).2.2
      rw [hvec _ g.2] at h
      rw [mem_traceZero, h]
      simp [radB]
    · intro g g' h
      have h50 := congrArg Subtype.val h
      have heq := eq_of_radVec_eq_zero (hA (g : A).2) ((g : A) : SU σ 6).2.2
        (hA (g' : A).2) ((g' : A) : SU σ 6).2.2 (hvec _ g.2) (hvec _ g'.2) h50
      exact Subtype.ext (Subtype.ext (Subtype.ext (Units.ext heq)))
  let W : AddSubgroup (Fin 4 → F) :=
    { carrier := {v | Multiplicative.ofAdd v ∈ φ.range}
      add_mem' := fun {a b} ha hb => by
        change Multiplicative.ofAdd (a + b) ∈ φ.range
        rw [ofAdd_add]
        exact φ.range.mul_mem ha hb
      zero_mem' := by
        change Multiplicative.ofAdd (0 : Fin 4 → F) ∈ φ.range
        rw [ofAdd_zero]
        exact φ.range.one_mem
      neg_mem' := fun {a} ha => by
        change Multiplicative.ofAdd (-a) ∈ φ.range
        rw [ofAdd_neg]
        exact φ.range.inv_mem ha }
  have hW : ∀ x ∈ W, ∀ y ∈ W, σ (radB σ x y) = radB σ x y := by
    rintro x ⟨g, hg⟩ y ⟨g', hg'⟩
    rw [hφapp] at hg hg'
    have hx := congrArg Multiplicative.toAdd hg
    have hy := congrArg Multiplicative.toAdd hg'
    simp only [toAdd_ofAdd] at hx hy
    subst hx hy
    have hcomm := hc _ g.2 _ g'.2
    have hm := congrArg (fun z : SU σ 6 => ((z : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul] at hm
    exact radB_fixed_of_commute hσ (hA g.2) (g : SU σ 6).2.2 (hA g'.2) (g' : SU σ 6).2.2 hm
  have hWcard : Nat.card W = Nat.card φ.range :=
    Nat.card_congr
      { toFun := fun v => ⟨Multiplicative.ofAdd (v : Fin 4 → F), v.2⟩
        invFun := fun m => ⟨Multiplicative.toAdd (m : Multiplicative (Fin 4 → F)), m.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hsq := card_sq_le_of_radB_fixed σ hθ hW
  rw [hF, ← pow_mul, show q ^ (2 * 4) = (q ^ 4) ^ 2 by ring] at hsq
  have hW4 : Nat.card W ≤ q ^ 4 := (Nat.pow_le_pow_iff_left (by norm_num)).mp hsq
  have hsplit := Subgroup.card_ker_mul_card_range φ
  rw [← hsplit, ← hWcard]
  calc Nat.card φ.ker * Nat.card W ≤ q * q ^ 4 := Nat.mul_le_mul hker hW4
    _ = q ^ 5 := by ring

end Card

end SUFacts

end CFSG.StandardType
