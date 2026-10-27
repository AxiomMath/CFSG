module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalStd

public section

namespace CFSG.StandardType

namespace GGOppRad

open Matrix CFSG.LieType.BorelTits

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

structure OppData (ℓ : ι → ℕ) (F' : ℕ → Submodule K (ι → K)) : Prop where
  mono : Monotone F'
  zero : F' 0 = ⊥
  top : ∃ m, F' m = ⊤
  compl : ∀ j, ∃ k, IsCompl (stdFlag ℓ k) (F' j)

namespace OppData

section

open scoped Classical

variable {ℓ : ι → ℕ} {F' : ℕ → Submodule K (ι → K)} (D : OppData ℓ F')

@[expose] noncomputable def level (j : ℕ) : ℕ :=
  Nat.find (D.compl j)

omit [Fintype ι] [DecidableEq ι] in
theorem isCompl_level (j : ℕ) : IsCompl (stdFlag ℓ (D.level j)) (F' j) :=
  Nat.find_spec (D.compl j)

omit [Fintype ι] [DecidableEq ι] in
theorem level_le {j k : ℕ} (h : IsCompl (stdFlag ℓ k) (F' j)) : D.level j ≤ k :=
  Nat.find_min' (D.compl j) h

omit [DecidableEq ι] in
theorem level_antitone : Antitone D.level := by
  intro j j' hjj'
  by_contra hlt
  rw [not_le] at hlt
  have hle : stdFlag (K := K) ℓ (D.level j) ≤ stdFlag ℓ (D.level j') := stdFlag_mono ℓ hlt.le
  have h1 := Submodule.finrank_add_eq_of_isCompl (D.isCompl_level j)
  have h2 := Submodule.finrank_add_eq_of_isCompl (D.isCompl_level j')
  have h3 := Submodule.finrank_mono (D.mono hjj')
  have heq : stdFlag (K := K) ℓ (D.level j) = stdFlag ℓ (D.level j') :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  have := D.level_le (j := j') (k := D.level j) (by rw [heq]; exact D.isCompl_level j')
  omega

omit [Fintype ι] in
theorem lt_level_zero (a : ι) : ℓ a < D.level 0 := by
  have h := D.isCompl_level 0
  rw [D.zero] at h
  have htop : stdFlag (K := K) ℓ (D.level 0) = ⊤ := by
    have := h.sup_eq_top
    rwa [sup_bot_eq] at this
  exact single_mem_stdFlag.mp (htop ▸ Submodule.mem_top : (Pi.single a (1 : K) : ι → K) ∈ _)

omit [Fintype ι] [DecidableEq ι] in
theorem level_eq_zero {j : ℕ} (hj : F' j = ⊤) : D.level j = 0 :=
  Nat.le_zero.mp (D.level_le (by rw [hj, stdFlag_zero]; exact isCompl_bot_top))

omit [Fintype ι] [DecidableEq ι] in
theorem exists_level_succ_le (a : ι) : ∃ j, D.level (j + 1) ≤ ℓ a := by
  obtain ⟨m, hm⟩ := D.top
  refine ⟨m, ?_⟩
  rw [D.level_eq_zero (top_le_iff.mp ((le_of_eq hm.symm).trans (D.mono (Nat.le_succ m))))]
  exact Nat.zero_le _

@[expose] noncomputable def idx (a : ι) : ℕ :=
  Nat.find (D.exists_level_succ_le a)

theorem idx_lt_iff {a : ι} {j : ℕ} : D.idx a < j ↔ D.level j ≤ ℓ a := by
  constructor
  · intro h
    exact (D.level_antitone (Nat.succ_le_of_lt h)).trans (Nat.find_spec (D.exists_level_succ_le a))
  · intro h
    cases j with
    | zero => exact absurd h (not_le.mpr (D.lt_level_zero a))
    | succ j => exact Nat.lt_succ_of_le (Nat.find_min' _ h)

@[expose] noncomputable def col (a : ι) : ι → K :=
  (F' (D.idx a + 1)).projection (stdFlag ℓ (D.level (D.idx a + 1)))
    (D.isCompl_level (D.idx a + 1)).symm (Pi.single a 1)

omit [Fintype ι] in
theorem col_mem (a : ι) : D.col a ∈ F' (D.idx a + 1) :=
  Submodule.projection_apply_mem _ _

@[expose] noncomputable def mat : Matrix ι ι K :=
  Matrix.of fun c a => D.col a c

theorem mat_apply_of_not_lt {c a : ι} (h : ¬ D.idx a < D.idx c) :
    D.mat c a = (1 : Matrix ι ι K) c a := by
  have hmem := Submodule.sub_projection_mem (D.isCompl_level (D.idx a + 1)).symm
    (Pi.single a (1 : K))
  have hc : D.level (D.idx a + 1) ≤ ℓ c := D.idx_lt_iff.mp (by omega)
  have h1 := hmem c hc
  rw [Pi.sub_apply, sub_eq_zero] at h1
  change D.col a c = _
  rw [col, ← h1, Pi.single_apply, Matrix.one_apply]

theorem det_mat : D.mat.det = 1 := by
  have hbt : D.mat.BlockTriangular (fun c => OrderDual.toDual (D.idx c)) := by
    intro r s hrs
    have h1 : D.idx r < D.idx s := hrs
    rw [D.mat_apply_of_not_lt (by omega), Matrix.one_apply_ne (by rintro rfl; omega)]
  rw [hbt.det]
  refine Finset.prod_eq_one fun x _ => ?_
  have hblk : D.mat.toSquareBlock (fun c => OrderDual.toDual (D.idx c)) x = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    have hrs : D.idx r = D.idx s := OrderDual.toDual.injective (hr.trans hs.symm)
    rw [Matrix.toSquareBlock_def, Matrix.of_apply]
    change D.mat r s = _
    rw [D.mat_apply_of_not_lt (by omega)]
    simp only [Matrix.one_apply, Subtype.mk.injEq]
  rw [hblk, Matrix.det_one]

@[expose] noncomputable def elt : Matrix.SpecialLinearGroup ι K :=
  ⟨D.mat, D.det_mat⟩

theorem elt_mem_stdUop [Finite K] : D.elt ∈ stdUop D.idx :=
  mem_stdUop_iff.mpr fun _ _ h => D.mat_apply_of_not_lt h

theorem stdUop_idx_le [Finite K] : stdUop (K := K) D.idx ≤ stdU ℓ :=
  stdUop_le_stdU fun c a h => by
    have h1 : ¬ D.level (D.idx a + 1) ≤ ℓ c := fun h' => by
      have := D.idx_lt_iff.mpr h'
      omega
    have h2 : D.level (D.idx a + 1) ≤ ℓ a := D.idx_lt_iff.mp (Nat.lt_succ_self _)
    omega

theorem slRep_elt_single (a : ι) : slRep D.elt (Pi.single a 1) = D.col a := by
  rw [slRep_apply]
  ext c
  rw [mulVec_single_one, col_apply]
  rfl

theorem flagMap_elt : flagMap slRep D.elt (stdFlag D.idx) = F' := by
  funext j
  have hinj : Function.Injective (slRep D.elt) := fun x y hxy => by
    simpa only [rep_inv_apply_rep] using congrArg (slRep D.elt⁻¹) hxy
  have hle : flagMap slRep D.elt (stdFlag D.idx) j ≤ F' j := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v = ∑ a, v a • (Pi.single a (1 : K) : ι → K) := by
      conv_lhs => rw [← (Pi.basisFun K ι).sum_repr v]
      simp
    rw [hv', map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [map_smul, D.slRep_elt_single]
    by_cases ha : D.idx a < j
    · exact Submodule.smul_mem _ _ (D.mono (Nat.succ_le_of_lt ha) (D.col_mem a))
    · rw [hv a (not_lt.mp ha), zero_smul]
      exact zero_mem _
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have e1 : Module.finrank K ((stdFlag (K := K) D.idx j).map (slRep D.elt)) =
      Module.finrank K (stdFlag (K := K) D.idx j) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm
  have e2 : Fintype.card {a // D.idx a < j} = Fintype.card {a // D.level j ≤ ℓ a} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun _ => D.idx_lt_iff)
  have e3 : Fintype.card {a // D.level j ≤ ℓ a} =
      Fintype.card ι - Fintype.card {a // ℓ a < D.level j} := by
    rw [← Fintype.card_subtype_compl]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => not_lt.symm)
  have e4 := Submodule.finrank_add_eq_of_isCompl (D.isCompl_level j)
  rw [finrank_stdFlag, Module.finrank_fintype_fun_eq_card] at e4
  have e5 : Fintype.card {a // ℓ a < D.level j} ≤ Fintype.card ι := Fintype.card_subtype_le _
  change Module.finrank K ((stdFlag (K := K) D.idx j).map (slRep D.elt)) =
    Module.finrank K (F' j)
  rw [e1, finrank_stdFlag, e2, e3]
  omega

theorem flagKernel_eq :
    flagKernel slRep F' = (stdU (K := K) D.idx).map (MulAut.conj D.elt).toMonoidHom := by
  rw [stdU, ← flagKernel_flagMap, D.flagMap_elt]

end

end OppData

end GGOppRad

end CFSG.StandardType
