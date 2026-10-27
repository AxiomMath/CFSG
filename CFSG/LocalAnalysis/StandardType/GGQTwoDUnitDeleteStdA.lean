module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs
public import CFSG.GH74.L5U5.IdentUnitary
public import CFSG.ClassicalInvolution.Phan.Center
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.TypeAChain

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear Additive
open scoped Matrix commutatorElement

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ} {ω : F0ˣ} {c : Fin m}

@[expose] noncomputable def qtwoDB39_delDiag (ω : F0ˣ) (c : Fin m) : Fin m → F0ˣ :=
  fun i => if i = c then ω else 1

private theorem qtwoDB39_diag_val (d : Fin m → F0ˣ) :
    ((qTwoChartTwoThree_diag d : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal fun i => (d i : F0) := rfl

theorem qtwoDB39_diag_conjTr_mul (hF0 : Nat.card F0 = 4) (d : Fin m → F0ˣ) :
    CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1)
        ((qTwoChartTwoThree_diag d : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
      ((qTwoChartTwoThree_diag d : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 := by
  classical
  haveI : Fintype F0 := Fintype.ofFinite F0
  have hcard : Fintype.card F0 = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF0
  have h3 : ∀ i : Fin m, (d i : F0) ^ 3 = 1 := by
    intro i
    have h := FiniteField.pow_card_sub_one_eq_one (d i : F0) (d i).ne_zero
    rw [hcard] at h
    simpa using h
  rw [qtwoDB39_diag_val, CFSG.LieType.Steinberg.conjTr_diagonal,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, show (2 : ℕ) ^ 1 = 2 from rfl]
  rw [show (d i : F0) ^ 2 * (d i : F0) = (d i : F0) ^ 3 by ring, h3 i]

noncomputable def qtwoDB39_conjAut (hF0 : Nat.card F0 = 4) (d : Fin m → F0ˣ) :
    MulAut (Su F0 2 1 m) :=
  CFSG.ClassicalInvolution.Balance.StrongBalance.conjSUid
    (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1) m
    ⟨qTwoChartTwoThree_diag d,
      (CFSG.ClassicalInvolution.Balance.StrongBalance.mem_GUid).mpr
        (qtwoDB39_diag_conjTr_mul hF0 d)⟩

theorem qtwoDB39_conjAut_apply (hF0 : Nat.card F0 = 4) (d : Fin m → F0ˣ)
    (u : Su F0 2 1 m) :
    ((qtwoDB39_conjAut hF0 d u : Su F0 2 1 m) : GL (Fin m) F0) =
      qTwoChartTwoThree_diag d * (u : GL (Fin m) F0) * (qTwoChartTwoThree_diag d)⁻¹ := by
  unfold qtwoDB39_conjAut
  rw [CFSG.ClassicalInvolution.Balance.StrongBalance.coe_conjSUid]

theorem qtwoDB39_mem_fixed_iff (hF0 : Nat.card F0 = 4) (d : Fin m → F0ˣ)
    (u : Su F0 2 1 m) :
    u ∈ fixedGroup (qtwoDB39_conjAut hF0 d) ↔
      qTwoChartTwoThree_diag d * (u : GL (Fin m) F0) =
        (u : GL (Fin m) F0) * qTwoChartTwoThree_diag d := by
  rw [mem_fixedGroup]
  constructor
  · intro h
    have h2 := congrArg (fun z : Su F0 2 1 m => (z : GL (Fin m) F0)) h
    rw [qtwoDB39_conjAut_apply] at h2
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  · intro h
    apply Subtype.ext
    rw [qtwoDB39_conjAut_apply]
    rw [h]
    group

private theorem qtwoDB39_entry_eq_zero {d : Fin m → F0ˣ} {y : Su F0 2 1 m}
    (hy : qTwoChartTwoThree_diag d * (y : GL (Fin m) F0) =
      (y : GL (Fin m) F0) * qTwoChartTwoThree_diag d)
    {i j : Fin m} (hij : d i ≠ d j) :
    ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j = 0 := by
  have h := congrArg (fun z : Matrix (Fin m) (Fin m) F0 => z i j)
    (congrArg (fun z : GL (Fin m) F0 => (z : Matrix (Fin m) (Fin m) F0)) hy)
  simp only [Units.val_mul, qtwoDB39_diag_val, Matrix.diagonal_mul,
    Matrix.mul_diagonal] at h
  have h3 : (((d i : F0ˣ) : F0) - ((d j : F0ˣ) : F0)) *
      ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j = 0 := by
    rw [sub_mul, mul_comm ((d j : F0ˣ) : F0)]
    linear_combination h
  exact (mul_eq_zero.mp h3).resolve_left (fun h => hij (Units.ext (sub_eq_zero.mp h)))

private theorem qtwoDB39_offdiag_zero (hF0 : Nat.card F0 = 4) {d : Fin m → F0ˣ}
    {y : Su F0 2 1 m} (hy : y ∈ fixedGroup (qtwoDB39_conjAut hF0 d))
    {i j : Fin m} (hij : d i ≠ d j) :
    ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j = 0 :=
  qtwoDB39_entry_eq_zero ((qtwoDB39_mem_fixed_iff hF0 d y).mp hy) hij

private theorem qtwoDB39_delDiag_apply_self : qtwoDB39_delDiag ω c c = ω := by
  simp [qtwoDB39_delDiag]

private theorem qtwoDB39_delDiag_apply_of_ne {i : Fin m} (hi : i ≠ c) :
    qtwoDB39_delDiag ω c i = 1 := by
  simp [qtwoDB39_delDiag, hi]

private theorem qtwoDB39_delDiag_ne_self (hω : ω ≠ 1) {i : Fin m} (hi : i ≠ c) :
    qtwoDB39_delDiag ω c i ≠ qtwoDB39_delDiag ω c c := by
  rw [qtwoDB39_delDiag_apply_of_ne hi, qtwoDB39_delDiag_apply_self]
  exact fun h => hω h.symm

private theorem qtwoDB39_delDiag_self_ne (hω : ω ≠ 1) {j : Fin m} (hj : j ≠ c) :
    qtwoDB39_delDiag ω c c ≠ qtwoDB39_delDiag ω c j := by
  rw [qtwoDB39_delDiag_apply_of_ne hj, qtwoDB39_delDiag_apply_self]
  exact hω

theorem qtwoDB39_coordBlock_le_fixed (hF0 : Nat.card F0 = 4) {J : Finset (Fin m)}
    {d : Fin m → F0ˣ} (hd : ∀ i ∈ J, ∀ j ∈ J, d i = d j) :
    coordBlockSU F0 2 1 J ≤ fixedGroup (qtwoDB39_conjAut hF0 d) := by
  intro u hu
  rw [qtwoDB39_mem_fixed_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, qtwoDB39_diag_val]
  exact diagonal_mul_comm_of_mem_coordBlockSU hu (fun i hi j hj => by rw [hd i hi j hj])

private theorem qtwoDB39_compIndicator_comm (hF0 : Nat.card F0 = 4) (hω : ω ≠ 1)
    {y : Su F0 2 1 m}
    (hy : y ∈ fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c))) :
    compIndicator F0 (Finset.univ.erase c) *
        ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        compIndicator F0 (Finset.univ.erase c) := by
  ext i j
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hi : i ∈ Finset.univ.erase c
  · have hic : i ≠ c := (Finset.mem_erase.mp hi).1
    by_cases hj : j ∈ Finset.univ.erase c
    · simp [hi, hj]
    · have hjc : j = c := by simpa using hj
      have hY : ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j = 0 := by
        rw [hjc]
        exact qtwoDB39_offdiag_zero hF0 hy (qtwoDB39_delDiag_ne_self hω hic)
      rw [if_pos hi, if_neg hj, hY]
  · have hic : i = c := by simpa using hi
    by_cases hj : j ∈ Finset.univ.erase c
    · have hjc : j ≠ c := (Finset.mem_erase.mp hj).1
      have hY : ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j = 0 := by
        rw [hic]
        exact qtwoDB39_offdiag_zero hF0 hy (qtwoDB39_delDiag_self_ne hω hjc)
      rw [if_neg hi, if_pos hj, hY]
    · simp [hi, hj]

theorem qtwoDB39_coordBlock_normal (hF0 : Nat.card F0 = 4) (hω : ω ≠ 1) :
    ((coordBlockSU F0 2 1 (Finset.univ.erase c)).subgroupOf
      (fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c)))).Normal := by
  have hle : coordBlockSU F0 2 1 (Finset.univ.erase c) ≤
      fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c)) :=
    qtwoDB39_coordBlock_le_fixed hF0 (fun i hi j hj => by
      rw [qtwoDB39_delDiag_apply_of_ne (Finset.mem_erase.mp hi).1,
        qtwoDB39_delDiag_apply_of_ne (Finset.mem_erase.mp hj).1])
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro x y hx hy
  exact conj_mem_coordBlockSU (qtwoDB39_compIndicator_comm hF0 hω hy) hx

theorem qtwoDB39_isQuasisimple (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m) :
    CFSG.IsQuasisimple (coordBlockSU F0 2 1 (Finset.univ.erase c)) := by
  have hcardS : (Finset.univ.erase c : Finset (Fin m)).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hsu : CFSG.IsQuasisimple (Su F0 2 1 (Finset.univ.erase c).card) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.GH74.L5U5.isQuasisimple_su (K := F0) (p := 2) (f := 1) ?_ ?_ ?_
    · rw [hF0]; norm_num
    · rw [hcardS]; omega
    · rw [hcardS]
      intro h
      exact absurd (Prod.mk.inj h).1 (by omega)
  exact IsQuasisimple.of_mulEquiv
    (MonoidHom.ofInjective (blockSUOn_injective (K := F0) (p := 2) (f := 1)
      (Finset.univ.erase c))).symm hsu

theorem qtwoDB39_isComponentOf (hF0 : Nat.card F0 = 4) (hω : ω ≠ 1) (hm : 5 ≤ m) :
    IsComponentOf (coordBlockSU F0 2 1 (Finset.univ.erase c))
      (fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c))) := by
  have hle : coordBlockSU F0 2 1 (Finset.univ.erase c) ≤
      fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c)) :=
    qtwoDB39_coordBlock_le_fixed hF0 (fun i hi j hj => by
      rw [qtwoDB39_delDiag_apply_of_ne (Finset.mem_erase.mp hi).1,
        qtwoDB39_delDiag_apply_of_ne (Finset.mem_erase.mp hj).1])
  refine ⟨hle, IsSubnormal.step hle (qtwoDB39_coordBlock_normal hF0 hω)
    (IsSubnormal.refl _), ?_⟩
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
    _).mpr (qtwoDB39_isQuasisimple hF0 hm)

theorem qtwoDB39_mem_coordBlock_iff (hF0 : Nat.card F0 = 4) (hω : ω ≠ 1)
    {y : Su F0 2 1 m}
    (hy : y ∈ fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c))) :
    y ∈ coordBlockSU F0 2 1 (Finset.univ.erase c) ↔
      ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) c c = 1 := by
  constructor
  · intro hyQ
    have h := (mem_coordBlockSU_iff.mp hyQ) c c (Or.inr (by simp))
    simpa using h
  · intro hcc
    rw [mem_coordBlockSU_iff]
    intro i j hij
    rcases hij with hi | hj
    · have hic : i = c := by simpa using hi
      by_cases hjc : j = c
      · rw [hic, hjc, hcc]; simp
      · have hY : (((y : GL (Fin m) F0)) : Matrix (Fin m) (Fin m) F0) i j = 0 := by
          rw [hic]
          exact qtwoDB39_offdiag_zero hF0 hy (qtwoDB39_delDiag_self_ne hω hjc)
        rw [hY, if_neg (fun h => hjc (h.symm.trans hic))]
    · have hjc : j = c := by simpa using hj
      by_cases hic : i = c
      · rw [hic, hjc, hcc]; simp
      · have hY : (((y : GL (Fin m) F0)) : Matrix (Fin m) (Fin m) F0) i j = 0 := by
          rw [hjc]
          exact qtwoDB39_offdiag_zero hF0 hy (qtwoDB39_delDiag_ne_self hω hic)
        rw [hY, if_neg (fun h => hic (h.trans hjc))]

private theorem qtwoDB39_mul_apply_cc (hF0 : Nat.card F0 = 4) (hω : ω ≠ 1)
    {y z : Su F0 2 1 m}
    (hy : y ∈ fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c)))
    (hz : z ∈ fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c))) :
    (((y * z : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) c c =
      (((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) c c) *
        (((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) c c) := by
  change ((((y : GL (Fin m) F0) * (z : GL (Fin m) F0) : GL (Fin m) F0) :
    Matrix (Fin m) (Fin m) F0)) c c = _
  rw [Units.val_mul, Matrix.mul_apply]
  refine (Finset.sum_eq_single c ?_ ?_).trans ?_
  · intro k _ hk
    rw [qtwoDB39_offdiag_zero hF0 hy (qtwoDB39_delDiag_self_ne hω hk), zero_mul]
  · intro hc; exact absurd (Finset.mem_univ c) hc
  · rfl

noncomputable def qtwoDB39_diagHom (hF0 : Nat.card F0 = 4) (hω : ω ≠ 1) :
    ↥(fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c))) →* F0ˣ where
  toFun y := Units.mk0 ((((y.1 : GL (Fin m) F0)) : Matrix (Fin m) (Fin m) F0) c c) (by
    intro hzero
    have hcol : ∀ i, (((y.1 : GL (Fin m) F0)) : Matrix (Fin m) (Fin m) F0) i c = 0 := by
      intro i
      by_cases hic : i = c
      · subst hic; exact hzero
      · exact qtwoDB39_offdiag_zero hF0 y.2 (qtwoDB39_delDiag_ne_self hω hic)
    exact (Matrix.GeneralLinearGroup.det_ne_zero (y.1 : GL (Fin m) F0))
      (Matrix.det_eq_zero_of_column_eq_zero c hcol))
  map_one' := by
    apply Units.ext
    simp
  map_mul' := by
    intro a b
    apply Units.ext
    simp only [Units.val_mul]
    exact qtwoDB39_mul_apply_cc hF0 hω a.2 b.2

theorem qtwoDB39_commutator_le (hF0 : Nat.card F0 = 4) (hω : ω ≠ 1) :
    ⁅fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c)),
      fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c))⁆ ≤
      coordBlockSU F0 2 1 (Finset.univ.erase c) := by
  rw [Subgroup.commutator_le]
  intro A hA B hB
  have hcom_fixed : ⁅A, B⁆ ∈ fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c)) := by
    rw [mem_fixedGroup, map_commutatorElement, mem_fixedGroup.mp hA, mem_fixedGroup.mp hB]
  refine (qtwoDB39_mem_coordBlock_iff hF0 hω hcom_fixed).mpr ?_
  have heq : (⟨⁅A, B⁆, hcom_fixed⟩ :
        ↥(fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c)))) =
      ⁅(⟨A, hA⟩ : ↥(fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c)))),
        (⟨B, hB⟩ : ↥(fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c))))⁆ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  have hone : qtwoDB39_diagHom hF0 hω
      (⟨⁅A, B⁆, hcom_fixed⟩ :
        ↥(fixedGroup (qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c)))) = 1 := by
    rw [heq, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hval := congrArg (fun t : F0ˣ => (t : F0)) hone
  simpa [qtwoDB39_diagHom] using hval

theorem qtwoDB39_fixed_of_conj_scalar (hF0 : Nat.card F0 = 4) (hm : 3 ≤ m)
    (hω : orderOf ω = 3) {u : Su F0 2 1 m} {z : Su F0 2 1 m}
    (hz : z ∈ Subgroup.center (Su F0 2 1 m))
    (h : qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c) u = z * u) :
    qtwoDB39_conjAut hF0 (qtwoDB39_delDiag ω c) u = u := by
  have hω1 : ω ≠ 1 := by
    rintro rfl
    simp at hω
  have hω1' : (ω : F0) ≠ 1 := fun h => hω1 (Units.ext h)
  have hω2 : ω ^ 2 ≠ 1 := by
    intro hh
    have hdvd : orderOf ω ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hh
    rw [hω] at hdvd
    norm_num at hdvd
  have hmat : qTwoChartTwoThree_diag (qtwoDB39_delDiag ω c) * (u : GL (Fin m) F0) =
      (z : GL (Fin m) F0) * (u : GL (Fin m) F0) *
        qTwoChartTwoThree_diag (qtwoDB39_delDiag ω c) := by
    have h2 := congrArg (fun t : Su F0 2 1 m => (t : GL (Fin m) F0)) h
    rw [qtwoDB39_conjAut_apply, Subgroup.coe_mul] at h2
    rw [← h2]
    group
  obtain ⟨lam, hlam⟩ := CFSG.ClassicalInvolution.Phan.exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := F0) (p := 2)
      (f := 1) (by rw [hF0]; norm_num)) hm hz
  have hentry : ∀ i j : Fin m,
      (((qtwoDB39_delDiag ω c i : F0ˣ) : F0) -
        (lam : F0) * ((qtwoDB39_delDiag ω c j : F0ˣ) : F0)) *
      (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j) = 0 := by
    intro i j
    have hh := congrFun (congrFun (congrArg (fun t : GL (Fin m) F0 =>
      (t : Matrix (Fin m) (Fin m) F0)) hmat) i) j
    simp only [Units.val_mul, qtwoDB39_diag_val, hlam, Matrix.scalar_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal] at hh
    rw [sub_mul]
    linear_combination hh
  by_cases hlam1 : lam = 1
  · have hz1 : z = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hlam, hlam1]
      simp
    rw [h, hz1, one_mul]
  · exfalso
    have hlam1' : (lam : F0) ≠ 1 := fun h => hlam1 (Units.ext h)
    have hdet_ne : (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero (u : GL (Fin m) F0)
    have hω2' : ((ω : F0) ^ 2) ≠ 1 := by
      intro hh
      exact hω2 (Units.ext (by simpa using hh))
    by_cases hlamω : lam = ω
    · apply hdet_ne
      apply Matrix.det_eq_zero_of_column_eq_zero c
      intro i
      by_cases hic : i = c
      · rw [hic]
        have h := hentry c c
        rw [qtwoDB39_delDiag_apply_self, hlamω] at h
        refine (mul_eq_zero.mp h).resolve_left ?_
        have hcoef : (ω : F0) - (ω : F0) * (ω : F0) ≠ 0 := by
          have : (ω : F0) - (ω : F0) * (ω : F0) = (ω : F0) * (1 - (ω : F0)) := by ring
          rw [this]
          exact mul_ne_zero (Units.ne_zero ω) (sub_ne_zero.mpr (Ne.symm hω1'))
        exact hcoef
      · have h := hentry i c
        rw [qtwoDB39_delDiag_apply_of_ne hic, qtwoDB39_delDiag_apply_self, hlamω] at h
        refine (mul_eq_zero.mp h).resolve_left ?_
        have hcoef : (1 : F0) - (ω : F0) * (ω : F0) ≠ 0 := by
          have hsq : (1 : F0) - (ω : F0) * (ω : F0) = 1 - (ω : F0) ^ 2 := by ring
          rw [hsq]
          exact sub_ne_zero.mpr (Ne.symm hω2')
        simpa using hcoef
    · apply hdet_ne
      apply Matrix.det_eq_zero_of_row_eq_zero c
      intro j
      have hlamω' : (lam : F0) ≠ (ω : F0) := fun h => hlamω (Units.ext h)
      by_cases hjc : j = c
      · rw [hjc]
        have h := hentry c c
        rw [qtwoDB39_delDiag_apply_self] at h
        refine (mul_eq_zero.mp h).resolve_left ?_
        have hcoef : (ω : F0) - (lam : F0) * (ω : F0) ≠ 0 := by
          have : (ω : F0) - (lam : F0) * (ω : F0) = (ω : F0) * (1 - (lam : F0)) := by ring
          rw [this]
          exact mul_ne_zero (Units.ne_zero ω) (sub_ne_zero.mpr (Ne.symm hlam1'))
        exact hcoef
      · have h := hentry c j
        rw [qtwoDB39_delDiag_apply_self, qtwoDB39_delDiag_apply_of_ne hjc] at h
        refine (mul_eq_zero.mp h).resolve_left ?_
        have hcoef : (ω : F0) - (lam : F0) * (1 : F0) ≠ 0 := by
          rw [mul_one]
          exact sub_ne_zero.mpr (Ne.symm hlamω')
        simpa using hcoef

end CFSG.StandardType.QTwo

end
