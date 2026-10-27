module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8
public import CFSG.HardMathSupport.Lang.E27Lie.MinusToralCore
public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec19.Step1914E
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.Walter.J1Props
public import Certificates.Certificate8166

public section

namespace CFSG.StandardType.HalfFusOm8

open CFSG.RankThree.PartTwo.Sec4.RonanK429F (Om8 bl submatrix_bl)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F.Om8
open CFSG.Open (StatedOmega StatedQuadMinus StatedQuadPlus)
open Matrix
open scoped commutatorElement

@[expose] def coord8 : ι → Fin 8
  | Sum.inl i => ⟨i.1, by have := i.2; omega⟩
  | Sum.inr (Sum.inl i) => ⟨i.1 + 3, by have := i.2; omega⟩
  | Sum.inr (Sum.inr i) => ⟨i.1 + 6, by have := i.2; omega⟩

@[expose] def coord6 : ι6 → Fin 6
  | Sum.inl i => ⟨i.1, by have := i.2; omega⟩
  | Sum.inr i => ⟨i.1 + 3, by have := i.2; omega⟩

@[expose] def mat8 (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix ι ι (ZMod 2) :=
  M.submatrix coord8 coord8

@[expose] def mat6 (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix ι6 ι6 (ZMod 2) :=
  M.submatrix coord6 coord6

@[expose] def tpL : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 1]

@[expose] def tpiL : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 0]

@[expose] def ccL : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0, 1, 1; 1, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 0, 0, 1, 0;
    0, 1, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 0]

@[expose] def cciL : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 1;
    0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0, 0, 0]

@[expose] def sgL : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 0, 0, 1, 0, 1, 1; 1, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0;
    1, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0, 0, 0]

@[expose] def s1L : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0; 1, 1, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def s1iL : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def s2L : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 1, 0; 1, 1, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def s2iL : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 1, 0, 0; 1, 1, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0; 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def tau1L : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0; 1, 1, 0, 1, 1, 0; 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def tau2L : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem ccL_mul_cciL : mat8 ccL * mat8 cciL = 1 := by decide +kernel

theorem cciL_mul_ccL : mat8 cciL * mat8 ccL = 1 := by decide +kernel

theorem sgL_mul_sgL : mat8 sgL * mat8 sgL = 1 := by decide +kernel

theorem tpL_mul_tpiL : mat8 tpL * mat8 tpiL = 1 := by decide +kernel

theorem s1L_mul_s1iL : mat6 s1L * mat6 s1iL = 1 := by decide +kernel

theorem s1iL_mul_s1L : mat6 s1iL * mat6 s1L = 1 := by decide +kernel

theorem s2L_mul_s2iL : mat6 s2L * mat6 s2iL = 1 := by decide +kernel

theorem s2iL_mul_s2L : mat6 s2iL * mat6 s2L = 1 := by decide +kernel

theorem tau1L_mul_tau1L : mat6 tau1L * mat6 tau1L = 1 := by decide +kernel

theorem tau2L_mul_tau2L : mat6 tau2L * mat6 tau2L = 1 := by decide +kernel

theorem ccL_iso : ∀ v : ι → ZMod 2, Q8 (mat8 ccL *ᵥ v) = Q8 v := by decide +kernel

theorem sgL_iso : ∀ v : ι → ZMod 2, Q8 (mat8 sgL *ᵥ v) = Q8 v := by decide +kernel

theorem s1L_iso : ∀ v : ι6 → ZMod 2,
    StatedQuadPlus 3 (ZMod 2) (mat6 s1L *ᵥ v) = StatedQuadPlus 3 (ZMod 2) v := by decide +kernel

theorem s2L_iso : ∀ v : ι6 → ZMod 2,
    StatedQuadPlus 3 (ZMod 2) (mat6 s2L *ᵥ v) = StatedQuadPlus 3 (ZMod 2) v := by decide +kernel

theorem tau1L_iso : ∀ v : ι6 → ZMod 2,
    StatedQuadPlus 3 (ZMod 2) (mat6 tau1L *ᵥ v) = StatedQuadPlus 3 (ZMod 2) v := by decide +kernel

theorem tau2L_iso : ∀ v : ι6 → ZMod 2,
    StatedQuadPlus 3 (ZMod 2) (mat6 tau2L *ᵥ v) = StatedQuadPlus 3 (ZMod 2) v := by decide +kernel

theorem comm_sgL_ccL : mat8 sgL * mat8 ccL * mat8 sgL * mat8 cciL = mat8 ccL := by decide +kernel

theorem comm_tau1L_s1L : mat6 tau1L * mat6 s1L * mat6 tau1L * mat6 s1iL = mat6 s1L := by
  decide +kernel

theorem comm_tau2L_s2L : mat6 tau2L * mat6 s2L * mat6 tau2L * mat6 s2iL = mat6 s2L := by
  decide +kernel

theorem conj_tpL : mat8 ccL * mat8 tpL * mat8 cciL = emb (mat6 s1L) := by decide +kernel

theorem conj_tpiL : mat8 ccL * mat8 tpiL * mat8 cciL = emb (mat6 s1iL) := by decide +kernel

theorem conj_s1L : mat8 ccL * emb (mat6 s1L) * mat8 cciL = emb (mat6 s2L) := by decide +kernel

theorem conj_s2L : mat8 ccL * emb (mat6 s2L) * mat8 cciL = mat8 tpL := by decide +kernel

theorem tForm_rho :
    (fromBlocks (1 : Matrix ι6 ι6 (ZMod 2)) 0 0 rho).submatrix eO eO = mat8 tpL := by
  decide +kernel

theorem tForm_rho_sq :
    (fromBlocks (1 : Matrix ι6 ι6 (ZMod 2)) 0 0 (rho ^ 2)).submatrix eO eO = mat8 tpiL := by
  decide +kernel

theorem s1L_mul_s2L : mat6 s1L * mat6 s2L = mat6 s2L * mat6 s1L := by decide +kernel

theorem s1L_pow_three : mat6 s1L ^ 3 = 1 := by decide +kernel

theorem s2L_pow_three : mat6 s2L ^ 3 = 1 := by decide +kernel

theorem s1L_ne_one : mat6 s1L ≠ 1 := by decide +kernel

theorem s2L_ne : mat6 s2L ≠ 1 ∧ mat6 s2L ≠ mat6 s1L ∧ mat6 s2L ≠ mat6 s1L ^ 2 := by
  decide +kernel

@[expose] def ccG : GL ι (ZMod 2) := Units.mk (mat8 ccL) (mat8 cciL) ccL_mul_cciL cciL_mul_ccL

@[expose] def sgG : GL ι (ZMod 2) := Units.mk (mat8 sgL) (mat8 sgL) sgL_mul_sgL sgL_mul_sgL

@[expose] def s1G : GL ι6 (ZMod 2) := Units.mk (mat6 s1L) (mat6 s1iL) s1L_mul_s1iL s1iL_mul_s1L

@[expose] def s2G : GL ι6 (ZMod 2) := Units.mk (mat6 s2L) (mat6 s2iL) s2L_mul_s2iL s2iL_mul_s2L

@[expose] def tau1G : GL ι6 (ZMod 2) :=
  Units.mk (mat6 tau1L) (mat6 tau1L) tau1L_mul_tau1L tau1L_mul_tau1L

@[expose] def tau2G : GL ι6 (ZMod 2) :=
  Units.mk (mat6 tau2L) (mat6 tau2L) tau2L_mul_tau2L tau2L_mul_tau2L

theorem comm_sgG_ccG : ⁅sgG, ccG⁆ = ccG := by
  apply Units.ext
  simp only [commutatorElement_def, sgG, ccG, Units.val_mul, Units.inv_mk, Units.val_mk]
  exact comm_sgL_ccL

theorem comm_tau1G_s1G : ⁅tau1G, s1G⁆ = s1G := by
  apply Units.ext
  simp only [commutatorElement_def, tau1G, s1G, Units.val_mul, Units.inv_mk, Units.val_mk]
  exact comm_tau1L_s1L

theorem comm_tau2G_s2G : ⁅tau2G, s2G⁆ = s2G := by
  apply Units.ext
  simp only [commutatorElement_def, tau2G, s2G, Units.val_mul, Units.inv_mk, Units.val_mk]
  exact comm_tau2L_s2L

theorem ccG_mem : ccG ∈ StatedOmega Q8 := by
  have h : ⁅sgG, ccG⁆ ∈ StatedOmega Q8 := by
    unfold StatedOmega
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure fun v => sgL_iso v)
      (Subgroup.subset_closure fun v => ccL_iso v)
  rwa [comm_sgG_ccG] at h

theorem s1G_mem : s1G ∈ StatedOmega (StatedQuadPlus 3 (ZMod 2)) := by
  have h : ⁅tau1G, s1G⁆ ∈ StatedOmega (StatedQuadPlus 3 (ZMod 2)) := by
    show ⁅tau1G, s1G⁆ ∈
      ⁅CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6,
        CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6⁆
    exact Subgroup.commutator_mem_commutator
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.mem_O6.mpr
        fun v => tau1L_iso v)
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.mem_O6.mpr
        fun v => s1L_iso v)
  rwa [comm_tau1G_s1G] at h

theorem s2G_mem : s2G ∈ StatedOmega (StatedQuadPlus 3 (ZMod 2)) := by
  have h : ⁅tau2G, s2G⁆ ∈ StatedOmega (StatedQuadPlus 3 (ZMod 2)) := by
    show ⁅tau2G, s2G⁆ ∈
      ⁅CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6,
        CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6⁆
    exact Subgroup.commutator_mem_commutator
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.mem_O6.mpr
        fun v => tau2L_iso v)
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.mem_O6.mpr
        fun v => s2L_iso v)
  rwa [comm_tau2G_s2G] at h

@[expose] def n0 : Om8 := ⟨ccG, ccG_mem⟩

@[expose] def s1 : Om8 := psiD ⟨s1G, s1G_mem⟩

@[expose] def s2 : Om8 := psiD ⟨s2G, s2G_mem⟩

@[expose] def T0 : Subgroup Om8 := Subgroup.zpowers s1 ⊔ Subgroup.zpowers s2

theorem matO_n0 : matO n0 = mat8 ccL := rfl

theorem matO_n0_inv : matO n0⁻¹ = mat8 cciL := rfl

theorem matO_s1 : matO s1 = emb (mat6 s1L) := rfl

theorem matO_s1_inv : matO s1⁻¹ = emb (mat6 s1iL) := rfl

theorem matO_s2 : matO s2 = emb (mat6 s2L) := rfl

theorem T0_le_D : T0 ≤ psiD.range :=
  sup_le (Subgroup.zpowers_le.mpr ⟨_, rfl⟩) (Subgroup.zpowers_le.mpr ⟨_, rfl⟩)

private theorem emb_pow_mat (M : Matrix ι6 ι6 (ZMod 2)) (k : ℕ) : emb (M ^ k) = emb M ^ k :=
  map_pow embHom M k

private theorem s1_mul_s2_comm : s1 * s2 = s2 * s1 := by
  apply matO_injective
  rw [map_mul, map_mul, matO_s1, matO_s2, ← emb_mul, ← emb_mul, s1L_mul_s2L]

private theorem s1_cube : s1 ^ 3 = 1 := by
  apply matO_injective
  rw [map_pow, map_one, matO_s1, ← emb_pow_mat (mat6 s1L) 3, s1L_pow_three, emb_one]

private theorem s2_cube : s2 ^ 3 = 1 := by
  apply matO_injective
  rw [map_pow, map_one, matO_s2, ← emb_pow_mat (mat6 s2L) 3, s2L_pow_three, emb_one]

private theorem s1_ne_one_Om8 : s1 ≠ 1 := by
  intro h
  apply s1L_ne_one
  apply emb_injective
  have hh : matO s1 = matO (1 : Om8) := congrArg matO h
  rw [matO_s1, map_one, ← emb_one] at hh
  exact hh

private theorem s2_ne_one_Om8 : s2 ≠ 1 := by
  intro h
  apply s2L_ne.1
  apply emb_injective
  have hh : matO s2 = matO (1 : Om8) := congrArg matO h
  rw [matO_s2, map_one, ← emb_one] at hh
  exact hh

private theorem s2_ne_s1_Om8 : s2 ≠ s1 := by
  intro h
  apply s2L_ne.2.1
  apply emb_injective
  have hh : matO s2 = matO s1 := congrArg matO h
  rw [matO_s2, matO_s1] at hh
  exact hh

private theorem s2_ne_s1_sq_Om8 : s2 ≠ s1 ^ 2 := by
  intro h
  apply s2L_ne.2.2
  apply emb_injective
  have hh : matO s2 = matO (s1 ^ 2) := congrArg matO h
  rw [matO_s2, map_pow, matO_s1, ← emb_pow_mat (mat6 s1L) 2] at hh
  exact hh

private theorem s2_notMem_zpowers_s1 : s2 ∉ Subgroup.zpowers s1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro hmem
  have horder : orderOf s1 = 3 := orderOf_eq_prime s1_cube s1_ne_one_Om8
  rw [mem_zpowers_iff_mem_range_orderOf, horder, Finset.mem_image] at hmem
  obtain ⟨i, hi, hix⟩ := hmem
  rw [Finset.mem_range] at hi
  interval_cases i
  · exact s2_ne_one_Om8 (by simpa using hix.symm)
  · exact s2_ne_s1_Om8 (by simpa using hix.symm)
  · exact s2_ne_s1_sq_Om8 (by simpa using hix.symm)

private theorem matO_n0_conj (x : Om8) :
    matO (n0 * x * n0⁻¹) = mat8 ccL * matO x * mat8 cciL := by
  rw [map_mul, map_mul, matO_n0, matO_n0_inv]

private theorem matO_inv_of_tpi {t : Om8} (h : matO t = mat8 tpiL) : matO t⁻¹ = mat8 tpL := by
  have hmul : mat8 tpiL * matO t⁻¹ = 1 := by
    rw [← h, ← map_mul, mul_inv_cancel, map_one]
  have h2 : mat8 tpL * (mat8 tpiL * matO t⁻¹) = mat8 tpL * 1 := by rw [hmul]
  rw [← mul_assoc, tpL_mul_tpiL, one_mul, mul_one] at h2
  exact h2

private theorem n0_conj_t_eq_s1 {t : Om8} (h : matO t = mat8 tpL) : n0 * t * n0⁻¹ = s1 := by
  apply matO_injective
  rw [matO_n0_conj, h, conj_tpL, ← matO_s1]

private theorem n0_conj_t_eq_s1i {t : Om8} (h : matO t = mat8 tpiL) : n0 * t * n0⁻¹ = s1⁻¹ := by
  apply matO_injective
  rw [matO_n0_conj, h, conj_tpiL, ← matO_s1_inv]

private theorem n0_conj_s1_eq_s2 : n0 * s1 * n0⁻¹ = s2 := by
  apply matO_injective
  rw [matO_n0_conj, matO_s1, conj_s1L, ← matO_s2]

private theorem n0_conj_s2_eq_t {t : Om8} (h : matO t = mat8 tpL) : n0 * s2 * n0⁻¹ = t := by
  apply matO_injective
  rw [matO_n0_conj, matO_s2, conj_s2L, ← h]

private theorem n0_conj_s2_eq_ti {t : Om8} (h : matO t = mat8 tpiL) : n0 * s2 * n0⁻¹ = t⁻¹ := by
  apply matO_injective
  rw [matO_n0_conj, matO_s2, conj_s2L, matO_inv_of_tpi h]

theorem card_T0 : Nat.card ↥T0 = 9 := by
  show Nat.card ↥(Subgroup.zpowers s1 ⊔ Subgroup.zpowers s2) = 9
  exact CFSG.HardMathSupport.Lang.E27Lie.card_zpowers_sup_zpowers_of_order_three
    s1_mul_s2_comm s1_cube s1_ne_one_Om8 s2_cube s2_notMem_zpowers_s1

theorem n0_fusion {t : Om8}
    (ht : bl eO (matO t) = fromBlocks 1 0 0 rho ∨ bl eO (matO t) = fromBlocks 1 0 0 (rho ^ 2)) :
    n0 ∈ Subgroup.normalizer ((Subgroup.zpowers t ⊔ T0 : Subgroup Om8) : Set Om8) ∧
      n0 * t * n0⁻¹ ∈ T0 ∧ n0 * t * n0⁻¹ ≠ 1 := by
  have hmt : matO t = mat8 tpL ∨ matO t = mat8 tpiL := by
    rcases ht with h | h
    · left
      rw [← submatrix_bl eO (matO t), h, tForm_rho]
    · right
      rw [← submatrix_bl eO (matO t), h, tForm_rho_sq]
  have hmap : (Subgroup.zpowers t ⊔ T0 : Subgroup Om8).map (MulAut.conj n0) =
      (Subgroup.zpowers t ⊔ T0 : Subgroup Om8) := by
    unfold T0
    rw [Subgroup.map_sup, Subgroup.map_sup]
    simp only [MonoidHom.map_zpowers]
    have hct : (↑(MulAut.conj n0) : Om8 →* Om8) t = n0 * t * n0⁻¹ :=
      MulAut.conj_apply n0 t
    have hc1 : (↑(MulAut.conj n0) : Om8 →* Om8) s1 = n0 * s1 * n0⁻¹ :=
      MulAut.conj_apply n0 s1
    have hc2 : (↑(MulAut.conj n0) : Om8 →* Om8) s2 = n0 * s2 * n0⁻¹ :=
      MulAut.conj_apply n0 s2
    rw [hct, hc1, hc2]
    rcases hmt with h | h
    · rw [n0_conj_t_eq_s1 h, n0_conj_s1_eq_s2, n0_conj_s2_eq_t h]
      ac_rfl
    · rw [n0_conj_t_eq_s1i h, n0_conj_s1_eq_s2, n0_conj_s2_eq_ti h]
      simp only [Subgroup.zpowers_inv]
      ac_rfl
  refine ⟨(Subgroup.mem_normalizer_iff_map_conj_eq
    (H := (Subgroup.zpowers t ⊔ T0 : Subgroup Om8))).mpr hmap, ?_, ?_⟩
  · rcases hmt with h | h
    · rw [n0_conj_t_eq_s1 h]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers s1)
    · rw [n0_conj_t_eq_s1i h]
      exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers s1))
  · rcases hmt with h | h
    · rw [n0_conj_t_eq_s1 h]
      exact s1_ne_one_Om8
    · rw [n0_conj_t_eq_s1i h]
      intro hh
      exact s1_ne_one_Om8 (inv_eq_one.mp hh)

end CFSG.StandardType.HalfFusOm8

end
