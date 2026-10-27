module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.Quasithin.Vol2.F134LieSp4Borel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torus coe_torusHom statedSp_ext
  mem_statedSp_iff torusHom_injective)
open Subgroup Matrix

variable {K : Type} [Field K]

theorem uc22pwI2_sp4_diagHom_torusHom (t : Fin 2 → Kˣ) :
    diagHom 2 K ⟨torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩ = t := by
  funext i
  apply Units.ext
  simp [diagHom, diagEntry, coe_torusHom]

theorem uc22pwI2_sp4_borel :
    borelSubgroup 2 K = unipotent 2 K ⊔ torus 2 K ∧ Disjoint (unipotent 2 K) (torus 2 K) := by
  constructor
  · refine le_antisymm (fun b hb => ?_) (sup_le unipotent_le_borelSubgroup torus_le_borelSubgroup)
    set d := diagHom 2 K ⟨b, hb⟩ with hd
    have ht : torusHom d ∈ borelSubgroup 2 K := torus_le_borelSubgroup ⟨d, rfl⟩
    have hker : (⟨b, hb⟩ : borelSubgroup 2 K) * (⟨torusHom d, ht⟩ : borelSubgroup 2 K)⁻¹ ∈
        (diagHom 2 K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, uc22pwI2_sp4_diagHom_torusHom, ← hd, mul_inv_cancel]
    rw [ker_diagHom] at hker
    have hu : b * (torusHom d)⁻¹ ∈ unipotent 2 K := hker
    have : b = (b * (torusHom d)⁻¹) * torusHom d := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ⟨d, rfl⟩)
  · rw [Subgroup.disjoint_def]
    rintro x hxU ⟨t, rfl⟩
    have hker : (⟨torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩ : borelSubgroup 2 K) ∈
        (diagHom 2 K).ker := by
      rw [ker_diagHom]
      exact hxU
    rw [MonoidHom.mem_ker, uc22pwI2_sp4_diagHom_torusHom] at hker
    rw [hker, map_one]

theorem uc22pwI2_sp4_decomp {b : StatedSp 2 K} (hb : b ∈ borelSubgroup 2 K) :
    b * (torusHom (diagHom 2 K ⟨b, hb⟩))⁻¹ ∈ unipotent 2 K := by
  have ht : torusHom (diagHom 2 K ⟨b, hb⟩) ∈ borelSubgroup 2 K :=
    torus_le_borelSubgroup ⟨_, rfl⟩
  have hker : (⟨b, hb⟩ : borelSubgroup 2 K) * (⟨torusHom (diagHom 2 K ⟨b, hb⟩), ht⟩ :
      borelSubgroup 2 K)⁻¹ ∈ (diagHom 2 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, uc22pwI2_sp4_diagHom_torusHom, mul_inv_cancel]
  rw [ker_diagHom] at hker
  exact hker

theorem uc22pwI2_sp4_conj_torus_mem {x : StatedSp 2 K} (hx : x ∈ borelSubgroup 2 K)
    (t : Fin 2 → Kˣ) : x * torusHom t * x⁻¹ * (torusHom t)⁻¹ ∈ unipotent 2 K := by
  have h1 : (⟨x, hx⟩ : borelSubgroup 2 K) * ⟨torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩ *
      (⟨x, hx⟩ : borelSubgroup 2 K)⁻¹ * (⟨torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩ :
        borelSubgroup 2 K)⁻¹ ∈ (diagHom 2 K).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_inv_cancel_comm, mul_inv_cancel]
  rw [ker_diagHom] at h1
  exact h1

variable (K) in
@[expose] def uc22pwI2Rho : (Fin 2 → Kˣ) →* (Fin 2 → Kˣ) where
  toFun t := ![t 0 * t 1, t 0 * (t 1)⁻¹]
  map_one' := by
    ext i
    fin_cases i <;> simp
  map_mul' s t := by
    ext i
    fin_cases i <;> simp [mul_inv, mul_mul_mul_comm] <;> ring

theorem uc22pwI2_sp4_tau_torus [CharP K 2] (t : Fin 2 → Kˣ) :
    CFSG.QuasithinUnique.Lin2.Five.tauSp (torusHom t) = torusHom (uc22pwI2Rho K t) := by
  apply statedSp_ext
  rw [CFSG.QuasithinUnique.Lin2.Five.coe_tauSp, coe_torusHom, coe_torusHom]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [CFSG.QuasithinUnique.Lin2.Five.tauMat_apply, CFSG.QuasithinUnique.Lin2.Five.tauPair,
      diagonal_apply, uc22pwI2Rho] <;> ring

theorem uc22pwI2_sp4_field_torus (σ : K ≃+* K) (t : Fin 2 → Kˣ) :
    fieldSp 2 K σ (torusHom t) = torusHom (fun i => Units.map (σ : K →* K) (t i)) := by
  apply statedSp_ext
  rw [coe_fieldSp, coe_torusHom, coe_torusHom]
  ext r c
  fin_cases r <;> fin_cases c <;> simp [Matrix.diagonal_apply]

variable (K) in
@[expose] def uc22pwI2WeylGL : GL (Fin 2 ⊕ Fin 2) K where
  val := fromBlocks 0 1 (-1) 0
  inv := fromBlocks 0 (-1) 1 0
  val_inv := by simp [fromBlocks_multiply]
  inv_val := by simp [fromBlocks_multiply]

theorem uc22pwI2WeylGL_mem : uc22pwI2WeylGL K ∈ StatedSp 2 K := by
  rw [mem_statedSp_iff]
  show (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * fromBlocks 0 1 (-1) 0 *
    fromBlocks 0 1 (-1) 0 = fromBlocks 0 1 (-1) 0
  simp [fromBlocks_transpose, fromBlocks_multiply]

variable (K) in
@[expose] def uc22pwI2Weyl : StatedSp 2 K := ⟨uc22pwI2WeylGL K, uc22pwI2WeylGL_mem⟩

theorem coe_uc22pwI2Weyl : (((uc22pwI2Weyl K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 0 1 (-1) 0 := rfl

theorem uc22pwI2_weyl_sq [CharP K 2] : uc22pwI2Weyl K ^ 2 = 1 := by
  apply statedSp_ext
  rw [pow_two, Subgroup.coe_mul, Units.val_mul, coe_uc22pwI2Weyl]
  simp [fromBlocks_multiply, CharTwo.neg_eq]

theorem uc22pwI2_weyl_inv_torus (t : Fin 2 → Kˣ) :
    uc22pwI2Weyl K * torusHom t * (uc22pwI2Weyl K)⁻¹ = (torusHom t)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  apply statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_uc22pwI2Weyl,
    ← map_inv, coe_torusHom, coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.diagonal_apply]

theorem uc22pwI2_weyl_not_mem_stabilizer_one :
    uc22pwI2Weyl K ∉ stabilizer 2 K (flag 2 K 1) := by
  intro h
  have := (CFSG.Quasithin.F134.Sp4.mem_stabilizer_one_iff.mp h).1
  simp [coe_uc22pwI2Weyl] at this

theorem uc22pwI2_weyl_not_mem_stabilizer_two :
    uc22pwI2Weyl K ∉ stabilizer 2 K (flag 2 K 2) := by
  intro h
  have := CFSG.Quasithin.F134.Sp4.mem_stabilizer_two_iff.mp h 0 0
  simp [coe_uc22pwI2Weyl] at this

theorem uc22pwI2_weyl_gen :
    borelSubgroup 2 K ⊔ Subgroup.zpowers (uc22pwI2Weyl K) = ⊤ := by
  set A := borelSubgroup 2 K ⊔ Subgroup.zpowers (uc22pwI2Weyl K) with hA
  have hBA : borelSubgroup 2 K ≤ A := le_sup_left
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  have hcuts : borelCuts K A = ∅ := by
    by_contra hne
    obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hwA : uc22pwI2Weyl K ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [hAeq] at hwA
    have hw' := (mem_flagStabilizer.mp hwA) i hi
    obtain ⟨hi1, hi2⟩ := borelCuts_le A i hi
    interval_cases i
    · exact uc22pwI2_weyl_not_mem_stabilizer_one hw'
    · exact uc22pwI2_weyl_not_mem_stabilizer_two hw'
  rw [hcuts, flagStabilizer_empty] at hAeq
  exact hAeq

theorem uc22pwI2_sp4_weyl [CharP K 2] :
    ∃ w : StatedSp 2 K, w ^ 2 = 1 ∧ (∀ t : Fin 2 → Kˣ, w * torusHom t * w⁻¹ = (torusHom t)⁻¹) ∧
      borelSubgroup 2 K ⊔ Subgroup.zpowers w = ⊤ :=
  ⟨uc22pwI2Weyl K, uc22pwI2_weyl_sq, uc22pwI2_weyl_inv_torus, uc22pwI2_weyl_gen⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
