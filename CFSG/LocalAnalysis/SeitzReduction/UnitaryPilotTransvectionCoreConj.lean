module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCore
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAutUBlock
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAutUCentralizer

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LinearGroups
open CFSG.Quasithin (perfectCore map_perfectCore)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem eq_of_mulVecLin_eq {M N : Matrix (Fin n) (Fin n) K} (hMN : M.mulVecLin = N.mulVecLin) :
    M = N :=
  Matrix.toLin'.injective (by rw [Matrix.toLin'_apply', Matrix.toLin'_apply', hMN])

theorem stdHermForm_tvVec (i j : Fin n) (x : Fin n → K) :
    stdHermForm h n (tvVec i j) x = tvVec i j ⬝ᵥ x := by
  rw [stdHermForm_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [bar_tvVec]

theorem mulVecLin_tvTransSU {i j : Fin n} (hij : i ≠ j) :
    (((tvTransSU h hij : unitarySU 2 f K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).mulVecLin = hermTransvection (stdHermForm h n) (tvVec i j) 1 := by
  refine LinearMap.ext fun x => ?_
  rw [Matrix.mulVecLin_apply, coe_tvTransSU, add_mulVec, one_mulVec, tvNil, vecMulVec_mulVec,
    hermTransvection_apply, one_mul, stdHermForm_tvVec, op_smul_eq_smul]

theorem exists_eq_hermTransvection_of_mem_isotropicTransvectionGroup {a : Fin n → K}
    (ha : stdHermForm h n a a = 0) {y : unitarySU 2 f K n}
    (hy : y ∈ isotropicTransvectionGroup h n (K ∙ a)) :
    ∃ c ∈ h.traceZero, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin =
      hermTransvection (stdHermForm h n) a c := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, c, hc, hxb⟩ := hx
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.1 hb
    refine ⟨c * h.norm l, ?_, ?_⟩
    · rw [h.mem_traceZero, UnitaryFieldData.trace] at hc ⊢
      have hN : h.bar (h.norm l) = h.norm l := by
        rw [UnitaryFieldData.norm, map_mul, h.bar_bar, mul_comm]
      rw [map_mul, hN]
      linear_combination h.norm l * hc
    · rw [hxb]
      refine LinearMap.ext fun x => ?_
      rw [hermTransvection_apply, hermTransvection_apply, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, smul_smul, UnitaryFieldData.norm]
      congr 2
      ring
  | one =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [hermTransvection_zero, Subgroup.coe_one, Units.val_one, Matrix.mulVecLin_one]
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨d, hd, hyd⟩ := hy
    refine ⟨c + d, add_mem hc hd, ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_mul, hxc, hyd,
      hermTransvection_comp _ ha]
  | inv x _ hx =>
    obtain ⟨c, hc, hxc⟩ := hx
    refine ⟨-c, neg_mem hc, ?_⟩
    have e1 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin ∘ₗ
        hermTransvection (stdHermForm h n) a (-c) = LinearMap.id := by
      rw [hxc, hermTransvection_comp _ ha, add_neg_cancel, hermTransvection_zero]
    have e2 : (((x⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin ∘ₗ
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin = LinearMap.id := by
      rw [← Matrix.mulVecLin_mul, coe_inv_mul_coe, Matrix.mulVecLin_one]
    calc (((x⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin
        = (((x⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin ∘ₗ
            (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin ∘ₗ
              hermTransvection (stdHermForm h n) a (-c)) := by rw [e1, LinearMap.comp_id]
      _ = hermTransvection (stdHermForm h n) a (-c) := by
          rw [← LinearMap.comp_assoc, e2, LinearMap.id_comp]

theorem exists_unitarySU_mulVec_eq (hn : 3 ≤ n) {a a' : Fin n → K} (ha0 : a ≠ 0)
    (ha : stdHermForm h n a a = 0) (ha0' : a' ≠ 0) (ha' : stdHermForm h n a' a' = 0) :
    ∃ g : unitarySU 2 f K n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a = a' := by
  have hherm : ∀ x y : Fin n → K,
      CFSG.ClassicalGroups.Unitary.herm h.barEquiv x y = stdHermForm h n x y := fun _ _ => rfl
  obtain ⟨t, -, ht⟩ := CFSG.ClassicalGroups.Unitary.exists_mem_T_smul_eq_of_iso
    h.isUnitaryInvolution_barEquiv hn ha0 (by rw [hherm]; exact ha) ha0'
    (by rw [hherm]; exact ha')
  have ht' : (t : GL (Fin n) K) ∈ unitarySU 2 f K n :=
    (mem_unitarySU_iff h).2 ⟨t.2.1, t.2.2⟩
  exact ⟨⟨t, ht'⟩, ht⟩

theorem exists_conj_eq_stdTransvection (hn : 3 ≤ n) {z : unitaryPSU h n}
    (hz : IsUnitaryTransvection h z) {i j : Fin n} (hij : i ≠ j) :
    ∃ g : unitaryPSU h n, g * z * g⁻¹ = stdTransvection h hij := by
  have := h.charP
  obtain ⟨hz1, ℓ, hℓ, hzℓ⟩ := hz
  obtain ⟨a, ha0, ha, rfl⟩ := UnitaryHigher.exists_eq_span_of_mem_isotropicLines hℓ
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hzℓ
  obtain ⟨c, hc, hyc⟩ := exists_eq_hermTransvection_of_mem_isotropicTransvectionGroup h ha hy
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hz1
    have hy1 : y = 1 := by
      refine eq_of_coe_eq (eq_of_mulVecLin_eq ?_)
      rw [hyc, hermTransvection_zero, Subgroup.coe_one, Units.val_one, Matrix.mulVecLin_one]
    rw [hy1, map_one]
  have hcbar : h.bar c = c := by
    have h1 := (h.mem_traceZero).1 hc
    rw [UnitaryFieldData.trace] at h1
    exact (CharTwo.add_eq_zero.1 h1).symm
  obtain ⟨l, hl⟩ := h.normHom_surjective ⟨c, h.mem_fixedField.2 hcbar⟩
  have hl' : h.norm l = c := congrArg Subtype.val hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hl'
    exact hc0 hl'.symm
  set b := l • a with hb
  have hb0 : b ≠ 0 := smul_ne_zero hl0 ha0
  have hbb : stdHermForm h n b b = 0 := by
    simp only [hb, map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
  have hyb : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin =
      hermTransvection (stdHermForm h n) b 1 := by
    rw [hyc]
    refine LinearMap.ext fun x => ?_
    rw [hermTransvection_apply, hermTransvection_apply, hb, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, smul_smul, ← hl', UnitaryFieldData.norm]
    congr 2
    ring
  have hv0 : tvVec (K := K) i j ≠ 0 := by
    intro h0
    have h1 := congrFun h0 i
    rw [tvVec_left hij, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have hvv : stdHermForm h n (tvVec i j) (tvVec i j) = 0 := by
    rw [stdHermForm_tvVec, tvVec_dotProduct_self hij]
  obtain ⟨g, hg⟩ := exists_unitarySU_mulVec_eq h hn hb0 hbb hv0 hvv
  have hconj := mulVecLin_conj_hermTransvection_unitarySU h g hyb
  have hgb : g • b = tvVec i j := hg
  rw [hgb] at hconj
  have hgy : g * y * g⁻¹ = tvTransSU h hij :=
    eq_of_coe_eq (eq_of_mulVecLin_eq (by rw [hconj, mulVecLin_tvTransSU]))
  refine ⟨unitaryProj h n g, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hgy]
  rfl

theorem mem_perfectCore_centralizer_of_isUnitaryTransvection_of_five_le (hn : 5 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (5, 2)) {z : unitaryPSU h n} (hz : IsUnitaryTransvection h z) :
    z ∈ perfectCore (centralizer ({z} : Set (unitaryPSU h n))) := by
  have := h.finite
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨g, hg⟩ := exists_conj_eq_stdTransvection h (by omega) hz hij
  have hstd := mem_perfectCore_centralizer_stdTransvection_of_five_le h hn hnq hij
  rw [← hg] at hstd
  set φ : unitaryPSU h n →* unitaryPSU h n := (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hφz : φ (g * z * g⁻¹) = z := by
    simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have h1 : φ (g * z * g⁻¹) ∈
      (perfectCore (centralizer ({g * z * g⁻¹} : Set (unitaryPSU h n)))).map φ :=
    ⟨_, hstd, rfl⟩
  rw [map_perfectCore, hφz] at h1
  refine CFSG.Quasithin.perfectCore_mono ?_ h1
  calc (centralizer ({g * z * g⁻¹} : Set (unitaryPSU h n))).map φ
      ≤ centralizer (φ '' {g * z * g⁻¹}) := map_centralizer_le_centralizer_image _ φ
    _ = centralizer {z} := by rw [Set.image_singleton, hφz]

theorem mem_perfectCore_centralizer_of_isUnitaryTransvection (hn : 6 ≤ n) {z : unitaryPSU h n}
    (hz : IsUnitaryTransvection h z) :
    z ∈ perfectCore (centralizer ({z} : Set (unitaryPSU h n))) :=
  mem_perfectCore_centralizer_of_isUnitaryTransvection_of_five_le h (by omega)
    (fun h' => by have := congrArg Prod.fst h'; simp only at this; omega) hz

end CFSG.SeitzReduction.UnitaryPilot
