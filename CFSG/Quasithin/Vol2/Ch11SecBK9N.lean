module

public import CFSG.Quasithin.Vol2.Ch11SecBK9L
public import CFSG.Quasithin.Vol2.Ch11SecBK9M
public import CFSG.Quasithin.Vol2.Ch11SecBK9K

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix QuadraticMap
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.LieType.Universal.Spin (quadPlus)

variable {K : Type} [Field K] [CharP K 2]

theorem qOf_add_apply (e b x : Fin 2 ⊕ Fin 2 → K) :
    qOf (e + b) x = qOf e x + spB K b x ^ 2 := by
  rw [qOf_apply, qOf_apply, spB_add_left, CharTwo.add_sq]
  ring

variable [Finite K] (hK : Nat.card K = 4)

@[expose] noncomputable def kapQ (e : Fin 2 ⊕ Fin 2 → K) (γ : ↥(StatedSp 2 K)) :
    Fin 2 ⊕ Fin 2 → K :=
  mat 2 K γ *ᵥ e + bm hK γ - e

theorem kapQ_mul (e : Fin 2 ⊕ Fin 2 → K) (γ δ : ↥(StatedSp 2 K)) :
    kapQ hK e (γ * δ) = kapQ hK e γ + mat 2 K γ *ᵥ kapQ hK e δ := by
  simp only [kapQ]
  rw [bm_mul, map_mul, ← mulVec_mulVec, mulVec_sub, mulVec_add]
  abel

theorem kapQ_one (e : Fin 2 ⊕ Fin 2 → K) : kapQ hK e 1 = 0 := by
  have h := kapQ_mul hK e 1 1
  rw [mul_one, map_one, one_mulVec] at h
  exact add_eq_left.mp h.symm

theorem kapQ_inv (e : Fin 2 ⊕ Fin 2 → K) (γ : ↥(StatedSp 2 K)) :
    kapQ hK e γ⁻¹ + mat 2 K γ⁻¹ *ᵥ kapQ hK e γ = 0 := by
  rw [← kapQ_mul, inv_mul_cancel, kapQ_one]

theorem add_kapQ (e : Fin 2 ⊕ Fin 2 → K) (γ : ↥(StatedSp 2 K)) :
    e + kapQ hK e γ = mat 2 K γ *ᵥ e + bm hK γ := by
  rw [kapQ]
  abel

theorem qOf_inv_apply (e : Fin 2 ⊕ Fin 2 → K) (γ : ↥(StatedSp 2 K)) (x : Fin 2 ⊕ Fin 2 → K) :
    qOf e (mat 2 K γ⁻¹ *ᵥ x) = qOf e x + spB K (kapQ hK e γ) x ^ 2 := by
  have h := congrArg (fun Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K) => Q x) (qOf_comp hK γ e)
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, linEquiv_apply] at h
  rw [h, ← add_kapQ, qOf_add_apply]

theorem mem_stabQ_iff_kapQ (e : Fin 2 ⊕ Fin 2 → K) (γ : ↥(StatedSp 2 K)) :
    γ ∈ stabQ (qOf e) ↔ kapQ hK e γ = 0 := by
  constructor
  · intro hγ
    apply KGNat.toBilin'_spJ_nondegenerate.1
    intro x
    have h := qOf_inv_apply hK e γ x
    rw [← mem_stabQ.mp hγ (mat 2 K γ⁻¹ *ᵥ x), KGNat.mat_mulVec_inv] at h
    have h' : spB K (kapQ hK e γ) x ^ 2 = 0 := by linear_combination -h
    exact pow_eq_zero_iff two_ne_zero |>.mp h'
  · intro hκ
    refine mem_stabQ.mpr fun x => ?_
    have h := qOf_inv_apply hK e γ (mat 2 K γ *ᵥ x)
    rw [KGNat.mat_inv_mulVec, hκ, map_zero, LinearMap.zero_apply, zero_pow two_ne_zero,
      add_zero] at h
    exact h.symm

theorem tr_qOf_kapQ (e : Fin 2 ⊕ Fin 2 → K) (γ : ↥(StatedSp 2 K)) :
    tr (qOf e (kapQ hK e γ)) = 0 := by
  have h := (exists_orbit_iff hK e (mat 2 K γ *ᵥ e + bm hK γ)).mp ⟨γ, rfl⟩
  rw [tr_qOf hK, add_kapQ, h, CharTwo.add_self_eq_zero]

theorem exists_kapQ_eq (e : Fin 2 ⊕ Fin 2 → K) {b : Fin 2 ⊕ Fin 2 → K}
    (hb : tr (qOf e b) = 0) : ∃ γ, kapQ hK e γ = b := by
  obtain ⟨γ, hγ⟩ := exists_orbit_of_tr hK (e := e) (e' := e + b) (by
    have h := tr_qOf hK e b
    rw [hb] at h
    rw [← sub_eq_zero, CharTwo.sub_eq_add]
    exact h.symm)
  exact ⟨γ, by rw [kapQ, hγ]; abel⟩

include hK in
theorem exists_qOf_eq_one (e : Fin 2 ⊕ Fin 2 → K) {b : Fin 2 ⊕ Fin 2 → K} (hb : b ≠ 0) :
    ∃ c, c ≠ 0 ∧ c ≠ b ∧ qOf e c = 1 := by
  obtain ⟨c, hbc, hc⟩ := exists_bil_quad hK (isSpForm_qOf e) hb 1 1
  refine ⟨c, fun h => ?_, fun h => ?_, hc⟩
  · rw [h, map_zero] at hbc
    exact zero_ne_one hbc
  · rw [h, K7.bil_self] at hbc
    exact zero_ne_one hbc

include hK in
theorem exists_not_mem_stabQ (e : Fin 2 ⊕ Fin 2 → K) : ∃ γ, γ ∉ stabQ (qOf e) := by
  obtain ⟨c, hc, -, hcq⟩ := exists_qOf_eq_one hK e (CovData.e0_ne (K := K))
  obtain ⟨γ, hγ⟩ := exists_kapQ_eq hK e (b := c) (by rw [hcq, tr_one])
  exact ⟨γ, fun h => hc (by rw [← hγ]; exact (mem_stabQ_iff_kapQ hK e γ).mp h)⟩

include hK in
theorem not_normal_stabQ (e : Fin 2 ⊕ Fin 2 → K) : ¬ (stabQ (qOf e)).Normal := by
  intro hN
  obtain ⟨c, hc, -, hcq⟩ := exists_qOf_eq_one hK e (CovData.e0_ne (K := K))
  obtain ⟨c', hc', hcc', hc'q⟩ := exists_qOf_eq_one hK e hc
  obtain ⟨γ, hγ⟩ := exists_kapQ_eq hK e (b := c) (by rw [hcq, tr_one])
  obtain ⟨δ, hδ, hδc⟩ := exists_stabQ_apply_eq (isSpForm_qOf e) hc hc' (by rw [hcq, hc'q])
  have hconj := (mem_stabQ_iff_kapQ hK e _).mp (hN.conj_mem δ hδ γ⁻¹)
  rw [inv_inv, kapQ_mul, kapQ_mul, (mem_stabQ_iff_kapQ hK e δ).mp hδ, mulVec_zero, add_zero,
    map_mul, ← mulVec_mulVec, hγ, hδc] at hconj
  have hinv := kapQ_inv hK e γ
  rw [hγ] at hinv
  apply hcc'
  have h3 : mat 2 K γ⁻¹ *ᵥ c' = mat 2 K γ⁻¹ *ᵥ c := add_left_cancel (hconj.trans hinv.symm)
  have h4 := congrArg (fun v => mat 2 K γ *ᵥ v) h3
  simpa only [KGNat.mat_mulVec_inv] using h4

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
