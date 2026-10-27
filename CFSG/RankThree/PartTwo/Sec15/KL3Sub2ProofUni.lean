module

public import CFSG.RankThree.PartTwo.Sec15.KL3Sub2ProofLin
public import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9U
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KL3Sub2Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec16.Proof166Res6
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem psuField_apply_of_mem_fourPSU (σ : K ≃+* K) {v : unitaryPSU h 3}
    (hv : v ∈ fourPSU h) : psuField h σ v = v := by
  obtain ⟨g, hg, rfl⟩ := hv
  change psuField h σ (g : unitaryPSU h 3) = (g : unitaryPSU h 3)
  rw [psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField]
  obtain ⟨u, hu, hug⟩ := coe_mem_diagSU hg
  rw [← hug]
  apply Units.ext
  rw [coe_glAut, coe_diagGL, diagonal_map (map_zero _)]
  congr 1
  funext i
  have hw : (u.1 * u.2)⁻¹ ∈ rootsOfUnity 2 K :=
    (rootsOfUnity 2 K).inv_mem ((rootsOfUnity 2 K).mul_mem hu.1 hu.2)
  fin_cases i
  · exact ringEquiv_apply_of_sq_eq_one σ hu.1
  · exact ringEquiv_apply_of_sq_eq_one σ hu.2
  · exact ringEquiv_apply_of_sq_eq_one σ hw

theorem psuConj_diagFirst_apply_of_mem_fourPSU {d : Kˣ} (hd : diagFirst d ∈ unitaryIsom3 h)
    {v : unitaryPSU h 3} (hv : v ∈ fourPSU h) : psuConj h ⟨diagFirst d, hd⟩ v = v := by
  obtain ⟨g, hg, rfl⟩ := hv
  change psuConj h ⟨diagFirst d, hd⟩ (g : unitaryPSU h 3) = (g : unitaryPSU h 3)
  rw [psuConj_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suConj]
  obtain ⟨u, -, hug⟩ := coe_mem_diagSU hg
  rw [← hug]
  have hc : diagFirst d * diagGL u = diagGL u * diagFirst d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagFirst, coe_diagGL, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  change diagFirst d * diagGL u * (diagFirst d)⁻¹ = diagGL u
  rw [hc, mul_inv_cancel_right]

theorem bar_det_mul_det (A : unitaryIsom3 h) :
    h.bar ((Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) : Kˣ) : K) *
      (Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) : Kˣ) = 1 := by
  have h1 := congrArg Matrix.det (mem_unitaryIsom3.mp A.2)
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_one] at h1
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact h1

theorem scalar_mem_unitaryIsom3 {d : Kˣ} (hd : h.bar (d : K) * d = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) d ∈ unitaryIsom3 h :=
  CFSG.RankThree.PartTwo.KFacts.scalar_mem_unitaryIsom3_of_norm (by rw [UnitaryFieldData.norm, mul_comm]; exact hd)

theorem psuConj_scalar {d : Kˣ} (hs : Matrix.GeneralLinearGroup.scalar (Fin 3) d ∈ unitaryIsom3 h) :
    psuConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) d, hs⟩ = 1 :=
  CFSG.RankThree.PartTwo.KFacts.psuConj_eq_one_of_coe_eq_scalar rfl

omit [Field K] in
theorem ringEquiv_sq_and_frobenius [Field K] {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (σ : K ≃+* K) : σ ^ 2 = 1 ∧ (σ ≠ 1 → ∀ x, σ x = x ^ r) := by
  obtain ⟨φ, hφ, hord, hzp, hcard, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality r 2 hr
      (by norm_num) K hK
  refine ⟨?_, fun hσ x => ?_⟩
  · have h1 := orderOf_dvd_natCard σ
    rw [hcard] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  · have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; norm_num)
    have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
    rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hk2 : φ ^ (k % 2) = σ := by rw [← hk, ← hord, pow_mod_orderOf]
    have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · rw [h0, pow_zero] at hk2
      exact absurd hk2.symm hσ
    · rw [h1, pow_one] at hk2
      rw [← hk2, hφ]

theorem aut_cases_unitaryPSU {r : ℕ} (h : UnitaryFieldData r 1 K) (hq : 2 < r ^ 1)
    (α : MulAut (unitaryPSU h 3)) :
    (∃ y, α ^ 3 = MulAut.conj y) ∨
      ∃ y, ((MulAut.conj y)⁻¹ * α) ^ 2 = 1 ∧ (∀ v ∈ fourPSU h, ((MulAut.conj y)⁻¹ * α) v = v) ∧
        ∀ z, (MulAut.conj y)⁻¹ * α ≠ MulAut.conj z := by
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  set d := Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) with hd
  have hnd : h.bar (d : K) * d = 1 := bar_det_mul_det h A
  by_cases hσ : σ = 1
  ·
    left
    rw [hσ, map_one, mul_one]
    have hs := scalar_mem_unitaryIsom3 h hnd
    set Y : GL (Fin 3) K := (A : GL (Fin 3) K) ^ 3 *
      (Matrix.GeneralLinearGroup.scalar (Fin 3) d)⁻¹ with hYdef
    have hYiso : Y ∈ unitaryIsom3 h := mul_mem (pow_mem A.2 3) (inv_mem hs)
    have hYdet : (Y : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hYdef, map_mul, map_inv, det_scalar_three,
        map_pow, ← hd, mul_inv_cancel, Units.val_one]
    have hYSU : Y ∈ unitarySU r 1 K 3 := (mem_unitarySU_iff h).mpr ⟨hYdet, hYiso⟩
    refine ⟨unitaryProj h 3 ⟨Y, hYSU⟩, ?_⟩
    have hA3 : A ^ 3 = ⟨Y, hYiso⟩ * ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) d, hs⟩ := by
      apply Subtype.ext
      change (A : GL (Fin 3) K) ^ 3 = Y * Matrix.GeneralLinearGroup.scalar (Fin 3) d
      rw [hYdef, inv_mul_cancel_right]
    rw [← map_pow, hA3, map_mul, psuConj_scalar, mul_one]
    exact (conj_mk_eq_psuConj (h := h) ⟨Y, hYSU⟩).symm
  ·
    right
    have hK : Nat.card K = r ^ 2 := by rw [h.card]
    obtain ⟨hσ2, hσfrob⟩ := ringEquiv_sq_and_frobenius h.prime hK σ
    have hσbar : ∀ x, σ x = h.bar x := fun x => by
      rw [hσfrob hσ x, UnitaryFieldData.bar_apply, pow_one]
    have hD := diagFirst_mem_unitaryIsom3 h hnd
    set X : GL (Fin 3) K := (A : GL (Fin 3) K) * (diagFirst d)⁻¹ with hX
    have hXiso : X ∈ unitaryIsom3 h := mul_mem A.2 (inv_mem hD)
    have hdetX : (X : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hX, map_mul, map_inv, det_diagFirst, ← hd,
        mul_inv_cancel, Units.val_one]
    have hXSU : X ∈ unitarySU r 1 K 3 := (mem_unitarySU_iff h).mpr ⟨hdetX, hXiso⟩
    have hA : A = ⟨X, hXiso⟩ * ⟨diagFirst d, hD⟩ := by
      apply Subtype.ext
      change (A : GL (Fin 3) K) = X * diagFirst d
      rw [hX, inv_mul_cancel_right]
    refine ⟨unitaryProj h 3 ⟨X, hXSU⟩, ?_⟩
    have hconj : MulAut.conj (unitaryProj h 3 ⟨X, hXSU⟩) = psuConj h ⟨X, hXiso⟩ :=
      conj_mk_eq_psuConj (h := h) ⟨X, hXSU⟩
    have hβ : (MulAut.conj (unitaryProj h 3 ⟨X, hXSU⟩))⁻¹ * (psuConj h A * psuField h σ) =
        psuConj h ⟨diagFirst d, hD⟩ * psuField h σ := by
      rw [hconj, hA, map_mul, mul_assoc, inv_mul_cancel_left]
    rw [hβ]
    refine ⟨?_, fun v hv => ?_, fun z hz => ?_⟩
    ·
      have hB1 : (⟨diagFirst d, hD⟩ : unitaryIsom3 h) *
          ⟨glAut σ (diagFirst d), glAut_mem_unitaryIsom3 σ hD⟩ = 1 := by
        apply Subtype.ext
        apply Units.ext
        change (diagFirst d : Matrix (Fin 3) (Fin 3) K) *
          ((diagFirst d : Matrix (Fin 3) (Fin 3) K).map σ) = 1
        rw [coe_diagFirst, diagonal_map (map_zero _), diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
          rw [hσbar, mul_comm]
          exact hnd
        · simp
        · simp
      have hconjB := psuField_mul_psuConj_mul_inv (h := h) σ ⟨diagFirst d, hD⟩
      calc (psuConj h ⟨diagFirst d, hD⟩ * psuField h σ) ^ 2
          = psuConj h ⟨diagFirst d, hD⟩ *
              (psuField h σ * psuConj h ⟨diagFirst d, hD⟩ * (psuField h σ)⁻¹) *
              (psuField h σ * psuField h σ) := by
            rw [pow_two]
            group
        _ = 1 := by
          rw [hconjB, ← map_mul, ← map_mul, hB1, ← pow_two, hσ2, map_one, map_one, mul_one]
    · rw [MulAut.mul_apply, psuField_apply_of_mem_fourPSU h σ hv,
        psuConj_diagFirst_apply_of_mem_fourPSU h hD hv]
    ·
      obtain ⟨Z, rfl⟩ := unitaryProj_surjective h 3 z
      have hz' : psuConj h ⟨diagFirst d, hD⟩ * psuField h σ =
          psuConj h ⟨Z, unitarySU_le_unitaryIsom3 Z.2⟩ :=
        hz.trans (conj_mk_eq_psuConj (h := h) Z)
      apply hσ
      refine (psuField_mem_range_psuConj_iff (h := h)).mp
        ⟨(⟨diagFirst d, hD⟩ : unitaryIsom3 h)⁻¹ * ⟨Z, unitarySU_le_unitaryIsom3 Z.2⟩, ?_⟩
      rw [map_mul, ← hz', map_inv, inv_mul_cancel_left]

theorem mul_self_of_mem_fourPSU {v : unitaryPSU h 3} (hv : v ∈ fourPSU h) : v * v = 1 := by
  obtain ⟨g, hg, rfl⟩ := hv
  rw [← map_mul, mul_self_of_mem_fourSU hg, map_one]

theorem card_fourPSU [Finite K] (hp : p ≠ 2) : Nat.card (fourPSU h) = 4 := by
  have : CharP K p := h.charP
  have hV : Nat.card (fourSU (p := p) (f := f) (K := K)) = 4 := by
    rw [fourSU, card_diagSU h _ (fun x hx => norm_eq_one_of_mem_rootsOfUnity_two h hx),
      card_rootsOfUnity_two hp]
    norm_num
  have hinj : Function.Injective
      ((unitaryProj h 3).comp (fourSU (p := p) (f := f) (K := K)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨g, hg⟩ hker
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← MonoidHom.mem_ker,
      ker_unitaryProj, mem_unitaryScalars] at hker
    obtain ⟨c, -, -, hc⟩ := hker
    rw [Subgroup.mem_bot]
    obtain ⟨u, hu, hug⟩ := coe_mem_diagSU hg
    have hc' := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) (hug.trans hc)
    simp only [coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar] at hc'
    have h0 := congrFun (congrFun hc' 0) 0
    have h1 := congrFun (congrFun hc' 1) 1
    have h2 := congrFun (congrFun hc' 2) 2
    simp only [diagonal_apply_eq, diagVec, scalar_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    have hu1 : u.1 = c := Units.ext h0
    have hu2 : u.2 = c := Units.ext h1
    have hu12 : (u.1 * u.2)⁻¹ = c := Units.ext h2
    have hc2 : c ^ 2 = 1 := by rw [← hu1]; exact (mem_rootsOfUnity 2 u.1).mp hu.1
    have hc1 : c = 1 := by
      rw [hu1, hu2, ← pow_two, hc2, inv_one] at hu12
      exact hu12.symm
    apply Subtype.ext
    apply Subtype.ext
    change (g : GL (Fin 3) K) = 1
    rw [← hug, show u = 1 from Prod.ext (hu1.trans hc1) (hu2.trans hc1), map_one]
  have hmap : (fourSU (p := p) (f := f) (K := K)).map (unitaryProj h 3) =
      ((unitaryProj h 3).comp (fourSU (p := p) (f := f) (K := K)).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [fourPSU, hmap, ← hV]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end KL3Sub2Proof

end CFSG.RankThree.PartTwo.Sec15
