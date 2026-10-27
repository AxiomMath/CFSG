module

public import CFSG.LocalAnalysis.StandardType.FS81.MonoRefl
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatWt
public import CFSG.LocalAnalysis.StandardType.FS81.N6MainMat

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {n : ℕ}

structure MonoN0Hyp (Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))) : Prop where
  norm : ∀ A ∈ Xg, (∀ i : Fin (n + 1), i ≠ 0 →
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 = 0) →
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n
  sub : ∀ M ∈ monoN0 n, ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = M
  odd : ∀ N : Subgroup ↥Xg, N.Normal → Odd (Nat.card N) → N = ⊥
  moves : ∃ A ∈ Xg, ∃ i : Fin (n + 1), i ≠ 0 ∧
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 ≠ 0

@[expose] def OrbN (Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))) (v : Fin (n + 1) → ZMod 3) :
    Prop :=
  ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = v

section General

variable {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}

theorem orbN_e0 : OrbN Xg (Pi.single 0 1) := by
  exact ⟨1, Xg.one_mem, by rw [Units.val_one, Matrix.one_mulVec]⟩

theorem orbN_mulVec {v : Fin (n + 1) → ZMod 3} (hv : OrbN Xg v) {B : GL (Fin (n + 1)) (ZMod 3)}
    (hB : B ∈ Xg) : OrbN Xg ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) := by
  obtain ⟨A, hA, rfl⟩ := hv
  exact ⟨B * A, Xg.mul_mem hB hA, gl_mul_mulVec B A _⟩

theorem orbN_ne_zero {v : Fin (n + 1) → ZMod 3} (hv : OrbN Xg v) : v ≠ 0 := by
  obtain ⟨A, -, rfl⟩ := hv
  exact gl_mulVec_ne_zero A (Pi.single_ne_zero_iff.mpr one_ne_zero)

private theorem monoHyp_coordRefl_sub {a : Fin (n + 1)} (y : Fin (n + 1) → ZMod 3) :
    coordRefl a *ᵥ y - y = y a • Pi.single a 1 := by
  have h3 : ∀ c : ZMod 3, -c - c = c := by
    intro c
    revert c
    decide
  rw [coordRefl_mulVec]
  funext i
  by_cases hi : i = a
  · subst hi
    rw [Pi.sub_apply, if_pos rfl, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact h3 _
  · rw [Pi.sub_apply, if_neg hi, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero, sub_self]

theorem conj_coordRefl_mulVec_sub {a : Fin (n + 1)} {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl a)
    (A : GL (Fin (n + 1)) (ZMod 3)) (z : Fin (n + 1) → ZMod 3) :
    ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        z - z =
      ((((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z)
          a) • ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single a 1) := by
  rw [gl_conj_mulVec, hT]
  calc (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        (coordRefl a *ᵥ (((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z)) - z
      = (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          (coordRefl a *ᵥ (((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z) -
            (((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z)) := by
        rw [Matrix.mulVec_sub, gl_mulVec_inv_mulVec]
    _ = (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          (((((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z) a) • Pi.single a 1) := by
        rw [monoHyp_coordRefl_sub]
    _ = _ := by rw [Matrix.mulVec_smul]

private theorem monoHyp_coordRefl_mulVec_axis (a : Fin (n + 1)) :
    coordRefl a *ᵥ Pi.single a 1 = -Pi.single a 1 := by
  rw [coordRefl_mulVec]
  funext i
  by_cases hi : i = a
  · subst hi
    rw [if_pos rfl, Pi.neg_apply, Pi.single_eq_same]
    rfl
  · rw [if_neg hi, Pi.neg_apply, Pi.single_eq_of_ne hi]
    exact neg_zero

theorem conj_coordRefl_mulVec_axis {a : Fin (n + 1)} {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl a)
    (A : GL (Fin (n + 1)) (ZMod 3)) :
    ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single a 1) =
      -((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single a 1) := by
  rw [gl_conj_mulVec, hT, gl_inv_mulVec_mulVec, monoHyp_coordRefl_mulVec_axis, Matrix.mulVec_neg]

theorem commute_of_mem_monoN0 {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {A : GL (Fin (n + 1)) (ZMod 3)}
    (hA : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n) : Commute A T := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hT]
  exact commute_coordRefl_zero_of_mem_monoN0 hA

private theorem monoHyp_coordRefl_neg_apply {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {v : Fin (n + 1) → ZMod 3}
    (hv : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = -v) {i : Fin (n + 1)}
    (hi : i ≠ 0) : v i = 0 := by
  have e := congrFun hv i
  simp only [hT, coordRefl_mulVec, Pi.neg_apply] at e
  rw [if_neg hi] at e
  exact zmod3_eq_zero_of_eq_neg e

private theorem monoHyp_mul_sub_ne_zero (c δ : ZMod 3) (hc : c ≠ 0) (hδ : δ ≠ 0) :
    c * (0 - δ * 1) ≠ 0 := by
  revert hc hδ
  revert c δ
  decide

end General

namespace MonoN0Hyp

variable {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))} (h : MonoN0Hyp Xg)
include h

theorem exists_coordRefl (a : Fin (n + 1)) :
    ∃ T ∈ Xg, (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl a := by
  exact h.sub (coordRefl a) (coordRefl_mem_monoN0 a)

private theorem monoHyp_mem_coordRefl {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0) : T ∈ Xg := by
  obtain ⟨T', hT', hT'eq⟩ := h.exists_coordRefl 0
  rwa [Units.ext (hT'eq.trans hT.symm)] at hT'

theorem mem_of_mulVec_e0 {A : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg) {c : ZMod 3}
    (hc : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = c • Pi.single 0 1) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
  refine h.norm A hA fun i hi => ?_
  have e := congrFun hc i
  rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne hi,
    smul_zero] at e

theorem mem_monoN0_of_commute {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {A : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg) (hc : Commute A T) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
  refine h.norm A hA fun i hi => ?_
  have hcomm : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *
      (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
      (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *
        (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by
    have := congrArg Units.val hc
    simpa only [Units.val_mul] using this
  have hneg : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
      -((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    calc (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)
        = ((T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *
            (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))) *ᵥ Pi.single 0 1 := by
          rw [Matrix.mulVec_mulVec]
      _ = ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *
            (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))) *ᵥ Pi.single 0 1 := by
          rw [hcomm]
      _ = (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
            ((T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
          rw [Matrix.mulVec_mulVec]
      _ = (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ (-Pi.single 0 1) := by
          rw [hT, monoHyp_coordRefl_mulVec_axis]
      _ = -((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
          rw [Matrix.mulVec_neg]
  have hcol : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 =
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) i := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol]
  exact monoHyp_coordRefl_neg_apply hT hneg hi

theorem orbN_smul {v : Fin (n + 1) → ZMod 3} (hv : OrbN Xg v) {c : ZMod 3} (hc : c ≠ 0) :
    OrbN Xg (c • v) := by
  obtain ⟨A, hA, rfl⟩ := hv
  obtain ⟨T, hTX, hT⟩ := h.exists_coordRefl 0
  rcases eq_one_or_of_ne_zero hc with h1 | h1
  · rw [h1, one_smul]
    exact ⟨A, hA, rfl⟩
  · rw [h1]
    refine ⟨A * T, Xg.mul_mem hA hTX, ?_⟩
    rw [gl_mul_mulVec, hT, monoHyp_coordRefl_mulVec_axis, Matrix.mulVec_neg, neg_one_smul (ZMod 3)]

theorem orbN_neg {v : Fin (n + 1) → ZMod 3} (hv : OrbN Xg v) : OrbN Xg (-v) := by
  have := h.orbN_smul hv (c := (-1 : ZMod 3)) (by decide)
  simpa [neg_one_smul (ZMod 3)] using this

theorem orbN_spMat {v : Fin (n + 1) → ZMod 3} (hv : OrbN Xg v) {σ : Equiv.Perm (Fin (n + 1))}
    {s : Fin (n + 1) → ZMod 3} (hs : IsSign s) (hσ : σ 0 = 0) : OrbN Xg (spMat σ s *ᵥ v) := by
  obtain ⟨B, hB, hBm⟩ := h.sub (spMat σ s) ⟨σ, s, hs, hσ, rfl⟩
  have h' := orbN_mulVec hv hB
  rwa [hBm] at h'

theorem conj_eq_of_mulVec_e0 {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {A B : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg) (hB : B ∈ Xg) {c : ZMod 3}
    (hAB : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      c • ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)) :
    A * T * A⁻¹ = B * T * B⁻¹ := by
  have hC : B⁻¹ * A ∈ Xg := Xg.mul_mem (Xg.inv_mem hB) hA
  have hCe : ((B⁻¹ * A : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = c • Pi.single 0 1 := by
    rw [gl_mul_mulVec, hAB, Matrix.mulVec_smul, gl_inv_mulVec_mulVec]
  have hcomm := commute_of_mem_monoN0 hT (h.mem_of_mulVec_e0 hC hCe)
  calc A * T * A⁻¹ = B * ((B⁻¹ * A) * T) * (B⁻¹ * A)⁻¹ * B⁻¹ := by group
    _ = B * (T * (B⁻¹ * A)) * (B⁻¹ * A)⁻¹ * B⁻¹ := by rw [hcomm.eq]
    _ = B * T * B⁻¹ := by group

theorem mulVec_e0_of_conj_eq {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {A B : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg) (hB : B ∈ Xg)
    (hAB : A * T * A⁻¹ = B * T * B⁻¹) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 ∨
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        -((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
  have hC : B⁻¹ * A ∈ Xg := Xg.mul_mem (Xg.inv_mem hB) hA
  have hCcomm : (B⁻¹ * A) * T = T * (B⁻¹ * A) := by
    calc (B⁻¹ * A) * T = B⁻¹ * (A * T * A⁻¹) * A := by group
      _ = B⁻¹ * (B * T * B⁻¹) * A := by rw [hAB]
      _ = T * (B⁻¹ * A) := by group
  have hCmem : ((B⁻¹ * A : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n :=
    h.mem_monoN0_of_commute hT hC hCcomm
  obtain ⟨σ, s, hs, hσ0, hCs⟩ := hCmem
  have hCe : ((B⁻¹ * A : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = s 0 • Pi.single 0 1 := by
    rw [hCs, spMat_mulVec]
    funext i
    by_cases hi : i = 0
    · subst hi
      have hsymm : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, hσ0]
      simp [hsymm]
    · have hsymm : σ.symm i ≠ 0 := by
        intro h0
        exact hi (by rw [← Equiv.apply_symm_apply σ i, h0, hσ0])
      simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hsymm]
  have hAe : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      s 0 • ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    rw [show A = B * (B⁻¹ * A) from by group, gl_mul_mulVec, hCe, Matrix.mulVec_smul]
  rcases hs 0 with h0 | h0
  · left
    rw [hAe, h0, one_smul]
  · right
    rw [hAe, h0]
    funext j
    rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    generalize ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) j = x
    revert x
    decide

theorem commute_conj_iff {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {A B : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg) (hB : B ∈ Xg) :
    Commute (A * T * A⁻¹) (B * T * B⁻¹) ↔
      ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
          (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 ∨
        ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
          -((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
  have hTX : T ∈ Xg := monoHyp_mem_coordRefl h hT
  have hrX : A * T * A⁻¹ ∈ Xg := Xg.mul_mem (Xg.mul_mem hA hTX) (Xg.inv_mem hA)
  constructor
  · intro hc
    have h1 : ((A * T * A⁻¹) * B) * T * ((A * T * A⁻¹) * B)⁻¹ = B * T * B⁻¹ := by
      calc ((A * T * A⁻¹) * B) * T * ((A * T * A⁻¹) * B)⁻¹
          = (A * T * A⁻¹) * (B * T * B⁻¹) * (A * T * A⁻¹)⁻¹ := by group
        _ = B * T * B⁻¹ := by rw [hc.eq]; group
    have h2 := h.mulVec_e0_of_conj_eq hT (Xg.mul_mem hrX hB) hB h1
    rwa [gl_mul_mulVec] at h2
  · intro hc
    have h1 : ((A * T * A⁻¹) * B) * T * ((A * T * A⁻¹) * B)⁻¹ = B * T * B⁻¹ := by
      rcases hc with hh | hh
      · refine h.conj_eq_of_mulVec_e0 hT (Xg.mul_mem hrX hB) hB (c := 1) ?_
        rw [gl_mul_mulVec, hh, one_smul]
      · refine h.conj_eq_of_mulVec_e0 hT (Xg.mul_mem hrX hB) hB (c := -1) ?_
        rw [gl_mul_mulVec, hh, neg_one_smul (ZMod 3)]
    have h2 : (A * T * A⁻¹) * (B * T * B⁻¹) * (A * T * A⁻¹)⁻¹ = B * T * B⁻¹ := by
      calc (A * T * A⁻¹) * (B * T * B⁻¹) * (A * T * A⁻¹)⁻¹
          = ((A * T * A⁻¹) * B) * T * ((A * T * A⁻¹) * B)⁻¹ := by group
        _ = B * T * B⁻¹ := h1
    calc (A * T * A⁻¹) * (B * T * B⁻¹)
        = (A * T * A⁻¹) * (B * T * B⁻¹) * (A * T * A⁻¹)⁻¹ * (A * T * A⁻¹) := by group
      _ = (B * T * B⁻¹) * (A * T * A⁻¹) := by rw [h2]

theorem commute_of_zero {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {A : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg)
    (h0 : ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0) :
    Commute (A * T * A⁻¹) T := by
  have hTv : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 := by
    rw [hT, coordRefl_mulVec]
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, h0]
      exact neg_zero
    · simp [hi]
  have hT_r : ((1 : GL (Fin (n + 1)) (ZMod 3)) * T * 1⁻¹) = T := by group
  have hiff := h.commute_conj_iff hT (A := (1 : GL (Fin (n + 1)) (ZMod 3))) (B := A)
    Xg.one_mem hA
  have hleft : Commute ((1 : GL (Fin (n + 1)) (ZMod 3)) * T * 1⁻¹) (A * T * A⁻¹) := by
    rw [hiff]
    left
    simpa [hT_r] using hTv
  simpa [hT_r] using hleft.symm

theorem zero_of_commute {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {A : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg) (hc : Commute (A * T * A⁻¹) T)
    (hne : A * T * A⁻¹ ≠ T) :
    ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
  have hT_r : ((1 : GL (Fin (n + 1)) (ZMod 3)) * T * 1⁻¹) = T := by group
  have hc' : Commute ((1 : GL (Fin (n + 1)) (ZMod 3)) * T * 1⁻¹) (A * T * A⁻¹) := by
    rw [hT_r]
    exact hc.symm
  have hiff := h.commute_conj_iff hT (A := (1 : GL (Fin (n + 1)) (ZMod 3))) (B := A)
    Xg.one_mem hA
  rw [hiff] at hc'
  rw [hT_r] at hc'
  rcases hc' with hplus | hminus
  · have e := congrFun hplus 0
    rw [hT, coordRefl_mulVec] at e
    beta_reduce at e
    rw [if_pos rfl] at e
    exact zmod3_eq_zero_of_eq_neg e.symm
  · have hAm : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
      refine h.norm A hA fun i hi => ?_
      have hcol : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 =
          ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) i := by
        rw [Matrix.mulVec_single_one, Matrix.col_apply]
      rw [hcol]
      exact monoHyp_coordRefl_neg_apply hT hminus hi
    have hAT : Commute A T := commute_of_mem_monoN0 hT hAm
    have hAT' : A * T * A⁻¹ = T := by
      calc A * T * A⁻¹ = T * A * A⁻¹ := by rw [hAT.eq]
        _ = T := by group
    exact absurd hAT' hne

theorem conj_cases {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {A : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg)
    (h0 : ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0) :
    (∃ a, a ≠ 0 ∧
        ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
          coordRefl a ∧ ∃ c : ZMod 3, c ≠ 0 ∧
            (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
              c • Pi.single a 1) ∨
      ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ ∃ δ : ZMod 3, δ ≠ 0 ∧
        ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
          swapRefl a b δ ∧ ∃ c : ZMod 3, c ≠ 0 ∧
            (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
              c • (Pi.single a 1 - δ • Pi.single b 1) := by
  have hTX : T ∈ Xg := monoHyp_mem_coordRefl h hT
  have hrX : A * T * A⁻¹ ∈ Xg := Xg.mul_mem (Xg.mul_mem hA hTX) (Xg.inv_mem hA)
  have hcomm : Commute (A * T * A⁻¹) T := h.commute_of_zero hT hA h0
  have hrm : (((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))) ∈ monoN0 n :=
    h.mem_monoN0_of_commute hT hrX hcomm
  obtain ⟨σ, s, hs, hσ0, hrs⟩ := hrm
  have hwne : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 ≠ 0 :=
    gl_mulVec_ne_zero A (Pi.single_ne_zero_iff.mpr one_ne_zero)
  have hneg := conj_coordRefl_mulVec_axis (a := 0) hT A
  have hne : spMat σ s ≠ 1 := by
    intro h1
    rw [hrs, h1, Matrix.one_mulVec] at hneg
    exact hwne (funext fun i => zmod3_eq_zero_of_eq_neg (congrFun hneg i))
  have hw : ∀ m : Fin (n + 1), ∃ c : ZMod 3,
      spMat σ s *ᵥ Pi.single m 1 - Pi.single m 1 =
        c • ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    intro m
    refine ⟨((((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) 0), ?_⟩
    rw [← hrs]
    exact conj_coordRefl_mulVec_sub hT A (Pi.single m 1)
  rcases spMat_refl_cases hs hne hw with ⟨a, hra, c, hc, hw⟩ | ⟨a, b, hab, δ, hδ, hra, c, hc, hw⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      rw [hw] at h0
      exact hc (by simpa only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] using h0)
    exact Or.inl ⟨a, ha0, by rw [hrs, hra], c, hc, hw⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      rw [hw] at h0
      exact hc (by
        simpa only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab,
          smul_eq_mul, mul_zero, sub_zero, mul_one] using h0)
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [hw] at h0
      have hv0 : c * (0 - δ * 1 : ZMod 3) = 0 := by
        simpa only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm ha0),
          Pi.single_eq_same, smul_eq_mul, mul_one] using h0
      exact monoHyp_mul_sub_ne_zero c δ hc hδ hv0
    exact Or.inr ⟨a, b, ha0, hb0, hab, δ, hδ, by rw [hrs, hra], c, hc, hw⟩

theorem wt_of_orbN_zero {v : Fin (n + 1) → ZMod 3} (hv : OrbN Xg v) (h0 : v 0 = 0) :
    wt v = 1 ∨ wt v = 2 := by
  obtain ⟨A, hA, hAv⟩ := hv
  obtain ⟨T, -, hT⟩ := h.exists_coordRefl 0
  have h0' : ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
    rw [hAv]
    exact h0
  rcases h.conj_cases hT hA h0' with ⟨a, -, -, c, hc, hw⟩ | ⟨a, b, -, -, hab, δ, hδ, -, c, hc, hw⟩
  · left
    rw [← hAv, hw, wt_smul_single hc a]
  · right
    rw [← hAv, hw, wt_smul_single_sub_smul hab hc hδ]

theorem exists_conj_coordRefl {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0) {a : Fin (n + 1)}
    (ha : a ≠ 0) {c : ZMod 3} (hc : c ≠ 0) (hv : OrbN Xg (c • Pi.single a 1)) :
    ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • Pi.single a 1 ∧
      ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
        coordRefl a := by
  obtain ⟨A, hA, hAe⟩ := hv
  have h0' : ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
    rw [hAe, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm ha), smul_zero]
  rcases h.conj_cases hT hA h0' with ⟨a', -, hra, c', hc', hw⟩ |
    ⟨a', b', -, -, hab', δ', hδ', hra, c', hc', hw⟩
  · refine ⟨A, hA, hAe, ?_⟩
    have haa : a' = a := by
      by_contra hne
      have e := congrFun hw a
      rw [hAe] at e
      simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne), smul_eq_mul,
        mul_one, mul_zero] at e
      exact hc e
    rw [hra, haa]
  · exfalso
    have h1 : wt ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) = 1 := by
      rw [hAe]
      exact wt_smul_single hc a
    have h2 : wt ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) = 2 := by
      rw [hw]
      exact wt_smul_single_sub_smul hab' hc' hδ'
    omega

theorem exists_conj_swapRefl {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0) {a b : Fin (n + 1)}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) {c δ : ZMod 3} (hc : c ≠ 0) (hδ : δ ≠ 0)
    (hv : OrbN Xg (c • (Pi.single a 1 - δ • Pi.single b 1))) :
    ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • (Pi.single a 1 - δ • Pi.single b 1) ∧
      ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
        swapRefl a b δ := by
  obtain ⟨A, hA, hAe⟩ := hv
  have h0' : ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
    rw [hAe, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm ha),
      Pi.single_eq_of_ne (Ne.symm hb), smul_zero, sub_self, smul_zero]
  rcases h.conj_cases hT hA h0' with ⟨a', -, hra, c', hc', hw⟩ |
    ⟨a', b', -, -, hab', δ', hδ', hra, c', hc', hw⟩
  · exfalso
    have h1 : wt ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) = 2 := by
      rw [hAe]
      exact wt_smul_single_sub_smul hab hc hδ
    have h2 : wt ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) = 1 := by
      rw [hw]
      exact wt_smul_single hc' a'
    omega
  · have hX : c • (Pi.single a 1 - δ • Pi.single b 1) =
        c' • (Pi.single a' 1 - δ' • Pi.single b' 1) := by rw [← hAe, hw]
    have hY : Pi.single a 1 - δ • Pi.single b 1 =
        (c⁻¹ * c') • (Pi.single a' 1 - δ' • Pi.single b' 1) := by
      have hc1 : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
      calc Pi.single a 1 - δ • Pi.single b 1
          = c⁻¹ • (c • (Pi.single a 1 - δ • Pi.single b 1)) := by rw [smul_smul, hc1, one_smul]
        _ = c⁻¹ • (c' • (Pi.single a' 1 - δ' • Pi.single b' 1)) := by rw [hX]
        _ = (c⁻¹ * c') • (Pi.single a' 1 - δ' • Pi.single b' 1) := by rw [smul_smul]
    exact ⟨A, hA, hAe, by rw [hra, swapRefl_eq_of_axis hab hab' hδ hδ' hY]⟩

theorem exists_orbN_zero : ∃ v, OrbN Xg v ∧ v 0 = 0 := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨T, hTX, hT⟩ := h.exists_coordRefl 0
  haveI : Fintype ↥Xg := Fintype.ofFinite _
  set τ : ↥Xg := ⟨T, hTX⟩ with hτ
  have hτ1 : τ ≠ 1 := by
    intro e
    apply coordRefl_ne_one (0 : Fin (n + 1))
    rw [← hT]
    have := congrArg (fun x : ↥Xg => ((x : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))) e
    simpa only [hτ, OneMemClass.coe_one, Units.val_one] using this
  have hτ2 : τ * τ = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) * T = 1
    rw [hT, coordRefl_mul_self]
  have hiso : ∀ g : ↥Xg, (g * τ * g⁻¹) * τ = τ * (g * τ * g⁻¹) → g * τ * g⁻¹ = τ := by
    intro g hc
    by_contra hne
    have hc' : ((g : GL (Fin (n + 1)) (ZMod 3)) * T *
        (g : GL (Fin (n + 1)) (ZMod 3))⁻¹) * T =
        T * ((g : GL (Fin (n + 1)) (ZMod 3)) * T *
          (g : GL (Fin (n + 1)) (ZMod 3))⁻¹) := by
      have := congrArg Subtype.val hc
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hτ] using this
    have hne' : (g : GL (Fin (n + 1)) (ZMod 3)) * T *
        (g : GL (Fin (n + 1)) (ZMod 3))⁻¹ ≠ T := by
      intro h
      apply hne
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hτ] using h
    have h0 := h.zero_of_commute hT g.2 hc' hne'
    exact hno _ ⟨(g : GL (Fin (n + 1)) (ZMod 3)), g.2, rfl⟩ h0
  obtain ⟨N, hNn, hNodd, hNτ⟩ := CFSG.ZStar.glauberman_zStar ↥Xg τ hτ1 hτ2 hiso
  have hN0 : N = ⊥ := h.odd N hNn hNodd
  obtain ⟨A, hA, i, hi, hAi⟩ := h.moves
  have h1 := hNτ ⟨A, hA⟩
  rw [hN0, Subgroup.mem_bot, mul_inv_eq_one] at h1
  have h2 : A * T * A⁻¹ = T := by
    have := congrArg (fun x : ↥Xg => ((x : GL (Fin (n + 1)) (ZMod 3)))) h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hτ] using this
  have hcomm : Commute A T := by
    have h3 : A * T = T * A := by
      calc A * T = A * T * A⁻¹ * A := by group
        _ = T * A := by rw [h2]
    exact h3
  have hAm := h.mem_monoN0_of_commute hT hA hcomm
  obtain ⟨σ, s, -, hσ0, hAs⟩ := hAm
  apply hAi
  have hcol : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 =
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) i := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol, hAs]
  have hsymm : σ.symm i ≠ 0 := by
    intro h0
    have h1 : i = 0 := by
      calc i = σ (σ.symm i) := (Equiv.apply_symm_apply σ i).symm
        _ = σ 0 := by rw [h0]
        _ = 0 := hσ0
    exact hi h1
  simp only [spMat_mulVec, Pi.single_eq_of_ne hsymm, mul_zero]

theorem orbN_of_wt_eq_zero {v : Fin (n + 1) → ZMod 3} (hv : OrbN Xg v) (hv0 : v 0 = 0)
    {w : Fin (n + 1) → ZMod 3} (hw0 : w 0 = 0) (hwt : wt w = wt v) : OrbN Xg w := by
  obtain ⟨σ, s, hs, hσ, hσv⟩ := exists_spMat_mulVec_eq_fix hwt.symm hv0 hw0
  rw [← hσv]
  exact h.orbN_spMat hv hs hσ

end MonoN0Hyp

end CFSG.StandardType.FrameRoute.FS81
