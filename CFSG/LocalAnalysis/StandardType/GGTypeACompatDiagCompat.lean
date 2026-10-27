module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix

private theorem conjSL_diagGL_eq_ggDiagConj {m : ℕ} {F : Type} [Field F]
    (v : Fin (m + 1) → Fˣ) (s : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (InnerDiagA.diagGL v) s = ggDiagConj v s := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv,
    coe_ggDiagConj]

private theorem diagGL_mul_diagGL {m : ℕ} {F : Type} [Field F]
    (v w : Fin (m + 1) → Fˣ) :
    InnerDiagA.diagGL v * InnerDiagA.diagGL w = InnerDiagA.diagGL (v * w) := by
  apply Units.ext
  rw [Units.val_mul, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL,
    Matrix.diagonal_mul_diagonal]
  rfl

private theorem mul_inv_mul_inv_of_mem_center {H : Type*} [Group H]
    {p p' q q' : H} (h : p' * q'⁻¹ ∈ Subgroup.center H) :
    p * p' * (q'⁻¹ * q⁻¹) = (p * q⁻¹) * (p' * q'⁻¹) := by
  have hc : (p' * q'⁻¹) * q⁻¹ = q⁻¹ * (p' * q'⁻¹) :=
    (Subgroup.mem_center_iff.mp h q⁻¹).symm
  calc p * p' * (q'⁻¹ * q⁻¹) = p * ((p' * q'⁻¹) * q⁻¹) := by group
    _ = p * (q⁻¹ * (p' * q'⁻¹)) := by rw [hc]
    _ = (p * q⁻¹) * (p' * q'⁻¹) := by group

private theorem exists_diagGL_of_conjSL_slUpperBlock {n : ℕ} {F : Type} [Field F]
    (hn : 2 ≤ n) {C : GL (Fin (n + 1)) F}
    (hC : ∀ t : SpecialLinearGroup (Fin n) F,
      InnerDiagA.conjSL C (slUpperBlockHom n F t) = slUpperBlockHom n F t) :
    ∃ c : Fin (n + 1) → Fˣ, C = InnerDiagA.diagGL c := by
  refine LinTorus.exists_eq_diagGL (M := C) fun k l hkl => ?_
  have key : ∀ (i j : Fin n), i ≠ j →
      (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
          Matrix.single i.castSucc j.castSucc (1 : F) =
        Matrix.single i.castSucc j.castSucc (1 : F) *
          (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := by
    intro i j hij
    have h1 := hC (Matrix.SpecialLinearGroup.transvection hij 1)
    rw [slUpperBlockHom_transvection hij 1] at h1
    have h2 : (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
          (((Matrix.SpecialLinearGroup.transvection ((Fin.castSucc_injective n).ne hij)
            (1 : F)) : SpecialLinearGroup (Fin (n + 1)) F) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
          (((C⁻¹ : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) =
        (((Matrix.SpecialLinearGroup.transvection ((Fin.castSucc_injective n).ne hij)
            (1 : F)) : SpecialLinearGroup (Fin (n + 1)) F) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F) := by
      have h := congrArg (fun x : SpecialLinearGroup (Fin (n + 1)) F =>
        (x : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) h1
      simpa only [InnerDiagA.coe_conjSL] using h
    rw [Matrix.SpecialLinearGroup.transvection_coe] at h2
    have hCin : (((C⁻¹ : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) *
        (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hCU : (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
          (1 + Matrix.single i.castSucc j.castSucc (1 : F)) =
        (1 + Matrix.single i.castSucc j.castSucc (1 : F)) *
          (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := by
      calc (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
            (1 + Matrix.single i.castSucc j.castSucc (1 : F))
          = (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
              (1 + Matrix.single i.castSucc j.castSucc (1 : F)) * 1 :=
            (Matrix.mul_one _).symm
        _ = (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
              (1 + Matrix.single i.castSucc j.castSucc (1 : F)) *
              ((((C⁻¹ : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) *
                (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) := by rw [hCin]
        _ = ((C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
              (1 + Matrix.single i.castSucc j.castSucc (1 : F)) *
              (((C⁻¹ : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F))) *
              (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
            (Matrix.mul_assoc _ _ _).symm
        _ = (1 + Matrix.single i.castSucc j.castSucc (1 : F)) *
              (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := by rw [h2]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at hCU
    exact add_left_cancel hCU
  have hcol : ∀ (i j : Fin n), i ≠ j → ∀ k : Fin (n + 1),
      k ≠ i.castSucc → (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) k i.castSucc = 0 := by
    intro i j hij k hk
    have h := congrFun (congrFun (key i j hij) k) j.castSucc
    rw [Matrix.mul_single_apply_same (1 : F) i.castSucc j.castSucc k
          (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F),
        Matrix.single_mul_apply_of_ne (1 : F) i.castSucc j.castSucc k j.castSucc hk
          (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F)] at h
    simpa using h
  have hrow : ∀ (i j : Fin n), i ≠ j → ∀ l : Fin (n + 1),
      l ≠ j.castSucc → (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F) j.castSucc l = 0 := by
    intro i j hij l hl
    have h := congrFun (congrFun (key i j hij) i.castSucc) l
    rw [Matrix.mul_single_apply_of_ne (1 : F) i.castSucc j.castSucc i.castSucc l hl
          (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F),
        Matrix.single_mul_apply_same (1 : F) i.castSucc j.castSucc l
          (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F)] at h
    simpa using h.symm
  have hn1 : 1 < n := by omega
  have hex : ∀ a : Fin n, ∃ b : Fin n, b ≠ a := fun a =>
    Fintype.exists_ne_of_one_lt_card (α := Fin n) (by simpa using hn1) a
  by_cases hl : l = Fin.last n
  · have hk : k ≠ Fin.last n := fun h => hkl (h.trans hl.symm)
    obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hk
    obtain ⟨i', hi'⟩ := hex i
    have h := hrow i' i hi' l (by rw [hl]; exact (Fin.castSucc_ne_last i).symm)
    rwa [hi] at h
  · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hl
    obtain ⟨j, hj⟩ := hex i
    have hkl' : k ≠ i.castSucc := by rw [hi]; exact hkl
    have h := hcol i j hj.symm k hkl'
    rwa [hi] at h

theorem ggActsDiag_of_compat {X : Type} [Group X] {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 3 ≤ n) {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F)) {b : X}
    (h₁ : GGActsDiag φ₁ b)
    (h₂ : ∃ A : GL (Fin (n + 1)) F, (b, A) ∈ LinFusion.ggInducedPairs φ₂) :
    GGActsDiag φ₂ b := by
  obtain ⟨h, hh⟩ := h₁
  obtain ⟨A, hA⟩ := h₂
  have hA' : ∀ u, b * φ₂ u * b⁻¹ = φ₂ (InnerDiagA.conjSL A u) :=
    LinFusion.mem_ggInducedPairs.mp hA
  set d : Fin n → Fˣ := h ∘ Fin.succ with hd
  have hcx : ∀ x : SpecialLinearGroup (Fin n) F,
      φ₁ (slLowerBlockHom n F x) = φ₂ (slUpperBlockHom n F x) :=
    fun x => DFunLike.congr_fun hc x
  have hcomm : ∀ t : SpecialLinearGroup (Fin n) F,
      φ₂ (InnerDiagA.conjSL A (slUpperBlockHom n F t)) =
        φ₂ (slUpperBlockHom n F (ggDiagConj d t)) := by
    intro t
    calc φ₂ (InnerDiagA.conjSL A (slUpperBlockHom n F t))
        = b * φ₂ (slUpperBlockHom n F t) * b⁻¹ := (hA' (slUpperBlockHom n F t)).symm
      _ = b * φ₁ (slLowerBlockHom n F t) * b⁻¹ := by rw [hcx t]
      _ = φ₁ (ggDiagConj h (slLowerBlockHom n F t)) := hh (slLowerBlockHom n F t)
      _ = φ₁ (slLowerBlockHom n F (ggDiagConj d t)) := by
            rw [ggDiagConj_slLowerBlockHom, ← hd]
      _ = φ₂ (slUpperBlockHom n F (ggDiagConj d t)) := hcx _
  let P : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin (n + 1)) F :=
    (InnerDiagA.conjSL A).comp (slUpperBlockHom n F)
  let Q : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin (n + 1)) F :=
    (slUpperBlockHom n F).comp (ggDiagConj d)
  let F0 : SpecialLinearGroup (Fin n) F → SpecialLinearGroup (Fin (n + 1)) F :=
    fun t => P t * (Q t)⁻¹
  have hu_mem : ∀ t, F0 t ∈ φ₂.ker := by
    intro t
    rw [MonoidHom.mem_ker]
    change φ₂ (InnerDiagA.conjSL A (slUpperBlockHom n F t) *
      (slUpperBlockHom n F (ggDiagConj d t))⁻¹) = 1
    rw [map_mul, map_inv, hcomm t, mul_inv_cancel]
  have hu_center : ∀ t, F0 t ∈ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) :=
    fun t => hker₂ (hu_mem t)
  let uc : SpecialLinearGroup (Fin n) F →*
      Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) :=
  { toFun := fun t => ⟨F0 t, hu_center t⟩
    map_one' := by
      apply Subtype.ext
      change P 1 * (Q 1)⁻¹ = 1
      simp only [P, Q, MonoidHom.comp_apply, map_one, inv_one, mul_one]
    map_mul' := fun t t' => by
      apply Subtype.ext
      change P (t * t') * (Q (t * t'))⁻¹ =
        (P t * (Q t)⁻¹) * (P t' * (Q t')⁻¹)
      rw [map_mul P, map_mul Q, _root_.mul_inv_rev]
      exact mul_inv_mul_inv_of_mem_center (p := P t) (q := Q t)
        (p' := P t') (q' := Q t') (hu_center t') }
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin n) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn
  have hker_top : uc.ker = ⊤ := eq_top_iff.mpr (by
    rw [← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker uc)
  have huc1 : uc = 1 := MonoidHom.ker_eq_top_iff.mp hker_top
  have hF0_one : ∀ t, F0 t = 1 := by
    intro t
    have h0 : uc t = 1 := by simpa using DFunLike.congr_fun huc1 t
    have h1 : (uc t).val = (1 : Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)).val :=
      congrArg Subtype.val h0
    show F0 t = 1
    exact h1
  have hconjA : ∀ t, InnerDiagA.conjSL A (slUpperBlockHom n F t) =
      slUpperBlockHom n F (ggDiagConj d t) := by
    intro t
    have h := hF0_one t
    change P t * (Q t)⁻¹ = 1 at h
    have h' : P t = Q t := by
      simpa using (mul_eq_one_iff_eq_inv.mp h)
    simpa only [P, Q, MonoidHom.comp_apply] using h'
  let e : Fin (n + 1) → Fˣ := Fin.snoc d 1
  have he : e ∘ Fin.castSucc = d := by
    change Fin.snoc d 1 ∘ Fin.castSucc = d
    exact Fin.snoc_comp_castSucc
  have hconj_e : ∀ t, InnerDiagA.conjSL (InnerDiagA.diagGL e)
      (slUpperBlockHom n F t) = slUpperBlockHom n F (ggDiagConj d t) := by
    intro t
    rw [conjSL_diagGL_eq_ggDiagConj, ggDiagConj_slUpperBlockHom, he]
  let C : GL (Fin (n + 1)) F := (InnerDiagA.diagGL e)⁻¹ * A
  have hC_conj : ∀ t, InnerDiagA.conjSL C (slUpperBlockHom n F t) = slUpperBlockHom n F t := by
    intro t
    change InnerDiagA.conjSL ((InnerDiagA.diagGL e)⁻¹ * A) (slUpperBlockHom n F t) =
      slUpperBlockHom n F t
    rw [LinFusion.conjSL_mul, hconjA t, ← hconj_e t]
    rw [← LinFusion.conjSL_mul, inv_mul_cancel, LinFusion.conjSL_one]
  obtain ⟨c, hc⟩ := exists_diagGL_of_conjSL_slUpperBlock (n := n) (F := F) (C := C)
    (by omega) hC_conj
  have hA_eq : A = InnerDiagA.diagGL (e * c) := by
    have hA1 : A = InnerDiagA.diagGL e * C := by
      change A = InnerDiagA.diagGL e * ((InnerDiagA.diagGL e)⁻¹ * A)
      group
    calc A = InnerDiagA.diagGL e * C := hA1
      _ = InnerDiagA.diagGL e * InnerDiagA.diagGL c := by rw [hc]
      _ = InnerDiagA.diagGL (e * c) := diagGL_mul_diagGL e c
  refine ⟨e * c, fun s => ?_⟩
  calc b * φ₂ s * b⁻¹ = φ₂ (InnerDiagA.conjSL A s) := hA' s
    _ = φ₂ (InnerDiagA.conjSL (InnerDiagA.diagGL (e * c)) s) := by rw [hA_eq]
    _ = φ₂ (ggDiagConj (e * c) s) := by rw [conjSL_diagGL_eq_ggDiagConj]

end CFSG.StandardType

end
