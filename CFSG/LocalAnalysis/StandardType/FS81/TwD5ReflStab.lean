module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Refl
public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Mat

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private abbrev e0 : Fin 6 → ZMod 3 := Pi.single 0 1

def conjMat {k : ℕ} (U : GL (Fin k) (ZMod 3))
    (s : Matrix (Fin k) (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3) :=
  (U : Matrix (Fin k) (Fin k) (ZMod 3)) * s *
    (((U⁻¹ : GL (Fin k) (ZMod 3))) : Matrix (Fin k) (Fin k) (ZMod 3))

private theorem conjMat_apply {k : ℕ} (U : GL (Fin k) (ZMod 3))
    (s : Matrix (Fin k) (Fin k) (ZMod 3)) :
    conjMat U s = (U : Matrix (Fin k) (Fin k) (ZMod 3)) * s *
      (((U⁻¹ : GL (Fin k) (ZMod 3))) : Matrix (Fin k) (Fin k) (ZMod 3)) := rfl

private theorem val_mul_inv {k : ℕ} (U : GL (Fin k) (ZMod 3)) :
    (U : Matrix (Fin k) (Fin k) (ZMod 3)) *
      (((U⁻¹ : GL (Fin k) (ZMod 3))) : Matrix (Fin k) (Fin k) (ZMod 3)) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

private theorem val_inv_mul {k : ℕ} (U : GL (Fin k) (ZMod 3)) :
    (((U⁻¹ : GL (Fin k) (ZMod 3))) : Matrix (Fin k) (Fin k) (ZMod 3)) *
      (U : Matrix (Fin k) (Fin k) (ZMod 3)) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem conjMat_id {k : ℕ} (U : GL (Fin k) (ZMod 3))
    (s : Matrix (Fin k) (Fin k) (ZMod 3)) : conjMat U⁻¹ (conjMat U s) = s := by
  rw [conjMat_apply, conjMat_apply, inv_inv]
  calc
    (↑U⁻¹ : Matrix (Fin k) (Fin k) (ZMod 3)) *
        ((↑U : Matrix (Fin k) (Fin k) (ZMod 3)) * s * ↑U⁻¹) * ↑U
        = ((↑U⁻¹ : Matrix (Fin k) (Fin k) (ZMod 3)) * ↑U) * s *
            ((↑U⁻¹ : Matrix (Fin k) (Fin k) (ZMod 3)) * ↑U) := by noncomm_ring
    _ = s := by rw [val_inv_mul, one_mul, mul_one]

theorem conjMat_injective {k : ℕ} (U : GL (Fin k) (ZMod 3)) :
    Function.Injective (conjMat U) := by
  intro s t h
  have h' := congrArg (conjMat U⁻¹) h
  rwa [conjMat_id, conjMat_id] at h'

theorem conjMat_mulVec {k : ℕ} (U : GL (Fin k) (ZMod 3))
    (s : Matrix (Fin k) (Fin k) (ZMod 3)) (z : Fin k → ZMod 3) :
    conjMat U s *ᵥ ((U : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z) =
      (U : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ (s *ᵥ z) := by
  rw [conjMat_apply]
  have hz : ((↑U⁻¹ : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ
      ((↑U : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, val_inv_mul, Matrix.one_mulVec]
  calc
    ((↑U : Matrix (Fin k) (Fin k) (ZMod 3)) * s * ↑U⁻¹) *ᵥ
        ((↑U : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z)
        = ((↑U : Matrix (Fin k) (Fin k) (ZMod 3)) * s) *ᵥ
            ((↑U⁻¹ : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ
              ((↑U : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z)) := by
          rw [← Matrix.mulVec_mulVec]
    _ = ((↑U : Matrix (Fin k) (Fin k) (ZMod 3)) * s) *ᵥ z := by
          rw [hz]
    _ = (↑U : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ (s *ᵥ z) := by
          rw [← Matrix.mulVec_mulVec]

theorem isRefl_conj {U : GL (Fin 6) (ZMod 3)}
    {s : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hs : IsRefl s) :
    IsRefl (conjMat U s) := by
  obtain ⟨v, f, hfv, rfl⟩ := hs
  refine ⟨(U : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v,
    f ᵥ* (((U⁻¹ : GL (Fin 6) (ZMod 3))) : Matrix (Fin 6) (Fin 6) (ZMod 3)), ?_, ?_⟩
  · rw [← Matrix.dotProduct_mulVec]
    have h : (((U⁻¹ : GL (Fin 6) (ZMod 3))) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
        ((U : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, val_inv_mul, Matrix.one_mulVec]
    rw [h, hfv]
  · rw [conjMat_apply]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, val_mul_inv]
    congr 1
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private theorem conjMat_mulVec_e0_iff (U : GL (Fin 6) (ZMod 3))
    (s : Matrix (Fin 6) (Fin 6) (ZMod 3)) :
    conjMat U s *ᵥ ((U : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0) =
        (U : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0 ↔ s *ᵥ e0 = e0 := by
  constructor
  · intro h
    have h' := congrArg (fun z => (((U⁻¹ : GL (Fin 6) (ZMod 3))) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ z) h
    rw [conjMat_mulVec] at h'
    rwa [gl_inv_mulVec_mulVec, gl_inv_mulVec_mulVec] at h'
  · intro h
    rw [conjMat_mulVec, h]

private def d1 : Matrix (Fin 6) (Fin 6) (ZMod 3) := spMat (Equiv.swap 1 2) (fun _ => 1)

private def d2 : Matrix (Fin 6) (Fin 6) (ZMod 3) := spMat (Equiv.swap 2 3) (fun _ => 1)

private def d3 : Matrix (Fin 6) (Fin 6) (ZMod 3) := spMat (Equiv.swap 3 4) (fun _ => 1)

private def d4 : Matrix (Fin 6) (Fin 6) (ZMod 3) := spMat (Equiv.swap 4 5) (fun _ => 1)

private def d5 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  spMat (Equiv.swap 4 5) (fun i => if i = 4 ∨ i = 5 then -1 else 1)

def dRefl : Fin 5 → Matrix (Fin 6) (Fin 6) (ZMod 3) := ![d1, d2, d3, d4, d5]

private theorem d1_mem : d1 ∈ evenFix0 5 :=
  ⟨Equiv.swap 1 2, fun _ => 1, fun _ => Or.inl rfl, ⟨by decide, rfl, by simp⟩, rfl⟩

private theorem d2_mem : d2 ∈ evenFix0 5 :=
  ⟨Equiv.swap 2 3, fun _ => 1, fun _ => Or.inl rfl, ⟨by decide, rfl, by simp⟩, rfl⟩

private theorem d3_mem : d3 ∈ evenFix0 5 :=
  ⟨Equiv.swap 3 4, fun _ => 1, fun _ => Or.inl rfl, ⟨by decide, rfl, by simp⟩, rfl⟩

private theorem d4_mem : d4 ∈ evenFix0 5 :=
  ⟨Equiv.swap 4 5, fun _ => 1, fun _ => Or.inl rfl, ⟨by decide, rfl, by simp⟩, rfl⟩

private theorem d5_mem : d5 ∈ evenFix0 5 :=
  ⟨Equiv.swap 4 5, (fun i => if i = 4 ∨ i = 5 then -1 else 1),
    (by
      intro i
      by_cases h : i = 4 ∨ i = 5
      · simp only [h, if_true]
        trivial
      · simp only [h, if_false]
        trivial),
    ⟨by decide, by decide +kernel, by decide +kernel⟩, rfl⟩

private theorem d1_refl : IsRefl d1 :=
  ⟨(fun i => if i = 1 then 1 else if i = 2 then -1 else 0),
    (fun i => if i = 1 then -1 else if i = 2 then 1 else 0),
    by decide +kernel, by decide +kernel⟩

private theorem d2_refl : IsRefl d2 :=
  ⟨(fun i => if i = 2 then 1 else if i = 3 then -1 else 0),
    (fun i => if i = 2 then -1 else if i = 3 then 1 else 0),
    by decide +kernel, by decide +kernel⟩

private theorem d3_refl : IsRefl d3 :=
  ⟨(fun i => if i = 3 then 1 else if i = 4 then -1 else 0),
    (fun i => if i = 3 then -1 else if i = 4 then 1 else 0),
    by decide +kernel, by decide +kernel⟩

private theorem d4_refl : IsRefl d4 :=
  ⟨(fun i => if i = 4 then 1 else if i = 5 then -1 else 0),
    (fun i => if i = 4 then -1 else if i = 5 then 1 else 0),
    by decide +kernel, by decide +kernel⟩

private theorem d5_refl : IsRefl d5 :=
  ⟨(fun i => if i = 4 ∨ i = 5 then 1 else 0),
    (fun i => if i = 4 ∨ i = 5 then -1 else 0),
    by decide +kernel, by decide +kernel⟩

theorem dRefl_mem : ∀ k : Fin 5, dRefl k ∈ evenFix0 5 := by
  intro k
  fin_cases k <;> simp [dRefl, d1_mem, d2_mem, d3_mem, d4_mem, d5_mem]

theorem dRefl_refl : ∀ k : Fin 5, IsRefl (dRefl k) := by
  intro k
  fin_cases k <;> simp [dRefl, d1_refl, d2_refl, d3_refl, d4_refl, d5_refl]

theorem dRefl_forall_fixed :
    ∀ (y : Fin 6 → ZMod 3),
      (∀ k : Fin 5, dRefl k *ᵥ y = y ∨ dRefl k *ᵥ y = -y) →
      ∀ j : Fin 6, j ≠ 0 → y j = 0 := by
  decide +kernel

private def MatOf (Xg : Subgroup (GL (Fin 6) (ZMod 3)))
    (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  ∃ A : GL (Fin 6) (ZMod 3), A ∈ Xg ∧ (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = M

private theorem matOf_one {Xg : Subgroup (GL (Fin 6) (ZMod 3))} : MatOf Xg 1 :=
  ⟨1, Xg.one_mem, rfl⟩

private theorem matOf_mul {Xg : Subgroup (GL (Fin 6) (ZMod 3))}
    {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : MatOf Xg M) (hN : MatOf Xg N) :
    MatOf Xg (M * N) := by
  obtain ⟨A, hA, rfl⟩ := hM
  obtain ⟨B, hB, rfl⟩ := hN
  exact ⟨A * B, Xg.mul_mem hA hB, by rw [Units.val_mul]⟩

private theorem matOf_submonoid {Xg : Subgroup (GL (Fin 6) (ZMod 3))}
    {H L : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    (hH : ∀ M ∈ H, MatOf Xg M) (hL : ∀ M ∈ L, MatOf Xg M) :
    ∀ M ∈ Submonoid.closure (H ∪ L), MatOf Xg M := by
  intro M hM
  induction hM using Submonoid.closure_induction with
  | mem x hx => exact hx.elim (hH x) (hL x)
  | one => exact matOf_one
  | mul x y _ _ hx hy => exact matOf_mul hx hy

private theorem matOf_of_mem_H {H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    {Xg : Subgroup (GL (Fin 6) (ZMod 3))} (h : StabMatHyp 5 H Xg) {M}
    (hM : M ∈ H) : MatOf Xg M :=
  h.sub M hM

private theorem mem_H_of_matOf {H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    {Xg : Subgroup (GL (Fin 6) (ZMod 3))} (h : StabMatHyp 5 H Xg) {M}
    (hM : MatOf Xg M) (hcol : ∀ i : Fin 6, i ≠ 0 → M i 0 = 0) : M ∈ H := by
  obtain ⟨A, hA, rfl⟩ := hM
  exact h.norm A hA hcol

private theorem not_badOver {H L : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    {Xg : Subgroup (GL (Fin 6) (ZMod 3))} (h : StabMatHyp 5 H Xg)
    (hL : ∀ R ∈ L, MatOf Xg R) : ¬ BadOver H L := by
  rintro ⟨M, hMcl, hcol, hMH⟩
  have hM : MatOf Xg M :=
    matOf_submonoid (fun N hN => matOf_of_mem_H h hN) hL M hMcl
  exact hMH (mem_H_of_matOf h hM hcol)

private theorem exists_refl_outside {H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    {Xg : Subgroup (GL (Fin 6) (ZMod 3))} (hD5 : evenFix0 5 ⊆ H)
    (hH : ∀ M ∈ H, M *ᵥ e0 = e0 ∨ M *ᵥ e0 = -e0)
    (h : StabMatHyp 5 H Xg) :
    ∃ S : Xg, IsRefl ((S : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∧
      ((S : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∉ H := by
  obtain ⟨A, hA, i, hi, hAi⟩ := h.moves
  choose D hD hDmat using fun k : Fin 5 => h.sub (dRefl k) (hD5 (dRefl_mem k))
  let S : Fin 5 → GL (Fin 6) (ZMod 3) := fun k => A⁻¹ * D k * A
  have hS : ∀ k, S k ∈ Xg := fun k =>
    Xg.mul_mem (Xg.mul_mem (Xg.inv_mem hA) (hD k)) hA
  have hSmat : ∀ k, ((S k : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
      conjMat A⁻¹ (dRefl k) := by
    intro k
    rw [conjMat_apply, inv_inv]
    simp only [S, Units.val_mul, hDmat k]
  have hrefl : ∀ k, IsRefl (((S k : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3))) := by
    intro k
    rw [hSmat k]
    exact isRefl_conj (dRefl_refl k)
  have hex : ∃ k : Fin 5, ((S k : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) ∉ H := by
    by_contra hcon
    have hcon' : ∀ k : Fin 5, ((S k : GL (Fin 6) (ZMod 3)) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ H := by
      intro k
      by_contra hk
      exact hcon ⟨k, hk⟩
    have hyi : ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0) i ≠ 0 := by
      simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hAi
    have hfixed : ∀ k : Fin 5,
        dRefl k *ᵥ ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0) =
            (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0 ∨
          dRefl k *ᵥ ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0) =
            -((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0) := by
      intro k
      have hk := hH _ (hcon' k)
      rw [hSmat k] at hk
      have hconj : conjMat A (conjMat A⁻¹ (dRefl k)) = dRefl k := by
        simpa using conjMat_id A⁻¹ (dRefl k)
      rcases hk with hk | hk
      · left
        calc dRefl k *ᵥ ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0)
            = conjMat A (conjMat A⁻¹ (dRefl k)) *ᵥ
                ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0) := by rw [hconj]
          _ = (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
                (conjMat A⁻¹ (dRefl k) *ᵥ e0) := by rw [conjMat_mulVec]
          _ = (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0 := by rw [hk]
      · right
        calc dRefl k *ᵥ ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0)
            = conjMat A (conjMat A⁻¹ (dRefl k)) *ᵥ
                ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0) := by rw [hconj]
          _ = (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
                (conjMat A⁻¹ (dRefl k) *ᵥ e0) := by rw [conjMat_mulVec]
          _ = (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (-e0) := by rw [hk]
          _ = -((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0) := by
              rw [Matrix.mulVec_neg]
    exact hyi (dRefl_forall_fixed _ hfixed i hi)
  obtain ⟨k, hk⟩ := hex
  exact ⟨⟨S k, hS k⟩, hrefl k, hk⟩

private theorem matOf_conj {Xg : Subgroup (GL (Fin 6) (ZMod 3))}
    {A : GL (Fin 6) (ZMod 3)} (hA : A ∈ Xg)
    {s : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hs : MatOf Xg s) :
    MatOf Xg (conjMat A s) := by
  obtain ⟨S, hS, rfl⟩ := hs
  refine ⟨A * S * A⁻¹, Xg.mul_mem (Xg.mul_mem hA hS) (Xg.inv_mem hA), ?_⟩
  rw [conjMat_apply, Units.val_mul, Units.val_mul]

private theorem exists_good_of_refl_outside {H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    {Xg : Subgroup (GL (Fin 6) (ZMod 3))} {m : ℕ}
    {good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hK1 : ReflCover H good) (h : StabMatHyp 5 H Xg)
    (S : Xg) (hrefl : IsRefl ((S : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)))
    (hSH : ((S : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∉ H) :
    ∃ c : Fin m, MatOf Xg (good c) := by
  have hL : ∀ R ∈ ({((S : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3))} : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))),
      MatOf Xg R := by
    intro R hR
    rw [Set.mem_singleton_iff] at hR
    subst hR
    exact ⟨S, S.2, rfl⟩
  rcases hK1 _ hrefl with hH | hbad | ⟨c, hc⟩
  · exact absurd hH hSH
  · exact absurd hbad (not_badOver h hL)
  · obtain ⟨h0, hh0, hmul⟩ := hc
    obtain ⟨H0, hH0, hH0mat⟩ := h.sub h0 hh0
    refine ⟨c, ⟨H0 * S * H0⁻¹, Xg.mul_mem (Xg.mul_mem hH0 S.2) (Xg.inv_mem hH0), ?_⟩⟩
    rw [Units.val_mul, Units.val_mul]
    have hmul' : (good c) * ((↑H0 : GL (Fin 6) (ZMod 3)) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) =
        ((↑H0 : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
          ((S : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
      rw [hH0mat]
      exact hmul.symm
    rw [← hmul', mul_assoc, val_mul_inv, mul_one]

private theorem reflSet_eq_reflOf {H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    {Xg : Subgroup (GL (Fin 6) (ZMod 3))} {m : ℕ}
    {good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)} {c : Fin m}
    (hK1 : ReflCover H good) (hK12 : ReflMix H good)
    (h : StabMatHyp 5 H Xg) (hgood : MatOf Xg (good c)) :
    ReflSet H (good c) =
      {s : Matrix (Fin 6) (Fin 6) (ZMod 3) | IsRefl s ∧ MatOf Xg s} := by
  ext s
  constructor
  · intro hs
    obtain ⟨hrefl, hmem | hconj⟩ := hs
    · exact ⟨hrefl, matOf_of_mem_H h hmem⟩
    · obtain ⟨h0, hh0, hmul⟩ := hconj
      obtain ⟨H0, hH0, hH0mat⟩ := h.sub h0 hh0
      obtain ⟨G, hG, hGmat⟩ := hgood
      refine ⟨hrefl, ⟨H0⁻¹ * G * H0, Xg.mul_mem (Xg.mul_mem (Xg.inv_mem hH0) hG) hH0, ?_⟩⟩
      rw [Units.val_mul, Units.val_mul]
      have hmul' : ((↑H0 : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) * s =
          ((↑G : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
            ((↑H0 : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
        simpa [hH0mat, hGmat] using hmul
      calc ((↑(H0⁻¹) : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
            ((↑G : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
            ((↑H0 : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3))
          = ((↑(H0⁻¹) : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
              (((↑G : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
                ((↑H0 : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3))) := by
            noncomm_ring
        _ = ((↑(H0⁻¹) : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
              (((↑H0 : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) * s) := by
            rw [← hmul']
        _ = s := by rw [← mul_assoc, val_inv_mul, one_mul]
  · intro hs
    obtain ⟨hrefl, hmat⟩ := hs
    refine ⟨hrefl, ?_⟩
    rcases hK1 s hrefl with hH | hbad | ⟨c', hc'⟩
    · exact Or.inl hH
    · exact absurd hbad (not_badOver h (by
        intro R hR
        rw [Set.mem_singleton_iff] at hR
        subst hR
        exact hmat))
    · by_cases hcc : c' = c
      · subst hcc
        exact Or.inr hc'
      · exfalso
        refine not_badOver h ?_ (hK12 c' c hcc s hc')
        intro R hR
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
        rcases hR with rfl | rfl
        · exact hmat
        · exact hgood

private theorem closure_le_Xg {H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    {Xg : Subgroup (GL (Fin 6) (ZMod 3))} {m : ℕ}
    {good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)} {c : Fin m}
    (h : StabMatHyp 5 H Xg) (hgood : MatOf Xg (good c)) :
    Subgroup.closure {A : GL (Fin 6) (ZMod 3) |
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ H ∨
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = good c} ≤ Xg := by
  rw [Subgroup.closure_le]
  intro A hA
  rcases hA with hAH | hAg
  · obtain ⟨B, hB, hBA⟩ := h.sub A hAH
    have hBA' : B = A := Units.ext hBA
    rwa [← hBA']
  · obtain ⟨B, hB, hBg⟩ := hgood
    have hBA' : B = A := Units.ext (by rw [hBg, hAg])
    rwa [← hBA']

private theorem mem_closure_of_mem_Xg {H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))}
    {Xg : Subgroup (GL (Fin 6) (ZMod 3))} {m : ℕ}
    {good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)} {c : Fin m}
    (h : StabMatHyp 5 H Xg) (hgood : MatOf Xg (good c))
    (hK3 : ReflLines H good)
    (hRefl : ReflSet H (good c) = {s | IsRefl s ∧ MatOf Xg s})
    (hYX : Subgroup.closure {A : GL (Fin 6) (ZMod 3) |
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ H ∨
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = good c} ≤ Xg)
    {A : GL (Fin 6) (ZMod 3)} (hA : A ∈ Xg) :
    A ∈ Subgroup.closure {A : GL (Fin 6) (ZMod 3) |
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ H ∨
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = good c} := by
  let Y := Subgroup.closure {A : GL (Fin 6) (ZMod 3) |
    (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ H ∨
    (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = good c}
  let x : Fin 6 → ZMod 3 := (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0
  have he0 : e0 ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp [e0] at this
  have hx : x ≠ 0 := by
    simpa [x] using gl_mulVec_ne_zero A he0
  let Bset : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
    {s | s ∈ ReflSet H (good c) ∧ s *ᵥ e0 = e0}
  let Cset : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
    {s | s ∈ ReflSet H (good c) ∧ s *ᵥ x = x}
  have hmem : ∀ s, s ∈ ReflSet H (good c) → conjMat A s ∈ ReflSet H (good c) := by
    intro s hs
    rw [hRefl] at hs ⊢
    exact ⟨isRefl_conj hs.1, matOf_conj hA hs.2⟩
  have hmem_inv : ∀ s, s ∈ ReflSet H (good c) → conjMat A⁻¹ s ∈ ReflSet H (good c) := by
    intro s hs
    rw [hRefl] at hs ⊢
    exact ⟨isRefl_conj hs.1, matOf_conj (Xg.inv_mem hA) hs.2⟩
  have himage : conjMat A '' Bset = Cset := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨hmem t ht.1, (conjMat_mulVec_e0_iff A t).mpr ht.2⟩
    · intro hs
      have hid : conjMat A (conjMat A⁻¹ s) = s := by simpa using conjMat_id A⁻¹ s
      refine ⟨conjMat A⁻¹ s, ⟨hmem_inv s hs.1, ?_⟩, hid⟩
      have hx' : s *ᵥ x = x := hs.2
      refine (conjMat_mulVec_e0_iff A (conjMat A⁻¹ s)).mp ?_
      rwa [hid]
  have hcard : Cset.ncard = Bset.ncard := by
    rw [← himage, Set.ncard_image_of_injective Bset (conjMat_injective A)]
  obtain ⟨M, hMcl, hMx⟩ := hK3 c x hx hcard
  have hMY : MatOf Y M := by
    refine matOf_submonoid (Xg := Y) ?_ ?_ M hMcl
    · intro N hN
      obtain ⟨B, hB, hBN⟩ := h.sub N hN
      exact ⟨B, Subgroup.subset_closure (Or.inl (by rwa [hBN])), hBN⟩
    · intro N hN
      rw [Set.mem_singleton_iff] at hN
      subst hN
      obtain ⟨G, hG, hGg⟩ := hgood
      exact ⟨G, Subgroup.subset_closure (Or.inr hGg), hGg⟩
  obtain ⟨B, hBY, hBM⟩ := hMY
  have hBX : B ∈ Xg := hYX hBY
  have hBA_X : B⁻¹ * A ∈ Xg := Xg.mul_mem (Xg.inv_mem hBX) hA
  have hcol : ∀ i : Fin 6, i ≠ 0 →
      ((B⁻¹ * A : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) i 0 = 0 := by
    intro i hi
    have hv : ((B⁻¹ * A : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0 =
        e0 ∨ ((B⁻¹ * A : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e0 =
        -e0 := by
      rcases hMx with hMx | hMx
      · left
        rw [gl_mul_mulVec]
        change (((B⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x) = e0
        rw [← hMx, ← hBM, gl_inv_mulVec_mulVec]
      · right
        rw [gl_mul_mulVec]
        change (((B⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x) = -e0
        have hxM : x = -(M *ᵥ e0) := by rw [hMx, neg_neg]
        rw [hxM, Matrix.mulVec_neg, ← hBM, gl_inv_mulVec_mulVec]
    rcases hv with hv | hv
    · have := congrFun hv i
      simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_of_ne hi] using this
    · have := congrFun hv i
      simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_of_ne hi] using this
  have hmatH : ((B⁻¹ * A : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ H :=
    h.norm _ hBA_X hcol
  have hBXA_Y : B⁻¹ * A ∈ Y := Subgroup.subset_closure (Or.inl hmatH)
  have hAeq : B * (B⁻¹ * A) = A := by group
  rw [← hAeq]
  exact Y.mul_mem hBY hBXA_Y

theorem eq_closure_of_refl {H : Set (Matrix (Fin 6) (Fin 6) (ZMod 3))} {m : ℕ}
    {good : Fin m → Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hH : ∀ M ∈ H, M *ᵥ Pi.single 0 1 = Pi.single 0 1 ∨ M *ᵥ Pi.single 0 1 = -Pi.single 0 1)
    (hD5 : evenFix0 5 ⊆ H) (hK1 : ReflCover H good) (hK12 : ReflMix H good)
    (hK3 : ReflLines H good) {Xg : Subgroup (GL (Fin 6) (ZMod 3))} (h : StabMatHyp 5 H Xg) :
    ∃ c, Xg = Subgroup.closure
      {A : GL (Fin 6) (ZMod 3) | (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ H ∨
        (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = good c} := by
  have hH' : ∀ M ∈ H, M *ᵥ e0 = e0 ∨ M *ᵥ e0 = -e0 := by
    intro M hM
    simpa [e0] using hH M hM
  obtain ⟨S, hreflS, hSH⟩ := exists_refl_outside hD5 hH' h
  obtain ⟨c, hgood⟩ := exists_good_of_refl_outside hK1 h S hreflS hSH
  let Y := Subgroup.closure {A : GL (Fin 6) (ZMod 3) |
    (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ H ∨
    (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = good c}
  have hYX : Y ≤ Xg := closure_le_Xg h hgood
  have hRefl : ReflSet H (good c) = {s | IsRefl s ∧ MatOf Xg s} :=
    reflSet_eq_reflOf hK1 hK12 h hgood
  refine ⟨c, ?_⟩
  change Xg = Y
  exact le_antisymm (fun A hA => mem_closure_of_mem_Xg h hgood hK3 hRefl hYX hA) hYX

end CFSG.StandardType.FrameRoute.FS81

end
