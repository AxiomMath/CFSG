module

public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.SzN22Rig

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1549C
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace SzN23

section Matrices

variable {F : Type} [Field F]

@[expose] def uSL (a : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lSL (a : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def dSL (s : F) (hs : s ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![s, 0; 0, s⁻¹], by simp [Matrix.det_fin_two, hs]⟩

@[expose] def wSL [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two]; exact CharTwo.neg_eq (1 : F)⟩

theorem uSL_mul (a b : F) : uSL a * uSL b = uSL (a + b) := by
  apply Subtype.ext
  show (!![1, a; 0, 1] * !![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, a + b; 0, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

theorem uSL_zero : uSL (0 : F) = 1 := by
  apply Subtype.ext
  show (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1
  exact Matrix.one_fin_two.symm

theorem uSL_injective : Function.Injective (uSL : F → SpecialLinearGroup (Fin 2) F) := by
  intro a b h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [uSL] using this

theorem dSL_mul_uSL (s : F) (hs : s ≠ 0) (a : F) :
    dSL s hs * uSL a = uSL (s * s * a) * dSL s hs := by
  apply Subtype.ext
  show (!![s, 0; 0, s⁻¹] * !![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
    !![1, s * s * a; 0, 1] * !![s, 0; 0, s⁻¹]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  field_simp
  simp

theorem dSL_mul_dSL (s t : F) (hs : s ≠ 0) (ht : t ≠ 0) :
    dSL s hs * dSL t ht = dSL (s * t) (mul_ne_zero hs ht) := by
  apply Subtype.ext
  show (!![s, 0; 0, s⁻¹] * !![t, 0; 0, t⁻¹] : Matrix (Fin 2) (Fin 2) F) = !![s * t, 0; 0, (s * t)⁻¹]
  rw [Matrix.mul_fin_two]
  simp [mul_comm]

theorem dSL_one : dSL (1 : F) one_ne_zero = 1 := by
  apply Subtype.ext
  show (!![1, 0; 0, 1⁻¹] : Matrix (Fin 2) (Fin 2) F) = 1
  simp [Matrix.one_fin_two]

theorem dSL_injective (s t : F) (hs : s ≠ 0) (ht : t ≠ 0) (h : dSL s hs = dSL t ht) : s = t := by
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simpa [dSL] using this

theorem wSL_mul_dSL [CharP F 2] (s : F) (hs : s ≠ 0) :
    wSL * dSL s hs = dSL s⁻¹ (inv_ne_zero hs) * wSL := by
  apply Subtype.ext
  show (!![0, 1; 1, 0] * !![s, 0; 0, s⁻¹] : Matrix (Fin 2) (Fin 2) F) =
    !![s⁻¹, 0; 0, s⁻¹⁻¹] * !![0, 1; 1, 0]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

theorem wSL_mul_uSL_mul_wSL [CharP F 2] (a : F) : wSL * uSL a * wSL = lSL a := by
  apply Subtype.ext
  show (!![0, 1; 1, 0] * !![1, a; 0, 1] * !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) = !![1, 0; a, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

theorem uSL_one_mul_wSL_mul [CharP F 2] : uSL (1 : F) * wSL * uSL 1 = lSL 1 := by
  apply Subtype.ext
  show (!![1, 1; 0, 1] * !![0, 1; 1, 0] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  have h2 : (1 + 1 : F) = 0 := by simpa using CharTwo.add_self_eq_zero (1 : F)
  simp [h2]

theorem mem_unitriangular_two {g : SpecialLinearGroup (Fin 2) F} :
    g ∈ unitriangular 2 F ↔ ∃ a, g = uSL a := by
  rw [mem_unitriangular]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uSL, h2 0, h2 1, h1 1 0 (by decide)]
  · rintro ⟨a, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [uSL] at hij ⊢
    · fin_cases i <;> simp [uSL]

theorem uSL_mem (a : F) : uSL a ∈ unitriangular 2 F := mem_unitriangular_two.mpr ⟨a, rfl⟩

theorem dSL_mem_normalizer (s : F) (hs : s ≠ 0) :
    dSL s hs ∈ Subgroup.normalizer ((unitriangular 2 F : Subgroup (SpecialLinearGroup (Fin 2) F)) :
      Set (SpecialLinearGroup (Fin 2) F)) := by
  have key : ∀ a : F, dSL s hs * uSL a * (dSL s hs)⁻¹ = uSL (s * s * a) := fun a => by
    rw [dSL_mul_uSL, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨a, rfl⟩ := mem_unitriangular_two.mp hg
    rw [key]
    exact uSL_mem _
  · intro hg
    obtain ⟨b, hb⟩ := mem_unitriangular_two.mp hg
    have hsq : s * s ≠ 0 := mul_ne_zero hs hs
    have : g = uSL (b / (s * s)) := by
      have h1 : g = (dSL s hs)⁻¹ * (dSL s hs * g * (dSL s hs)⁻¹) * dSL s hs := by group
      rw [h1, hb]
      have h2 : dSL s hs * uSL (b / (s * s)) * (dSL s hs)⁻¹ = uSL b := by
        rw [key]; congr 1; field_simp
      rw [← h2]
      group
    rw [this]
    exact uSL_mem _

end Matrices

section Standard

variable {F : Type} [Field F]

theorem sl_mul_apply (g h : SpecialLinearGroup (Fin 2) F) (i j : Fin 2) :
    ((g * h : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      (g : Matrix (Fin 2) (Fin 2) F) i 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 j +
        (g : Matrix (Fin 2) (Fin 2) F) i 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem uSL_mul_apply_zero (a : F) (g : SpecialLinearGroup (Fin 2) F) (j : Fin 2) :
    ((uSL a * g : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 j =
      (g : Matrix (Fin 2) (Fin 2) F) 0 j + a * (g : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [sl_mul_apply]
  simp [uSL]

theorem mul_uSL_apply_zero (g : SpecialLinearGroup (Fin 2) F) (a : F) (i : Fin 2) :
    ((g * uSL a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 0 =
      (g : Matrix (Fin 2) (Fin 2) F) i 0 := by
  rw [sl_mul_apply]
  simp [uSL]

theorem mul_uSL_apply_one (g : SpecialLinearGroup (Fin 2) F) (a : F) (i : Fin 2) :
    ((g * uSL a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 1 =
      (g : Matrix (Fin 2) (Fin 2) F) i 0 * a + (g : Matrix (Fin 2) (Fin 2) F) i 1 := by
  rw [sl_mul_apply]
  simp [uSL]

theorem eq_wSL [CharP F 2] (g : SpecialLinearGroup (Fin 2) F)
    (hx : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0) (ht : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    (heq : uSL (1 : F) * g * uSL 1 = g * uSL 1 * g) : g = wSL := by
  have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  have hdet := g.2
  rw [Matrix.det_fin_two, hx, ht] at hdet
  have e00 := congrArg (fun m : SpecialLinearGroup (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F) 0 0) heq
  have e01 := congrArg (fun m : SpecialLinearGroup (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F) 0 1) heq
  rw [mul_uSL_apply_zero, uSL_mul_apply_zero, sl_mul_apply, mul_uSL_apply_zero,
    mul_uSL_apply_one] at e00
  rw [mul_uSL_apply_one, uSL_mul_apply_zero, uSL_mul_apply_zero, sl_mul_apply, mul_uSL_apply_zero,
    mul_uSL_apply_one] at e01
  rw [hx] at e00 e01
  rw [ht] at e01
  have hyz : (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    linear_combination (-1 : F) * hdet + (-1 : F) * h2
  have hz : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by linear_combination e00 + hyz
  have hy : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by linear_combination e01 - hz - h2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSL, hx, ht, hy, hz]

theorem diag_entries_zero [CharP F 2] (hF : ∃ s : F, s ≠ 0 ∧ s ≠ 1) (g : SpecialLinearGroup (Fin 2) F)
    (h : ∀ (s : F) (hs : s ≠ 0), g * dSL s hs = dSL s⁻¹ (inv_ne_zero hs) * g) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  obtain ⟨s, hs0, hs1⟩ := hF
  have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  have e := h s hs0
  have e00 := congrArg (fun m : SpecialLinearGroup (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F) 0 0) e
  have e11 := congrArg (fun m : SpecialLinearGroup (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F) 1 1) e
  rw [sl_mul_apply, sl_mul_apply] at e00 e11
  simp [dSL] at e00 e11
  have hne : s - s⁻¹ ≠ 0 := by
    intro hsub
    have hss : s * s = 1 := by
      have : s = s⁻¹ := sub_eq_zero.mp hsub
      field_simp at this
      linear_combination this
    have : (s - 1) * (s - 1) = 0 := by linear_combination hss - (s - 1) * h2
    exact hs1 (sub_eq_zero.mp (mul_self_eq_zero.mp this))
  constructor
  · have : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (s - s⁻¹) = 0 := by linear_combination e00
    exact (mul_eq_zero.mp this).resolve_right hne
  · have : (g : Matrix (Fin 2) (Fin 2) F) 1 1 * (s - s⁻¹) = 0 := by linear_combination -e11
    exact (mul_eq_zero.mp this).resolve_right hne

theorem sl2_rigid_std [Finite F] [CharP F 2] (hF : ∃ s : F, s ≠ 0 ∧ s ≠ 1)
    (α : SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F)
    (h1 : ∀ a : F, ∃ b : F, α (uSL a) = uSL b)
    (h2 : ∀ (s : F) (hs : s ≠ 0), ∃ c : F, α (dSL s hs) = uSL c * dSL s hs)
    (h3 : ∀ m, α (α (α m)) = m)
    (h4 : ∀ μ : F, μ ≠ 0 → μ ≠ 1 → μ ^ 3 = 1 → False) : ∀ m, α m = m := by
  have hchar : ringChar F = 2 := ringChar.eq F 2
  have h2' : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  choose ψ hψ using h1
  choose c hc using h2
  have hadd : ∀ a b, ψ (a + b) = ψ a + ψ b := by
    intro a b
    apply uSL_injective
    rw [← hψ, ← uSL_mul, map_mul, hψ, hψ, uSL_mul]
  have hψ0 : ψ 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact add_left_cancel (a := ψ 0) (by rw [add_zero]; exact this.symm)
  have hscale : ∀ (s : F) (hs : s ≠ 0) (a : F), ψ (s * s * a) = s * s * ψ a := by
    intro s hs a
    have e3 : uSL (c s hs + s * s * ψ a) * dSL s hs = uSL (ψ (s * s * a) + c s hs) * dSL s hs := by
      calc uSL (c s hs + s * s * ψ a) * dSL s hs
          = uSL (c s hs) * (uSL (s * s * ψ a) * dSL s hs) := by rw [← uSL_mul, mul_assoc]
        _ = uSL (c s hs) * (dSL s hs * uSL (ψ a)) := by rw [dSL_mul_uSL]
        _ = (uSL (c s hs) * dSL s hs) * uSL (ψ a) := by rw [mul_assoc]
        _ = α (dSL s hs) * α (uSL a) := by rw [hc, hψ]
        _ = α (dSL s hs * uSL a) := by rw [map_mul]
        _ = α (uSL (s * s * a) * dSL s hs) := by rw [dSL_mul_uSL]
        _ = α (uSL (s * s * a)) * α (dSL s hs) := by rw [map_mul]
        _ = uSL (ψ (s * s * a)) * (uSL (c s hs) * dSL s hs) := by rw [hψ, hc]
        _ = uSL (ψ (s * s * a) + c s hs) * dSL s hs := by rw [← mul_assoc, uSL_mul]
    have e4 := uSL_injective (mul_right_cancel e3)
    linear_combination -e4
  have hlin : ∀ t a : F, ψ (t * a) = t * ψ a := by
    intro t a
    by_cases ht : t = 0
    · rw [ht, zero_mul, hψ0, zero_mul]
    · obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hchar t
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact ht (by rw [hs, mul_zero])
      rw [hs]
      exact hscale s hs0 a
  have hψmul : ∀ a, ψ a = a * ψ 1 := fun a => by
    have := hlin a 1
    rwa [mul_one] at this
  set μ := ψ 1 with hμ
  have hμ3 : μ ^ 3 = 1 := by
    have e := h3 (uSL 1)
    rw [hψ, hψ, hψ] at e
    have e' := uSL_injective e
    have : ψ (ψ (ψ 1)) = μ ^ 3 := by
      rw [hψmul (ψ (ψ 1)), hψmul (ψ 1)]
      simp only [← hμ]
      ring
    rw [← this]
    exact e'
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0] at hμ3
    norm_num at hμ3
  have hμ1 : μ = 1 := by
    by_contra hne
    exact h4 μ hμ0 hne hμ3
  have hid : ∀ a, α (uSL a) = uSL a := fun a => by
    rw [hψ, hψmul a, hμ1, mul_one]
  have hdfix : ∀ (s : F) (hs : s ≠ 0), α (dSL s hs) = dSL s hs := by
    intro s hs
    have hd := hc s hs
    have hsq : α (α (dSL s hs)) = dSL s hs := by
      rw [hd, map_mul, hid, hd, ← mul_assoc, uSL_mul, CharTwo.add_self_eq_zero, uSL_zero, one_mul]
    have := h3 (dSL s hs)
    rw [hsq] at this
    exact this
  have hw : α wSL = wSL := by
    set g := α wSL with hg
    have hconj : ∀ (s : F) (hs : s ≠ 0), g * dSL s hs = dSL s⁻¹ (inv_ne_zero hs) * g := by
      intro s hs
      have e := congrArg α (wSL_mul_dSL s hs)
      rw [map_mul, map_mul, hdfix, hdfix] at e
      exact e
    obtain ⟨hx, ht⟩ := diag_entries_zero hF g hconj
    refine eq_wSL g hx ht ?_
    have e1 := congrArg α (uSL_one_mul_wSL_mul (F := F))
    have e2 := congrArg α (wSL_mul_uSL_mul_wSL (1 : F))
    rw [map_mul, map_mul, hid] at e1 e2
    exact e1.trans e2.symm
  have hl : ∀ a : F, α (lSL a) = lSL a := fun a => by
    rw [← wSL_mul_uSL_mul_wSL, map_mul, map_mul, hid, hw]
  have hel : ∀ (i j : Fin 2) (hij : i ≠ j) (c : F),
      α (SpecialLinearGroup.transvection hij c) = SpecialLinearGroup.transvection hij c := by
    intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · have : SpecialLinearGroup.transvection hij c = uSL c := by
        apply Subtype.ext
        rw [CFSG.LinearGroups.coe_transvection]
        ext a b
        fin_cases a <;> fin_cases b <;> simp [uSL]
      rw [this, hid]
    · have : SpecialLinearGroup.transvection hij c = lSL c := by
        apply Subtype.ext
        rw [CFSG.LinearGroups.coe_transvection]
        ext a b
        fin_cases a <;> fin_cases b <;> simp [lSL]
      rw [this, hl]
    · exact absurd rfl hij
  intro m
  have hmem : m ∈ MonoidHom.eqLocus (α : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F)
      (MonoidHom.id _) := by
    have htop := CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := F)
    have hm : m ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 2 F) := by
      rw [htop]
      trivial
    refine (Subgroup.closure_le _).mpr ?_ hm
    rintro _ ⟨i, j, hij, c, rfl⟩
    exact hel i j hij c
  exact hmem

end Standard

section Sylow

variable {F : Type} [Field F]

theorem dSL_congr {s t : F} (hst : s = t) (hs : s ≠ 0) (ht : t ≠ 0) : dSL s hs = dSL t ht := by
  subst hst
  rfl

theorem sl2_rigid_sylow [Finite F] [CharP F 2] (hF : ∃ s : F, s ≠ 0 ∧ s ≠ 1)
    {Ŝ : Subgroup (SpecialLinearGroup (Fin 2) F)} (hŜ : IsSylowTwoOf Ŝ ⊤)
    (α : SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F)
    (h1 : ∀ g ∈ Ŝ, α g ∈ Ŝ)
    (h2 : ∀ b ∈ Subgroup.normalizer (Ŝ : Set (SpecialLinearGroup (Fin 2) F)), α b * b⁻¹ ∈ Ŝ)
    (h3 : ∀ m, α (α (α m)) = m)
    (h4 : ∀ b ∈ Subgroup.normalizer (Ŝ : Set (SpecialLinearGroup (Fin 2) F)), orderOf b ≠ 3) :
    ∀ m, α m = m := by
  have hU : IsSylowTwoOf (unitriangular 2 F) ⊤ := SzN2.isSylowTwoOf_unitriangular (by norm_num)
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hU hŜ
  have hmem : ∀ x, x ∈ Ŝ ↔ g⁻¹ * x * g ∈ unitriangular 2 F := by
    intro x
    rw [hg]
    constructor
    · rintro ⟨u, hu, rfl⟩
      show g⁻¹ * (g * u * g⁻¹) * g ∈ unitriangular 2 F
      rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
      exact hu
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  let β : SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F :=
    (MulAut.conj g).trans (α.trans (MulAut.conj g⁻¹))
  have hβ : ∀ x, β x = g⁻¹ * α (g * x * g⁻¹) * g := fun x => by
    simp [β, MulAut.conj_apply]
  have hgU : ∀ u ∈ unitriangular 2 F, g * u * g⁻¹ ∈ Ŝ := fun u hu =>
    (hmem _).mpr (by simpa [mul_assoc] using hu)
  have hβU : ∀ u ∈ unitriangular 2 F, β u ∈ unitriangular 2 F := fun u hu => by
    rw [hβ]
    exact (hmem _).mp (h1 _ (hgU u hu))
  have hdN : ∀ (s : F) (hs : s ≠ 0),
      g * dSL s hs * g⁻¹ ∈ Subgroup.normalizer (Ŝ : Set (SpecialLinearGroup (Fin 2) F)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem, hmem]
    have hd := (Subgroup.mem_normalizer_iff.mp (dSL_mem_normalizer s hs) (g⁻¹ * x * g))
    have e : g⁻¹ * (g * dSL s hs * g⁻¹ * x * (g * dSL s hs * g⁻¹)⁻¹) * g =
        dSL s hs * (g⁻¹ * x * g) * (dSL s hs)⁻¹ := by group
    rw [e]
    exact hd
  refine fun m => ?_
  have key := sl2_rigid_std hF β
    (fun a => by
      obtain ⟨b, hb⟩ := mem_unitriangular_two.mp (hβU _ (uSL_mem a))
      exact ⟨b, hb⟩)
    (fun s hs => by
      have h2' := h2 _ (hdN s hs)
      have hmem2 := (hmem _).mp h2'
      have : β (dSL s hs) * (dSL s hs)⁻¹ ∈ unitriangular 2 F := by
        rw [hβ]
        have e : g⁻¹ * (α (g * (dSL s hs) * g⁻¹) * (g * dSL s hs * g⁻¹)⁻¹) * g =
            g⁻¹ * α (g * (dSL s hs) * g⁻¹) * g * (dSL s hs)⁻¹ := by group
        rw [← e]
        exact hmem2
      obtain ⟨c, hc⟩ := mem_unitriangular_two.mp this
      exact ⟨c, by rw [← hc]; group⟩)
    (fun x => by
      have e1 : ∀ y, g * β y * g⁻¹ = α (g * y * g⁻¹) := fun y => by rw [hβ]; group
      calc β (β (β x)) = g⁻¹ * (g * β (β (β x)) * g⁻¹) * g := by group
        _ = g⁻¹ * α (g * β (β x) * g⁻¹) * g := by rw [e1]
        _ = g⁻¹ * α (α (g * β x * g⁻¹)) * g := by rw [e1]
        _ = g⁻¹ * α (α (α (g * x * g⁻¹))) * g := by rw [e1]
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [h3]
        _ = x := by group)
    (fun μ hμ0 hμ1 hμ3 => by
      have hd3 : dSL μ hμ0 ^ 3 = 1 := by
        have h3' : μ * μ * μ = 1 := by rw [← hμ3]; ring
        rw [pow_succ, pow_two, dSL_mul_dSL, dSL_mul_dSL, dSL_congr h3' _ one_ne_zero, dSL_one]
      have hd1 : dSL μ hμ0 ≠ 1 := fun h =>
        hμ1 (dSL_injective μ 1 hμ0 one_ne_zero (h.trans dSL_one.symm))
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hord : orderOf (dSL μ hμ0) = 3 := orderOf_eq_prime hd3 hd1
      have hco := MulEquiv.orderOf_eq (MulAut.conj g) (dSL μ hμ0)
      rw [MulAut.conj_apply] at hco
      exact h4 _ (hdN μ hμ0) (by rw [hco]; exact hord)) (g⁻¹ * m * g)
  rw [hβ] at key
  have e : g * (g⁻¹ * m * g) * g⁻¹ = m := by group
  rw [e] at key
  exact mul_left_cancel (mul_right_cancel key)

end Sylow

section Glue

variable {Ω : Type} [Group Ω]

theorem krig_of_sl2 {K : Subgroup Ω} {F : Type} [Field F] [Finite F] {e : ℕ}
    (hF : Nat.card F = 2 ^ e) (he : 2 ≤ e) (iso : ↥K ≃* ↥(StatedSL 2 F)) : SzN22.KRig K := by
  intro S z hS hzK hzS hz3 hno hcomm
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFin : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ e := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hcp : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hex : ∃ s : F, s ≠ 0 ∧ s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have h1 := Finset.card_le_card hsub
    have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, hcard] at h1
    have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  let Φ : ↥K ≃* SpecialLinearGroup (Fin 2) F :=
    iso.trans (specialLinearGroupEquivStatedSL 2 F).symm
  let σ : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨z, hzK⟩
  have hσ : ∀ k : ↥K, ((σ k : ↥K) : Ω) = z * (k : Ω) * z⁻¹ := fun k => rfl
  have hσ3 : ∀ k, σ (σ (σ k)) = k := by
    have hz3' : (⟨z, hzK⟩ : ↥(Subgroup.normalizer (K : Set Ω))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hz3)
    have h' : σ ^ 3 = 1 := by
      show (Subgroup.normalizerMonoidHom K ⟨z, hzK⟩) ^ 3 = 1
      rw [← map_pow, hz3', map_one]
    intro k
    have := congrArg (fun φ : MulAut ↥K => φ k) h'
    simpa [pow_succ, MulAut.mul_apply] using this
  let α : SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F :=
    Φ.symm.trans (σ.trans Φ)
  have hα : ∀ k : ↥K, α (Φ k) = Φ (σ k) := fun k => by
    show Φ (σ (Φ.symm (Φ k))) = Φ (σ k)
    rw [MulEquiv.symm_apply_apply]
  have hSt : IsSylowTwoOf (S.subgroupOf K) ⊤ := (SBd8.isSylowTwoOf_iff_subgroupOf hS.1).mp hS
  have hŜ : IsSylowTwoOf ((S.subgroupOf K).map Φ.toMonoidHom) ⊤ :=
    GoldS146R.isSylowTwoOf_top_map_equiv Φ hSt
  have hnorm : ∀ b ∈ Subgroup.normalizer
      (((S.subgroupOf K).map Φ.toMonoidHom : Subgroup (SpecialLinearGroup (Fin 2) F)) :
        Set (SpecialLinearGroup (Fin 2) F)),
      ((Φ.symm b : ↥K) : Ω) ∈ Subgroup.normalizer (S : Set Ω) := by
    intro b hb
    rw [← Subgroup.map_equiv_normalizer_eq] at hb
    obtain ⟨k, hk, hkb⟩ := hb
    have : Φ.symm b = k := by rw [← hkb]; simp
    rw [this]
    exact (SBd8.mem_normalizer_subgroupOf_iff hS.1 k).mp hk
  have h1 : ∀ g ∈ (S.subgroupOf K).map Φ.toMonoidHom, α g ∈ (S.subgroupOf K).map Φ.toMonoidHom := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨σ k, ?_, (hα k).symm⟩
    show σ k ∈ S.subgroupOf K
    rw [Subgroup.mem_subgroupOf, hσ]
    exact (Subgroup.mem_normalizer_iff.mp hzS _).mp (Subgroup.mem_subgroupOf.mp hk)
  have h2 : ∀ b ∈ Subgroup.normalizer
      (((S.subgroupOf K).map Φ.toMonoidHom : Subgroup (SpecialLinearGroup (Fin 2) F)) :
        Set (SpecialLinearGroup (Fin 2) F)),
      α b * b⁻¹ ∈ (S.subgroupOf K).map Φ.toMonoidHom := by
    intro b hb
    obtain ⟨k, rfl⟩ := Φ.surjective b
    have hk := hnorm _ hb
    rw [MulEquiv.symm_apply_apply] at hk
    refine ⟨σ k * k⁻¹, ?_, ?_⟩
    · show σ k * k⁻¹ ∈ S.subgroupOf K
      rw [Subgroup.mem_subgroupOf]
      have := hcomm (k : Ω) ⟨hk, k.2⟩
      simpa [hσ] using this
    · simp [hα]
  have h3 : ∀ m, α (α (α m)) = m := by
    intro m
    obtain ⟨k, rfl⟩ := Φ.surjective m
    rw [hα, hα, hα, hσ3]
  have h4 : ∀ b ∈ Subgroup.normalizer
      (((S.subgroupOf K).map Φ.toMonoidHom : Subgroup (SpecialLinearGroup (Fin 2) F)) :
        Set (SpecialLinearGroup (Fin 2) F)), orderOf b ≠ 3 := by
    intro b hb
    obtain ⟨k, rfl⟩ := Φ.surjective b
    have hk := hnorm _ hb
    rw [MulEquiv.symm_apply_apply] at hk
    have := hno (k : Ω) ⟨hk, k.2⟩
    rwa [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq Φ k] at this
  have key := sl2_rigid_sylow hex hŜ α h1 h2 h3 h4
  refine ⟨1, K.one_mem, fun n hn => ?_⟩
  have h5 := key (Φ ⟨n, hn⟩)
  rw [hα] at h5
  have h6 := congrArg (fun k : ↥K => (k : Ω)) (Φ.injective h5)
  simpa [hσ] using h6

end Glue
