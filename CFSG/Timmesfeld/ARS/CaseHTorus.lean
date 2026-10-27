module

public import CFSG.Timmesfeld.ARS.CaseHAdj

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section SL3

variable {F : Type} [Field F]

theorem diag_mul_tv {D : SpecialLinearGroup (Fin 3) F} {d : Fin 3 → F}
    (hD : D.1 = Matrix.diagonal d) (hd : ∀ i, d i ≠ 0) {i j : Fin 3} (hij : i ≠ j) (u : F) :
    D * SpecialLinearGroup.transvection hij u =
      SpecialLinearGroup.transvection hij (d i * u * (d j)⁻¹) * D := by
  have hdj := hd j
  apply Subtype.ext
  rw [val_mul3, val_mul3, val_tv, val_tv, hD]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [this]
  · by_cases hia : i = a <;> by_cases hjb : j = b
    · subst hia hjb
      simp [hab, hdj]
    all_goals simp [hab, hia, hjb]

@[expose] noncomputable def diag3' (l : Fˣ) : SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![1, ((l⁻¹ : Fˣ) : F), (l : F)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

@[expose] def dvec' (l : Fˣ) : Fin 3 → F := ![1, ((l⁻¹ : Fˣ) : F), (l : F)]

theorem dvec'_ne_zero (l : Fˣ) (i : Fin 3) : dvec' l i ≠ 0 := by
  fin_cases i <;> simp [dvec']

theorem diag3'_mul_tv {i j : Fin 3} (hij : i ≠ j) (l : Fˣ) (u : F) :
    diag3' l * SpecialLinearGroup.transvection hij u =
      SpecialLinearGroup.transvection hij (dvec' l i * u * (dvec' l j)⁻¹) * diag3' l :=
  diag_mul_tv rfl (dvec'_ne_zero l) hij u

theorem diag3'_mul (l l' : Fˣ) :
    diag3' l * diag3' l' = (diag3' (l * l') : SpecialLinearGroup (Fin 3) F) := by
  apply Subtype.ext
  rw [val_mul3]
  simp only [diag3', Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

theorem diag3'_one : (diag3' 1 : SpecialLinearGroup (Fin 3) F) = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ = (1 : Matrix (Fin 3) (Fin 3) F)
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diag3'_inv (l : Fˣ) : (diag3' l)⁻¹ = (diag3' l⁻¹ : SpecialLinearGroup (Fin 3) F) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, diag3'_mul, inv_mul_cancel, diag3'_one]

theorem conjSub_rootSubgroup_diag3' {i j : Fin 3} (hij : i ≠ j) (l : Fˣ) :
    conjSub (SpecialLinear.rootSubgroup 2 F hij) (diag3' l) =
      SpecialLinear.rootSubgroup 2 F hij := by
  have key : ∀ (l : Fˣ) (x : SpecialLinearGroup (Fin 3) F),
      x ∈ SpecialLinear.rootSubgroup 2 F hij →
        diag3' l * x * (diag3' l)⁻¹ ∈ SpecialLinear.rootSubgroup 2 F hij := by
    intro l x hx
    obtain ⟨u, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij x).1 hx
    rw [diag3'_mul_tv, mul_inv_cancel_right]
    exact SpecialLinear.transvection_mem_rootSubgroup hij _
  refine conjSub_eq_self_iff.2 (Subgroup.mem_normalizer_iff.2 fun x => ⟨key l x, fun hx => ?_⟩)
  have := key l⁻¹ _ hx
  rwa [← diag3'_inv, inv_inv, show (diag3' l)⁻¹ * (diag3' l * x * (diag3' l)⁻¹) * diag3' l = x by
    group] at this

theorem diag3'_eq [CharP F 2] (l : Fˣ) :
    diag3' l = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) ((l⁻¹ : Fˣ) : F) *
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (l : F) *
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) ((l⁻¹ : Fˣ) : F) *
      (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1 *
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) 1 *
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : F) = 1 := by
    rw [show (3 : F) = 2 + 1 by norm_num, h2, zero_add]
  have h4 : (4 : F) = 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num, h2, zero_mul]
  have h6 : (6 : F) = 0 := by
    rw [show (6 : F) = 2 * 3 by norm_num, h2, zero_mul]
  apply Subtype.ext
  simp only [val_mul3, val_tv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag3', Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] <;>
    ring_nf <;> simp [h2, h3, h4, h6]

end SL3

variable {A A₀ P P' : Subgroup G}

namespace Setup

variable (S : Setup R A A₀ P P')

theorem proj_conj_of {g₀ : G} (hA : g₀ ∈ Subgroup.normalizer (A : Set G)) (hP : conjSub P g₀ = P)
    (h5 : conjSub (shortRoot R P' ⁅A₀, P⁆ A) g₀ = shortRoot R P' ⁅A₀, P⁆ A)
    (h3 : conjSub (shortRoot R P ⁅A₀, P'⁆ A) g₀ = shortRoot R P ⁅A₀, P'⁆ A)
    (hP' : conjSub P' g₀ = P') (g : ↥(M R A)) (hg : g₀ * g * g₀⁻¹ ∈ M R A) :
    ((S.proj ⟨g₀ * g * g₀⁻¹, hg⟩).1 : G) = g₀ * (S.proj g).1 * g₀⁻¹ ∧
      ((S.proj ⟨g₀ * g * g₀⁻¹, hg⟩).2.1 : G) = g₀ * (S.proj g).2.1 * g₀⁻¹ ∧
      ((S.proj ⟨g₀ * g * g₀⁻¹, hg⟩).2.2.1 : G) = g₀ * (S.proj g).2.2.1 * g₀⁻¹ ∧
      ((S.proj ⟨g₀ * g * g₀⁻¹, hg⟩).2.2.2 : G) = g₀ * (S.proj g).2.2.2 * g₀⁻¹ := by
  rw [S.proj_conj hA g]
  have m1 : g₀ * (S.proj g).1 * g₀⁻¹ ∈ P := by
    have := conj_mem_conjSub g₀ (S.proj g).1.2
    rwa [hP] at this
  have m2 : g₀ * (S.proj g).2.1 * g₀⁻¹ ∈ shortRoot R P' ⁅A₀, P⁆ A := by
    have := conj_mem_conjSub g₀ (S.proj g).2.1.2
    rwa [h5] at this
  have m3 : g₀ * (S.proj g).2.2.1 * g₀⁻¹ ∈ shortRoot R P ⁅A₀, P'⁆ A := by
    have := conj_mem_conjSub g₀ (S.proj g).2.2.1.2
    rwa [h3] at this
  have m4 : g₀ * (S.proj g).2.2.2 * g₀⁻¹ ∈ P' := by
    have := conj_mem_conjSub g₀ (S.proj g).2.2.2.2
    rwa [hP'] at this
  rw [S.proj_P m1, S.proj_U5 m2, S.proj_U3 m3, S.proj_P' m4]
  simp

end Setup

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E)

@[expose] noncomputable def d' (l : Fˣ) : G := c.ψ (diag3' l)

theorem conjSub_d' {i j : Fin 3} (hij : i ≠ j) {X : Subgroup G}
    (hX : (SpecialLinear.rootSubgroup 2 F hij).map c.ψ = X) (l : Fˣ) : conjSub X (c.d' l) = X := by
  rw [← hX, d', conjSub_map, conjSub_rootSubgroup_diag3']

theorem d'_conj_x6 (l : Fˣ) (u : F) : c.d' l * c.x6 u * (c.d' l)⁻¹ = c.x6 (l * u) := by
  rw [d', x6, x6, ← map_mul, ← map_inv, ← map_mul, diag3'_mul_tv, mul_inv_cancel_right]
  congr 2
  simp [dvec', mul_comm]

theorem d'_conj_x2 (l : Fˣ) (u : F) :
    c.d' l * c.x2 u * (c.d' l)⁻¹ = c.x2 ((l⁻¹ : Fˣ) * (l⁻¹ : Fˣ) * u) := by
  rw [d', x2, x2, ← map_mul, ← map_inv, ← map_mul, diag3'_mul_tv, mul_inv_cancel_right]
  congr 2
  simp [dvec']
  ring

theorem d'_mem [CharP F 2] (l : Fˣ) : c.d' l ∈ P' ⊔ ⁅A₀, P⁆ := by
  rw [d', diag3'_eq]
  simp only [map_mul]
  have ha := fun u => Subgroup.mem_sup_left (S := P') (T := ⁅A₀, P⁆) (psi_tv_mem _ c.hψP' u)
  have hb := fun u => Subgroup.mem_sup_right (S := P') (T := ⁅A₀, P⁆) (psi_tv_mem _ c.hψQ u)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (ha _) (hb _)) (ha _))
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (ha _) (hb _)) (ha _))

theorem d'_conj_U5 [CharP F 2] (l : Fˣ) {y : G} (hy : y ∈ shortRoot R P' ⁅A₀, P⁆ A) :
    c.d' l * y * (c.d' l)⁻¹ = y := by
  rw [Subgroup.mem_centralizer_iff.1 hy.1 _ (c.d'_mem l), mul_inv_cancel_right]

theorem conjSub_U5_d' (l : Fˣ) :
    conjSub (shortRoot R P' ⁅A₀, P⁆ A) (c.d' l) = shortRoot R P' ⁅A₀, P⁆ A := by
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_d' _ c.hψP' l, c.conjSub_d' _ c.hψQ l,
    c.conjSub_d' _ c.hψA l]

theorem conjSub_U3_d' (l : Fˣ) :
    conjSub (shortRoot R P ⁅A₀, P'⁆ A) (c.d' l) = shortRoot R P ⁅A₀, P'⁆ A := by
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_d' _ c.hψP l, c.conjSub_d' _ c.hψQ' l,
    c.conjSub_d' _ c.hψA l]

theorem conjSub_Xa_d' (l : Fˣ) :
    conjSub (shortRoot R A A₀ P') (c.d' l) = shortRoot R A A₀ P' := by
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_d' _ c.hψA l, c.conjSub_d' _ c.hψA₀ l,
    c.conjSub_d' _ c.hψP' l]

theorem d'_conj_x1 [CharP F 2] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
    (l : Fˣ) (s : E) : c.d' l * c.x1 s * (c.d' l)⁻¹ = c.x1 (e (l⁻¹ : Fˣ) * s) := by
  have hmem : c.d' l * c.x1 s * (c.d' l)⁻¹ ∈ shortRoot R A A₀ P' :=
    c.conjSub_Xa_d' l ▸ conj_mem_conjSub _ (c.x1_mem s)
  obtain ⟨t, ht⟩ := exists_upPar_eq c.hφU le_sup_left hmem
  change c.x1 t = _ at ht
  have h6 : c.d' l * c.x6 1 * (c.d' l)⁻¹ ∈ P := by
    rw [c.d'_conj_x6]
    exact c.x6_mem _
  have key : c.c5 s 1 = c.c5 (e l * t) 1 :=
    calc c.c5 s 1 = c.d' l * c.c5 s 1 * (c.d' l)⁻¹ := (c.d'_conj_U5 l (c.c5_mem s 1)).symm
      _ = cxy S (c.d' l * c.x1 s * (c.d' l)⁻¹) (c.d' l * c.x6 1 * (c.d' l)⁻¹) :=
          (cxy_conj S (c.conjSub_d' _ c.hψA l) (c.conjSub_d' _ c.hψP' l)
            (c.conjSub_d' _ c.hψQ l) (c.x1_mem s) (c.x6_mem 1) hmem h6).symm
      _ = c.c5 t l := by rw [← ht, c.d'_conj_x6, mul_one]; rfl
      _ = c.c5 (e l * t) 1 := he t l
  have := c.x5_injective key
  rw [← ht, this, ← mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    map_one, one_mul]

theorem comm_mem (s : E) (u : F) : ⁅c.x1 s, c.x6 u⁆ ∈ M R A :=
  (commutator_mem_H S (c.x1_mem s) (c.x6_mem u)).1

theorem d_conj_comm [CharP F 2] (l : Fˣ) (s : E) (u : F) :
    c.d l * ⁅c.x1 s, c.x6 u⁆ * (c.d l)⁻¹ = ⁅c.x1 s, c.x6 (l * u)⁆ := by
  rw [← FrameSL3.commutatorElement_conj, c.d_conj_x1, c.d_conj_x6]

theorem conjSub_U3_d [CharP F 2] (l : Fˣ) :
    conjSub (shortRoot R P ⁅A₀, P'⁆ A) (c.d l) = shortRoot R P ⁅A₀, P'⁆ A := by
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_d _ c.hψP l, c.conjSub_d _ c.hψQ' l,
    c.conjSub_d _ c.hψA l]

theorem conjSub_U5_d [CharP F 2] (l : Fˣ) :
    conjSub (shortRoot R P' ⁅A₀, P⁆ A) (c.d l) = shortRoot R P' ⁅A₀, P⁆ A := by
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_d _ c.hψP' l, c.conjSub_d _ c.hψQ l,
    c.conjSub_d _ c.hψA l]

theorem proj_comm_P' [CharP F 2] (s : E) (u : F) :
    ((S.proj ⟨_, c.comm_mem s u⟩).2.2.2 : G) = c.x2 (u * c.N s) := by
  by_cases hu : u = 0
  · subst hu
    have : (⟨_, c.comm_mem s 0⟩ : ↥(M R A)) = 1 :=
      Subtype.ext (by simp only [c.x6_zero, commutatorElement_one_right]; rfl)
    rw [this, map_one, zero_mul, c.x2_zero]
    rfl
  · have hd := (S.proj_conj_of (conjSub_eq_self_iff.1 (c.conjSub_d _ c.hψA (Units.mk0 u hu)))
      (c.conjSub_d _ c.hψP _) (c.conjSub_U5_d _) (c.conjSub_U3_d _) (c.conjSub_d _ c.hψP' _)
      ⟨_, c.comm1_mem s⟩
      (by rw [c.d_conj_comm]; exact c.comm_mem s _)).2.2.2
    have e : (⟨c.d (Units.mk0 u hu) * ⁅c.x1 s, c.x6 1⁆ * (c.d (Units.mk0 u hu))⁻¹,
        by rw [c.d_conj_comm]; exact c.comm_mem s _⟩ : ↥(M R A)) = ⟨_, c.comm_mem s u⟩ :=
      Subtype.ext (by simp only; rw [c.d_conj_comm, Units.val_mk0, mul_one])
    rw [e] at hd
    rw [hd]
    change c.d (Units.mk0 u hu) * c.n2 s * (c.d (Units.mk0 u hu))⁻¹ = _
    rw [← c.x2_N, c.d_conj_x2, Units.val_mk0]

theorem N_smul [CharP F 2] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1) (l : Fˣ)
    (s : E) : c.N (e l * s) = (l : F) ^ 3 * c.N s := by
  have := S.hyp.finite
  have hinj := c.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1)
  have hconj : c.d' l * ⁅c.x1 (e l * s), c.x6 1⁆ * (c.d' l)⁻¹ = ⁅c.x1 s, c.x6 l⁆ := by
    rw [← FrameSL3.commutatorElement_conj, c.d'_conj_x1 e he, c.d'_conj_x6, mul_one,
      ← mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, one_mul]
  have hd := (S.proj_conj_of (conjSub_eq_self_iff.1 (c.conjSub_d' _ c.hψA l))
      (c.conjSub_d' _ c.hψP _) (c.conjSub_U5_d' _) (c.conjSub_U3_d' _) (c.conjSub_d' _ c.hψP' _)
      ⟨_, c.comm1_mem (e l * s)⟩ (by rw [hconj]; exact c.comm_mem s _)).2.2.2
  have e2 : (⟨c.d' l * ⁅c.x1 (e l * s), c.x6 1⁆ * (c.d' l)⁻¹,
      by rw [hconj]; exact c.comm_mem s _⟩ : ↥(M R A)) = ⟨_, c.comm_mem s l⟩ := Subtype.ext hconj
  rw [e2, c.proj_comm_P'] at hd
  change _ = c.d' l * c.n2 (e l * s) * (c.d' l)⁻¹ at hd
  rw [← c.x2_N, c.d'_conj_x2] at hd
  have h := hinj hd
  rw [Units.val_inv_eq_inv_val] at h
  have hl : (l : F) ≠ 0 := l.ne_zero
  calc c.N (e l * s) = ((l : F) * l) * ((l : F)⁻¹ * (l : F)⁻¹ * c.N (e l * s)) := by
        field_simp
    _ = ((l : F) * l) * (l * c.N s) := by rw [← h]
    _ = (l : F) ^ 3 * c.N s := by ring

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
