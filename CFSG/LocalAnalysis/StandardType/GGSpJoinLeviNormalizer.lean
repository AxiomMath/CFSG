module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviPlane
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)

variable {F : Type} [Field F]

theorem pairMat_mulVec_apply_inl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (v : ι → R) :
    (pairMat a b g *ᵥ v) a = g 0 0 * v a + g 0 1 * v b := by
  change (∑ x, pairMat a b g a x * v x) = g 0 0 * v a + g 0 1 * v b
  rw [Fintype.sum_eq_add a b hab (fun x hx => by
    rw [pairMat_apply_fst, if_neg hx.1, if_neg hx.2, zero_mul])]
  obtain ⟨h1, h2, _, _⟩ := pairMat_apply_pair hab g
  rw [h1, h2]

theorem pairMat_mulVec_apply_inr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (v : ι → R) :
    (pairMat a b g *ᵥ v) b = g 1 0 * v a + g 1 1 * v b := by
  change (∑ x, pairMat a b g b x * v x) = g 1 0 * v a + g 1 1 * v b
  rw [Fintype.sum_eq_add a b hab (fun x hx => by
    rw [pairMat_apply_snd hab, if_neg hx.1, if_neg hx.2, zero_mul])]
  obtain ⟨_, _, h3, h4⟩ := pairMat_apply_pair hab g
  rw [h3, h4]

theorem pairMat_mulVec_apply_of_notMem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι}
    (g : Matrix (Fin 2) (Fin 2) R) {r : ι} (hra : r ≠ a) (hrb : r ≠ b) (v : ι → R) :
    (pairMat a b g *ᵥ v) r = v r := by
  change (∑ x, pairMat a b g r x * v x) = v r
  rw [Finset.sum_eq_single r]
  · rw [pairMat_apply_of_ne hra hrb, one_apply_eq, one_mul]
  · intro x _ hxr
    rw [pairMat_apply_of_ne hra hrb, one_apply_ne (Ne.symm hxr), zero_mul]
  · simp

theorem mat_lam {r : ℕ} (i : Fin r) (g : SpecialLinearGroup (Fin 2) F) :
    mat r F (lam i g) = pairMat (Sum.inl i) (Sum.inr i)
      ((g : Matrix (Fin 2) (Fin 2) F)) := by
  rw [mat_apply, coe_lam]

theorem not_mem_succRange_of_plane {m : ℕ}
    {b : Fin (m + 1) ⊕ Fin (m + 1)} (hb : b = Sum.inl 0 ∨ b = Sum.inr 0) :
    b ∉ Set.range (Sum.map (Fin.succ : Fin m → Fin (m + 1))
      (Fin.succ : Fin m → Fin (m + 1))) := by
  rcases hb with rfl | rfl
  · rintro ⟨y, hy⟩
    cases y with
    | inl i => exact Fin.succ_ne_zero i (Sum.inl.inj hy)
    | inr i => exact Sum.inr_ne_inl hy
  · rintro ⟨y, hy⟩
    cases y with
    | inl i => exact Sum.inl_ne_inr hy
    | inr i => exact Fin.succ_ne_zero i (Sum.inr.inj hy)

theorem eq_plane_of_not_mem_succRange {m : ℕ}
    {c : Fin (m + 1) ⊕ Fin (m + 1)}
    (hc : c ∉ Set.range (Sum.map (Fin.succ : Fin m → Fin (m + 1))
      (Fin.succ : Fin m → Fin (m + 1)))) :
    c = Sum.inl 0 ∨ c = Sum.inr 0 := by
  cases c with
  | inl i =>
    by_cases hi : i = 0
    · exact Or.inl (by rw [hi])
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
      exact absurd ⟨Sum.inl j, rfl⟩ hc
  | inr i =>
    by_cases hi : i = 0
    · exact Or.inr (by rw [hi])
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
      exact absurd ⟨Sum.inr j, rfl⟩ hc

theorem exists_succ_of_ne_plane {m : ℕ}
    {c : Fin (m + 1) ⊕ Fin (m + 1)}
    (hc : c ≠ Sum.inl 0 ∧ c ≠ Sum.inr 0) :
    (∃ j : Fin m, c = Sum.inl j.succ) ∨ (∃ j : Fin m, c = Sum.inr j.succ) := by
  cases c with
  | inl i =>
    obtain ⟨j, rfl⟩ := (Fin.exists_succ_eq (x := i)).mpr (fun h => hc.1 (by rw [h]))
    exact Or.inl ⟨j, rfl⟩
  | inr i =>
    obtain ⟨j, rfl⟩ := (Fin.exists_succ_eq (x := i)).mpr (fun h => hc.2 (by rw [h]))
    exact Or.inr ⟨j, rfl⟩

private theorem parClosed_succRange (m : ℕ) :
    ParClosed (Set.range (Sum.map (Fin.succ : Fin m → Fin (m + 1))
      (Fin.succ : Fin m → Fin (m + 1)))) := by
  rintro x ⟨y, rfl⟩
  cases y with
  | inl i => exact ⟨Sum.inr i, rfl⟩
  | inr i => exact ⟨Sum.inl i, rfl⟩

theorem forall_mulVec_eq_levi {m : ℕ} {v : Fin (m + 1) ⊕ Fin (m + 1) → F}
    (hv : ∀ y ∈ (CFSG.StandardType.spLeviBlock m F).range,
      ((y : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
        Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F).mulVec v = v)
    (j : Fin m) : v (Sum.inl j.succ) = 0 ∧ v (Sum.inr j.succ) = 0 := by
  have hb : v (Sum.inr j.succ) = 0 := by
    have h := hv (CFSG.StandardType.spLeviBlock m F (lam j (sl2Upper (1 : F))))
      ⟨lam j (sl2Upper (1 : F)), rfl⟩
    rw [spLeviBlock_lam] at h
    have h2 := congrFun h (Sum.inl j.succ)
    rw [coe_lam, pairMat_mulVec_apply_inl
      (by simp : (Sum.inl j.succ : Fin (m + 1) ⊕ Fin (m + 1)) ≠ Sum.inr j.succ)] at h2
    simp [sl2Upper] at h2
    exact add_left_cancel (show v (Sum.inl j.succ) + v (Sum.inr j.succ) =
      v (Sum.inl j.succ) + 0 by simpa using h2)
  have ha : v (Sum.inl j.succ) = 0 := by
    have h := hv (CFSG.StandardType.spLeviBlock m F (lam j (sl2Lower (1 : F))))
      ⟨lam j (sl2Lower (1 : F)), rfl⟩
    rw [spLeviBlock_lam] at h
    have h2 := congrFun h (Sum.inr j.succ)
    rw [coe_lam, pairMat_mulVec_apply_inr
      (by simp : (Sum.inl j.succ : Fin (m + 1) ⊕ Fin (m + 1)) ≠ Sum.inr j.succ)] at h2
    simp [sl2Lower] at h2
    exact add_right_cancel (show v (Sum.inl j.succ) + v (Sum.inr j.succ) =
      0 + v (Sum.inr j.succ) by simpa using h2)
  exact ⟨ha, hb⟩

private theorem column_zero_of_mem_normalizer {m : ℕ} {w : StatedSp (m + 1) F}
    (hw : w ∈ Subgroup.normalizer (CFSG.StandardType.spLeviBlock m F).range) (j : Fin m)
    {b : Fin (m + 1) ⊕ Fin (m + 1)} (hb : b = Sum.inl 0 ∨ b = Sum.inr 0) :
    mat (m + 1) F w (Sum.inl j.succ) b = 0 ∧ mat (m + 1) F w (Sum.inr j.succ) b = 0 := by
  have hbS : b ∉ Set.range (Sum.map (Fin.succ : Fin m → Fin (m + 1))
      (Fin.succ : Fin m → Fin (m + 1))) := not_mem_succRange_of_plane hb
  have hfix : ∀ y ∈ (CFSG.StandardType.spLeviBlock m F).range,
      mat (m + 1) F y *ᵥ (mat (m + 1) F w *ᵥ Pi.single b 1)
        = mat (m + 1) F w *ᵥ Pi.single b 1 := by
    intro y hy
    have hw'y : w⁻¹ * y * w ∈ (CFSG.StandardType.spLeviBlock m F).range :=
      (Subgroup.mem_normalizer_iff''.mp hw y).mp hy
    have hSupp : CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp
        (Set.range (Sum.map (Fin.succ : Fin m → Fin (m + 1))
          (Fin.succ : Fin m → Fin (m + 1)))) (mat (m + 1) F (w⁻¹ * y * w)) := by
      have h : (w⁻¹ * y * w) ∈ suppGroup (Set.range (Sum.map (Fin.succ : Fin m → Fin (m + 1))
          (Fin.succ : Fin m → Fin (m + 1)))) := by
        have h2 : (w⁻¹ * y * w) ∈ (spEmbed (K := F) (σ := (Fin.succ : Fin m → Fin (m + 1)))
            (Fin.succ_injective m)).range := hw'y
        rwa [range_spEmbed] at h2
      exact h
    have hfix' : mat (m + 1) F (w⁻¹ * y * w) *ᵥ Pi.single b 1 = Pi.single b 1 := by
      funext r
      rw [mulVec_single_one_apply (mat (m + 1) F (w⁻¹ * y * w)) b r,
        hSupp r b (fun hh => hbS hh.2)]
      by_cases hr : r = b
      · subst hr; simp [one_apply]
      · rw [Pi.single_eq_of_ne hr, one_apply_ne hr]
    have hcomm : mat (m + 1) F y * mat (m + 1) F w
        = mat (m + 1) F w * mat (m + 1) F (w⁻¹ * y * w) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    calc mat (m + 1) F y *ᵥ (mat (m + 1) F w *ᵥ Pi.single b 1)
        = (mat (m + 1) F y * mat (m + 1) F w) *ᵥ Pi.single b 1 :=
          Matrix.mulVec_mulVec (Pi.single b 1) (mat (m + 1) F y) (mat (m + 1) F w)
      _ = (mat (m + 1) F w * mat (m + 1) F (w⁻¹ * y * w)) *ᵥ Pi.single b 1 := by rw [hcomm]
      _ = mat (m + 1) F w *ᵥ (mat (m + 1) F (w⁻¹ * y * w) *ᵥ Pi.single b 1) :=
          (Matrix.mulVec_mulVec (Pi.single b 1) (mat (m + 1) F w)
            (mat (m + 1) F (w⁻¹ * y * w))).symm
      _ = mat (m + 1) F w *ᵥ Pi.single b 1 := by rw [hfix']
  obtain ⟨h1, h2⟩ := forall_mulVec_eq_levi hfix j
  refine ⟨?_, ?_⟩
  · rw [← mulVec_single_one_apply (mat (m + 1) F w) b (Sum.inl j.succ)]
    exact h1
  · rw [← mulVec_single_one_apply (mat (m + 1) F w) b (Sum.inr j.succ)]
    exact h2

theorem entry_eq_zero_of_mem_normalizer_levi {m : ℕ} {u : StatedSp (m + 1) F}
    (hu : u ∈ Subgroup.normalizer (CFSG.StandardType.spLeviBlock m F).range) (j : Fin m) :
    (∀ a : Fin (m + 1) ⊕ Fin (m + 1), a = Sum.inl 0 ∨ a = Sum.inr 0 →
      ((u : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
          Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) (Sum.inl j.succ) a = 0 ∧
        ((u : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
          Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) (Sum.inr j.succ) a = 0 ∧
        ((u : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
          Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) a (Sum.inl j.succ) = 0 ∧
        ((u : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
          Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) a (Sum.inr j.succ) = 0) := by
  intro a ha
  have hpa : par a = Sum.inl 0 ∨ par a = Sum.inr 0 := by
    rcases ha with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  obtain ⟨hc1, hc2⟩ := column_zero_of_mem_normalizer (Subgroup.inv_mem _ hu) j hpa
  obtain ⟨h1, h2⟩ := column_zero_of_mem_normalizer hu j ha
  refine ⟨h1, h2, ?_, ?_⟩
  · have h := hc2
    rw [mat_inv_apply] at h
    simp only [par_par, par_inr, sgn_inr] at h
    refine (mul_eq_zero.mp h).resolve_left ?_
    exact mul_ne_zero (by norm_num) (sgn_ne_zero (par a))
  · have h := hc1
    rw [mat_inv_apply] at h
    simp only [par_par, par_inl, sgn_inl] at h
    refine (mul_eq_zero.mp h).resolve_left ?_
    exact mul_ne_zero (by norm_num) (sgn_ne_zero (par a))

theorem exists_lam_mul_levi_of_entries_zero {m : ℕ} {u : StatedSp (m + 1) F}
    (hu : ∀ j : Fin m, ∀ a : Fin (m + 1) ⊕ Fin (m + 1), a = Sum.inl 0 ∨ a = Sum.inr 0 →
      ((u : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
          Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) (Sum.inl j.succ) a = 0 ∧
        ((u : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
          Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) (Sum.inr j.succ) a = 0 ∧
        ((u : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
          Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) a (Sum.inl j.succ) = 0 ∧
        ((u : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) :
          Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) a (Sum.inr j.succ) = 0) :
    ∃ (g : SpecialLinearGroup (Fin 2) F) (h : StatedSp m F),
      u = lam (0 : Fin (m + 1)) g * CFSG.StandardType.spLeviBlock m F h := by
  let g₀ : Matrix (Fin 2) (Fin 2) F :=
    !![(mat (m + 1) F u) (Sum.inl 0) (Sum.inl 0), (mat (m + 1) F u) (Sum.inl 0) (Sum.inr 0);
       (mat (m + 1) F u) (Sum.inr 0) (Sum.inl 0), (mat (m + 1) F u) (Sum.inr 0) (Sum.inr 0)]
  have hdet : g₀.det = 1 := by
    have hUU := congrFun (congrFun (mat_transpose_mul_gram_mul u) (Sum.inl 0)) (Sum.inr 0)
    rw [transpose_mul_gram_mul_apply,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, par_inl, if_pos rfl,
      sgn_inl] at hUU
    rw [Fintype.sum_eq_add (Sum.inl 0) (Sum.inr 0) (by simp) (fun c hc => by
      rcases exists_succ_of_ne_plane hc with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [mat_apply, (hu j (Sum.inl 0) (Or.inl rfl)).1,
          zero_mul]
      · rw [mat_apply, (hu j (Sum.inl 0) (Or.inl rfl)).2.1,
          zero_mul])] at hUU
    rw [sgn_inl, par_inl, sgn_inr, par_inr] at hUU
    rw [show g₀.det = (mat (m + 1) F u) (Sum.inl 0) (Sum.inl 0) *
        (mat (m + 1) F u) (Sum.inr 0) (Sum.inr 0) -
        (mat (m + 1) F u) (Sum.inl 0) (Sum.inr 0) *
        (mat (m + 1) F u) (Sum.inr 0) (Sum.inl 0) by
      simp [g₀, det_fin_two]]
    linear_combination hUU
  let g : SpecialLinearGroup (Fin 2) F := ⟨g₀, hdet⟩
  have hsame : ∀ t, t = Sum.inl 0 ∨ t = Sum.inr 0 →
      mat (m + 1) F u *ᵥ Pi.single t 1
        = mat (m + 1) F (lam (0 : Fin (m + 1)) g) *ᵥ Pi.single t 1 := by
    intro t ht
    funext r
    rw [mulVec_single_one_apply (mat (m + 1) F u) t r, mat_lam,
      mulVec_single_one_apply (pairMat (Sum.inl 0) (Sum.inr 0)
        ((g : Matrix (Fin 2) (Fin 2) F))) t r]
    by_cases hr : r = Sum.inl 0 ∨ r = Sum.inr 0
    · rcases hr with rfl | rfl
      · rw [pairMat_apply_fst]
        rcases ht with rfl | rfl <;> simp [g, g₀]
      · rw [pairMat_apply_snd (by simp : (Sum.inl (0 : Fin (m + 1)) :
            Fin (m + 1) ⊕ Fin (m + 1)) ≠ Sum.inr 0)]
        rcases ht with rfl | rfl <;> simp [g, g₀]
    · simp only [not_or] at hr
      rw [pairMat_apply_of_ne hr.1 hr.2]
      have hrS := exists_succ_of_ne_plane hr
      have hrmem : r ∈ Set.range (Sum.map (Fin.succ : Fin m → Fin (m + 1))
          (Fin.succ : Fin m → Fin (m + 1))) := by
        rcases hrS with ⟨j, hj⟩ | ⟨j, hj⟩
        · rw [hj]; exact ⟨Sum.inl j, rfl⟩
        · rw [hj]; exact ⟨Sum.inr j, rfl⟩
      have hrt : r ≠ t := fun h => not_mem_succRange_of_plane ht (h ▸ hrmem)
      rcases hrS with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [mat_apply, (hu j t ht).1, one_apply_ne hrt]
      · rw [mat_apply, (hu j t ht).2.1, one_apply_ne hrt]
  let u₁ : StatedSp (m + 1) F := (lam (0 : Fin (m + 1)) g)⁻¹ * u
  have hu₁ : u₁ ∈ suppGroup (Set.range (Sum.map (Fin.succ : Fin m → Fin (m + 1))
      (Fin.succ : Fin m → Fin (m + 1)))) := by
    rw [mem_suppGroup_iff (parClosed_succRange m)]
    intro t ht r
    have htA : t = Sum.inl 0 ∨ t = Sum.inr 0 := eq_plane_of_not_mem_succRange ht
    have hcol : mat (m + 1) F u₁ *ᵥ Pi.single t 1 = Pi.single t 1 := by
      have hmat : mat (m + 1) F u₁ = mat (m + 1) F ((lam (0 : Fin (m + 1)) g)⁻¹) *
          mat (m + 1) F u := by
        change mat (m + 1) F ((lam (0 : Fin (m + 1)) g)⁻¹ * u) =
          mat (m + 1) F ((lam (0 : Fin (m + 1)) g)⁻¹) * mat (m + 1) F u
        rw [map_mul]
      rw [hmat, ← Matrix.mulVec_mulVec, hsame t htA, Matrix.mulVec_mulVec,
        ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [← mulVec_single_one_apply (mat (m + 1) F u₁) t r, hcol]
    by_cases hrt : r = t
    · subst hrt; simp [one_apply]
    · rw [Pi.single_eq_of_ne hrt, one_apply_ne hrt]
  have hmem : u₁ ∈ (spEmbed (K := F) (σ := (Fin.succ : Fin m → Fin (m + 1)))
      (Fin.succ_injective m)).range := by
    rw [range_spEmbed]
    exact hu₁
  obtain ⟨h, hh⟩ := hmem
  exact ⟨g, h, by
    calc u = lam (0 : Fin (m + 1)) g * u₁ := (mul_inv_cancel_left _ _).symm
      _ = lam (0 : Fin (m + 1)) g * CFSG.StandardType.spLeviBlock m F h := by
        rw [show u₁ = CFSG.StandardType.spLeviBlock m F h from hh.symm]⟩

theorem exists_lam_mul_levi_of_mem_normalizer {m : ℕ} {u : StatedSp (m + 1) F}
    (hu : u ∈ Subgroup.normalizer (CFSG.StandardType.spLeviBlock m F).range) :
    ∃ (g : SpecialLinearGroup (Fin 2) F) (h : StatedSp m F),
      u = lam (0 : Fin (m + 1)) g * CFSG.StandardType.spLeviBlock m F h :=
  exists_lam_mul_levi_of_entries_zero (fun j a ha => entry_eq_zero_of_mem_normalizer_levi hu j a ha)

private theorem lam_mem_normalizer (m : ℕ) (g : SpecialLinearGroup (Fin 2) F) :
    lam (0 : Fin (m + 1)) g ∈ Subgroup.normalizer (CFSG.StandardType.spLeviBlock m F).range := by
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  constructor
  · intro hh
    obtain ⟨h', rfl⟩ := hh
    have hc := lam_zero_commute_spLeviBlock g h'
    rw [hc.inv_mul_cancel]
    exact ⟨h', rfl⟩
  · intro hh
    obtain ⟨z, hz⟩ := hh
    have hc := lam_zero_commute_spLeviBlock g z
    have h1 : h = CFSG.StandardType.spLeviBlock m F z := by
      calc h = lam (0 : Fin (m + 1)) g *
            ((lam (0 : Fin (m + 1)) g)⁻¹ * h * lam (0 : Fin (m + 1)) g) *
            (lam (0 : Fin (m + 1)) g)⁻¹ := by group
        _ = lam (0 : Fin (m + 1)) g * CFSG.StandardType.spLeviBlock m F z *
            (lam (0 : Fin (m + 1)) g)⁻¹ := by rw [← hz]
        _ = CFSG.StandardType.spLeviBlock m F z := by
            simpa using (hc.inv_left).inv_mul_cancel
    rw [h1]
    exact ⟨z, rfl⟩

theorem normalizer_spLeviBlock_range (m : ℕ) :
    Subgroup.normalizer (CFSG.StandardType.spLeviBlock m F).range = (spPlaneLevi m F).range := by
  apply le_antisymm
  · intro u hu
    obtain ⟨g, h, rfl⟩ := exists_lam_mul_levi_of_mem_normalizer hu
    exact ⟨(g, h), spPlaneLevi_apply g h⟩
  · rintro _ ⟨⟨g, h⟩, rfl⟩
    rw [spPlaneLevi_apply]
    exact mul_mem (lam_mem_normalizer m g) (Subgroup.le_normalizer ⟨h, rfl⟩)

end CFSG.StandardType.SpJoin
