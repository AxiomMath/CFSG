module

public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped Matrix

@[expose] def spDiagIdem (K : Type) [Field K] (n r : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun a => if a.val < r then 1 else 0

@[expose] def spHypIdem (K : Type) [Field K] (n j : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b =>
    if a.val < 2 * j ∧ b.val < 2 * j ∧ a.val / 2 = b.val / 2 ∧ a ≠ b then 1 else 0

open LinearMap (BilinForm)
open Module

private lemma mem_orthogonal_span_singleton_iff' {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (B : BilinForm K V) (x z : V) :
    z ∈ B.orthogonal (K ∙ x) ↔ B x z = 0 := by
  rw [BilinForm.mem_orthogonal_iff]
  constructor
  · intro h; exact h x (Submodule.mem_span_singleton_self x)
  · intro h n hn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hn
    rw [map_smul, LinearMap.smul_apply, h, smul_zero]

private theorem exists_apply_self_ne_zero_and_not_isAlt_restrict_orthogonal
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}
    (hB : B.IsSymm) {x : V} (hx : B x x ≠ 0)
    (halt : (B.restrict (B.orthogonal (K ∙ x))).IsAlt)
    (hne : B.restrict (B.orthogonal (K ∙ x)) ≠ 0) :
    ∃ y, B y y ≠ 0 ∧ ¬ (B.restrict (B.orthogonal (K ∙ y))).IsAlt := by
  obtain ⟨u, w, huw⟩ : ∃ u w : B.orthogonal (K ∙ x), B u w ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext fun u => LinearMap.ext fun w => by simpa using h u w)
  have hxu : B x u = 0 := (mem_orthogonal_span_singleton_iff' B x u).1 u.2
  have hxw : B x w = 0 := (mem_orthogonal_span_singleton_iff' B x w).1 w.2
  have huu : B u u = 0 := by simpa using halt u
  have hww : B w w = 0 := by simpa using halt w
  set z := x + u with hz
  have hzz : B z z = B x x := by simp [hz, hxu, hB.eq u x, huu]
  have hzw : B z w = B u w := by simp [hz, hxw]
  refine ⟨z, hzz ▸ hx, fun halt' => huw ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c * B z z = B z w := ⟨B z w / B z z, div_mul_cancel₀ _ (hzz ▸ hx)⟩
  have hw' : w - c • z ∈ B.orthogonal (K ∙ z) := by
    rw [mem_orthogonal_span_singleton_iff']
    simp only [map_sub, map_smul, smul_eq_mul]
    rw [hc, sub_self]
  have h0 : B w w - c * B z w - c * (B z w - c * B z z) = 0 := by
    simpa [hB.eq w z] using halt' ⟨w - c • z, hw'⟩
  have hcb : c * B z w = 0 := by linear_combination -h0 + c * hc + hww
  rw [← hzw]
  rcases mul_eq_zero.1 hcb with hc0 | hb0
  · rw [← hc, hc0, zero_mul]
  · exact hb0

private theorem exists_apply_self_ne_zero_and_restrict_orthogonal_isAlt_imp_eq_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}
    (hB : B.IsSymm) (h : ¬B.IsAlt) :
    ∃ x, B x x ≠ 0 ∧
      ((B.restrict (B.orthogonal (K ∙ x))).IsAlt → B.restrict (B.orthogonal (K ∙ x)) = 0) := by
  obtain ⟨x, hx⟩ : ∃ x, B x x ≠ 0 := by
    by_contra! hx
    exact h hx
  by_cases hW : (B.restrict (B.orthogonal (K ∙ x))).IsAlt ∧
      B.restrict (B.orthogonal (K ∙ x)) ≠ 0
  · obtain ⟨y, hy, hy'⟩ :=
      exists_apply_self_ne_zero_and_not_isAlt_restrict_orthogonal hB hx hW.1 hW.2
    exact ⟨y, hy, fun h' => (hy' h').elim⟩
  · exact ⟨x, hx, fun h' => not_not.1 (not_and.1 hW h')⟩

private lemma spDiagIdem_apply (K : Type) [Field K] (n r : ℕ) (i j : Fin n) :
    spDiagIdem K n r i j = if i = j then (if i.val < r then 1 else 0) else 0 := by
  simp [spDiagIdem, Matrix.diagonal_apply]

private lemma spDiagIdem_zero_zero {K : Type} [Field K] {m r : ℕ} (hr : 0 < r) :
    spDiagIdem K (m + 1) r 0 0 = 1 := by
  rw [spDiagIdem_apply, if_pos rfl, if_pos (by simpa using hr)]

private lemma spDiagIdem_zero_succ {K : Type} [Field K] {d r : ℕ} (j : Fin d) :
    spDiagIdem K (d + 1) r 0 j.succ = 0 := by
  rw [spDiagIdem_apply, if_neg (Fin.succ_ne_zero j).symm]

private lemma spDiagIdem_succ_zero {K : Type} [Field K] {d r : ℕ} (i : Fin d) :
    spDiagIdem K (d + 1) r i.succ 0 = 0 := by
  rw [spDiagIdem_apply, if_neg (Fin.succ_ne_zero i)]

private lemma spDiagIdem_succ_succ {K : Type} [Field K] {d r : ℕ} (i j : Fin d) :
    spDiagIdem K (d + 1) (r + 1) i.succ j.succ = spDiagIdem K d r i j := by
  rw [spDiagIdem_apply, spDiagIdem_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
    by_cases hi : i.val < r
    · rw [if_pos hi, if_pos (by rw [Fin.val_succ]; omega)]
    · rw [if_neg hi, if_neg (by rw [Fin.val_succ]; omega)]
  · rw [if_neg h, if_neg fun hij => h (Fin.succ_injective d hij)]

private lemma toMatrix_mkFinCons_eq_spDiagIdem_one {K : Type} {V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] {d : ℕ}
    {B : BilinForm K V} {y : V} {W : Submodule K V} (bW : Basis (Fin d) K W) (hB : B.IsSymm)
    (hli : ∀ c : K, ∀ x ∈ W, c • y + x = 0 → c = 0)
    (hsp : ∀ z : V, ∃ c : K, z + c • y ∈ W) (hy : B y y = 1)
    (hW0 : B.restrict W = 0) (hyW : ∀ z ∈ W, B y z = 0) :
    BilinForm.toMatrix (Basis.mkFinCons y bW hli hsp) B = spDiagIdem K (d + 1) 1 := by
  ext i j
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Fin.cons_zero]
          rw [hy, spDiagIdem_zero_zero (m := d) (r := 1) (by omega)]
      | succ j =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Fin.cons_zero,
            Fin.cons_succ, Function.comp_apply]
          rw [hyW (bW j) (bW j).2, spDiagIdem_zero_succ j]
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Fin.cons_zero,
            Fin.cons_succ, Function.comp_apply]
          rw [hB.eq, hyW (bW i) (bW i).2, spDiagIdem_succ_zero i]
      | succ j =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Fin.cons_succ,
            Function.comp_apply]
          have hres : BilinForm.toMatrix bW (B.restrict W) i j = B (↑(bW i)) (↑(bW j)) := by
            rw [BilinForm.toMatrix_apply]
            rfl
          rw [← hres, hW0]
          simp [BilinForm.toMatrix_apply, spDiagIdem_apply]

private lemma toMatrix_mkFinCons_eq_spDiagIdem_succ {K : Type} {V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] {d r : ℕ} {B : BilinForm K V} {y : V}
    {W : Submodule K V} (bW : Basis (Fin d) K W)
    (hB : B.IsSymm) (hli : ∀ c : K, ∀ x ∈ W, c • y + x = 0 → c = 0)
    (hsp : ∀ z : V, ∃ c : K, z + c • y ∈ W) (hy : B y y = 1)
    (hbW : BilinForm.toMatrix bW (B.restrict W) = spDiagIdem K d r)
    (hyW : ∀ z ∈ W, B y z = 0) :
    BilinForm.toMatrix (Basis.mkFinCons y bW hli hsp) B = spDiagIdem K (d + 1) (r + 1) := by
  ext i j
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Fin.cons_zero]
          rw [hy, spDiagIdem_zero_zero (m := d) (r := r + 1) (by omega)]
      | succ j =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Fin.cons_zero,
            Fin.cons_succ, Function.comp_apply]
          rw [hyW (bW j) (bW j).2, spDiagIdem_zero_succ j]
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Fin.cons_zero,
            Fin.cons_succ, Function.comp_apply]
          rw [hB.eq, hyW (bW i) (bW i).2, spDiagIdem_succ_zero i]
      | succ j =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Fin.cons_succ,
            Function.comp_apply]
          have hres : BilinForm.toMatrix bW (B.restrict W) i j = B (↑(bW i)) (↑(bW j)) := by
            rw [BilinForm.toMatrix_apply]
            rfl
          rw [← hres, hbW, spDiagIdem_succ_succ i j]

private lemma mkFinCons_li_of_disjoint {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {y : V} {N : Submodule K V} (hdisj : Disjoint (K ∙ y) N) (hy : y ≠ 0) :
    ∀ c : K, ∀ x ∈ N, c • y + x = 0 → c = 0 := by
  intro c x hx h
  have hcy : c • y ∈ N := by
    rw [eq_neg_of_add_eq_zero_left h]
    exact Submodule.neg_mem _ hx
  have h0 : c • y = 0 := by
    have hmem : c • y ∈ K ∙ y ⊓ N :=
      Submodule.mem_inf.mpr ⟨Submodule.smul_mem _ c (Submodule.mem_span_singleton_self y), hcy⟩
    rw [disjoint_iff.mp hdisj, Submodule.mem_bot] at hmem
    exact hmem
  exact (smul_eq_zero.mp h0).resolve_right hy

private lemma mkFinCons_sp_of_sup {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {y : V} {N O : Submodule K V} (hO : O ≤ K ∙ y ⊔ N) :
    ∀ z ∈ O, ∃ c : K, z + c • y ∈ N := by
  intro z hz
  obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp (hO hz)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
  refine ⟨-c, ?_⟩
  have hb : (c • y + w) + (-c) • y = w := by rw [neg_smul]; abel
  rw [← hpw, hb]
  exact hw

private lemma exists_normalized_orthogonal_decomposition {K : Type} {V : Type*} [Field K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : BilinForm K V} (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm) (hna : ¬B.IsAlt)
    {d : ℕ} (hd : finrank K V = d + 1) :
    ∃ y : V, B y y = 1 ∧ y ≠ 0 ∧
      ((B.restrict (B.orthogonal (K ∙ y))).IsAlt → B.restrict (B.orthogonal (K ∙ y)) = 0) ∧
      IsCompl (K ∙ y) (B.orthogonal (K ∙ y)) ∧
      finrank K (B.orthogonal (K ∙ y)) = d := by
  obtain ⟨x, hx, hW⟩ := exists_apply_self_ne_zero_and_restrict_orthogonal_isAlt_imp_eq_zero hB hna
  obtain ⟨s, hs⟩ := hsq (B x x)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hs
    exact hx hs
  set y := s⁻¹ • x with hy_def
  have hy : B y y = 1 := by
    rw [hy_def]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hs]
    field_simp
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact zero_ne_one hy
  have hspan : K ∙ y = K ∙ x := by
    rw [hy_def]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hs0)) x
  have hW' : (B.restrict (B.orthogonal (K ∙ y))).IsAlt →
      B.restrict (B.orthogonal (K ∙ y)) = 0 := by
    rw [hspan]
    exact hW
  have hIC : IsCompl (K ∙ y) (B.orthogonal (K ∙ y)) :=
    BilinForm.isCompl_span_singleton_orthogonal (by rw [hy]; exact one_ne_zero)
  have hdW : finrank K (B.orthogonal (K ∙ y)) = d := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hIC
    rw [finrank_span_singleton hy0, hd] at h1
    omega
  exact ⟨y, hy, hy0, hW', hIC, hdW⟩

private theorem exists_basis_toMatrix_eq_spDiagIdem {K : Type} [Field K] [CharP K 2]
    (hsq : ∀ a : K, IsSquare a) :
    ∀ (d : ℕ) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = d → ∀ {B : BilinForm K V}, B.IsSymm → ¬B.IsAlt →
      ∃ r, 1 ≤ r ∧ r ≤ d ∧ ∃ b : Basis (Fin d) K V,
        BilinForm.toMatrix b B = spDiagIdem K d r := by
  intro d
  induction d with
  | zero =>
      intro V _ _ _ hd B _ hna
      refine absurd ?_ hna
      have hsub : Subsingleton V := Module.finrank_zero_iff.mp hd
      intro x
      rw [hsub.elim x 0]
      simp
  | succ d ih =>
      intro V _ _ _ hd B hB hna
      obtain ⟨y, hy, hy0, hW', hIC, hdW⟩ :=
        exists_normalized_orthogonal_decomposition hsq hB hna (d := d) hd
      have hmem : ∀ z ∈ B.orthogonal (K ∙ y), B y z = 0 := fun z hz =>
        (mem_orthogonal_span_singleton_iff' B y z).1 hz
      have hli : ∀ c : K, ∀ z ∈ B.orthogonal (K ∙ y), c • y + z = 0 → c = 0 :=
        mkFinCons_li_of_disjoint hIC.disjoint hy0
      have hsp : ∀ z : V, ∃ c : K, z + c • y ∈ B.orthogonal (K ∙ y) := fun z =>
        mkFinCons_sp_of_sup (le_of_eq hIC.sup_eq_top.symm) z Submodule.mem_top
      by_cases hWalt : (B.restrict (B.orthogonal (K ∙ y))).IsAlt
      · have hW0 : B.restrict (B.orthogonal (K ∙ y)) = 0 := hW' hWalt
        let bW := Module.finBasisOfFinrankEq K (B.orthogonal (K ∙ y)) hdW
        exact ⟨1, le_refl 1, by omega, Basis.mkFinCons y bW hli hsp,
          toMatrix_mkFinCons_eq_spDiagIdem_one bW hB hli hsp hy hW0 hmem⟩
      · obtain ⟨r', hr'1, hr'le, bW, hbW⟩ := ih hdW (hB.restrict _) hWalt
        exact ⟨r' + 1, by omega, by omega, Basis.mkFinCons y bW hli hsp,
          toMatrix_mkFinCons_eq_spDiagIdem_succ bW hB hli hsp hy hbW hmem⟩

private lemma spHypIdem_apply (K : Type) [Field K] (n j : ℕ) (a b : Fin n) :
    spHypIdem K n j a b =
      if a.val < 2 * j ∧ b.val < 2 * j ∧ a.val / 2 = b.val / 2 ∧ a ≠ b then 1 else 0 := rfl

private lemma spHypIdem_zero (K : Type) [Field K] (n : ℕ) : spHypIdem K n 0 = 0 := by
  ext a b
  rw [spHypIdem_apply]
  simp

private lemma spHypIdem_zero_zero {K : Type} [Field K] (n j : ℕ) :
    spHypIdem K (n + 2) j 0 0 = 0 := by
  rw [spHypIdem_apply]
  exact if_neg (by rintro ⟨-, -, -, h⟩; exact h rfl)

private lemma spHypIdem_zero_one {K : Type} [Field K] (n j : ℕ) :
    spHypIdem K (n + 2) (j + 1) 0 (Fin.succ 0) = 1 := by
  rw [spHypIdem_apply]
  exact if_pos ⟨by simp only [Fin.val_zero]; omega,
    by simp only [Fin.val_succ, Fin.val_zero]; omega, by simp, by simp⟩

private lemma spHypIdem_zero_succ_succ {K : Type} [Field K] {n j : ℕ} (k : Fin n) :
    spHypIdem K (n + 2) (j + 1) 0 k.succ.succ = 0 := by
  rw [spHypIdem_apply]
  exact if_neg (by
    rintro ⟨-, -, h3, -⟩
    simp only [Fin.val_zero, Nat.zero_div, Fin.val_succ] at h3
    omega)

private lemma spHypIdem_one_zero {K : Type} [Field K] (n j : ℕ) :
    spHypIdem K (n + 2) (j + 1) (Fin.succ 0) 0 = 1 := by
  rw [spHypIdem_apply]
  exact if_pos ⟨by simp only [Fin.val_succ, Fin.val_zero]; omega,
    by simp only [Fin.val_zero]; omega, by simp, by simp⟩

private lemma spHypIdem_one_one {K : Type} [Field K] (n j : ℕ) :
    spHypIdem K (n + 2) (j + 1) (Fin.succ 0) (Fin.succ 0) = 0 := by
  rw [spHypIdem_apply]
  exact if_neg (by rintro ⟨-, -, -, h⟩; exact h rfl)

private lemma spHypIdem_one_succ_succ {K : Type} [Field K] {n j : ℕ} (k : Fin n) :
    spHypIdem K (n + 2) (j + 1) (Fin.succ 0) k.succ.succ = 0 := by
  rw [spHypIdem_apply]
  exact if_neg (by
    rintro ⟨-, -, h3, -⟩
    simp only [Fin.val_succ, Fin.val_zero] at h3
    omega)

private lemma spHypIdem_succ_succ_zero {K : Type} [Field K] {n j : ℕ} (k : Fin n) :
    spHypIdem K (n + 2) (j + 1) k.succ.succ 0 = 0 := by
  rw [spHypIdem_apply]
  exact if_neg (by
    rintro ⟨-, -, h3, -⟩
    simp only [Fin.val_zero, Nat.zero_div, Fin.val_succ] at h3
    omega)

private lemma spHypIdem_succ_succ_one {K : Type} [Field K] {n j : ℕ} (k : Fin n) :
    spHypIdem K (n + 2) (j + 1) k.succ.succ (Fin.succ 0) = 0 := by
  rw [spHypIdem_apply]
  exact if_neg (by
    rintro ⟨-, -, h3, -⟩
    simp only [Fin.val_succ, Fin.val_zero] at h3
    omega)

private lemma spHypIdem_succ_succ_succ_succ {K : Type} [Field K] {n j : ℕ} (i k : Fin n) :
    spHypIdem K (n + 2) (j + 1) i.succ.succ k.succ.succ = spHypIdem K n j i k := by
  rw [spHypIdem_apply, spHypIdem_apply]
  have h : (i.succ.succ.val < 2 * (j + 1) ∧ k.succ.succ.val < 2 * (j + 1) ∧
        i.succ.succ.val / 2 = k.succ.succ.val / 2 ∧ i.succ.succ ≠ k.succ.succ) ↔
      (i.val < 2 * j ∧ k.val < 2 * j ∧ i.val / 2 = k.val / 2 ∧ i ≠ k) := by
    simp only [Fin.val_succ]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by omega, by omega, by omega, fun hik => h4 (by rw [hik])⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by omega, by omega, by omega,
        fun hik => h4 (Fin.succ_injective n (Fin.succ_injective (n + 1) hik))⟩
  exact if_congr h rfl rfl

private lemma disjoint_span_pair_orthogonal {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {B : BilinForm K V} {a b' : V} (haa : B a a = 0)
    (hbb : B b' b' = 0) (hab : B a b' = 1) (hba : B b' a = 1) :
    Disjoint (K ∙ a ⊔ K ∙ b') (B.orthogonal (K ∙ a ⊔ K ∙ b')) := by
  have haP : a ∈ K ∙ a ⊔ K ∙ b' := Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)
  have hbP : b' ∈ K ∙ a ⊔ K ∙ b' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self b')
  rw [Submodule.disjoint_def]
  intro x hxP hxW
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hxP
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hp
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hq
  have h1 : B a (α • a + β • b') = 0 := by
    rw [hpq]
    exact (BilinForm.mem_orthogonal_iff.mp hxW) a haP
  have h2 : B b' (α • a + β • b') = 0 := by
    rw [hpq]
    exact (BilinForm.mem_orthogonal_iff.mp hxW) b' hbP
  have hβ : β = 0 := by
    simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      haa, hab, mul_zero, mul_one, add_zero, zero_add] using h1
  have hα : α = 0 := by
    simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hbb, hba, mul_zero, mul_one, zero_add, add_zero] using h2
  rw [← hpq, hα, hβ, zero_smul, zero_smul, add_zero]

private lemma codisjoint_span_pair_orthogonal {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {B : BilinForm K V} (hB : B.IsSymm) {a b' : V} (haa : B a a = 0)
    (hbb : B b' b' = 0) (hab : B a b' = 1) (hba : B b' a = 1) :
    Codisjoint (K ∙ a ⊔ K ∙ b') (B.orthogonal (K ∙ a ⊔ K ∙ b')) := by
  have haP : a ∈ K ∙ a ⊔ K ∙ b' := Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)
  have hbP : b' ∈ K ∙ a ⊔ K ∙ b' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self b')
  rw [codisjoint_iff, eq_top_iff]
  intro v _
  refine Submodule.mem_sup.mpr ⟨B v b' • a + B v a • b', ?_,
    v - (B v b' • a + B v a • b'), ?_, by abel⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ haP) (Submodule.smul_mem _ _ hbP)
  · rw [BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have hva : B a (v - (B v b' • a + B v a • b')) = 0 := by
      rw [map_sub, map_add, hB.eq a v]
      simp only [map_smul, smul_eq_mul, haa, hab, mul_zero, mul_one, zero_add, sub_self]
    have hvb : B b' (v - (B v b' • a + B v a • b')) = 0 := by
      rw [map_sub, map_add, hB.eq b' v]
      simp only [map_smul, smul_eq_mul, hbb, hba, mul_zero, mul_one, add_zero, sub_self]
    rw [← hpq]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hva, hvb, mul_zero, add_zero]

private lemma isCompl_span_pair_orthogonal {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {B : BilinForm K V} (hB : B.IsSymm) {a b' : V} (haa : B a a = 0)
    (hbb : B b' b' = 0) (hab : B a b' = 1) :
    IsCompl (K ∙ a ⊔ K ∙ b') (B.orthogonal (K ∙ a ⊔ K ∙ b')) := by
  have hba : B b' a = 1 := by rw [hB.eq, hab]
  exact ⟨disjoint_span_pair_orthogonal haa hbb hab hba,
    codisjoint_span_pair_orthogonal hB haa hbb hab hba⟩

private lemma toMatrix_mkFinCons_mkFinConsOfLE_row_zero {K : Type} {V : Type*}
    [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {n j : ℕ} {B : BilinForm K V} {a b' : V} {W N₁ : Submodule K V}
    (c' : Basis (Fin n) K W) (hb'N₁ : b' ∈ N₁) (hNO : W ≤ N₁)
    (hli₁ : ∀ c : K, ∀ x ∈ W, c • b' + x = 0 → c = 0)
    (hsp₁ : ∀ z ∈ N₁, ∃ c : K, z + c • b' ∈ W)
    (hli₂ : ∀ c : K, ∀ x ∈ N₁, c • a + x = 0 → c = 0)
    (hsp₂ : ∀ z : V, ∃ c : K, z + c • a ∈ N₁)
    (haa : B a a = 0) (hab : B a b' = 1) (hmemW : ∀ k : Fin n, B a (c' k) = 0) :
    ∀ t : Fin (n + 2),
      BilinForm.toMatrix
          (Basis.mkFinCons a (Basis.mkFinConsOfLE b' hb'N₁ c' hNO hli₁ hsp₁) hli₂ hsp₂) B
        0 t = spHypIdem K (n + 2) (j + 1) 0 t := by
  intro t
  induction t using Fin.cases with
  | zero =>
      simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Fin.cons_zero]
      rw [haa, spHypIdem_zero_zero]
  | succ t =>
      induction t using Fin.cases with
      | zero =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Basis.coe_mkFinConsOfLE,
            Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
          rw [hab, spHypIdem_zero_one]
      | succ t =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Basis.coe_mkFinConsOfLE,
            Fin.cons_zero, Fin.cons_succ, Function.comp_apply, Submodule.coe_inclusion]
          rw [hmemW t, spHypIdem_zero_succ_succ]

private lemma toMatrix_mkFinCons_mkFinConsOfLE_row_one {K : Type} {V : Type*}
    [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {n j : ℕ} {B : BilinForm K V} {a b' : V} {W N₁ : Submodule K V}
    (c' : Basis (Fin n) K W) (hb'N₁ : b' ∈ N₁) (hNO : W ≤ N₁)
    (hli₁ : ∀ c : K, ∀ x ∈ W, c • b' + x = 0 → c = 0)
    (hsp₁ : ∀ z ∈ N₁, ∃ c : K, z + c • b' ∈ W)
    (hli₂ : ∀ c : K, ∀ x ∈ N₁, c • a + x = 0 → c = 0)
    (hsp₂ : ∀ z : V, ∃ c : K, z + c • a ∈ N₁)
    (hbb : B b' b' = 0) (hba : B b' a = 1) (hmemW' : ∀ k : Fin n, B b' (c' k) = 0) :
    ∀ t : Fin (n + 2),
      BilinForm.toMatrix
          (Basis.mkFinCons a (Basis.mkFinConsOfLE b' hb'N₁ c' hNO hli₁ hsp₁) hli₂ hsp₂) B
        (Fin.succ 0) t = spHypIdem K (n + 2) (j + 1) (Fin.succ 0) t := by
  intro t
  induction t using Fin.cases with
  | zero =>
      simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Basis.coe_mkFinConsOfLE,
        Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
      rw [hba, spHypIdem_one_zero]
  | succ t =>
      induction t using Fin.cases with
      | zero =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Basis.coe_mkFinConsOfLE,
            Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
          rw [hbb, spHypIdem_one_one]
      | succ t =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Basis.coe_mkFinConsOfLE,
            Fin.cons_zero, Fin.cons_succ, Function.comp_apply, Submodule.coe_inclusion]
          rw [hmemW' t, spHypIdem_one_succ_succ]

private lemma toMatrix_mkFinCons_mkFinConsOfLE_row_succ_succ {K : Type} {V : Type*}
    [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {n j : ℕ} {B : BilinForm K V} {a b' : V} {W N₁ : Submodule K V}
    (c' : Basis (Fin n) K W) (hb'N₁ : b' ∈ N₁) (hNO : W ≤ N₁)
    (hli₁ : ∀ c : K, ∀ x ∈ W, c • b' + x = 0 → c = 0)
    (hsp₁ : ∀ z ∈ N₁, ∃ c : K, z + c • b' ∈ W)
    (hli₂ : ∀ c : K, ∀ x ∈ N₁, c • a + x = 0 → c = 0)
    (hsp₂ : ∀ z : V, ∃ c : K, z + c • a ∈ N₁)
    (hmemW'' : ∀ k : Fin n, B (c' k) a = 0) (hmemW''' : ∀ k : Fin n, B (c' k) b' = 0)
    (htrail : ∀ i k : Fin n, B (↑(c' i)) (↑(c' k)) = spHypIdem K n j i k) :
    ∀ (i : Fin n) (t : Fin (n + 2)),
      BilinForm.toMatrix
          (Basis.mkFinCons a (Basis.mkFinConsOfLE b' hb'N₁ c' hNO hli₁ hsp₁) hli₂ hsp₂) B
        i.succ.succ t = spHypIdem K (n + 2) (j + 1) i.succ.succ t := by
  intro i t
  induction t using Fin.cases with
  | zero =>
      simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Basis.coe_mkFinConsOfLE,
        Fin.cons_zero, Fin.cons_succ, Function.comp_apply, Submodule.coe_inclusion]
      rw [hmemW'' i, spHypIdem_succ_succ_zero]
  | succ t =>
      induction t using Fin.cases with
      | zero =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Basis.coe_mkFinConsOfLE,
            Fin.cons_zero, Fin.cons_succ, Function.comp_apply, Submodule.coe_inclusion]
          rw [hmemW''' i, spHypIdem_succ_succ_one]
      | succ t =>
          simp only [BilinForm.toMatrix_apply, Basis.coe_mkFinCons, Basis.coe_mkFinConsOfLE,
            Fin.cons_succ, Function.comp_apply, Submodule.coe_inclusion]
          rw [htrail i t, spHypIdem_succ_succ_succ_succ]

private lemma toMatrix_mkFinCons_mkFinConsOfLE_eq_spHypIdem {K : Type} {V : Type*}
    [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {n j : ℕ} {B : BilinForm K V} {a b' : V} {W N₁ : Submodule K V}
    (c' : Basis (Fin n) K W) (hb'N₁ : b' ∈ N₁) (hNO : W ≤ N₁)
    (hli₁ : ∀ c : K, ∀ x ∈ W, c • b' + x = 0 → c = 0)
    (hsp₁ : ∀ z ∈ N₁, ∃ c : K, z + c • b' ∈ W)
    (hli₂ : ∀ c : K, ∀ x ∈ N₁, c • a + x = 0 → c = 0)
    (hsp₂ : ∀ z : V, ∃ c : K, z + c • a ∈ N₁)
    (haa : B a a = 0) (hab : B a b' = 1) (hba : B b' a = 1) (hbb : B b' b' = 0)
    (hmemW : ∀ k : Fin n, B a (c' k) = 0) (hmemW' : ∀ k : Fin n, B b' (c' k) = 0)
    (hmemW'' : ∀ k : Fin n, B (c' k) a = 0) (hmemW''' : ∀ k : Fin n, B (c' k) b' = 0)
    (htrail : ∀ i k : Fin n, B (↑(c' i)) (↑(c' k)) = spHypIdem K n j i k) :
    BilinForm.toMatrix
        (Basis.mkFinCons a (Basis.mkFinConsOfLE b' hb'N₁ c' hNO hli₁ hsp₁)
          hli₂ hsp₂) B =
      spHypIdem K (n + 2) (j + 1) := by
  ext i j
  induction i using Fin.cases with
  | zero =>
      exact toMatrix_mkFinCons_mkFinConsOfLE_row_zero c' hb'N₁ hNO hli₁ hsp₁ hli₂ hsp₂
        haa hab hmemW j
  | succ i =>
      induction i using Fin.cases with
      | zero =>
          exact toMatrix_mkFinCons_mkFinConsOfLE_row_one c' hb'N₁ hNO hli₁ hsp₁ hli₂ hsp₂
            hbb hba hmemW' j
      | succ i =>
          exact toMatrix_mkFinCons_mkFinConsOfLE_row_succ_succ c' hb'N₁ hNO hli₁ hsp₁ hli₂
            hsp₂ hmemW'' hmemW''' htrail i j

private lemma inf_span_pair_eq_bot {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : BilinForm K V} {a b' : V} (hba : B b' a = 1) (hb'b' : B b' b' = 0) :
    K ∙ a ⊓ K ∙ b' = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx2
  have h : B b' (s • a) = B b' (t • b') := by rw [ht]
  rw [map_smul, smul_eq_mul, hba, mul_one, map_smul, smul_eq_mul, hb'b', mul_zero] at h
  rw [h, zero_smul]

private lemma finrank_span_pair {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {a b' : V} (hinf : K ∙ a ⊓ K ∙ b' = ⊥) (ha0 : a ≠ 0)
    (hb'0 : b' ≠ 0) : finrank K ↥(K ∙ a ⊔ K ∙ b') = 2 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ a) (K ∙ b')
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton ha0,
    finrank_span_singleton hb'0] at h1
  omega

private lemma disjoint_span_singleton_pair_orthogonal {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {B : BilinForm K V} (hB : B.IsSymm) {a b' : V} (hab' : B a b' = 1)
    (hb'b' : B b' b' = 0) :
    Disjoint (K ∙ b') (B.orthogonal (K ∙ a ⊔ K ∙ b')) ∧
      Disjoint (K ∙ a) (K ∙ b' ⊔ B.orthogonal (K ∙ a ⊔ K ∙ b')) := by
  have haP : a ∈ K ∙ a ⊔ K ∙ b' := Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)
  have hb'P : b' ∈ K ∙ a ⊔ K ∙ b' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self b')
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    have h : B a (t • b') = 0 := (BilinForm.mem_orthogonal_iff.mp hx2) a haP
    have ht : t = 0 := by simpa [hab'] using h
    rw [ht, zero_smul]
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hwb : B w b' = 0 := by
      rw [hB.eq]
      exact (BilinForm.mem_orthogonal_iff.mp hw) b' hb'P
    have h : B (s • b' + w) b' = 0 := by
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        hb'b', hwb, mul_zero, zero_add]
    rw [huw] at h
    have ht : t = 0 := by simpa [hab'] using h
    rw [ht, zero_smul]

private lemma hyperbolic_trailing_entries {K : Type} {V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {B : BilinForm K V} (hB : B.IsSymm) {a b' : V} {W : Submodule K V}
    (hW : W = B.orthogonal (K ∙ a ⊔ K ∙ b')) {n' j' : ℕ}
    (haP : a ∈ K ∙ a ⊔ K ∙ b') (hb'P : b' ∈ K ∙ a ⊔ K ∙ b')
    (c' : Basis (Fin n') K W)
    (hc' : BilinForm.toMatrix c' (B.restrict W) = spHypIdem K n' j') :
    (∀ k : Fin n', B a (c' k) = 0) ∧ (∀ k : Fin n', B b' (c' k) = 0) ∧
      (∀ k : Fin n', B (c' k) a = 0) ∧ (∀ k : Fin n', B (c' k) b' = 0) ∧
      (∀ i k : Fin n', B (↑(c' i)) (↑(c' k)) = spHypIdem K n' j' i k) := by
  have hmem : ∀ k : Fin n', (c' k : V) ∈ B.orthogonal (K ∙ a ⊔ K ∙ b') := by
    intro k
    rw [← hW]
    exact (c' k).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact (BilinForm.mem_orthogonal_iff.mp (hmem k)) a haP
  · intro k; exact (BilinForm.mem_orthogonal_iff.mp (hmem k)) b' hb'P
  · intro k; rw [hB.eq]; exact (BilinForm.mem_orthogonal_iff.mp (hmem k)) a haP
  · intro k; rw [hB.eq]; exact (BilinForm.mem_orthogonal_iff.mp (hmem k)) b' hb'P
  · intro i k
    have h := congrFun (congrFun hc' i) k
    rwa [BilinForm.toMatrix_apply] at h

private lemma exists_hyperbolic_pair_data {K : Type} {V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : BilinForm K V}
    (hB : B.IsSymm) (halt : B.IsAlt) (hB0 : B ≠ 0) {n : ℕ} (hd : finrank K V = n) :
    ∃ a b' : V, a ≠ 0 ∧ b' ≠ 0 ∧ B a a = 0 ∧ B a b' = 1 ∧ B b' a = 1 ∧ B b' b' = 0 ∧
      IsCompl (K ∙ a ⊔ K ∙ b') (B.orthogonal (K ∙ a ⊔ K ∙ b')) ∧
      finrank K ↥(K ∙ a ⊔ K ∙ b') = 2 ∧
      finrank K ↥(B.orthogonal (K ∙ a ⊔ K ∙ b')) = n - 2 ∧ 2 ≤ n := by
  obtain ⟨a, b, hab⟩ : ∃ a b : V, B a b ≠ 0 := by
    by_contra! h
    exact hB0 (BilinForm.ext h)
  have haa : B a a = 0 := halt a
  have hbb : B b b = 0 := halt b
  set c := (B a b)⁻¹ with hc_def
  have hc0 : c ≠ 0 := inv_ne_zero hab
  set b' := c • b with hb'_def
  have hab' : B a b' = 1 := by
    rw [hb'_def, map_smul, smul_eq_mul, hc_def, inv_mul_cancel₀ hab]
  have hba : B b' a = 1 := by rw [hB.eq, hab']
  have hb'b' : B b' b' = 0 := by
    rw [hb'_def, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, hbb]
    ring
  have ha0 : a ≠ 0 := fun h => by rw [h, map_zero] at hab'; exact zero_ne_one hab'
  have hb'0 : b' ≠ 0 := fun h => by rw [h, map_zero] at hab'; exact zero_ne_one hab'
  have hIC : IsCompl (K ∙ a ⊔ K ∙ b') (B.orthogonal (K ∙ a ⊔ K ∙ b')) :=
    isCompl_span_pair_orthogonal hB haa hb'b' hab'
  have hinf : K ∙ a ⊓ K ∙ b' = ⊥ := inf_span_pair_eq_bot hba hb'b'
  have hfinP : finrank K ↥(K ∙ a ⊔ K ∙ b') = 2 := finrank_span_pair hinf ha0 hb'0
  have hdW : finrank K ↥(B.orthogonal (K ∙ a ⊔ K ∙ b')) = n - 2 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hIC
    rw [hfinP, hd] at h1
    omega
  have hn2 : 2 ≤ n := by
    have hle : finrank K ↥(K ∙ a ⊔ K ∙ b') ≤ finrank K V := Submodule.finrank_le _
    rw [hfinP, hd] at hle
    exact hle
  exact ⟨a, b', ha0, hb'0, haa, hab', hba, hb'b', hIC, hfinP, hdW, hn2⟩

universe u

private theorem exists_basis_toMatrix_eq_spHypIdem_step {K : Type} [Field K] [CharP K 2]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n : ℕ)
    (ih : ∀ m < n, ∀ {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W],
      finrank K W = m → ∀ {B : BilinForm K W}, B.IsSymm → B.IsAlt →
      ∃ j, 2 * j ≤ m ∧ ∃ b : Basis (Fin m) K W, BilinForm.toMatrix b B = spHypIdem K m j)
    (hd : finrank K V = n) {B : BilinForm K V} (hB : B.IsSymm) (halt : B.IsAlt) :
    ∃ j, 2 * j ≤ n ∧ ∃ b : Basis (Fin n) K V, BilinForm.toMatrix b B = spHypIdem K n j := by
  by_cases hB0 : B = 0
  · refine ⟨0, by omega, Module.finBasisOfFinrankEq K V hd, ?_⟩
    rw [hB0]
    ext i j
    rw [BilinForm.toMatrix_apply, spHypIdem_apply]
    simp
  · obtain ⟨a, b', ha0, hb'0, haa, hab', hba, hb'b', hIC, hfinP, hdW, hn2⟩ :=
      exists_hyperbolic_pair_data hB halt hB0 hd
    obtain ⟨hdisj_b', hdisj_a⟩ := disjoint_span_singleton_pair_orthogonal hB hab' hb'b'
    set W := B.orthogonal (K ∙ a ⊔ K ∙ b') with hW_def
    obtain ⟨j', hj', c', hc'⟩ := ih (n - 2) (by omega) hdW (hB.restrict W) (fun x => halt x.1)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    obtain ⟨hmemW, hmemW', hmemW'', hmemW''', htrail⟩ :=
      hyperbolic_trailing_entries hB hW_def
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self a))
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b')) c' hc'
    set N₁ := K ∙ b' ⊔ W with hN₁_def
    have hb'N₁ : b' ∈ N₁ := Submodule.mem_sup_left (Submodule.mem_span_singleton_self b')
    let hb₁ : Basis (Fin (n' + 1)) K N₁ :=
      Basis.mkFinConsOfLE b' hb'N₁ c' le_sup_right
        (mkFinCons_li_of_disjoint hdisj_b' hb'0) (mkFinCons_sp_of_sup le_rfl)
    have hsup_a : K ∙ a ⊔ N₁ = ⊤ := by
      rw [hN₁_def, ← sup_assoc]
      exact hIC.sup_eq_top
    let hb₂ : Basis (Fin ((n' + 1) + 1)) K V :=
      Basis.mkFinCons a hb₁ (mkFinCons_li_of_disjoint hdisj_a ha0)
        (fun z => mkFinCons_sp_of_sup (le_of_eq hsup_a.symm) z Submodule.mem_top)
    refine ⟨j' + 1, by omega, hb₂, ?_⟩
    exact toMatrix_mkFinCons_mkFinConsOfLE_eq_spHypIdem c' hb'N₁ le_sup_right
      (mkFinCons_li_of_disjoint hdisj_b' hb'0) (mkFinCons_sp_of_sup le_rfl)
      (mkFinCons_li_of_disjoint hdisj_a ha0)
      (fun z => mkFinCons_sp_of_sup (le_of_eq hsup_a.symm) z Submodule.mem_top)
      haa hab' hba hb'b' hmemW hmemW' hmemW'' hmemW''' htrail

private theorem exists_basis_toMatrix_eq_spHypIdem {K : Type} [Field K] [CharP K 2] :
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = n → ∀ {B : BilinForm K V}, B.IsSymm → B.IsAlt →
      ∃ j, 2 * j ≤ n ∧ ∃ b : Basis (Fin n) K V,
        BilinForm.toMatrix b B = spHypIdem K n j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hd B hB halt
    exact exists_basis_toMatrix_eq_spHypIdem_step n ih hd hB halt

private lemma exists_GL_mul_mul_transpose_eq {K : Type} [Field K] {n : ℕ}
    {S M : Matrix (Fin n) (Fin n) K} (b : Basis (Fin n) K (Fin n → K))
    (hb : BilinForm.toMatrix b (Matrix.toBilin' S) = M) :
    ∃ P : GL (Fin n) K,
      (P : Matrix (Fin n) (Fin n) K) * S * (P : Matrix (Fin n) (Fin n) K)ᵀ = M := by
  set Q := (Pi.basisFun K (Fin n)).toMatrix b with hQ
  have hQS : Qᵀ * S * Q = M := by
    have h := BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K (Fin n)) b (Matrix.toBilin' S)
    rw [BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin'] at h
    exact h.trans hb
  have hQu : IsUnit Q := IsUnit.of_mul_eq_one _ (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  have hQtu : IsUnit Qᵀ := (Matrix.isUnit_transpose Q).mpr hQu
  refine ⟨hQtu.unit, ?_⟩
  rw [IsUnit.unit_spec, Matrix.transpose_transpose]
  exact hQS

theorem exists_mul_mul_transpose_eq_spDiagIdem_or_spHypIdem {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} {S : Matrix (Fin n) (Fin n) K} (hS : Sᵀ = S) (hS0 : S ≠ 0) :
    ∃ P : GL (Fin n) K,
      (∃ r, 1 ≤ r ∧ r ≤ n ∧ (P : Matrix (Fin n) (Fin n) K) * S * (P : Matrix (Fin n) (Fin n) K)ᵀ =
        spDiagIdem K n r) ∨
      (∃ j, 1 ≤ j ∧ 2 * j ≤ n ∧
        (P : Matrix (Fin n) (Fin n) K) * S * (P : Matrix (Fin n) (Fin n) K)ᵀ =
          spHypIdem K n j) := by
  have hsq : ∀ a : K, IsSquare a := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
  have hBsymm : (Matrix.toBilin' S).IsSymm := ⟨fun v w => by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hS, dotProduct_comm]⟩
  have hB0 : Matrix.toBilin' S ≠ 0 := fun h =>
    hS0 (Matrix.toBilin'.injective (by rw [h, map_zero]))
  have hd : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  by_cases halt : (Matrix.toBilin' S).IsAlt
  · obtain ⟨j, hj, b, hb⟩ :=
      exists_basis_toMatrix_eq_spHypIdem n hd hBsymm halt
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hB0 (by
        have h : BilinForm.toMatrix b (Matrix.toBilin' S) = 0 := by
          rw [hb, spHypIdem_zero]
        exact (BilinForm.toMatrix b).injective (by rw [h, map_zero]))
    obtain ⟨P, hP⟩ := exists_GL_mul_mul_transpose_eq b hb
    exact ⟨P, Or.inr ⟨j, by omega, hj, hP⟩⟩
  · obtain ⟨r, hr1, hrle, b, hb⟩ :=
      exists_basis_toMatrix_eq_spDiagIdem hsq n hd hBsymm halt
    obtain ⟨P, hP⟩ := exists_GL_mul_mul_transpose_eq b hb
    exact ⟨P, Or.inl ⟨r, hr1, hrle, hP⟩⟩

end CFSG.LocalAnalysis.WeakClosure81
