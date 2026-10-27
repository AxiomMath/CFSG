module

public import CFSG.Quasithin.Background.C116Two.NatLin2Defs

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open
open scoped Matrix

private theorem lines_addMap_zero {N : Type} [AddCommGroup N] (g : MulAut (Multiplicative N)) :
    addMap g 0 = 0 := by
  simp [addMap]

private theorem lines_addMap_inj {N : Type} [AddCommGroup N] (g : MulAut (Multiplicative N)) :
    Function.Injective (addMap g) := by
  intro x y h
  have h1 : g (Multiplicative.ofAdd x) = g (Multiplicative.ofAdd y) :=
    Multiplicative.toAdd.injective h
  exact Multiplicative.ofAdd.injective (g.injective h1)

private theorem lines_addMap_ne_zero {N : Type} [AddCommGroup N] (g : MulAut (Multiplicative N))
    {x : N} (hx : x ≠ 0) : addMap g x ≠ 0 := by
  intro h
  apply hx
  apply lines_addMap_inj g
  rw [h, lines_addMap_zero]

private theorem lines_exists_transvec {F : Type} [Field F] (v : Fin 2 → F) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) F, ∀ z : Fin 2 → F,
      (M : Matrix (Fin 2) (Fin 2) F) *ᵥ z = z + (v 0 * z 1 - v 1 * z 0) • v := by
  refine ⟨⟨!![1 - v 0 * v 1, v 0 * v 0; -(v 1 * v 1), 1 + v 0 * v 1], ?_⟩, fun z => ?_⟩
  · rw [Matrix.det_fin_two_of]; ring
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

private theorem lines_fix_of_fixed {F : Type} [Field F] (g : MulAut (Multiplicative (Fin 2 → F)))
    (B M : Matrix.SpecialLinearGroup (Fin 2) F) (hB : slAct F B = g * slAct F M * g⁻¹)
    (z : Fin 2 → F) (hz : (M : Matrix (Fin 2) (Fin 2) F) *ᵥ z = z) :
    (B : Matrix (Fin 2) (Fin 2) F) *ᵥ addMap g z = addMap g z := by
  have h3 : slAct F M (Multiplicative.ofAdd z) = Multiplicative.ofAdd z := by
    apply Multiplicative.toAdd.injective
    simpa [slAct_apply] using hz
  have h1 : slAct F B (g (Multiplicative.ofAdd z)) = g (Multiplicative.ofAdd z) := by
    rw [hB, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, h3]
  have h4 := congrArg Multiplicative.toAdd h1
  rw [slAct_apply] at h4
  exact h4

private theorem lines_mat_one_of_fixed {F : Type} [Field F]
    (g : MulAut (Multiplicative (Fin 2 → F))) (B M : Matrix.SpecialLinearGroup (Fin 2) F)
    (hB : slAct F B = g * slAct F M * g⁻¹)
    (hall : ∀ w : Fin 2 → F, (B : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w) (z : Fin 2 → F) :
    (M : Matrix (Fin 2) (Fin 2) F) *ᵥ z = z := by
  have hfix : slAct F B (g (Multiplicative.ofAdd z)) = g (Multiplicative.ofAdd z) := by
    apply Multiplicative.toAdd.injective
    rw [slAct_apply]
    exact hall _
  have h1 : g (slAct F M (Multiplicative.ofAdd z)) = g (Multiplicative.ofAdd z) := by
    rw [← hfix, hB, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have h2 := congrArg Multiplicative.toAdd (g.injective h1)
  simpa [slAct_apply] using h2

private theorem lines_transvec_not_all_fixed {F : Type} [Field F] {v : Fin 2 → F} (hv : v ≠ 0)
    (M : Matrix.SpecialLinearGroup (Fin 2) F)
    (hM : ∀ z : Fin 2 → F, (M : Matrix (Fin 2) (Fin 2) F) *ᵥ z = z + (v 0 * z 1 - v 1 * z 0) • v)
    (hall : ∀ z : Fin 2 → F, (M : Matrix (Fin 2) (Fin 2) F) *ᵥ z = z) : False := by
  have e0 := hM ![1, 0]
  have e1 := hM ![0, 1]
  rw [hall] at e0 e1
  have hc0 := add_eq_left.mp e0.symm
  have hc1 := add_eq_left.mp e1.symm
  have hv1 : v 1 = 0 := by
    rcases smul_eq_zero.mp hc0 with h | h
    · simpa using h
    · exact absurd h hv
  have hv0 : v 0 = 0 := by
    rcases smul_eq_zero.mp hc1 with h | h
    · simpa using h
    · exact absurd h hv
  exact hv (by funext i; fin_cases i <;> simp [hv0, hv1])

private theorem lines_fix_all {F : Type} [Field F] (B : Matrix (Fin 2) (Fin 2) F) (x y : Fin 2 → F)
    (hx : B *ᵥ x = x) (hy : B *ᵥ y = y) (hd : x 0 * y 1 - x 1 * y 0 ≠ 0) (z : Fin 2 → F) :
    B *ᵥ z = z := by
  have key : ∀ a b : F, B *ᵥ (a • x + b • y) = a • x + b • y := by
    intro a b
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hy]
  obtain ⟨a, ha⟩ : ∃ a : F, a = (z 0 * y 1 - z 1 * y 0) / (x 0 * y 1 - x 1 * y 0) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : F, b = (x 0 * z 1 - x 1 * z 0) / (x 0 * y 1 - x 1 * y 0) := ⟨_, rfl⟩
  have hd2 : y 1 * x 0 - y 0 * x 1 ≠ 0 := by
    intro h
    apply hd
    linear_combination h
  have hz : z = a • x + b • y := by
    rw [ha, hb]
    funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  have h := key a b
  rw [← hz] at h
  exact h

private theorem lines_smul_of_det_zero {F : Type} [Field F] {x y : Fin 2 → F} (hx : x ≠ 0)
    (hd : x 0 * y 1 - x 1 * y 0 = 0) : ∃ d : F, y = d • x := by
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      funext i
      fin_cases i <;> simp [h0, h1]
    have hy0 : y 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at hd
      exact (mul_eq_zero.mp hd).resolve_left h1
    refine ⟨y 1 / x 1, ?_⟩
    funext i
    fin_cases i <;> simp [h0, hy0, h1]
  · refine ⟨y 0 / x 0, ?_⟩
    funext i
    fin_cases i
    · simp [h0]
    · simp [h0]
      field_simp
      linear_combination hd

theorem normalizer_maps_lines {F : Type} [Field F] [Fintype F] [CharP F 2]
    (g : MulAut (Multiplicative (Fin 2 → F)))
    (hg : ∀ l ∈ (slAct F).range, g * l * g⁻¹ ∈ (slAct F).range) :
    ∀ v : Fin 2 → F, v ≠ 0 → ∃ w : Fin 2 → F, w ≠ 0 ∧ ∀ c : F, ∃ d : F,
      addMap g (c • v) = d • w := by
  intro v hv
  obtain ⟨M, hM⟩ := lines_exists_transvec v
  obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp
    (hg (slAct F M) (MonoidHom.mem_range.mpr ⟨M, rfl⟩))
  have hMv : (M : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
    rw [hM v, show v 0 * v 1 - v 1 * v 0 = 0 by ring, zero_smul, add_zero]
  refine ⟨addMap g v, lines_addMap_ne_zero g hv, fun c => ?_⟩
  have hx := lines_fix_of_fixed g B M hB (c • v) (by rw [Matrix.mulVec_smul, hMv])
  have hy := lines_fix_of_fixed g B M hB v hMv
  have hdet : addMap g v 0 * addMap g (c • v) 1 - addMap g v 1 * addMap g (c • v) 0 = 0 := by
    by_contra hne
    have hall := lines_fix_all (B : Matrix (Fin 2) (Fin 2) F) _ _ hy hx hne
    exact lines_transvec_not_all_fixed hv M hM (lines_mat_one_of_fixed g B M hB hall)
  exact lines_smul_of_det_zero (lines_addMap_ne_zero g hv) hdet

private theorem lines_smul_cancel {F : Type} [Field F] {v : Fin 2 → F} (hv : v ≠ 0) {a b : F}
    (h : a • v = b • v) : a = b := by
  have h' : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h' with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hv

private theorem lines_coeff_zero {F : Type} [Field F] {u v : Fin 2 → F} (hv : v ≠ 0)
    (hnot : ∀ k : F, u ≠ k • v) {p q : F} (h : p • u + q • v = 0) : p = 0 ∧ q = 0 := by
  by_cases hp : p = 0
  · rw [hp, zero_smul, zero_add] at h
    exact ⟨hp, (smul_eq_zero.mp h).resolve_right hv⟩
  · exfalso
    have h2 : p • u = -(q • v) := eq_neg_of_add_eq_zero_left h
    have hu : u = (-(p⁻¹ * q)) • v := by
      calc u = p⁻¹ • (p • u) := by rw [smul_smul, inv_mul_cancel₀ hp, one_smul]
        _ = p⁻¹ • (-(q • v)) := by rw [h2]
        _ = (-(p⁻¹ * q)) • v := by rw [smul_neg, smul_smul, neg_smul]
    exact hnot _ hu

private theorem lines_scal_exists {F : Type} [Field F] (g : MulAut (Multiplicative (Fin 2 → F)))
    (hg : ∀ v : Fin 2 → F, v ≠ 0 → ∃ w : Fin 2 → F, w ≠ 0 ∧ ∀ c : F, ∃ d : F,
      addMap g (c • v) = d • w)
    {x : Fin 2 → F} (hx : x ≠ 0) :
    ∃ σ : F → F, ∀ c : F, addMap g (c • x) = σ c • addMap g x := by
  obtain ⟨w, _, hw⟩ := hg x hx
  choose d hd using hw
  have h1 : addMap g x = d 1 • w := by
    have h := hd 1
    rwa [one_smul] at h
  have hd1 : d 1 ≠ 0 := by
    intro h
    apply lines_addMap_ne_zero g hx
    rw [h1, h, zero_smul]
  refine ⟨fun c => d c * (d 1)⁻¹, fun c => ?_⟩
  show addMap g (c • x) = (d c * (d 1)⁻¹) • addMap g x
  rw [hd c, h1, smul_smul, mul_assoc, inv_mul_cancel₀ hd1, mul_one]

private theorem lines_lam_surj {F : Type} [Field F] [Finite F]
    (g : MulAut (Multiplicative (Fin 2 → F)))
    (lam : (Fin 2 → F) → F → F)
    (hlam : ∀ x : Fin 2 → F, x ≠ 0 → ∀ c : F, addMap g (c • x) = lam x c • addMap g x)
    {x : Fin 2 → F} (hx : x ≠ 0) (k : F) : ∃ c : F, lam x c = k := by
  have hinj : Function.Injective (lam x) := by
    intro c c' h
    apply lines_smul_cancel hx
    apply lines_addMap_inj g
    rw [hlam x hx c, hlam x hx c', h]
  exact Finite.injective_iff_surjective.mp hinj k

private theorem lines_lam_indep {F : Type} [Field F] [Finite F]
    (g : MulAut (Multiplicative (Fin 2 → F)))
    (lam : (Fin 2 → F) → F → F)
    (hlam : ∀ x : Fin 2 → F, x ≠ 0 → ∀ c : F, addMap g (c • x) = lam x c • addMap g x)
    {v w : Fin 2 → F} (hv : v ≠ 0) (hnot : ∀ k : F, w ≠ k • v) (c : F) :
    lam v c = lam w c := by
  have hw : w ≠ 0 := by simpa using hnot 0
  have hs : v + w ≠ 0 := by
    intro h
    apply hnot (-1)
    rw [neg_one_smul]
    exact eq_neg_of_add_eq_zero_right h
  have hfv : addMap g v ≠ 0 := lines_addMap_ne_zero g hv
  have hsum := hlam (v + w) hs c
  rw [smul_add, addMap_add, addMap_add, hlam v hv c, hlam w hw c] at hsum
  have key : (lam (v + w) c - lam w c) • addMap g w + (lam (v + w) c - lam v c) • addMap g v
      = lam (v + w) c • (addMap g v + addMap g w)
        - (lam v c • addMap g v + lam w c • addMap g w) := by
    module
  have hcoef : (lam (v + w) c - lam w c) • addMap g w + (lam (v + w) c - lam v c) • addMap g v
      = 0 := by
    rw [key, hsum, sub_self]
  have hnot' : ∀ k : F, addMap g w ≠ k • addMap g v := by
    intro k hk
    obtain ⟨c', hc'⟩ := lines_lam_surj g lam hlam hv k
    apply hnot c'
    apply lines_addMap_inj g
    rw [hlam v hv c', hc']
    exact hk
  obtain ⟨hp, hq⟩ := lines_coeff_zero hfv hnot' hcoef
  exact (sub_eq_zero.mp hq).symm.trans (sub_eq_zero.mp hp)

private theorem lines_exists_indep {F : Type} [Field F] (v : Fin 2 → F) :
    ∃ u : Fin 2 → F, ∀ k : F, u ≠ k • v := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha⟩ := hcon (Pi.single 0 1)
  obtain ⟨b, hb⟩ := hcon (Pi.single 1 1)
  have h0 : (1 : F) = a * v 0 := by simpa [Pi.single_apply] using congrFun ha 0
  have h1 : a * v 1 = 0 := by simpa [Pi.single_apply] using (congrFun ha 1).symm
  have h2 : (1 : F) = b * v 1 := by simpa [Pi.single_apply] using congrFun hb 1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h0
    exact one_ne_zero h0
  have hv1 : v 1 = 0 := (mul_eq_zero.mp h1).resolve_left ha0
  rw [hv1, mul_zero] at h2
  exact one_ne_zero h2

private theorem lines_lam_eq {F : Type} [Field F] [Finite F]
    (g : MulAut (Multiplicative (Fin 2 → F)))
    (lam : (Fin 2 → F) → F → F)
    (hlam : ∀ x : Fin 2 → F, x ≠ 0 → ∀ c : F, addMap g (c • x) = lam x c • addMap g x)
    {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) : lam v = lam w := by
  funext c
  by_cases hdep : ∃ k : F, w = k • v
  · obtain ⟨u, hu⟩ := lines_exists_indep v
    have hu0 : u ≠ 0 := by simpa using hu 0
    have huw : ∀ k : F, w ≠ k • u := by
      intro k hk
      obtain ⟨m, hm⟩ := hdep
      by_cases hk0 : k = 0
      · exact hw (by rw [hk, hk0, zero_smul])
      · apply hu (k⁻¹ * m)
        calc u = (k⁻¹ * k) • u := by rw [inv_mul_cancel₀ hk0, one_smul]
          _ = k⁻¹ • (k • u) := by rw [mul_smul]
          _ = k⁻¹ • (m • v) := by rw [← hk, ← hm]
          _ = (k⁻¹ * m) • v := by rw [smul_smul]
    exact (lines_lam_indep g lam hlam hv hu c).trans (lines_lam_indep g lam hlam hu0 huw c)
  · push_neg at hdep
    exact lines_lam_indep g lam hlam hv hdep c

theorem semilinear_of_maps_lines {F : Type} [Field F] [Finite F]
    (g : MulAut (Multiplicative (Fin 2 → F)))
    (hg : ∀ v : Fin 2 → F, v ≠ 0 → ∃ w : Fin 2 → F, w ≠ 0 ∧ ∀ c : F, ∃ d : F,
      addMap g (c • v) = d • w) :
    ∃ σ : F ≃+* F, IsSemilinear σ g := by
  have hex : ∀ x : Fin 2 → F, x ≠ 0 → ∃ σ : F → F, ∀ c : F, addMap g (c • x) = σ c • addMap g x :=
    fun x hx => lines_scal_exists g hg hx
  choose! lam hlam using hex
  obtain ⟨e, he0⟩ : ∃ e : Fin 2 → F, e ≠ 0 := by
    refine ⟨Pi.single 0 1, fun h => ?_⟩
    have h10 : (1 : F) = 0 := by simpa [Pi.single_apply] using congrFun h 0
    exact one_ne_zero h10
  have hfe : addMap g e ≠ 0 := lines_addMap_ne_zero g he0
  have hsem : ∀ (c : F) (x : Fin 2 → F), addMap g (c • x) = lam e c • addMap g x := by
    intro c x
    by_cases hx : x = 0
    · subst hx
      simp [lines_addMap_zero]
    · rw [hlam x hx c, lines_lam_eq g lam hlam hx he0]
  have h0 : lam e 0 = 0 := by
    have h := hsem 0 e
    rw [zero_smul, lines_addMap_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_right hfe
  have h1 : lam e 1 = 1 := by
    have h := hsem 1 e
    rw [one_smul] at h
    exact lines_smul_cancel hfe (by rw [one_smul]; exact h.symm)
  have hadd : ∀ a b : F, lam e (a + b) = lam e a + lam e b := by
    intro a b
    apply lines_smul_cancel hfe
    rw [← hsem (a + b) e, add_smul a b e, addMap_add, hsem a e, hsem b e,
      add_smul (lam e a) (lam e b)]
  have hmul : ∀ a b : F, lam e (a * b) = lam e a * lam e b := by
    intro a b
    apply lines_smul_cancel hfe
    rw [← hsem (a * b) e, mul_smul a b e, hsem a (b • e), hsem b e,
      smul_smul (lam e a) (lam e b)]
  let σh : F →+* F :=
    { toFun := lam e
      map_one' := h1
      map_mul' := hmul
      map_zero' := h0
      map_add' := hadd }
  have hinj : Function.Injective σh := RingHom.injective σh
  have hsurj : Function.Surjective σh := Finite.injective_iff_surjective.mp hinj
  refine ⟨RingEquiv.ofBijective σh ⟨hinj, hsurj⟩, ?_⟩
  intro c x
  exact hsem c x

theorem exists_semilinear_of_normalizer {F : Type} [Field F] [Fintype F] [CharP F 2]
    (g : MulAut (Multiplicative (Fin 2 → F)))
    (hg : ∀ l ∈ (slAct F).range, g * l * g⁻¹ ∈ (slAct F).range) :
    ∃ σ : F ≃+* F, IsSemilinear σ g :=
  semilinear_of_maps_lines g (normalizer_maps_lines g hg)

end CFSG.Quasithin.C116Two
