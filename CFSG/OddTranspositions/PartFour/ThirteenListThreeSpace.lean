module

public import CFSG.Fischer.Classification.PartIII.Beta.Forms
public import CFSG.Fischer.Classification.Orthogonal3.Local
public import CFSG.Fischer.Classification.PartIII.Beta.Transport
import CFSG.Fischer.Classification.PartIII.U.SixForms

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification

variable {m n : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem finrank_perpOne_of_ne_zero {v : Fin m → ZMod 3} (hv : f v v ≠ 0) :
    Module.finrank (ZMod 3) (F3.perpOne f v) = m - 1 := by
  have hr : LinearMap.range (f.flip v) = ⊤ :=
    LinearMap.range_eq_top.2 fun c => ⟨(c / f v v) • v, by
      show f ((c / f v v) • v) v = c
      rw [LinearMap.BilinForm.smul_left, div_mul_cancel₀ _ hv]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (f.flip v)
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  show Module.finrank (ZMod 3) (LinearMap.ker (f.flip v)) = m - 1
  omega

theorem isF3Form_restrictForm_of_ne_zero (hf : IsF3Form f) {v : Fin m → ZMod 3}
    (hv : f v v ≠ 0) (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    IsF3Form (restrictForm f e) := by
  have happ : ∀ x y, restrictForm f e x y = f (e.symm x) (e.symm y) := fun x y => by
    rw [← restrictForm_apply e, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨fun x y => by rw [happ, happ, hf.symm], fun x hx => ?_⟩
  have hs : ∀ z, f (e.symm x) z = 0 := fun z => by
    have hz : z - (f z v / f v v) • v ∈ F3.perpOne f v := F3.mem_perpOne.2 (by
      rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
        div_mul_cancel₀ _ hv, sub_self])
    have h1 := hx (e ⟨_, hz⟩)
    rw [happ, e.symm_apply_apply] at h1
    have h2 : f (e.symm x) v = 0 := F3.mem_perpOne.1 (e.symm x).2
    rw [show z = (z - (f z v / f v v) • v) + (f z v / f v v) • v by abel,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, h2, mul_zero, add_zero]
    exact h1
  have : ((e.symm x : F3.perpOne f v) : Fin m → ZMod 3) = 0 := hf.nondeg _ hs
  rw [← e.apply_symm_apply x, show e.symm x = 0 from Subtype.ext this, map_zero]

theorem perpToGL_injective_of_ne_zero (hf : IsF3Form f) {v : Fin m → ZMod 3}
    (hv : f v v ≠ 0) (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    Function.Injective (perpToGL e) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  have hW : ∀ x : F3.perpOne f v, F3.act (g : GL (Fin m) (ZMod 3)) x = x := fun x => by
    have := coe_perpToGL_symm e g (e x)
    rw [hg, F3.act_one, e.symm_apply_apply] at this
    exact this.symm
  have hfix := F3.act_eq_of_mem_reflGroupPerp hf g.2
  apply Subtype.ext
  refine F3.gl_ext fun x => ?_
  have hx : x - (f x v / f v v) • v ∈ F3.perpOne f v := F3.mem_perpOne.2 (by
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      div_mul_cancel₀ _ hv, sub_self])
  have := hW ⟨_, hx⟩
  simp only at this
  rw [F3.act_sub, F3.act_smul, hfix] at this
  rw [Subgroup.coe_one, F3.act_one]
  linear_combination (norm := module) this

open CFSG.Fischer.Classification.LocalU in
theorem exists_isometry_restrict_diagF3_norm {n : ℕ} (hn : 1 ≤ n) {δ c : ZMod 3}
    (hδ : δ ≠ 0) (hc : c ≠ 0) {v : Fin (n + 1) → ZMod 3}
    (hv : diagF3 (n + 1) δ v v = c)
    {f' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)} (hf' : IsF3Form f')
    (e : F3.perpOne (diagF3 (n + 1) δ) v ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (he : ∀ a b : F3.perpOne (diagF3 (n + 1) δ) v,
      f' (e a) (e b) = diagF3 (n + 1) δ a b) :
    ∃ e' : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3),
      ∀ x y, f' x y = diagF3 n (δ / c) (e' x) (e' y) := by
  obtain ⟨δ', e', hδ', he'⟩ := exists_linearEquiv_diagF3 hn hf'
  have hδ'0 : δ' ≠ 0 := by rcases hδ' with rfl | rfl <;> decide
  let b : Fin n → Fin (n + 1) → ZMod 3 := fun i => (e.symm (e'.symm (Pi.single i 1)) : _)
  have hbv : ∀ i, diagF3 (n + 1) δ (b i) v = 0 := fun i => F3.mem_perpOne.1 (e.symm _).2
  have hbb : ∀ i j, diagF3 (n + 1) δ (b i) (b j) =
      if i = j then diagF3Entry n δ' i else 0 := by
    intro i j
    rw [show b i = (e.symm (e'.symm (Pi.single i 1)) : _) from rfl,
      show b j = (e.symm (e'.symm (Pi.single j 1)) : _) from rfl,
      ← he, e.apply_symm_apply, e.apply_symm_apply, he', e'.apply_symm_apply,
      e'.apply_symm_apply, diagF3_single]
  let B : Fin (n + 1) → Fin (n + 1) → ZMod 3 := Fin.cons v b
  have hG : (Matrix.of fun i j => diagF3 (n + 1) δ (B i) (B j)) =
      Matrix.diagonal (Fin.cons c (diagF3Entry n δ')) := by
    ext i j
    rw [Matrix.of_apply, Matrix.diagonal_apply]
    have hvb : ∀ j, diagF3 (n + 1) δ v (b j) = 0 := fun j => by
      rw [(isF3Form_diagF3 hδ).symm]; exact hbv j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [B, hv]
    · simp [B, hvb, (Fin.succ_ne_zero _).symm]
    · simp [B, hbv, Fin.succ_ne_zero]
    · simp [B, hbb, Fin.succ_inj]
  have hdet := det_gram_diagF3 δ B
  rw [hG, Matrix.det_diagonal, Fin.prod_univ_succ, Fin.cons_zero] at hdet
  simp only [Fin.cons_succ] at hdet
  rw [prod_diagF3Entry hn, prod_diagF3Entry (by omega)] at hdet
  have hP : (Matrix.of fun i j => B j i).det ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide), zero_mul] at hdet
    exact (mul_ne_zero hc hδ'0) hdet
  rw [sq_eq_one_of_ne_zero hP, one_mul] at hdet
  have hδ'eq : δ' = δ / c := (eq_div_iff hc).mpr (by simpa [mul_comm] using hdet)
  exact ⟨e', fun x y => by rw [he', hδ'eq]⟩

theorem exists_reflGroup_perp_embedding (hf : IsF3Form f) {u : Fin m → ZMod 3}
    (hu : f u u ≠ 0) (e : F3.perpOne f u ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    {f' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}
    (he : ∀ a b : F3.perpOne f u, f' (e a) (e b) = f a b) :
    ∃ ψ : F3.reflGroup f' →* F3.reflGroup f,
      Function.Injective ψ ∧
      (∀ g, F3.act (ψ g : GL (Fin m) (ZMod 3)) u = u) ∧
      (∀ (w : Fin m → ZMod 3) (_hw : f w w = 1) (hwu : f w u = 0),
        (ψ ⟨F3.refl f' (e ⟨w, F3.mem_perpOne.2 hwu⟩),
          F3.refl_mem_reflGroup _⟩ : GL (Fin m) (ZMod 3)) = F3.refl f w) := by
  let ε : F3.reflGroupPerp f u ≃* F3.reflGroup f' :=
    (MonoidHom.ofInjective (perpToGL_injective_of_ne_zero hf hu e)).trans
      (MulEquiv.subgroupCongr (range_perpToGL e he))
  refine ⟨(Subgroup.inclusion (F3.reflGroupPerp_le_reflGroup u)).comp ε.symm.toMonoidHom,
    (Subgroup.inclusion_injective (F3.reflGroupPerp_le_reflGroup u)).comp ε.symm.injective,
    fun g => ?_, fun w hw hwu => ?_⟩
  · exact F3.act_eq_of_mem_reflGroupPerp hf (ε.symm g).2
  · have hε : ε ⟨F3.refl f w, refl_mem_reflGroupPerp hw hwu⟩ =
        ⟨F3.refl f' (e ⟨w, F3.mem_perpOne.2 hwu⟩),
          F3.refl_mem_reflGroup _⟩ :=
      Subtype.ext (perpToGL_refl e he hw hwu)
    change ((ε.symm _ : F3.reflGroupPerp f u) : GL (Fin m) (ZMod 3)) = _
    rw [← hε, MulEquiv.symm_apply_apply]

theorem reflGroupEquiv_refl {m : ℕ}
    {f f' : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    {e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)}
    (he : ∀ x y, f x y = f' (e x) (e y)) (v : Fin m → ZMod 3) :
    Beta.reflGroupEquiv he ⟨F3.refl f v, F3.refl_mem_reflGroup v⟩ =
      ⟨F3.refl f' (e v), F3.refl_mem_reflGroup _⟩ :=
  Subtype.ext (Beta.glOf_conj_refl he v)

theorem coe_reflGroupEquiv_eq_neg_one {m : ℕ}
    {f f' : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    {e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)}
    (he : ∀ x y, f x y = f' (e x) (e y)) {g : F3.reflGroup f}
    (hg : (g : GL (Fin m) (ZMod 3)) = -1) :
    (Beta.reflGroupEquiv he g : GL (Fin m) (ZMod 3)) = -1 := by
  rw [Beta.coe_reflGroupEquiv, hg, mul_neg_one, neg_mul, mul_inv_cancel]

theorem exists_reflGroup_embedding_of_isometries {m n : ℕ}
    {f f' : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    {g g' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}
    {e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)}
    {a : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)}
    (he : ∀ x y, f x y = f' (e x) (e y))
    (ha : ∀ x y, g x y = g' (a x) (a y))
    (ψ : F3.reflGroup g →* F3.reflGroup f') (hψ : Function.Injective ψ)
    {v : Fin m → ZMod 3} {w : Fin n → ZMod 3}
    (hψr : ψ ⟨F3.refl g w, F3.refl_mem_reflGroup _⟩ =
      ⟨F3.refl f' (e v), F3.refl_mem_reflGroup _⟩)
    (hne : ∀ x, (ψ x : GL (Fin m) (ZMod 3)) ≠ -1) :
    ∃ Φ : F3.reflGroup g' →* F3.reflGroup f, Function.Injective Φ ∧
      (Φ ⟨F3.refl g' (a w), F3.refl_mem_reflGroup _⟩ : GL (Fin m) (ZMod 3)) = F3.refl f v ∧
      (∀ x, (Φ x : GL (Fin m) (ZMod 3)) ≠ -1) := by
  let β := Beta.reflGroupEquiv he
  let α := Beta.reflGroupEquiv ha
  let Φ := β.symm.toMonoidHom.comp (ψ.comp α.symm.toMonoidHom)
  refine ⟨Φ, β.symm.injective.comp (hψ.comp α.symm.injective), ?_, fun x hx => ?_⟩
  · have hα := reflGroupEquiv_refl ha w
    have hβ := reflGroupEquiv_refl he v
    change (β.symm (ψ (α.symm _)) : GL (Fin m) (ZMod 3)) = _
    rw [← hα, MulEquiv.symm_apply_apply, hψr, ← hβ, MulEquiv.symm_apply_apply]
  · apply hne (α.symm x)
    have h := coe_reflGroupEquiv_eq_neg_one he hx
    have hβ : β (Φ x) = ψ (α.symm x) := β.apply_symm_apply _
    change (β (Φ x) : GL (Fin m) (ZMod 3)) = -1 at h
    rwa [hβ] at h

private theorem exists_reflGroup_split_six_embedding_seven
    (f : LinearMap.BilinForm (ZMod 3) (Fin 7 → ZMod 3)) (hf : IsF3Form f)
    (v : Fin 7 → ZMod 3) (hv : f v v = 1) :
    ∃ c : Fin 6 → ZMod 3, diagF3 6 2 c c = 1 ∧
      ∃ Φ : F3.reflGroup (diagF3 6 2) →* F3.reflGroup f,
        Function.Injective Φ ∧
        (Φ ⟨F3.refl (diagF3 6 2) c, F3.refl_mem_reflGroup c⟩ : GL (Fin 7) (ZMod 3)) =
          F3.refl f v ∧ (∀ g, (Φ g : GL (Fin 7) (ZMod 3)) ≠ -1) := by
  obtain ⟨δ, E, hδ, hE⟩ := exists_linearEquiv_diagF3 (by omega) hf
  have hδ0 : δ ≠ 0 := by rcases hδ with rfl | rfl <;> decide
  have hc0 : δ / 2 ≠ 0 := div_ne_zero hδ0 (by decide)
  have hvE : diagF3 7 δ (E v) (E v) = 1 := by rw [← hE]; exact hv
  obtain ⟨u, hu, huv⟩ := F3.exists_norm_eq_perp (isF3Form_diagF3 hδ0) (by omega) hvE hc0
  obtain ⟨e⟩ : Nonempty (F3.perpOne (diagF3 7 δ) u ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)) :=
    ⟨LinearEquiv.ofFinrankEq _ _ (by
      rw [finrank_perpOne_of_ne_zero (hu ▸ hc0), Module.finrank_fin_fun])⟩
  obtain ⟨f₆, hf₆eq⟩ : ∃ f₆, f₆ = restrictForm (diagF3 7 δ) e := ⟨_, rfl⟩
  have hf₆ : IsF3Form f₆ := hf₆eq ▸
    isF3Form_restrictForm_of_ne_zero (isF3Form_diagF3 hδ0) (hu ▸ hc0) e
  have hfe : ∀ a b : F3.perpOne (diagF3 7 δ) u, f₆ (e a) (e b) = diagF3 7 δ a b := by
    rw [hf₆eq]
    exact restrictForm_apply e
  obtain ⟨E₆, hE₆⟩ := exists_isometry_restrict_diagF3_norm (by omega) hδ0 hc0 hu hf₆ e hfe
  have hδdiv : δ / (δ / 2) = 2 := div_div_cancel₀ hδ0
  rw [hδdiv] at hE₆
  have hvu : diagF3 7 δ (E v) u = 0 := by rw [(isF3Form_diagF3 hδ0).symm]; exact huv
  let w : F3.perpOne (diagF3 7 δ) u := ⟨E v, F3.mem_perpOne.2 hvu⟩
  have hw : f₆ (e w) (e w) = 1 := by rw [hfe]; exact hvE
  obtain ⟨ψ, hψ, hfix, hψr⟩ := exists_reflGroup_perp_embedding (isF3Form_diagF3 hδ0)
    (hu ▸ hc0) e hfe
  have hψr' : ψ ⟨F3.refl f₆ (e w), F3.refl_mem_reflGroup _⟩ =
      ⟨F3.refl (diagF3 7 δ) (E v), F3.refl_mem_reflGroup _⟩ :=
    Subtype.ext (hψr (E v) hvE hvu)
  have hne : ∀ g, (ψ g : GL (Fin 7) (ZMod 3)) ≠ -1 := by
    intro g hg
    have h := hfix g
    rw [hg, F3.act_neg_one] at h
    have hu0 : u = 0 := F3.eq_zero_of_eq_neg h.symm
    rw [hu0, LinearMap.BilinForm.zero_left] at hu
    exact hc0 hu.symm
  exact ⟨E₆ (e w), by rw [← hE₆]; exact hw,
    exists_reflGroup_embedding_of_isometries hE hE₆ ψ hψ hψr' hne⟩

theorem exists_reflGroup_split_six_embedding {m : ℕ} (hm : 7 ≤ m) :
    ∀ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3), IsF3Form f →
      ∀ v : Fin m → ZMod 3, f v v = 1 →
      ∃ c : Fin 6 → ZMod 3, diagF3 6 2 c c = 1 ∧
        ∃ Φ : F3.reflGroup (diagF3 6 2) →* F3.reflGroup f,
          Function.Injective Φ ∧
          (Φ ⟨F3.refl (diagF3 6 2) c, F3.refl_mem_reflGroup c⟩ : GL (Fin m) (ZMod 3)) =
            F3.refl f v ∧
          (∀ g, (Φ g : GL (Fin m) (ZMod 3)) ≠ -1) := by
  induction m, hm using Nat.le_induction with
  | base => exact exists_reflGroup_split_six_embedding_seven
  | succ m hm ih =>
    intro f hf v hv
    obtain ⟨u, hu, huv⟩ := F3.exists_norm_eq_perp hf (by omega) hv (one_ne_zero (α := ZMod 3))
    let e : F3.perpOne f u ≃ₗ[ZMod 3] (Fin m → ZMod 3) :=
      LinearEquiv.ofFinrankEq _ _ (by
        rw [F3.finrank_perpOne hu, Module.finrank_fin_fun, Nat.add_sub_cancel])
    have hvu : f v u = 0 := by rw [hf.symm]; exact huv
    have hv' : restrictForm f e (e ⟨v, F3.mem_perpOne.2 hvu⟩)
        (e ⟨v, F3.mem_perpOne.2 hvu⟩) = 1 := by rw [restrictForm_apply]; exact hv
    obtain ⟨c, hc, Φ, hΦ, hΦc, -⟩ := ih (restrictForm f e) (isF3Form_restrictForm hf hu e) _ hv'
    obtain ⟨ψ, hψ, hfix, hψr⟩ :=
      exists_reflGroup_perp_embedding hf (hu ▸ one_ne_zero) e (restrictForm_apply e)
    refine ⟨c, hc, ψ.comp Φ, hψ.comp hΦ, ?_, fun g hg => ?_⟩
    · have hΦc' : Φ ⟨F3.refl (diagF3 6 2) c, F3.refl_mem_reflGroup _⟩ =
          ⟨F3.refl (restrictForm f e) (e ⟨v, F3.mem_perpOne.2 hvu⟩), F3.refl_mem_reflGroup _⟩ :=
        Subtype.ext hΦc
      change (ψ (Φ _) : GL (Fin (m + 1)) (ZMod 3)) = _
      rw [hΦc']
      exact hψr v hv hvu
    · have h := hfix (Φ g)
      change (ψ (Φ g) : GL (Fin (m + 1)) (ZMod 3)) = -1 at hg
      rw [hg, F3.act_neg_one] at h
      exact F3.ne_zero_of_norm_one hu (F3.eq_zero_of_eq_neg h.symm)

theorem exists_totallySingular_diagF3_six_two :
    ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
      ∀ x ∈ T, LinearMap.BilinMap.toQuadraticMap (diagF3 6 2) x = 0 := by
  let j : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
    { toFun := fun x => ![x 0 + x 1, x 0 - x 1, x 0, x 1, x 2, x 2]
      map_add' := fun x y => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun a x => by ext i; fin_cases i <;> simp [mul_add, mul_sub] }
  have hj : Function.Injective j := by
    intro x y h
    have ha := congrFun h (2 : Fin 6)
    have hb := congrFun h (3 : Fin 6)
    have hc := congrFun h (4 : Fin 6)
    ext i
    fin_cases i
    · simpa [j] using ha
    · simpa [j] using hb
    · simpa [j] using hc
  refine ⟨j.range, by rw [LinearMap.finrank_range_of_inj hj, Module.finrank_fin_fun], ?_⟩
  rintro x ⟨a, rfl⟩
  rw [LinearMap.BilinMap.toQuadraticMap_apply, diagF3_apply]
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one]
  simp [j, diagF3Entry]
  ring_nf
  simp [show (3 : ZMod 3) = 0 by decide]

end CFSG.OddTranspositions.PartFour
