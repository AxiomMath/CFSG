module

public import CFSG.Quasithin.MS93.ML3Sec

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin Matrix ML3

variable {F : Type} [Field F]

namespace ML3

theorem cyc_mul_cyc_mulVec_e0 :
    ((cyc * cyc : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![0, 0, 1] := by
  rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, coe_cyc]
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem diagPt_mulVec_e0 (a : F) (ha : a ≠ 0) :
    ((diagPt a ha : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = a • ![1, 0, 0] := by
  rw [diagPt_mulVec]
  funext k
  fin_cases k <;> simp

theorem diagPt_apply_zero_zero (a : F) (ha : a ≠ 0) :
    ((diagPt a ha : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 = a := by
  rw [diagPt, SpecialLinearGroup.diag2n_coe]
  simp

theorem mem_ptStab_of_mulVec_e0 {g : SL3 F}
    (h : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) :
    g ∈ (ptStab : Subgroup (SL3 F)) ∧ ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
  rw [mulVec_e0] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  exact ⟨⟨h1, h2⟩, h0⟩

theorem mulVec_e0_ne_zero (g : SL3 F) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] ≠ 0 := by
  intro h
  have h' := congrArg (fun v => ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) h
  simp only [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3,
    Matrix.one_mulVec, Matrix.mulVec_zero] at h'
  have := congrFun h' 0
  simp at this

theorem exists_stab_mulVec_e2_eq {u : Fin 3 → F} (hu : u ∉ pt0) :
    ∃ k : SL3 F, ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] ∧
      ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = u := by
  rw [mem_pt0, not_and_or] at hu
  by_cases h2 : u 2 = 0
  · have h1 : u 1 ≠ 0 := by
      rcases hu with h | h
      · exact h
      · exact absurd h2 h
    refine ⟨⟨!![1, 0, u 0; 0, 0, u 1; 0, -(u 1)⁻¹, u 2], ?_⟩, ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [h1, h2]
    · funext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · funext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · refine ⟨⟨!![1, 0, u 0; 0, (u 2)⁻¹, u 1; 0, 0, u 2], ?_⟩, ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [h2]
    · funext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · funext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end ML3

@[expose] def lnLevi : Subgroup (SL3 F) :=
  rootGroup 0 1 ⊔ rootGroup 1 0 ⊔ rootGroup 0 2 ⊔ rootGroup 1 2

namespace ML3

theorem rootElt_mul_apply {i j : Fin 3} (h : i ≠ j) (c : F) (g : SL3 F) (k l : Fin 3) :
    ((rootElt i j c * g : SL3 F) : Matrix (Fin 3) (Fin 3) F) k l =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) k l +
        if k = i then c * ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) j l else 0 := by
  rw [coe_mul_SL3, coe_rootElt h, add_mul, one_mul, Matrix.add_apply]
  by_cases hk : k = i
  · subst hk
    rw [Matrix.single_mul_apply_same]
    simp
  · rw [Matrix.single_mul_apply_of_ne (c := c) i j k l hk]
    simp [hk]

end ML3

private theorem rootElt_mem_ptLevi {i j : Fin 3} (h : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) (c : F) : rootElt i j c ∈ (ptLevi : Subgroup (SL3 F)) :=
  rootGroup_le_ptLevi h (rootElt_mem_rootGroup i j c)

theorem mem_ptLevi_of_mulVec_e0 {g : SL3 F}
    (hg : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) :
    g ∈ (ptLevi : Subgroup (SL3 F)) := by
  have hcol : ∀ g : SL3 F,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] ↔
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧
          ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
            ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
    intro g
    rw [mulVec_e0]
    constructor
    · intro h
      exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1,
        by simpa using congrFun h 2⟩
    · rintro ⟨h0, h1, h2⟩
      funext k
      fin_cases k <;> simp [h0, h1, h2]
  have hstep : ∀ {i j : Fin 3} (hij : i ≠ j), j ≠ 0 → ∀ (c : F) (g : SL3 F),
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
        ((rootElt i j c * g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
          ![1, 0, 0] := by
    intro i j hij hj c g hg
    rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hg, rootElt_mulVec hij]
    fin_cases j
    · exact absurd rfl hj
    all_goals simp
  have hdet : ∀ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 1 * ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2 -
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 2 *
          ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 1 := by
    intro g hg
    obtain ⟨h0, h1, h2⟩ := (hcol g).mp hg
    have := g.2
    rw [Matrix.det_fin_three, h0, h1, h2] at this
    linear_combination this
  have hfin : ∀ g : SL3 F,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 →
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 →
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 → g ∈ (ptLevi : Subgroup (SL3 F)) := by
    intro g hg h11 h12 h21
    obtain ⟨h0, h1, h2⟩ := (hcol g).mp hg
    have h22 : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
      have := hdet g hg
      rw [h11, h12, h21] at this
      linear_combination this
    have he : g = rootElt 0 1 (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 1) *
        rootElt 0 2 (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 2) := by
      apply Subtype.ext
      change ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
        ((rootElt 0 1 _ : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt 0 2 _ : SL3 F) :
          Matrix (Fin 3) (Fin 3) F)
      rw [coe_rootElt (by decide), coe_rootElt (by decide)]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply, h0,
          h1, h2, h11, h12, h21, h22]
    rw [he]
    exact Subgroup.mul_mem _ (rootElt_mem_ptLevi (Or.inl ⟨rfl, rfl⟩) _)
      (rootElt_mem_ptLevi (Or.inr (Or.inl ⟨rfl, rfl⟩)) _)
  have hred : ∀ {i j : Fin 3} (hij : i ≠ j), ((i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) → ∀ (c : F) (g : SL3 F),
        rootElt i j c * g ∈ (ptLevi : Subgroup (SL3 F)) → g ∈ (ptLevi : Subgroup (SL3 F)) := by
    intro i j hij hmem c g h
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (rootElt_mem_ptLevi hmem c)) h
    rwa [inv_mul_cancel_left] at this
  have h3 : ∀ g : SL3 F,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 →
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 → g ∈ (ptLevi : Subgroup (SL3 F)) := by
    intro g hg h11 h21
    obtain ⟨-, -, h2⟩ := (hcol g).mp hg
    have h22 : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
      have := hdet g hg
      rw [h11, h21] at this
      linear_combination this
    apply hred (i := 1) (j := 2) (by decide) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      (-((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 2)
    refine hfin _ (hstep (by decide) (by decide) _ g hg) ?_ ?_ ?_
    · rw [rootElt_mul_apply (by decide)]
      simp [h21]
      exact h11
    · rw [rootElt_mul_apply (by decide)]
      simp [h22]
    · rw [rootElt_mul_apply (by decide)]
      simp [h21]
  have h2' : ∀ g : SL3 F,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 → g ∈ (ptLevi : Subgroup (SL3 F)) := by
    intro g hg h11
    apply hred (i := 2) (j := 1) (by decide) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      (-((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1)
    refine h3 _ (hstep (by decide) (by decide) _ g hg) ?_ ?_
    · rw [rootElt_mul_apply (by decide)]
      simp
      exact h11
    · rw [rootElt_mul_apply (by decide)]
      simp [h11]
  have h1' : ∀ g : SL3 F,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 ≠ 0 → g ∈ (ptLevi : Subgroup (SL3 F)) := by
    intro g hg h21
    apply hred (i := 1) (j := 2) (by decide) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      ((1 - ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 1) /
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1)
    refine h2' _ (hstep (by decide) (by decide) _ g hg) ?_
    rw [rootElt_mul_apply (by decide)]
    simp only [↓reduceIte]
    rw [div_mul_cancel₀ _ h21]
    ring
  by_cases h21 : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0
  · apply hred (i := 2) (j := 1) (by decide) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) 1
    refine h1' _ (hstep (by decide) (by decide) _ g hg) ?_
    rw [rootElt_mul_apply (by decide)]
    simp only [↓reduceIte, one_mul, h21, zero_add]
    intro h11
    have := hdet g hg
    rw [h11, h21] at this
    simp at this
  · exact h1' g hg h21

section Recognition

variable {V : Type*} [CommGroup V]

theorem exists_natural_of_point_data (ρ : SL3 F →* MulAut V) (ζ : Multiplicative F →* V)
    (hζ : ζ (Multiplicative.ofAdd 1) ≠ 1)
    (hP : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ a : F,
      ρ g (ζ (Multiplicative.ofAdd a)) =
        ζ (Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 * a)))
    (hrel : ρ (rootElt 0 2 1) (ρ (cyc * cyc) (ζ (Multiplicative.ofAdd 1))) =
      ρ (cyc * cyc) (ζ (Multiplicative.ofAdd 1)) * ζ (Multiplicative.ofAdd 1)) :
    ∃ ψ : Multiplicative (Fin 3 → F) →* V, Function.Injective ψ ∧
      (∀ (g : SL3 F) (v : Fin 3 → F),
        ψ (Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) =
          ρ g (ψ (Multiplicative.ofAdd v))) ∧
      ∀ a : F, ψ (Multiplicative.ofAdd (a • ![1, 0, 0])) = ζ (Multiplicative.ofAdd a) := by
  classical
  have hex : ∀ v : Fin 3 → F, v ≠ 0 →
      ∃ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = v :=
    fun v hv => exists_mulVec_e0_eq hv
  choose! gv hgv using hex
  set f : (Fin 3 → F) → V := fun v => if v = 0 then 1 else ρ (gv v) (ζ (Multiplicative.ofAdd 1))
    with hf_def
  have hf0 : f 0 = 1 := by simp [f]
  have hfv : ∀ v, v ≠ 0 → f v = ρ (gv v) (ζ (Multiplicative.ofAdd 1)) := fun v hv => by
    simp [f, hv]
  have hwd : ∀ (g : SL3 F) (a : F),
      f (a • (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0])) =
        ρ g (ζ (Multiplicative.ofAdd a)) := by
    intro g a
    by_cases ha : a = 0
    · rw [ha, zero_smul, hf0, ofAdd_zero, map_one, map_one]
    have hv : a • (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) ≠ 0 :=
      smul_ne_zero ha (mulVec_e0_ne_zero g)
    rw [hfv _ hv]
    set w' := gv (a • (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0])) with hw'_def
    have hw' : ((w' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
        a • (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) := hgv _ hv
    set k := w'⁻¹ * g * diagPt a ha with hk
    have hke : ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
      rw [hk, coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        diagPt_mulVec_e0, Matrix.mulVec_smul, ← hw', Matrix.mulVec_mulVec, ← coe_mul_SL3,
        inv_mul_cancel, coe_one_SL3, Matrix.one_mulVec]
    obtain ⟨hkP, hk00⟩ := mem_ptStab_of_mulVec_e0 hke
    have h1 := hP k hkP 1
    rw [hk00, one_mul] at h1
    have hgk : w' * k = g * diagPt a ha := by
      rw [hk]
      group
    have h2 : ρ w' (ζ (Multiplicative.ofAdd 1)) = ρ (w' * k) (ζ (Multiplicative.ofAdd 1)) := by
      rw [map_mul, MulAut.mul_apply, h1]
    rw [h2, hgk, map_mul, MulAut.mul_apply, hP _ (diagPt_mem_ptStab a ha),
      diagPt_apply_zero_zero, mul_one]
  have hfe : ∀ a : F, f (a • ![1, 0, 0]) = ζ (Multiplicative.ofAdd a) := fun a => by
    have := hwd 1 a
    rwa [coe_one_SL3, Matrix.one_mulVec, map_one, MulAut.one_apply] at this
  have hequiv : ∀ (h : SL3 F) (v : Fin 3 → F),
      f (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = ρ h (f v) := by
    intro h v
    by_cases hv : v = 0
    · rw [hv, Matrix.mulVec_zero, hf0, map_one]
    have h1 := hwd (h * gv v) 1
    rw [one_smul, coe_mul_SL3, ← Matrix.mulVec_mulVec, hgv v hv, map_mul, MulAut.mul_apply,
      ← hfv v hv] at h1
    exact h1
  have he2 : f ![0, 0, 1] = ρ (cyc * cyc) (ζ (Multiplicative.ofAdd 1)) := by
    have := hwd (cyc * cyc) 1
    rwa [one_smul, cyc_mul_cyc_mulVec_e0] at this
  have he0 : f ![1, 0, 0] = ζ (Multiplicative.ofAdd 1) := by
    have := hfe 1
    rwa [one_smul] at this
  have hline : f (![0, 0, 1] + ![1, 0, 0]) = f ![0, 0, 1] * f ![1, 0, 0] := by
    have hx : ((rootElt 0 2 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] =
        ![0, 0, 1] + ![1, 0, 0] := by
      rw [rootElt_mulVec (by decide)]
      funext k
      fin_cases k <;> simp
    rw [← hx, hequiv, he2, he0, hrel]
  have hadd : ∀ v v' : Fin 3 → F, f (v + v') = f v * f v' := by
    intro v v'
    by_cases hv : v = 0
    · rw [hv, zero_add, hf0, one_mul]
    by_cases hv' : v' = 0
    · rw [hv', add_zero, hf0, mul_one]
    set g := gv v' with hg
    have hge : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = v' := hgv v' hv'
    set u := ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v with hu
    have hgu : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = v := by
      rw [hu, Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3,
        Matrix.one_mulVec]
    by_cases hu0 : u ∈ pt0
    ·
      obtain ⟨c, hcu⟩ : ∃ c : F, u = c • ![1, 0, 0] := ⟨_, eq_smul_e0_of_mem_pt0 hu0⟩
      have hc : v = c • v' := by
        rw [← hgu, hcu, Matrix.mulVec_smul, hge]
      have e1 : v + v' = (c + 1) • (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) := by
        rw [hge, add_smul, one_smul, ← hc]
      have e2 : v = c • (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) := by
        rw [hge]
        exact hc
      have e3 : v' = (1 : F) • (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) := by
        rw [hge, one_smul]
      have hL : f (v + v') = ρ g (ζ (Multiplicative.ofAdd c)) *
          ρ g (ζ (Multiplicative.ofAdd 1)) := by
        rw [e1, hwd, ofAdd_add, map_mul, map_mul]
      have hv1 : f v = ρ g (ζ (Multiplicative.ofAdd c)) := by
        rw [e2, hwd]
      have hv2 : f v' = ρ g (ζ (Multiplicative.ofAdd 1)) := by
        rw [e3, hwd]
      rw [hL, hv1, hv2]
    · obtain ⟨k, hk0, hk2⟩ := exists_stab_mulVec_e2_eq hu0
      have hg0 : ((g * k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = v' := by
        rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hk0, hge]
      have hg2 : ((g * k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = v := by
        rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hk2, hgu]
      have hsum : v + v' = ((g * k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (![0, 0, 1] + ![1, 0, 0]) := by
        rw [Matrix.mulVec_add, hg0, hg2]
      rw [hsum, hequiv, hline, map_mul, ← hequiv, ← hequiv, hg0, hg2]
  refine ⟨{ toFun := fun x => f (Multiplicative.toAdd x)
            map_one' := hf0
            map_mul' := fun x y => hadd _ _ }, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    change f (Multiplicative.toAdd x) = 1 at hx
    by_contra hx1
    have hne : Multiplicative.toAdd x ≠ 0 := fun h => hx1 (by
      rw [← ofAdd_toAdd x, h, ofAdd_zero])
    rw [hfv _ hne] at hx
    exact hζ ((ρ (gv (Multiplicative.toAdd x))).injective (hx.trans (map_one _).symm))
  · intro g v
    exact hequiv g v
  · intro a
    exact hfe a

end Recognition

section CharTwo

variable [CharP F 2]

namespace ML3

omit [CharP F 2] in
theorem conj_rootElt_of_mul_eq {i j i' j' : Fin 3} (hij : i ≠ j) (hij' : i' ≠ j') (g : SL3 F)
    (c : F) (h : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) * (1 + single i j c) =
      (1 + single i' j' c) * ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)) :
    g * rootElt i j c * g⁻¹ = rootElt i' j' c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt i j c : SL3 F) :
      Matrix _ _ F) = ((rootElt i' j' c : SL3 F) : Matrix _ _ F) * ((g : SL3 F) :
      Matrix _ _ F)
  rw [coe_rootElt hij, coe_rootElt hij']
  exact h

theorem swap01_conj_rootElt01 (c : F) :
    swap01 * rootElt 0 1 c * swap01⁻¹ = rootElt 1 0 c := by
  refine conj_rootElt_of_mul_eq (by decide) (by decide) _ c ?_
  rw [coe_swap01]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem rootElt01_mul_swap01 :
    rootElt 0 1 (1 : F) * swap01 = rootElt 1 0 1 * rootElt 0 1 1 := by
  apply Subtype.ext
  change ((rootElt 0 1 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((swap01 : SL3 F) :
      Matrix _ _ F) = ((rootElt 1 0 (1 : F) : SL3 F) : Matrix _ _ F) *
      ((rootElt 0 1 (1 : F) : SL3 F) : Matrix _ _ F)
  rw [coe_rootElt (by decide), coe_rootElt (by decide), coe_swap01]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      CharTwo.add_self_eq_zero]

theorem rootElt01_inv_conj_rootElt12 (s : F) :
    (rootElt 0 1 (1 : F))⁻¹ * rootElt 1 2 s * rootElt 0 1 1 = rootElt 1 2 s * rootElt 0 2 s := by
  rw [← rootElt_neg]
  apply Subtype.ext
  change ((rootElt 0 1 (-1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *
      ((rootElt 1 2 s : SL3 F) : Matrix _ _ F) * ((rootElt 0 1 (1 : F) : SL3 F) : Matrix _ _ F) =
      ((rootElt 1 2 s : SL3 F) : Matrix _ _ F) * ((rootElt 0 2 s : SL3 F) : Matrix _ _ F)
  rw [coe_rootElt (by decide), coe_rootElt (by decide), coe_rootElt (by decide),
    coe_rootElt (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem swap01_mul_diagPt (c : F) (hc : c ≠ 0) :
    swap01 * diagPt c hc = diagPt c⁻¹ (inv_ne_zero hc) * swap01 := by
  apply Subtype.ext
  change ((swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((diagPt c hc : SL3 F) :
      Matrix _ _ F) = ((diagPt c⁻¹ (inv_ne_zero hc) : SL3 F) : Matrix _ _ F) *
      ((swap01 : SL3 F) : Matrix _ _ F)
  rw [coe_swap01, diagPt, diagPt, SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.diag2n_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

omit [CharP F 2] in
theorem diagPt_conj_rootElt01 (c : F) (hc : c ≠ 0) (t : F) :
    diagPt c hc * rootElt 0 1 t * (diagPt c hc)⁻¹ = rootElt 0 1 (c * c * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change ((diagPt c hc : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt 0 1 t : SL3 F) :
      Matrix _ _ F) = ((rootElt 0 1 (c * c * t) : SL3 F) : Matrix _ _ F) *
      ((diagPt c hc : SL3 F) : Matrix _ _ F)
  rw [coe_rootElt (by decide), coe_rootElt (by decide), diagPt, SpecialLinearGroup.diag2n_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
  field_simp

omit [CharP F 2] in
theorem diagPt_mul_self (c : F) (hc : c ≠ 0) :
    diagPt c hc * diagPt c hc = diagPt (c * c) (mul_ne_zero hc hc) := by
  apply Subtype.ext
  change ((diagPt c hc : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((diagPt c hc : SL3 F) :
      Matrix _ _ F) = ((diagPt (c * c) (mul_ne_zero hc hc) : SL3 F) : Matrix _ _ F)
  rw [diagPt, diagPt, SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.diag2n_coe,
    Matrix.diagonal_mul_diagonal]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

@[expose] def swap12 : SL3 F :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by
    simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

theorem coe_swap12 :
    ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] :=
  rfl

theorem swap12_conj_rootElt01 (c : F) :
    swap12 * rootElt 0 1 c * swap12⁻¹ = rootElt 0 2 c := by
  refine conj_rootElt_of_mul_eq (by decide) (by decide) _ c ?_
  rw [coe_swap12]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem swap12_mul_rootElt01 (c : F) : swap12 * rootElt 0 1 c = rootElt 0 2 c * swap12 := by
  rw [← swap12_conj_rootElt01]
  group

theorem swap12_mulVec_e0 :
    ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  rw [coe_swap12]
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem swap12_mul_swap01_mulVec_e0 :
    ((swap12 * swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![0, 0, 1] := by
  rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, swap01_mulVec, coe_swap12]
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end ML3

end CharTwo

section Derivation

variable [CharP F 2] {V : Type*} [CommGroup V] (ρ : SL3 F →* MulAut V)

namespace ML3

omit [CharP F 2] in
theorem rho_mul_apply (g h : SL3 F) (v : V) : ρ (g * h) v = ρ g (ρ h v) := by
  rw [map_mul, MulAut.mul_apply]

theorem rho_swap01_swap01 (v : V) : ρ swap01 (ρ swap01 v) = v := by
  rw [← rho_mul_apply, swap01_mul_self, map_one, MulAut.one_apply]

theorem quad10_of_quad01 (hquad : ∀ a ∈ rootGroup 0 1, ∀ a' ∈ rootGroup 0 1, ∀ v : V,
      ρ a' (ρ a v * v⁻¹) = ρ a v * v⁻¹) (s t : F) (v : V) :
    ρ (rootElt 1 0 s) (ρ (rootElt 1 0 t) v * v⁻¹) = ρ (rootElt 1 0 t) v * v⁻¹ := by
  have hc : ∀ (r : F) (y : V),
      ρ (rootElt 1 0 r) y = ρ swap01 (ρ (rootElt 0 1 r) (ρ swap01 y)) := fun r y => by
    rw [← swap01_conj_rootElt01, swap01_inv, rho_mul_apply, rho_mul_apply]
  have key : ρ (rootElt 1 0 t) v * v⁻¹ =
      ρ swap01 (ρ (rootElt 0 1 t) (ρ swap01 v) * (ρ swap01 v)⁻¹) := by
    rw [hc, map_mul, map_inv, rho_swap01_swap01]
  rw [key, hc, rho_swap01_swap01,
    hquad _ (rootElt_mem_rootGroup 0 1 t) _ (rootElt_mem_rootGroup 0 1 s)]

variable (hquad : ∀ a ∈ rootGroup 0 1, ∀ a' ∈ rootGroup 0 1, ∀ v : V,
      ρ a' (ρ a v * v⁻¹) = ρ a v * v⁻¹)
  (hfix : ∀ v : V, (∀ g ∈ (lnLevi : Subgroup (SL3 F)), ρ g v = v) → v = 1)
include hquad hfix

theorem comm_swap01_eq {w : V} (hw : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ρ g w = w) :
    ρ (rootElt 0 1 1) (ρ swap01 w) * (ρ swap01 w)⁻¹ = w := by
  set u := ρ swap01 w with hu
  have hwl : ∀ {i j : Fin 3}, ((i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
      (i = 2 ∧ j = 1)) → ∀ c : F, ρ (rootElt i j c) w = w := fun h c =>
    hw _ (rootGroup_le_ptLevi h (rootElt_mem_rootGroup _ _ c))
  have hu02 : ∀ c : F, ρ (rootElt 0 2 c) u = u := fun c => by
    rw [hu, ← rho_mul_apply, ← swap01_conj_rootElt12, swap01_inv, mul_assoc, swap01_mul_self,
      mul_one, rho_mul_apply, hwl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))]
  have hu12 : ∀ c : F, ρ (rootElt 1 2 c) u = u := fun c => by
    rw [hu, ← rho_mul_apply, ← swap01_conj_rootElt02, swap01_inv, mul_assoc, swap01_mul_self,
      mul_one, rho_mul_apply, hwl (Or.inr (Or.inl ⟨rfl, rfl⟩))]
  have hu10 : ∀ c : F, ρ (rootElt 1 0 c) u = u := fun c => by
    rw [hu, ← rho_mul_apply, ← swap01_conj_rootElt01, swap01_inv, mul_assoc, swap01_mul_self,
      mul_one, rho_mul_apply, hwl (Or.inl ⟨rfl, rfl⟩)]
  have hu01 : ρ (rootElt 0 1 1) u = ρ (rootElt 1 0 1) w := by
    rw [hu, ← rho_mul_apply, rootElt01_mul_swap01, rho_mul_apply,
      hwl (Or.inl ⟨rfl, rfl⟩)]
  set z := ρ (rootElt 0 1 1) u * u⁻¹ * w⁻¹ with hz
  let S : Subgroup (SL3 F) :=
    { carrier := {g | ρ g z = z}
      one_mem' := by
        show ρ 1 z = z
        rw [map_one, MulAut.one_apply]
      mul_mem' := fun {a b} ha hb => by
        show ρ (a * b) z = z
        rw [rho_mul_apply, show ρ b z = z from hb, show ρ a z = z from ha]
      inv_mem' := fun {a} ha => by
        show ρ a⁻¹ z = z
        conv_lhs => rw [← show ρ a z = z from ha]
        rw [← rho_mul_apply, inv_mul_cancel, map_one, MulAut.one_apply] }
  have hS : ∀ {i j : Fin 3}, (∀ c : F, ρ (rootElt i j c) z = z) → rootGroup i j ≤ S :=
    fun h g hg => by
      obtain ⟨c, rfl⟩ := mem_rootGroup.mp hg
      exact h c
  have h01 : rootGroup 0 1 ≤ S := hS fun c => by
    rw [hz, map_mul (ρ (rootElt 0 1 c)) (ρ (rootElt 0 1 1) u * u⁻¹) w⁻¹,
      hquad _ (rootElt_mem_rootGroup 0 1 1) _ (rootElt_mem_rootGroup 0 1 c), map_inv,
      hwl (Or.inl ⟨rfl, rfl⟩)]
  have h02 : rootGroup 0 2 ≤ S := hS fun c => by
    have hA : ρ (rootElt 0 2 c) (ρ (rootElt 0 1 1) u) = ρ (rootElt 0 1 1) u := by
      rw [← rho_mul_apply,
        (rootElt_commute (i := 0) (j := 2) (k := 0) (l := 1) (by decide) (by decide) c 1).eq,
        rho_mul_apply, hu02]
    rw [hz, map_mul, map_mul, map_inv, map_inv, hA, hu02,
      hwl (Or.inr (Or.inl ⟨rfl, rfl⟩))]
  have h12 : rootGroup 1 2 ≤ S := hS fun c => by
    have he : rootElt 1 2 c * rootElt 0 1 (1 : F) =
        rootElt 0 1 1 * (rootElt 1 2 c * rootElt 0 2 c) := by
      rw [← rootElt01_inv_conj_rootElt12]
      group
    have hA : ρ (rootElt 1 2 c) (ρ (rootElt 0 1 1) u) = ρ (rootElt 0 1 1) u := by
      rw [← rho_mul_apply, he, rho_mul_apply, rho_mul_apply, hu02, hu12]
    rw [hz, map_mul, map_mul, map_inv, map_inv, hA, hu12,
      hwl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))]
  have h10 : rootGroup 1 0 ≤ S := hS fun c => by
    have hz' : z = (ρ (rootElt 1 0 1) w * w⁻¹) * u⁻¹ := by
      rw [hz, hu01, mul_right_comm]
    rw [hz', map_mul (ρ (rootElt 1 0 c)) (ρ (rootElt 1 0 1) w * w⁻¹) u⁻¹,
      quad10_of_quad01 ρ hquad, map_inv, hu10]
  have hle : (lnLevi : Subgroup (SL3 F)) ≤ S :=
    sup_le (sup_le (sup_le h01 h10) h02) h12
  have hz1 : z = 1 := hfix z fun g hg => hle hg
  rw [hz] at hz1
  exact mul_inv_eq_one.mp hz1

omit [CharP F 2] hquad hfix in
theorem diagPt_fix_of_fix {w : V} (hw : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ρ g w = w) (c : F)
    (hc : c ≠ 0) :
    ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ρ g (ρ (diagPt c hc) w) = ρ (diagPt c hc) w := by
  intro g hg
  have hk : (diagPt c hc)⁻¹ * g * diagPt c hc ∈ (ptLevi : Subgroup (SL3 F)) := by
    apply mem_ptLevi_of_mulVec_e0
    rw [inv_eq_of_mul_eq_one_right (diagPt_mul_inv c hc), coe_mul_SL3, coe_mul_SL3,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, diagPt_mulVec_e0, Matrix.mulVec_smul,
      mulVec_of_mem_ptLevi hg (by rw [mem_pt0]; simp), Matrix.mulVec_smul, diagPt_mulVec_e0,
      smul_smul, mul_inv_cancel₀ hc, one_smul]
  have h := hw _ hk
  rw [rho_mul_apply, rho_mul_apply] at h
  calc ρ g (ρ (diagPt c hc) w) = ρ (diagPt c hc) (ρ (diagPt c hc)⁻¹ (ρ g (ρ (diagPt c hc) w))) := by
        rw [← rho_mul_apply ρ (diagPt c hc), mul_inv_cancel, map_one, MulAut.one_apply]
    _ = ρ (diagPt c hc) w := by rw [h]

theorem comm_swap01_eq_diagPt [Finite F] {w : V}
    (hw : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ρ g w = w) {t : F} (ht : t ≠ 0) :
    ρ (rootElt 0 1 t) (ρ swap01 w) * (ρ swap01 w)⁻¹ = ρ (diagPt t ht) w := by
  obtain ⟨c, hc⟩ := surjective_frobenius F 2 t
  rw [frobenius_def, sq] at hc
  subst hc
  have hc0 : c ≠ 0 := fun h => ht (by rw [h, mul_zero])
  have h := comm_swap01_eq ρ hquad hfix (diagPt_fix_of_fix ρ hw c hc0)
  have hdinv : diagPt c⁻¹ (inv_ne_zero hc0) = (diagPt c hc0)⁻¹ :=
    (eq_inv_of_mul_eq_one_right (diagPt_mul_inv c hc0))
  have hω : ρ swap01 (ρ (diagPt c hc0) w) = ρ (diagPt c hc0)⁻¹ (ρ swap01 w) := by
    rw [← rho_mul_apply, swap01_mul_diagPt, hdinv, rho_mul_apply]
  have hx : ρ (rootElt 0 1 1) (ρ (diagPt c hc0)⁻¹ (ρ swap01 w)) =
      ρ (diagPt c hc0)⁻¹ (ρ (rootElt 0 1 (c * c)) (ρ swap01 w)) := by
    have he : rootElt 0 1 (1 : F) * (diagPt c hc0)⁻¹ =
        (diagPt c hc0)⁻¹ * rootElt 0 1 (c * c) := by
      rw [← mul_one (c * c), ← diagPt_conj_rootElt01 c hc0]
      group
    rw [← rho_mul_apply, he, rho_mul_apply]
  rw [hω, hx, ← map_inv, ← map_mul] at h
  set X := ρ (rootElt 0 1 (c * c)) (ρ swap01 w) * (ρ swap01 w)⁻¹ with hX
  calc X = ρ (diagPt c hc0) (ρ (diagPt c hc0)⁻¹ X) := by
        rw [← rho_mul_apply ρ (diagPt c hc0) (diagPt c hc0)⁻¹ X, mul_inv_cancel, map_one,
          MulAut.one_apply]
    _ = ρ (diagPt c hc0) (ρ (diagPt c hc0) w) := by rw [h]
    _ = ρ (diagPt c hc0 * diagPt c hc0) w := by rw [rho_mul_apply]
    _ = ρ (diagPt (c * c) ht) w := by rw [diagPt_mul_self]

end ML3

variable (hquad : ∀ a ∈ rootGroup 0 1, ∀ a' ∈ rootGroup 0 1, ∀ v : V,
      ρ a' (ρ a v * v⁻¹) = ρ a v * v⁻¹)
  (hfix : ∀ v : V, (∀ g ∈ (lnLevi : Subgroup (SL3 F)), ρ g v = v) → v = 1)
include hquad hfix

theorem exists_point_data_of_vecStab [Finite F] {w : V}
    (hw : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ρ g w = w) :
    ∃ ζ : Multiplicative F →* V, ζ (Multiplicative.ofAdd 1) = w ∧
      (∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ a : F,
        ρ g (ζ (Multiplicative.ofAdd a)) =
          ζ (Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 * a))) ∧
      ρ (rootElt 0 2 1) (ρ (cyc * cyc) (ζ (Multiplicative.ofAdd 1))) =
        ρ (cyc * cyc) (ζ (Multiplicative.ofAdd 1)) * ζ (Multiplicative.ofAdd 1) := by
  set u := ρ swap01 w with hu
  let ζ : Multiplicative F →* V :=
    { toFun := fun x => ρ (rootElt 0 1 (Multiplicative.toAdd x)) u * u⁻¹
      map_one' := by
        simp [rootElt_zero]
      map_mul' := fun x y => by
        simp only [toAdd_mul]
        set A := ρ (rootElt 0 1 (Multiplicative.toAdd x)) u with hA
        set D := ρ (rootElt 0 1 (Multiplicative.toAdd y)) u * u⁻¹ with hD
        have hB : ρ (rootElt 0 1 (Multiplicative.toAdd y)) u = D * u := by
          rw [hD]
          group
        have hq : ρ (rootElt 0 1 (Multiplicative.toAdd x)) D = D :=
          hquad _ (rootElt_mem_rootGroup 0 1 _) _ (rootElt_mem_rootGroup 0 1 _) u
        rw [rootElt_add, rho_mul_apply, hB, map_mul, hq, ← hA, mul_comm D A, mul_right_comm] }
  have hζ : ∀ t : F, ζ (Multiplicative.ofAdd t) = ρ (rootElt 0 1 t) u * u⁻¹ := fun t => rfl
  have hζ1 : ζ (Multiplicative.ofAdd 1) = w := by
    rw [hζ]
    exact comm_swap01_eq ρ hquad hfix hw
  refine ⟨ζ, hζ1, ?_, ?_⟩
  · intro g hg a
    by_cases ha : a = 0
    · rw [ha, mul_zero, ofAdd_zero, map_one, map_one]
    have hg00 : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
      intro h0
      have hdet := g.2
      rw [Matrix.det_fin_three, h0, hg.1, hg.2] at hdet
      simp at hdet
    have hb : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 * a ≠ 0 := mul_ne_zero hg00 ha
    rw [hζ, hζ, comm_swap01_eq_diagPt ρ hquad hfix hw ha,
      comm_swap01_eq_diagPt ρ hquad hfix hw hb]
    set b := ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 * a with hb_def
    have hk : (diagPt b hb)⁻¹ * g * diagPt a ha ∈ (ptLevi : Subgroup (SL3 F)) := by
      apply mem_ptLevi_of_mulVec_e0
      have hge : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
          ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 • ![1, 0, 0] := by
        rw [mulVec_e0]
        funext k
        fin_cases k <;> simp [hg.1, hg.2]
      rw [inv_eq_of_mul_eq_one_right (diagPt_mul_inv b hb), coe_mul_SL3, coe_mul_SL3,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, diagPt_mulVec_e0, Matrix.mulVec_smul,
        hge, smul_smul, Matrix.mulVec_smul, diagPt_mulVec_e0, smul_smul]
      convert one_smul F (![1, 0, 0] : Fin 3 → F) using 2
      rw [hb_def]
      field_simp
    have h := hw _ hk
    calc ρ g (ρ (diagPt a ha) w)
        = ρ (diagPt b hb) (ρ ((diagPt b hb)⁻¹ * g * diagPt a ha) w) := by
          rw [← rho_mul_apply, ← rho_mul_apply, ← mul_assoc, ← mul_assoc, mul_inv_cancel,
            one_mul, rho_mul_apply]
      _ = ρ (diagPt b hb) w := by rw [h]
  · rw [hζ1]
    have h := comm_swap01_eq ρ hquad hfix hw
    have hσ : swap12 ∈ (ptLevi : Subgroup (SL3 F)) := mem_ptLevi_of_mulVec_e0 swap12_mulVec_e0
    have hk : (cyc * cyc)⁻¹ * (swap12 * swap01) ∈ (ptLevi : Subgroup (SL3 F)) := by
      apply mem_ptLevi_of_mulVec_e0
      rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, swap12_mul_swap01_mulVec_e0,
        ← cyc_mul_cyc_mulVec_e0, Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel,
        coe_one_SL3, Matrix.one_mulVec]
    have hcyc : ρ (cyc * cyc) w = ρ swap12 u := by
      rw [hu, ← rho_mul_apply]
      calc ρ (cyc * cyc) w = ρ (cyc * cyc) (ρ ((cyc * cyc)⁻¹ * (swap12 * swap01)) w) := by
            rw [hw _ hk]
        _ = ρ (swap12 * swap01) w := by
            rw [← rho_mul_apply, mul_inv_cancel_left]
    have h2 := congrArg (ρ swap12) h
    rw [map_mul, map_inv, hw _ hσ, ← rho_mul_apply, swap12_mul_rootElt01, rho_mul_apply,
      ← hu, ← hcyc] at h2
    calc ρ (rootElt 0 2 1) (ρ (cyc * cyc) w)
        = (ρ (rootElt 0 2 1) (ρ (cyc * cyc) w) * (ρ (cyc * cyc) w)⁻¹) * ρ (cyc * cyc) w := by
          group
      _ = w * ρ (cyc * cyc) w := by rw [h2]
      _ = ρ (cyc * cyc) w * w := mul_comm _ _

end Derivation

@[expose] noncomputable def transposeInv : SL3 F →* SL3 F where
  toFun g := ⟨dualMat g, by
    rw [dualMat, Matrix.det_transpose]
    exact (g⁻¹).2⟩
  map_one' := Subtype.ext dualMat_one
  map_mul' g h := Subtype.ext (dualMat_mul g h)

theorem coe_transposeInv (g : SL3 F) :
    ((transposeInv g : SL3 F) : Matrix (Fin 3) (Fin 3) F) = dualMat g :=
  rfl

theorem transposeInv_transposeInv (g : SL3 F) : transposeInv (transposeInv g) = g := by
  apply Subtype.ext
  change dualMat (transposeInv g) = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)
  rw [dualMat, ← map_inv, coe_transposeInv, dualMat, inv_inv, Matrix.transpose_transpose]

section VecStab

variable [Finite F] [CharP F 2] {V : Type*} [CommGroup V]

theorem exists_natEquiv_of_vecStab (ρ : SL3 F →* MulAut V) (w : V) (hw1 : w ≠ 1)
    (hw : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ρ g w = w)
    (hquad : ∀ a ∈ rootGroup 0 1, ∀ a' ∈ rootGroup 0 1, ∀ v : V,
      ρ a' (ρ a v * v⁻¹) = ρ a v * v⁻¹)
    (hfix : ∀ v : V, (∀ g ∈ (lnLevi : Subgroup (SL3 F)), ρ g v = v) → v = 1)
    (hgen : Subgroup.closure (Set.range fun g : SL3 F => ρ g w) = ⊤) :
    ∃ β : V ≃* Multiplicative (Fin 3 → F),
      (∀ (g : SL3 F) (v : V), Multiplicative.toAdd (β (ρ g v)) =
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v)) ∧
      β.symm (Multiplicative.ofAdd ![1, 0, 0]) = w := by
  obtain ⟨ζ, hζ1, hP, hrel⟩ := exists_point_data_of_vecStab ρ hquad hfix hw
  obtain ⟨ψ, hinj, heq, he⟩ := exists_natural_of_point_data ρ ζ (hζ1 ▸ hw1) hP hrel
  have hψe : ψ (Multiplicative.ofAdd ![1, 0, 0]) = w := by
    have := he 1
    rwa [one_smul, hζ1] at this
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    refine ⟨Multiplicative.ofAdd (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]), ?_⟩
    rw [heq, hψe]
  set e := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩ with he_def
  refine ⟨e.symm, fun g v => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj v
    have h1 : e.symm (ψ y) = y := e.symm_apply_apply y
    have h2 : e.symm (ρ g (ψ y)) = Multiplicative.ofAdd
        (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd y) := by
      rw [MulEquiv.symm_apply_eq]
      change ρ g (ψ y) = ψ _
      rw [heq, ofAdd_toAdd]
    rw [h1, h2, toAdd_ofAdd]
  · rw [MulEquiv.symm_symm]
    exact hψe

end VecStab

end CFSG.Quasithin.MS93
