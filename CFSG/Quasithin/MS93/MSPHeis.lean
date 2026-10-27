module

public import CFSG.Quasithin.MS93.MSPOpp

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

theorem form_e₁ (v : V4 F) : form F (e₁ F) v = v (.inr 0) := by
  rw [form_apply]
  simp

theorem form_e₂ (v : V4 F) : form F (e₂ F) v = v (.inr 1) := by
  rw [form_apply]
  simp

theorem form_f₂ (v : V4 F) : form F (f₂ F) v = -v (.inl 1) := by
  rw [form_apply]
  simp

theorem mulVec_inr_zero_of_fix {g : Sp4 F} (hg : mat g *ᵥ e₁ F = e₁ F) {w : V4 F}
    (hw : w (.inr 0) = 0) : (mat g *ᵥ w) (.inr 0) = 0 := by
  rw [← form_e₁ (mat g *ᵥ w), ← hg, form_mat, form_e₁, hw]

theorem eq_one_of_mem_Q₂ {g : Sp4 F} (hg : g ∈ Q₂ F) (hf : mat g *ᵥ f₁ F = f₁ F) : g = 1 := by
  have hperp : ∀ v : V4 F, v (.inr 0) = 0 → ∃ c : F, mat g *ᵥ v = v + c • e₁ F := fun v hv => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (show mat g *ᵥ v - v ∈ F ∙ e₁ F from pt₀_eq_span (F := F) ▸ hg.2 v (mem_perp_pt₀.2 hv))
    exact ⟨c, by rw [hc]; abel⟩
  have hfix : ∀ v : V4 F, v (.inr 0) = 0 → mat g *ᵥ v = v := fun v hv => by
    obtain ⟨c, hc⟩ := hperp v hv
    have h := form_mat g v (f₁ F)
    rw [hc, hf, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, form_e₁] at h
    simp at h
    rw [hc, h, zero_smul, add_zero]
  refine ext_mulVec fun v => ?_
  have hv : v = (v - v (.inr 0) • f₁ F) + v (.inr 0) • f₁ F := by abel
  rw [mat_one, one_mulVec, hv, mulVec_add, mulVec_smul, hf, hfix _ (by simp)]

section CharTwo

variable [CharP F 2]

@[expose] def qw (w : V4 F) (s : F) : Sp4 F :=
  transv (e₁ F + w) 1 * transv w 1 * transv (e₁ F) (s + 1)

theorem qw_mulVec {w : V4 F} (hw : w (.inr 0) = 0) (s : F) (v : V4 F) :
    mat (qw w s) *ᵥ v = v + (s * form F (e₁ F) v + form F w v) • e₁ F +
      form F (e₁ F) v • w := by
  rw [qw, mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, hw] <;> grind

theorem qw_add_e₁ {w : V4 F} (hw : w (.inr 0) = 0) (μ s : F) :
    qw (w + μ • e₁ F) s = qw w s := by
  have hw' : (w + μ • e₁ F) (.inr 0) = 0 := by simp [hw]
  refine ext_mulVec fun v => ?_
  rw [qw_mulVec hw', qw_mulVec hw]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, hw]
  grind

theorem qw_zero (s : F) : qw 0 s = transv (e₁ F) s := by
  refine ext_mulVec fun v => ?_
  rw [qw_mulVec (by simp), transv_mulVec]
  simp

theorem qw_conj {g : Sp4 F} (hg : mat g *ᵥ e₁ F = e₁ F) {w : V4 F} (hw : w (.inr 0) = 0)
    (s : F) : g * qw w s * g⁻¹ = qw (mat g *ᵥ w) s := by
  refine ext_mulVec fun v => ?_
  have h1 : form F (e₁ F) (mat g⁻¹ *ᵥ v) = form F (e₁ F) v := by
    rw [← form_mat g, hg, mat_mulVec_inv]
  have h2 : form F w (mat g⁻¹ *ᵥ v) = form F (mat g *ᵥ w) v := by
    rw [← form_mat g, mat_mulVec_inv]
  rw [mat_mul_mulVec, mat_mul_mulVec, qw_mulVec hw, qw_mulVec (mulVec_inr_zero_of_fix hg hw),
    mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mat_mulVec_inv, hg, h1, h2]

theorem qw_mem_Q₂ {w : V4 F} (hw : w (.inr 0) = 0) (s : F) : qw w s ∈ Q₂ F := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [pt₀_eq_span] at hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [qw_mulVec hw]
    simp [form_apply, hw]
  · have h0 : v (.inr 0) = 0 := mem_perp_pt₀.1 hv
    rw [qw_mulVec hw, form_e₁, h0, mul_zero, zero_add, zero_smul, add_zero, add_sub_cancel_left,
      pt₀_eq_span]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem qw_mulVec_f₁ {w : V4 F} (hw0 : w (.inl 0) = 0) (hw : w (.inr 0) = 0) (s : F) :
    mat (qw w s) *ᵥ f₁ F = f₁ F + s • e₁ F + w := by
  rw [qw_mulVec hw]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, hw, hw0]

theorem exists_qw_mulVec_f₁ {x : V4 F} (hx : x (.inr 0) = 1) :
    ∃ w : V4 F, w (.inr 0) = 0 ∧ mat (qw w (x (.inl 0))) *ᵥ f₁ F = x := by
  refine ⟨x (.inl 1) • e₂ F + x (.inr 1) • f₂ F, by simp, ?_⟩
  rw [qw_mulVec_f₁ (by simp) (by simp)]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [hx]

theorem Q₂_sup_qPoint_of_opp {x : V4 F} (hx : x (.inr 0) ≠ 0) :
    Q₂ F ⊔ qPoint (F ∙ x) = ⊤ := by
  set x' := (x (.inr 0))⁻¹ • x with hx'
  have hspan : (F ∙ x') = F ∙ x := by
    rw [hx']
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hx)) x
  have hx'1 : x' (.inr 0) = 1 := by
    rw [hx']
    simp [inv_mul_cancel₀ hx]
  obtain ⟨w, hw, hh⟩ := exists_qw_mulVec_f₁ hx'1
  set h := qw w (x' (.inl 0))
  have hQ : (Q₂ F).map (MulAut.conj h).toMonoidHom = Q₂ F :=
    mem_normalizer_iff_map_conj.1 (P₂_le_normalizer_Q₂ (Q₂_le_P₂ (qw_mem_Q₂ hw _)))
  have hP : (qPoint (F ∙ f₁ F)).map (MulAut.conj h).toMonoidHom = qPoint (F ∙ x) := by
    rw [qPoint_map_conj, Submodule.map_span, Set.image_singleton, mulVecLin_apply, hh, hspan]
  rw [← hQ, ← hP, ← Subgroup.map_sup, Q₂_sup_qPoint_f₁, Subgroup.map_top_of_surjective]
  exact (MulAut.conj h).surjective

theorem qPoint_sup_qPoint_eq_top {p p' : Submodule F (V4 F)} (hp : IsPoint p)
    (hp' : IsPoint p') (hopp : ¬ p' ≤ perp p) : qPoint p ⊔ qPoint p' = ⊤ := by
  obtain ⟨g, rfl⟩ := exists_map_pt₀_eq hp
  obtain ⟨x, -, hx⟩ := exists_eq_span_of_isPoint
    (show IsPoint (p'.map (mulVecLin (mat g⁻¹))) from by
      rw [IsPoint, ← (Submodule.equivMapOfInjective _ (mulVec_mat_injective g⁻¹) p').finrank_eq]
      exact hp')
  have hgp' : p' = (F ∙ x).map (mulVecLin (mat g)) := by rw [← hx, map_map_mat_inv]
  have hxo : x (.inr 0) ≠ 0 := by
    intro h0
    refine hopp ?_
    rw [hgp', perp_map]
    refine Submodule.map_mono ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact mem_perp_pt₀.2 h0
  rw [hgp', ← qPoint_map_conj, ← qPoint_map_conj, ← Subgroup.map_sup, Q₂_sup_qPoint_of_opp hxo,
    Subgroup.map_top_of_surjective]
  exact (MulAut.conj g).surjective

@[expose] def qe (x y s : F) : Sp4 F := qw (x • e₂ F + y • f₂ F) s

theorem qe_mulVec (x y s : F) (v : V4 F) :
    mat (qe x y s) *ᵥ v = v + (s * v (.inr 0) + x * v (.inr 1) + y * v (.inl 1)) • e₁ F +
      (x * v (.inr 0)) • e₂ F + (y * v (.inr 0)) • f₂ F := by
  rw [qe, qw_mulVec (by simp)]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply] <;> grind

theorem qe_mul (x y s x' y' s' : F) :
    qe x y s * qe x' y' s' = qe (x + x') (y + y') (s + s' + x * y' + x' * y) := by
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, qe_mulVec, qe_mulVec, qe_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp <;> grind

theorem qe_zero_zero (s : F) : qe 0 0 s = transv (e₁ F) s := by
  rw [qe, zero_smul, zero_smul, add_zero, qw_zero]

theorem qe_mem_Q₂ (x y s : F) : qe x y s ∈ Q₂ F := qw_mem_Q₂ (by simp) s

theorem qe_conj_transv_f₂ (c x y s : F) :
    transv (f₂ F) c * qe x y s * (transv (f₂ F) c)⁻¹ = qe x (y + c * x) s := by
  rw [qe, qw_conj (by rw [transv_mulVec]; simp [form_apply]) (by simp)]
  congr 1
  rw [transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply]
  all_goals grind

theorem exists_eq_qe_of_mem_Q₂ {g : Sp4 F} (hg : g ∈ Q₂ F) : ∃ x y s : F, g = qe x y s := by
  have he₁ : mat g *ᵥ e₁ F = e₁ F :=
    hg.1 _ (by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _)
  set u := mat g *ᵥ f₁ F with hu
  have hu1 : u (.inr 0) = 1 := by
    rw [← form_e₁ u, hu, ← he₁, form_mat, form_e₁]
    simp
  refine ⟨u (.inl 1), u (.inr 1), u (.inl 0), ?_⟩
  set h := qe (u (.inl 1)) (u (.inr 1)) (u (.inl 0)) with hhdef
  have hh : mat h *ᵥ f₁ F = u := by
    rw [hhdef, qe_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [hu1]
  have hmem : h⁻¹ * g ∈ Q₂ F := mul_mem (inv_mem (qe_mem_Q₂ _ _ _)) hg
  have h1 := eq_one_of_mem_Q₂ hmem (by rw [mat_mul_mulVec, ← hu, ← hh, mat_inv_mulVec])
  rw [inv_mul_eq_one] at h1
  exact h1.symm

end CharTwo

end CFSG.Quasithin.MS93.MSP
