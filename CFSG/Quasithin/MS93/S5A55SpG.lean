module

public import CFSG.Quasithin.MS93.S5A55SpR
public import CFSG.Quasithin.MS93.S5A55SpZ

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix MSP

variable {F : Type} [Field F] [CharP F 2]

@[expose] def gEl (ν ν' : F) : Sp4 F := nuE (ν + ν') * transv (f₁ F + ν • f₂ F) 1

theorem gEl_mulVec (ν ν' : F) {x : V4 F} (hx : x ∈ ln₀ F) :
    mat (gEl ν ν') *ᵥ x = (x (.inl 0) + (ν + ν') * x (.inl 1)) • e₁ F + x (.inl 1) • e₂ F +
      (x (.inl 0) + ν * x (.inl 1)) • f₁ F + ((x (.inl 0) + ν * x (.inl 1)) * ν') • f₂ F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hx
  rw [gEl, mat_mul_mulVec, transv_mulVec, nuE_mulVec, form_apply]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [h0, h1]
  · linear_combination (-(x (.inl 0) + ν * x (.inl 1))) * h2
  · linear_combination (-((x (.inl 0) + ν * x (.inl 1)) * (ν + ν'))) * h2

theorem gEl_mulVec_gv (ν ν' : F) : mat (gEl ν ν') *ᵥ gv ν = gv ν' := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hf : form F (f₁ F + ν • f₂ F) (gv ν) = 0 := by
    rw [form_apply]
    simp
    linear_combination (-ν) * h2
  rw [gEl, mat_mul_mulVec, transv_mulVec, hf, mul_zero, zero_smul, add_zero, nuE_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp
  linear_combination ν * h2

theorem gEl_mulVec_e₁_not_mem (ν ν' : F) : mat (gEl ν ν') *ᵥ e₁ F ∉ ln₀ F := by
  rw [gEl_mulVec ν ν' (mem_ln₀.2 ⟨by simp, by simp⟩), mem_ln₀]
  simp

theorem pt₀_inf_map_gEl (ν ν' : F) :
    pt₀ F ⊓ (ln₀ F).map (mulVecLin (mat (gEl ν ν')⁻¹)) = ⊥ := by
  refine eq_bot_iff.2 fun v hv => ?_
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  rw [pt₀_eq_span] at hv1
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv1
  rw [mem_map_mulVecLin, inv_inv, mulVec_smul] at hv2
  by_contra hc
  rw [Submodule.mem_bot, smul_eq_zero, not_or] at hc
  have := (ln₀ F).smul_mem c⁻¹ hv2
  rw [smul_smul, inv_mul_cancel₀ hc.1, one_smul] at this
  exact gEl_mulVec_e₁_not_mem ν ν' this

theorem map_gEl_ne (ν ν' : F) : (ln₀ F).map (mulVecLin (mat (gEl ν ν'))) ≠ ln₀ F := fun h =>
  gEl_mulVec_e₁_not_mem ν ν' (h ▸ mulVec_mem_map _ (mem_ln₀.2 ⟨by simp, by simp⟩))

theorem form_gEl_gv (ν ν' : F) {x : V4 F} (hx : x ∈ ln₀ F) (μ : F) :
    form F (mat (gEl ν ν') *ᵥ x) (gv μ) = (x (.inl 0) + ν * x (.inl 1)) * (μ + ν') := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [gEl_mulVec ν ν' hx, form_apply]
  simp
  linear_combination (-(x (.inl 0) + ν * x (.inl 1)) * (μ + ν')) * h2

theorem eq_top_of_gEl' (hq : (∃ t : F, t ≠ 0 ∧ t ≠ 1) ∨ Nat.card F = 2) {H Z : Subgroup (Sp4 F)}
    {ν ν' : F}
    (hZ : ∀ s : F, ∃ y ∈ Z, y ∈ Q₁ F ∧
      mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s)
    (hZH : Z.map (MulAut.conj (gEl ν ν')).toMonoidHom ≤ H)
    (h2 : ∃ n ∈ H, n ∈ Q₁ F ∧ n ∉ qPoint (F ∙ gv ν'))
    (h3 : ∃ h ∈ H, h ∈ qPoint (F ∙ gv ν') ∧ h ∉ xPoint (F ∙ gv ν') ∧
      ((∃ t : F, t ≠ 0 ∧ t ≠ 1) ∨ h ∉ commutator (Sp4 F)) ∧
      (h ∈ Q₁ F ∨ h ∈ (Q₁ F).map (MulAut.conj (gEl ν ν')).toMonoidHom))
    (h4 : ∃ e ∈ H, e ∈ stab (ln₀ F) ∧ mat e *ᵥ e₁ F = e₁ F ∧ mat e (.inl 1) (.inl 1) = 1 ∧
      mat e (.inl 0) (.inl 1) ≠ 0) : H = ⊤ := by
  set g := gEl ν ν' with hg
  have hγ : (F ∙ gv ν).map (mulVecLin (mat g)) = F ∙ gv ν' := by
    rw [map_span_eq, hg, gEl_mulVec_gv]
  have hQl : qLine ((ln₀ F).map (mulVecLin (mat g))) = (Q₁ F).map (MulAut.conj g).toMonoidHom :=
    qLine_map_eq g
  have hQp : qPoint (F ∙ gv ν') = (qPoint (F ∙ gv ν)).map (MulAut.conj g).toMonoidHom := by
    rw [qPoint_map_conj, hγ]
  refine eq_top_of_frame' hq (isPoint_gv ν') (isLine_map isLine_ln₀ g) isLine_ln₀
    (by rw [← hγ]; exact Submodule.map_mono (span_gv_le_ln₀ ν)) (span_gv_le_ln₀ ν')
    (map_gEl_ne ν ν') ?_ ?_ ?_ ?_
  · intro k hk
    rw [hQl, mem_map_conj] at hk
    obtain ⟨y, hyZ, hyQ, hyk⟩ := covers_of_lam hZ _ hk
    refine ⟨g * y * g⁻¹, hZH ⟨y, hyZ, rfl⟩, ?_, ?_⟩
    · rw [hQl, mem_map_conj]
      convert hyQ using 1
      group
    · rw [hQp, mem_map_conj]
      convert hyk using 1
      group
  · obtain ⟨n, hnH, hnQ, hnγ⟩ := h2
    exact ⟨n, hnH, hnQ, hnγ⟩
  · obtain ⟨h, hhH, hhq, hhx, hodd, hhl⟩ := h3
    refine ⟨h, hhH, hhq, hhx, hodd, ?_⟩
    rcases hhl with hl | hl
    · exact Or.inr hl
    · exact Or.inl (by rw [hQl]; exact hl)
  · obtain ⟨e, heH, hes, hee, het, hea⟩ := h4
    refine ⟨e, heH, ?_, Or.inr ?_⟩
    · rw [map_span_eq]
      intro h
      have hmem : gv ν' ∈ F ∙ (mat e *ᵥ gv ν') := h ▸ Submodule.mem_span_singleton_self _
      have hev : mat e *ᵥ gv ν' = gv (ν' + mat e (.inl 0) (.inl 1)) := by
        rw [mulVec_add, mulVec_smul, hee, mulVec_e₂_of_stab hes het]
        refine ext4 ?_ ?_ ?_ ?_ <;> simp
      rw [hev] at hmem h
      have := span_gv_inj h
      exact hea (by linear_combination this)
    · rw [map_span_eq]
      exact (Submodule.span_singleton_le_iff_mem _ _).2 (mulVec_mem_of_mem_stab hes (gv_mem_ln₀ ν'))

theorem eq_top_of_gEl (hq : ∃ t : F, t ≠ 0 ∧ t ≠ 1) {H Z : Subgroup (Sp4 F)} {ν ν' : F}
    (hZ : ∀ s : F, ∃ y ∈ Z, y ∈ Q₁ F ∧
      mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s)
    (hZH : Z.map (MulAut.conj (gEl ν ν')).toMonoidHom ≤ H)
    (h2 : ∃ n ∈ H, n ∈ Q₁ F ∧ n ∉ qPoint (F ∙ gv ν'))
    (h3 : ∃ h ∈ H, h ∈ qPoint (F ∙ gv ν') ∧ h ∉ xPoint (F ∙ gv ν') ∧
      (h ∈ Q₁ F ∨ h ∈ (Q₁ F).map (MulAut.conj (gEl ν ν')).toMonoidHom))
    (h4 : ∃ e ∈ H, e ∈ stab (ln₀ F) ∧ mat e *ᵥ e₁ F = e₁ F ∧ mat e (.inl 1) (.inl 1) = 1 ∧
      mat e (.inl 0) (.inl 1) ≠ 0) : H = ⊤ := by
  obtain ⟨h, hhH, hhq, hhx, hhl⟩ := h3
  exact eq_top_of_gEl' (Or.inl hq) hZ hZH h2 ⟨h, hhH, hhq, hhx, Or.inl hq, hhl⟩ h4

omit [CharP F 2] in
theorem exists_two_ne (hq : ∃ t : F, t ≠ 0 ∧ t ≠ 1) (ν' : F) :
    ∃ μ₁ μ₂ : F, μ₁ ≠ μ₂ ∧ μ₁ ≠ ν' ∧ μ₂ ≠ ν' := by
  obtain ⟨t, ht0, ht1⟩ := hq
  by_cases h0 : ν' = 0
  · exact ⟨1, t, Ne.symm ht1, h0 ▸ one_ne_zero, h0 ▸ ht0⟩
  · by_cases h1 : ν' = 1
    · exact ⟨0, t, Ne.symm ht0, h1 ▸ zero_ne_one, h1 ▸ ht1⟩
    · exact ⟨0, 1, zero_ne_one, Ne.symm h0, Ne.symm h1⟩

theorem transv_gv_mem_of_xPoint {H : Subgroup (Sp4 F)} {ν ν' : F} {c : Submodule F (V4 F)}
    (hc : IsPoint c) (hcl : c ≤ ln₀ F) (hcν : c ≠ F ∙ gv ν)
    (hXH : (xPoint c).map (MulAut.conj (gEl ν ν')).toMonoidHom ≤ H) {μ : F} (hμ : μ ≠ ν')
    {s : F} (hs : s ≠ 0) (hsH : transv (gv μ) s ∈ H) (d : F) : transv (gv μ) d ∈ H := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨x, hx0, rfl⟩ := exists_eq_span_of_isPoint hc
  have hxl : x ∈ ln₀ F := hcl (Submodule.mem_span_singleton_self x)
  have hxν : x (.inl 0) + ν * x (.inl 1) ≠ 0 := by
    intro h
    apply hcν
    obtain ⟨h2', h3⟩ := mem_ln₀.1 hxl
    have hx : x = x (.inl 1) • gv ν := by
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [h2', h3]
      linear_combination h - ν * x (.inl 1) * h2
    have hx1 : x (.inl 1) ≠ 0 := fun h1 => hx0 (by rw [hx, h1, zero_smul])
    conv_lhs => rw [hx]
    rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hx1)]
  set B := form F (mat (gEl ν ν') *ᵥ x) (gv μ) with hB
  have hB0 : B ≠ 0 := by
    rw [hB, form_gEl_gv ν ν' hxl]
    exact mul_ne_zero hxν (fun h => hμ (by linear_combination h - ν' * h2))
  refine transv_mem_of_weyl (a := B⁻¹ • (mat (gEl ν ν') *ᵥ x)) ?_ (fun r => ?_) hs hsH d
  · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← hB, inv_mul_cancel₀ hB0]
  · rw [transv_smul_vec, ← transv_conj]
    exact hXH ⟨_, transv_mem_xPoint x _, rfl⟩

variable [Finite F]

theorem sp4Case55_std (hq : ∃ t : F, t ≠ 0 ∧ t ≠ 1) {R A₀ D Z : Subgroup (Sp4 F)}
    (hR : IsPGroup 2 R) (hA : candMax R = {A₀}) (hRl : R ≤ stab (ln₀ F))
    (hRe : ∀ r ∈ R, mat r *ᵥ e₁ F = e₁ F) (hA₀ : A₀ = Q₁ F ⊓ R)
    (hA₀c : Nat.card F ^ 2 ≤ Nat.card A₀)
    (h51 : ∀ p₁ p₂ : Submodule F (V4 F), IsPoint p₁ → IsPoint p₂ → A₀ ≠ xPoint p₁ ⊔ xPoint p₂)
    (hDR : D ≤ R) (hDn : R ≤ Subgroup.normalizer (D : Set (Sp4 F)))
    (hAD : Nat.card A₀ ≤ Nat.card D) (hDQ : ¬ D ≤ Q₁ F)
    (hZ : (∃ c : Submodule F (V4 F), IsPoint c ∧ c ≤ ln₀ F ∧ xPoint c ≤ Z) ∨
      (Z ≤ Q₁ F ∧ Nat.card F ^ 2 ≤ Nat.card Z)) :
    ∃ g : Sp4 F, pt₀ F ⊓ (ln₀ F).map (mulVecLin (mat g⁻¹)) = ⊥ ∧
      (D.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z = ⊤ ∨
        (R.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z = ⊤ ∧ Nat.card D = Nat.card A₀ ∧
          Nat.card ↥(D ⊓ A₀) ≤ Nat.card F ^ 2)) := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hRt : ∀ r ∈ R, mat r (.inl 1) (.inl 1) = 1 := fun r hr => by
    obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
    exact entry_e₂_eq_one (hRl hr) (hRe r hr) (by simpa using congrArg Subtype.val hn)
  obtain ⟨u₀, hu₀D, hu₀Q⟩ := Set.not_subset.1 hDQ
  have hu₀ : u₀ ∈ stab (ln₀ F) ∧ mat u₀ *ᵥ e₁ F = e₁ F ∧ mat u₀ (.inl 1) (.inl 1) = 1 ∧
      mat u₀ (.inl 0) (.inl 1) ≠ 0 :=
    ⟨hRl (hDR hu₀D), hRe _ (hDR hu₀D), hRt _ (hDR hu₀D), fun h => hu₀Q
      ((mem_Q₁_iff_of_stab (hRl (hDR hu₀D)) (hRe _ (hDR hu₀D)) (hRt _ (hDR hu₀D))).2 h)⟩
  have hNγ : ∀ ν' : F, ∃ n ∈ D, n ∈ Q₁ F ∧ n ∉ qPoint (F ∙ gv ν') := fun ν' => by
    obtain ⟨n, hn, hnq⟩ := Set.not_subset.1
      (not_inf_le_qPoint_gv hR hA hRl hRe hA₀ hA₀c hDR hDn hAD hDQ ν')
    exact ⟨n, (Subgroup.mem_inf.1 hn).1, (Subgroup.mem_inf.1 hn).2, hnq⟩
  have hfin : ∀ {ν ν' : F} {H : Subgroup (Sp4 F)},
      H ⊔ Z.map (MulAut.conj (gEl ν ν')).toMonoidHom = ⊤ →
      H.map (MulAut.conj (gEl ν ν')⁻¹).toMonoidHom ⊔ Z = ⊤ := by
    intro ν ν' H h
    have := congrArg (Subgroup.map (MulAut.conj (gEl ν ν')⁻¹).toMonoidHom) h
    rwa [Subgroup.map_sup, map_conj_map_conj', inv_mul_cancel, map_conj_one,
      Subgroup.map_top_of_surjective _ (MulAut.conj _).surjective] at this
  rcases hZ with ⟨c, hc, hcl, hXc⟩ | ⟨hZQ, hZc⟩
  ·
    obtain ⟨ν, hcν⟩ : ∃ ν : F, c ≠ F ∙ gv ν := by
      rcases eq_pt₀_or_span_gv hc hcl with rfl | ⟨κ, rfl⟩
      · exact ⟨0, (span_gv_ne_pt₀ 0).symm⟩
      · exact ⟨κ + 1, fun h => one_ne_zero (by linear_combination (span_gv_inj h).symm)⟩
    have hZν : ∀ s : F, ∃ y ∈ Z, y ∈ Q₁ F ∧
        mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s := fun s => by
      obtain ⟨y, hyX, hyQ, hy⟩ := exists_lam_xPoint hc hcl hcν s
      exact ⟨y, hXc hyX, hyQ, hy⟩
    by_cases h1 : ∃ ν' : F, ¬ (D ⊓ Q₁ F) ⊓ qPoint (F ∙ gv ν') ≤ xPoint (F ∙ gv ν')
    ·
      obtain ⟨ν', hν'⟩ := h1
      obtain ⟨h, hh, hhx⟩ := Set.not_subset.1 hν'
      obtain ⟨hhN, hhq⟩ := Subgroup.mem_inf.1 hh
      obtain ⟨hhD, hhQ⟩ := Subgroup.mem_inf.1 hhN
      refine ⟨gEl ν ν', pt₀_inf_map_gEl ν ν', Or.inl (hfin ?_)⟩
      obtain ⟨n, hnD, hnQ, hnq⟩ := hNγ ν'
      exact eq_top_of_gEl hq hZν le_sup_right ⟨n, Subgroup.mem_sup_left hnD, hnQ, hnq⟩
        ⟨h, Subgroup.mem_sup_left hhD, hhq, hhx, Or.inl hhQ⟩
        ⟨u₀, Subgroup.mem_sup_left hu₀D, hu₀⟩
    push Not at h1
    have hNle : Nat.card ↥(D ⊓ Q₁ F) ≤ Nat.card F ^ 2 :=
      card_le_sq_of_inf_le_xPoint inf_le_right (h1 0)
    have hDA : D ⊓ A₀ = D ⊓ Q₁ F := by
      rw [hA₀]
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hDR h.1⟩⟩
    by_cases h2 : Nat.card D = Nat.card A₀
    ·
      have hA₀Q : A₀ ≤ Q₁ F := hA₀ ▸ inf_le_left
      have hA₀R : A₀ ≤ R := hA₀ ▸ inf_le_right
      obtain ⟨ν', hν'⟩ := exists_not_inf_le_xPoint hA₀Q hA₀c h51
      obtain ⟨h, hh, hhx⟩ := Set.not_subset.1 hν'
      obtain ⟨hhA, hhq⟩ := Subgroup.mem_inf.1 hh
      refine ⟨gEl ν ν', pt₀_inf_map_gEl ν ν', Or.inr ⟨hfin ?_, h2, by
        rw [hDA]; exact hNle⟩⟩
      obtain ⟨n, hnD, hnQ, hnq⟩ := hNγ ν'
      exact eq_top_of_gEl hq hZν le_sup_right
        ⟨n, Subgroup.mem_sup_left (hDR hnD), hnQ, hnq⟩
        ⟨h, Subgroup.mem_sup_left (hA₀R hhA), hhq, hhx, Or.inl (hA₀Q hhA)⟩
        ⟨u₀, Subgroup.mem_sup_left (hDR hu₀D), hu₀⟩
    ·
      have hNq : Nat.card F < Nat.card ↥(D ⊓ Q₁ F) := by
        have hDle := card_le_card_inf_Q₁_mul fun r hr =>
          (⟨hRl (hDR hr), hRe r (hDR hr), hRt r (hDR hr)⟩ :
            r ∈ stab (ln₀ F) ∧ mat r *ᵥ e₁ F = e₁ F ∧ mat r (.inl 1) (.inl 1) = 1)
        have hlt : Nat.card A₀ < Nat.card D := lt_of_le_of_ne hAD (Ne.symm h2)
        by_contra hle
        push Not at hle
        have : Nat.card D ≤ Nat.card F * Nat.card F :=
          hDle.trans (Nat.mul_le_mul_right _ hle)
        rw [← sq] at this
        omega
      have htr : ∀ μ : F, ∃ s : F, s ≠ 0 ∧ transv (gv μ) s ∈ D := fun μ => by
        obtain ⟨s, hs, hsN⟩ := exists_transv_mem_of_inf_le_xPoint inf_le_right (h1 μ) hNq
        exact ⟨s, hs, (Subgroup.mem_inf.1 hsN).1⟩
      set H := D ⊔ Z.map (MulAut.conj (gEl ν ν)).toMonoidHom with hH
      have hXH : (xPoint c).map (MulAut.conj (gEl ν ν)).toMonoidHom ≤ H :=
        (Subgroup.map_mono hXc).trans le_sup_right
      have hfull : ∀ μ : F, μ ≠ ν → ∀ d : F, transv (gv μ) d ∈ H := by
        intro μ hμ d
        obtain ⟨s, hs, hsD⟩ := htr μ
        exact transv_gv_mem_of_xPoint hc hcl hcν hXH hμ hs (Subgroup.mem_sup_left hsD) d
      obtain ⟨μ₁, μ₂, h12, h1ν, h2ν⟩ := exists_two_ne hq ν
      obtain ⟨hmq, hmx⟩ := transv_mul_transv_gv h12 h1ν h2ν
      refine ⟨gEl ν ν, pt₀_inf_map_gEl ν ν, Or.inl (hfin ?_)⟩
      obtain ⟨n, hnD, hnQ, hnq⟩ := hNγ ν
      exact eq_top_of_gEl hq hZν le_sup_right ⟨n, Subgroup.mem_sup_left hnD, hnQ, hnq⟩
        ⟨_, mul_mem (hfull μ₁ h1ν _) (hfull μ₂ h2ν _), hmq, hmx,
          Or.inl (mul_mem (transv_gv_mem_Q₁ _ _) (transv_gv_mem_Q₁ _ _))⟩
        ⟨u₀, Subgroup.mem_sup_left hu₀D, hu₀⟩
  ·
    obtain ⟨ν, hZν, z, hzZ, hzq, hzx⟩ := exists_gv_of_le_Q₁ hq hZQ hZc
    have hγ : (F ∙ gv ν).map (mulVecLin (mat (gEl ν ν))) = F ∙ gv ν := by
      rw [map_span_eq, gEl_mulVec_gv]
    refine ⟨gEl ν ν, pt₀_inf_map_gEl ν ν, Or.inl (hfin ?_)⟩
    obtain ⟨n, hnD, hnQ, hnq⟩ := hNγ ν
    refine eq_top_of_gEl hq hZν le_sup_right ⟨n, Subgroup.mem_sup_left hnD, hnQ, hnq⟩
      ⟨gEl ν ν * z * (gEl ν ν)⁻¹, Subgroup.mem_sup_right ⟨z, hzZ, rfl⟩, ?_, ?_,
        Or.inr ⟨z, hZQ hzZ, rfl⟩⟩ ⟨u₀, Subgroup.mem_sup_left hu₀D, hu₀⟩
    · rw [← hγ, ← qPoint_map_conj]
      exact ⟨z, hzq, rfl⟩
    · rw [← hγ, ← xPoint_map_conj, mem_map_conj]
      convert hzx using 1
      group

end CFSG.Quasithin.MS93.S5
