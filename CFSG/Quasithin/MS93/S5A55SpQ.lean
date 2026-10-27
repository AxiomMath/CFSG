module

public import CFSG.Quasithin.MS93.S5A55SpT
public import CFSG.Quasithin.MS93.S5A56Hat
public import CFSG.Quasithin.MS93.S5A55Stmt
public import CFSG.Quasithin.MS93.S5A56L

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix MSP

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem mul_not_mem_commutator (hq2 : Nat.card F = 2) {a b : Sp4 F}
    (ha : a ∈ commutator (Sp4 F)) (hb : b ∉ commutator (Sp4 F)) :
    a * b ∉ commutator (Sp4 F) := by
  obtain ⟨c⟩ := nonempty_ringEquiv_of_card_two hq2
  rw [Subgroup.mul_mem_iff_of_index_two (index_commutator c)]
  exact fun h => hb (h.1 ha)

omit [CharP F 2] in
theorem mul_mem_commutator_of_not (hq2 : Nat.card F = 2) {a b : Sp4 F}
    (ha : a ∉ commutator (Sp4 F)) (hb : b ∉ commutator (Sp4 F)) :
    a * b ∈ commutator (Sp4 F) := by
  obtain ⟨c⟩ := nonempty_ringEquiv_of_card_two hq2
  rw [Subgroup.mul_mem_iff_of_index_two (index_commutator c)]
  exact iff_of_false ha hb

omit [CharP F 2] in
theorem transv_one_not_mem (hq2 : Nat.card F = 2) {v : V4 F} (hv : v ≠ 0) :
    transv v 1 ∉ commutator (Sp4 F) :=
  transv_not_mem_commutator_of_card_two hq2 hv 1 one_ne_zero

omit [CharP F 2] in
theorem transv_mul_transv_mem (hq2 : Nat.card F = 2) {u v : V4 F} (hu : u ≠ 0) (hv : v ≠ 0) :
    transv u 1 * transv v 1 ∈ commutator (Sp4 F) :=
  mul_mem_commutator_of_not hq2 (transv_one_not_mem hq2 hu) (transv_one_not_mem hq2 hv)

omit [CharP F 2] in
theorem xAlt_not_mem_commutator (hq2 : Nat.card F = 2) : xAlt F ∉ commutator (Sp4 F) :=
  mul_not_mem_commutator hq2 (transv_mul_transv_mem hq2 e₁_ne_zero e₂_ne_zero)
    (transv_one_not_mem hq2 e₁_add_e₂_ne_zero)

omit [CharP F 2] in
theorem nuE_one_not_mem_commutator (hq2 : Nat.card F = 2) : nuE (1 : F) ∉ commutator (Sp4 F) :=
  mul_not_mem_commutator hq2 (transv_mul_transv_mem hq2 f₂_add_e₁_ne_zero f₂_ne_zero)
    (transv_one_not_mem hq2 e₁_ne_zero)

theorem entry_xAlt : mat (xAlt F) (.inl 0) (.inr 0) = 0 ∧ mat (xAlt F) (.inl 0) (.inr 1) = 1 ∧
    mat (xAlt F) (.inl 1) (.inr 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [mat_apply_eq, xAlt_mulVec] <;> simp

theorem xAlt_mem_qPoint (ν : F) : xAlt F ∈ qPoint (F ∙ gv ν) ∧ xAlt F ∉ xPoint (F ∙ gv ν) := by
  obtain ⟨h0, h1, h2⟩ := entry_xAlt (F := F)
  refine ⟨mem_qPoint_gv_of xAlt_mem_Q₁ h0 h2 ν, fun hx => ?_⟩
  have := eq_one_of_mem_xPoint_gv xAlt_mem_Q₁ h0 h2 hx
  rw [this, entry_one] at h1
  exact zero_ne_one h1

omit [CharP F 2] in
theorem mem_ln₀_of_transv_mem_stab {v : V4 F} (hv : v ≠ 0)
    (hs : transv v 1 ∈ MSP.stab (ln₀ F)) (he : mat (transv v 1) *ᵥ e₁ F = e₁ F) :
    v ∈ ln₀ F := by
  rw [transv_mulVec, add_eq_left, smul_eq_zero, one_mul] at he
  have h1 : form F v (e₁ F) = 0 := he.resolve_right hv
  have he2 := mulVec_mem_of_mem_stab hs (mem_ln₀.2 ⟨by simp, by simp⟩ : e₂ F ∈ ln₀ F)
  rw [transv_mulVec, one_mul] at he2
  have he2' := (ln₀ F).sub_mem he2 (mem_ln₀.2 ⟨by simp, by simp⟩ : e₂ F ∈ ln₀ F)
  rw [add_sub_cancel_left] at he2'
  by_cases h2 : form F v (e₂ F) = 0
  · rw [form_apply] at h1 h2
    simp at h1 h2
    exact mem_ln₀.2 ⟨h1, h2⟩
  · have := (ln₀ F).smul_mem (form F v (e₂ F))⁻¹ he2'
    rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at this

abbrev wq (F : Type) [Field F] : Subgroup (Sp4 F) := Q₁ F ⊓ commutator (Sp4 F)

omit [CharP F 2] in
theorem conj_mem_wq {p : Sp4 F} (hp : p ∈ MSP.stab (ln₀ F)) {k : Sp4 F} (hk : k ∈ wq F) :
    p * k * p⁻¹ ∈ wq F :=
  ⟨conj_mem_Q₁ hp hk.1, (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ hk.2 p⟩

omit [CharP F 2] in
theorem wq_map_conj_eq {a b : Sp4 F} (hab : a⁻¹ * b ∈ MSP.stab (ln₀ F)) :
    (wq F).map (MulAut.conj b).toMonoidHom = (wq F).map (MulAut.conj a).toMonoidHom := by
  have hW : (wq F).map (MulAut.conj (a⁻¹ * b)).toMonoidHom = wq F := by
    refine le_antisymm ?_ fun k hk => ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact conj_mem_wq hab hk
    · refine ⟨(a⁻¹ * b)⁻¹ * k * (a⁻¹ * b)⁻¹⁻¹, conj_mem_wq (inv_mem hab) hk, ?_⟩
      change (a⁻¹ * b) * ((a⁻¹ * b)⁻¹ * k * (a⁻¹ * b)⁻¹⁻¹) * (a⁻¹ * b)⁻¹ = k
      group
  rw [show b = a * (a⁻¹ * b) by group, ← map_conj_map_conj', hW]

omit [CharP F 2] in
theorem exists_lam_of_two (hq2 : Nat.card F = 2) {Y : Subgroup (Sp4 F)} {z : Sp4 F}
    (hz : z ∈ Y) (hzQ : z ∈ Q₁ F)
    (hbd : mat z (.inl 0) (.inr 0) ≠ 0 ∨ mat z (.inl 1) (.inr 1) ≠ 0) :
    ∃ ν : F, ∀ s : F, ∃ y ∈ Y, y ∈ Q₁ F ∧
      mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s := by
  have h01 := eq_zero_or_eq_one_of_card_two hq2
  have h1 : ∀ ν : F,
      mat (1 : Sp4 F) (.inl 0) (.inr 0) + ν ^ 2 * mat (1 : Sp4 F) (.inl 1) (.inr 1) = 0 := by
    intro ν
    rw [entry_one, entry_one]
    ring
  by_cases hb : mat z (.inl 0) (.inr 0) = 0
  · have hd1 : mat z (.inl 1) (.inr 1) = 1 := (h01 _).resolve_left (hbd.resolve_left (· hb))
    refine ⟨1, fun s => ?_⟩
    rcases h01 s with rfl | rfl
    · exact ⟨1, one_mem _, one_mem _, h1 1⟩
    · exact ⟨z, hz, hzQ, by rw [hb, hd1]; ring⟩
  · have hb1 : mat z (.inl 0) (.inr 0) = 1 := (h01 _).resolve_left hb
    refine ⟨0, fun s => ?_⟩
    rcases h01 s with rfl | rfl
    · exact ⟨1, one_mem _, one_mem _, h1 0⟩
    · exact ⟨z, hz, hzQ, by rw [hb1]; ring⟩

theorem eq_one_or_eq_xAlt (hq2 : Nat.card F = 2) {k : Sp4 F} (hk : k ∈ Q₁ F)
    (hb : mat k (.inl 0) (.inr 0) = 0) (hd : mat k (.inl 1) (.inr 1) = 0) :
    k = 1 ∨ k = xAlt F := by
  obtain ⟨x0, x1, x2⟩ := entry_xAlt (F := F)
  rcases eq_zero_or_eq_one_of_card_two hq2 (mat k (.inl 0) (.inr 1)) with hc | hc
  · exact Or.inl (eq_of_mem_Q₁ hk (one_mem _) (by rw [hb, entry_one]) (by rw [hc, entry_one])
      (by rw [hd, entry_one]))
  · exact Or.inr (eq_of_mem_Q₁ hk xAlt_mem_Q₁ (by rw [hb, x0]) (by rw [hc, x1]) (by rw [hd, x2]))

theorem xPoint_le_or_le_Q₁ [Finite F] {R Z : Subgroup (Sp4 F)} (hR : IsPGroup 2 R)
    (hRl : R ≤ MSP.stab (ln₀ F)) (hRe : ∀ r ∈ R, mat r *ᵥ e₁ F = e₁ F) (hZR : Z ≤ R)
    (hZ : (∃ c : Submodule F (V4 F), IsPoint c ∧ Z = xPoint c) ∨
      (Nat.card F ^ 2 ≤ Nat.card Z ∧ commSp Z ≤ fixSp Z ∧ Module.finrank F (fixSp Z) ≤ 2)) :
    (∃ c : Submodule F (V4 F), IsPoint c ∧ c ≤ ln₀ F ∧ xPoint c ≤ Z) ∨
      (Z ≤ Q₁ F ∧ Nat.card F ^ 2 ≤ Nat.card Z) := by
  have hpR : pt₀ F ≤ fixSp R := by
    rw [pt₀_eq_span, Submodule.span_singleton_le_iff_mem]
    exact mem_fixSp.2 hRe
  rcases hZ with ⟨c, hc, rfl⟩ | ⟨hZc, hZq, hZf⟩
  · exact Or.inl ⟨c, hc, le_of_xPoint_le_stab hc isLine_ln₀ (hZR.trans hRl), le_rfl⟩
  · have hZ2 : IsPGroup 2 Z := hR.to_le hZR
    have hf2 : Module.finrank F (fixSp Z) = 2 := le_antisymm hZf (two_le_finrank_fixSp hZq)
    obtain ⟨hm, hZm⟩ := isLine_fixSp_of_finrank_two hZ2 hf2
    have hpm : pt₀ F ≤ fixSp Z := hpR.trans (fixSp_antitone hZR)
    by_cases hml : fixSp Z = ln₀ F
    · refine Or.inr ⟨?_, hZc⟩
      show Z ≤ qLine (ln₀ F)
      rw [← hml]
      exact hZm
    · have hinf : fixSp Z ⊓ ln₀ F = pt₀ F := by
        have h0 : fixSp Z ⊓ ln₀ F ≠ ⊥ := fun h =>
          isPoint_ne_bot isPoint_pt₀ (le_bot_iff.1 (h ▸ le_inf hpm pt₀_le_ln₀))
        have hpt := isPoint_inf hm isLine_ln₀ hml h0
        exact (Submodule.eq_of_le_of_finrank_eq (le_inf hpm pt₀_le_ln₀)
          (by rw [isPoint_pt₀, hpt])).symm
      have hZp : Z ≤ qLine (fixSp Z) ⊓ qPoint (pt₀ F) :=
        le_inf hZm ((le_inf hZm (hZR.trans hRl)).trans
          (qLine_inf_stab_le_qPoint hm isLine_ln₀ isPoint_pt₀ hinf))
      have heq : Z = qLine (fixSp Z) ⊓ qPoint (pt₀ F) := Subgroup.eq_of_le_of_card_ge hZp
        (by rw [card_qLine_inf_qPoint isPoint_pt₀ hm hpm]; exact hZc)
      refine Or.inl ⟨pt₀ F, isPoint_pt₀, pt₀_le_ln₀, ?_⟩
      rw [heq]
      exact le_inf (xPoint_le_qLine hm hpm) (xPoint_le_qPoint isPoint_pt₀)

omit [CharP F 2] in
theorem exists_ne_span_gv {c : Submodule F (V4 F)} (hc : IsPoint c) (hcl : c ≤ ln₀ F) :
    ∃ ν : F, c ≠ F ∙ gv ν := by
  rcases eq_pt₀_or_span_gv hc hcl with rfl | ⟨κ, rfl⟩
  · exact ⟨0, (span_gv_ne_pt₀ 0).symm⟩
  · exact ⟨κ + 1, fun h => one_ne_zero (by linear_combination (span_gv_inj h).symm)⟩

theorem exists_lam_shape_two (hq2 : Nat.card F = 2) {R Z : Subgroup (Sp4 F)}
    (hR : IsPGroup 2 R) (hRl : R ≤ MSP.stab (ln₀ F)) (hRe : ∀ r ∈ R, mat r *ᵥ e₁ F = e₁ F)
    (hZR : Z ≤ R)
    (hZ : (∃ c : Submodule F (V4 F), IsPoint c ∧ Z = xPoint c) ∨
      (Nat.card F ^ 2 ≤ Nat.card Z ∧ commSp Z ≤ fixSp Z ∧ Module.finrank F (fixSp Z) ≤ 2) ∨
      (Nat.card F = 2 ∧ ∃ v₁ v₂ : V4 F, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧ form F v₁ v₂ = 0 ∧
        transv v₁ 1 ∈ R ∧ transv v₂ 1 ∈ R ∧
        (transv v₁ 1 ∈ Z ∨ transv v₂ 1 ∈ Z ∨ transv v₁ 1 * transv v₂ 1 ∈ Z))) :
    ∃ ν : F, ∀ s : F, ∃ y ∈ Z, y ∈ Q₁ F ∧
      mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hX : ∀ {c : Submodule F (V4 F)}, IsPoint c → c ≤ ln₀ F → xPoint c ≤ Z →
      ∃ ν : F, ∀ s : F, ∃ y ∈ Z, y ∈ Q₁ F ∧
        mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s := by
    intro c hc hcl hcZ
    obtain ⟨ν, hcν⟩ := exists_ne_span_gv hc hcl
    refine ⟨ν, fun s => ?_⟩
    obtain ⟨y, hyX, hyQ, hy⟩ := exists_lam_xPoint hc hcl hcν s
    exact ⟨y, hcZ hyX, hyQ, hy⟩
  have hv : ∀ {v : V4 F}, v ≠ 0 → transv v 1 ∈ R → v ∈ ln₀ F := fun hv hvR =>
    mem_ln₀_of_transv_mem_stab hv (hRl hvR) (hRe _ hvR)
  rcases hZ with hZ | hZ | ⟨-, v₁, v₂, h₁, h₂, h₁₂, -, hR₁, hR₂, hs⟩
  · obtain ⟨c, hc, rfl⟩ := hZ
    exact hX hc (le_of_xPoint_le_stab hc isLine_ln₀ (hZR.trans hRl)) le_rfl
  · rcases xPoint_le_or_le_Q₁ hR hRl hRe hZR (Or.inr hZ) with ⟨c, hc, hcl, hcZ⟩ | ⟨hZQ, hZc⟩
    · exact hX hc hcl hcZ
    ·
      by_contra hno
      have hall : ∀ z ∈ Z, mat z (.inl 0) (.inr 0) = 0 ∧ mat z (.inl 1) (.inr 1) = 0 := by
        intro z hz
        by_contra hbd
        rw [not_and_or] at hbd
        exact hno (exists_lam_of_two hq2 hz (hZQ hz) hbd)
      have hinj : Function.Injective fun z : Z => mat (z : Sp4 F) (.inl 0) (.inr 1) := by
        intro x y hxy
        simp only at hxy
        exact Subtype.ext (eq_of_mem_Q₁ (hZQ x.2) (hZQ y.2)
          (by rw [(hall x x.2).1, (hall y y.2).1]) hxy (by rw [(hall x x.2).2, (hall y y.2).2]))
      have := Nat.card_le_card_of_injective _ hinj
      rw [hq2] at this hZc
      norm_num at hZc
      omega
  · have hl₁ := hv h₁ hR₁
    have hl₂ := hv h₂ hR₂
    have hcl : ∀ {v : V4 F}, v ∈ ln₀ F → (F ∙ v) ≤ ln₀ F := fun h =>
      (Submodule.span_singleton_le_iff_mem _ _).2 h
    rcases hs with hs | hs | hs
    · exact hX (isPoint_span h₁) (hcl hl₁) (xPoint_span_le_of_card_two hq2 h₁ hs)
    · exact hX (isPoint_span h₂) (hcl hl₂) (xPoint_span_le_of_card_two hq2 h₂ hs)
    · have hzQ : transv v₁ 1 * transv v₂ 1 ∈ Q₁ F :=
        mul_mem (transv_mem_qLine isLine_ln₀ hl₁ 1) (transv_mem_qLine isLine_ln₀ hl₂ 1)
      refine exists_lam_of_two hq2 hs hzQ ?_
      by_contra hbd
      push Not at hbd
      rcases eq_one_or_eq_xAlt hq2 hzQ hbd.1 hbd.2 with h | h
      · apply h₁₂
        have : transv v₁ 1 = transv v₂ 1 := by
          rw [← mul_left_inj (transv v₂ 1), h, transv_mul, CharTwo.add_self_eq_zero, transv_zero]
        exact (transv_eq_transv_iff h₂).1 this
      · exact xAlt_not_mem_commutator hq2 (h ▸ transv_mul_transv_mem hq2 h₁ h₂)

theorem top_of_xAlt_mem (hq2 : Nat.card F = 2) {R A₀ D Z : Subgroup (Sp4 F)}
    (hR : IsPGroup 2 R) (hA : candMax R = {A₀}) (hRl : R ≤ MSP.stab (ln₀ F))
    (hRe : ∀ r ∈ R, mat r *ᵥ e₁ F = e₁ F) (hA₀ : A₀ = Q₁ F ⊓ R)
    (hA₀c : Nat.card F ^ 2 ≤ Nat.card A₀) (hDR : D ≤ R)
    (hDn : R ≤ Subgroup.normalizer (D : Set (Sp4 F))) (hAD : Nat.card A₀ ≤ Nat.card D)
    (hDQ : ¬ D ≤ Q₁ F) {ν : F}
    (hZν : ∀ s : F, ∃ y ∈ Z, y ∈ Q₁ F ∧
      mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s)
    (hxA : xAlt F ∈ A₀) :
    R.map (MulAut.conj (gEl ν ν)⁻¹).toMonoidHom ⊔ Z = ⊤ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hRt : ∀ r ∈ R, mat r (.inl 1) (.inl 1) = 1 := fun r hr => by
    obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
    exact entry_e₂_eq_one (hRl hr) (hRe r hr) (by simpa using congrArg Subtype.val hn)
  obtain ⟨u₀, hu₀D, hu₀Q⟩ := Set.not_subset.1 hDQ
  have hu₀ : u₀ ∈ MSP.stab (ln₀ F) ∧ mat u₀ *ᵥ e₁ F = e₁ F ∧ mat u₀ (.inl 1) (.inl 1) = 1 ∧
      mat u₀ (.inl 0) (.inl 1) ≠ 0 :=
    ⟨hRl (hDR hu₀D), hRe _ (hDR hu₀D), hRt _ (hDR hu₀D), fun h => hu₀Q
      ((mem_Q₁_iff_of_stab (hRl (hDR hu₀D)) (hRe _ (hDR hu₀D)) (hRt _ (hDR hu₀D))).2 h)⟩
  obtain ⟨n, hn, hnq⟩ := Set.not_subset.1
    (not_inf_le_qPoint_gv hR hA hRl hRe hA₀ hA₀c hDR hDn hAD hDQ ν)
  have hxR : xAlt F ∈ R := (Subgroup.mem_inf.1 (hA₀ ▸ hxA : xAlt F ∈ Q₁ F ⊓ R)).2
  have htop := eq_top_of_gEl' (Or.inr hq2) hZν le_sup_right
    ⟨n, Subgroup.mem_sup_left (hDR (Subgroup.mem_inf.1 hn).1), (Subgroup.mem_inf.1 hn).2, hnq⟩
    ⟨xAlt F, Subgroup.mem_sup_left hxR, (xAlt_mem_qPoint ν).1, (xAlt_mem_qPoint ν).2,
      Or.inr (xAlt_not_mem_commutator hq2), Or.inl xAlt_mem_Q₁⟩
    ⟨u₀, Subgroup.mem_sup_left (hDR hu₀D), hu₀⟩
  have := congrArg (Subgroup.map (MulAut.conj (gEl ν ν)⁻¹).toMonoidHom) htop
  rwa [Subgroup.map_sup, map_conj_map_conj', inv_mul_cancel, map_conj_one,
    Subgroup.map_top_of_surjective _ (MulAut.conj _).surjective] at this

theorem nuE_zero : nuE (0 : F) = 1 :=
  ext_mulVec fun v => by
    rw [nuE_mulVec, mat_one, one_mulVec]
    simp

theorem gEl_zero_zero : gEl (0 : F) 0 = transv (f₁ F) 1 := by
  rw [gEl, add_zero, nuE_zero, one_mul, zero_smul, add_zero]

theorem transv_one_inv (x : V4 F) : (transv x 1)⁻¹ = transv x 1 := by
  rw [transv_inv, CharTwo.neg_eq]

@[expose] def yEl (F : Type) [Field F] : Sp4 F :=
  wAl F * transv (e₂ F) 1 * transv (e₁ F + e₂ F) 1

theorem yEl_mem_stab : yEl F ∈ MSP.stab (ln₀ F) :=
  mul_mem (mul_mem wAl_mem_stab (Q₁_le_P₁ (transv_e₂_mem_Q₁ 1)))
    (Q₁_le_P₁ (transv_e₁_add_e₂_mem_Q₁ 1))

omit [CharP F 2] in
theorem mem_stab_of_swap {p : Sp4 F} (h1 : mat p *ᵥ e₁ F = e₂ F) (h2 : mat p *ᵥ e₂ F = e₁ F) :
    p ∈ MSP.stab (ln₀ F) := mem_stab_of_le fun v hv => by
  obtain ⟨h2', h3⟩ := mem_ln₀.1 hv
  have hv' : v = v (.inl 0) • e₁ F + v (.inl 1) • e₂ F :=
    ext4 (by simp) (by simp) (by simp [h2']) (by simp [h3])
  rw [hv', mulVec_add, mulVec_smul, mulVec_smul, h1, h2]
  exact add_mem ((ln₀ F).smul_mem _ (mem_ln₀.2 ⟨by simp, by simp⟩))
    ((ln₀ F).smul_mem _ (mem_ln₀.2 ⟨by simp, by simp⟩))

theorem xW_inv_mul_yEl_mem : (xW F)⁻¹ * (yEl F * transv (f₁ F) 1) ∈ MSP.stab (ln₀ F) := by
  have hx : (xW F)⁻¹ = transv (e₁ F + f₂ F) 1 * transv (e₂ F) 1 := by
    rw [xW, _root_.mul_inv_rev, transv_one_inv, transv_one_inv]
  rw [hx, yEl]
  refine mem_stab_of_swap ?_ ?_
  · simp only [mat_mul_mulVec, transv_mulVec, wAl_mulVec, form_apply]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
    grind
  · simp only [mat_mul_mulVec, transv_mulVec, wAl_mulVec, form_apply]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem sig_inv_mul_yEl_mem :
    (sig F)⁻¹ * (yEl F * (transv (f₁ F) 1 * nuE 1 * (transv (f₁ F) 1)⁻¹)) ∈
      MSP.stab (ln₀ F) := by
  rw [sig_inv, transv_one_inv, yEl]
  refine mem_stab_of_swap ?_ ?_
  · simp only [mat_mul_mulVec, transv_mulVec, wAl_mulVec, form_apply, sig_mulVec, nuE_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp <;> grind
  · simp only [mat_mul_mulVec, transv_mulVec, wAl_mulVec, form_apply, sig_mulVec, nuE_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
    grind

theorem top_of_wq (hq2 : Nat.card F = 2) {R Z : Subgroup (Sp4 F)} (hWR : wq F ≤ R)
    (hnR : nuE 1 ∈ R) (hWZ : wq F ≤ Z) :
    R.map (MulAut.conj (gEl (0 : F) 0)⁻¹).toMonoidHom ⊔ Z = ⊤ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  rw [gEl_zero_zero, transv_one_inv]
  set t := transv (f₁ F) 1 with ht
  set H := R.map (MulAut.conj t).toMonoidHom ⊔ Z with hH
  have hmH : t * nuE 1 * t⁻¹ ∈ H := Subgroup.mem_sup_left ⟨nuE 1, hnR, rfl⟩
  have hc2 : (xW F)⁻¹ * (yEl F * t) ∈ MSP.stab (ln₀ F) := xW_inv_mul_yEl_mem
  have hc3 : (sig F)⁻¹ * (yEl F * (t * nuE 1 * t⁻¹)) ∈ MSP.stab (ln₀ F) := sig_inv_mul_yEl_mem
  have hc1 : (1 : Sp4 F)⁻¹ * yEl F ∈ MSP.stab (ln₀ F) := by
    rw [inv_one, one_mul]
    exact yEl_mem_stab
  have h₁ : transv (e₁ F) 1 * transv (e₂ F) 1 ∈ wq F :=
    ⟨mul_mem (transv_e₁_mem_Q₁ 1) (transv_e₂_mem_Q₁ 1),
      transv_mul_transv_mem hq2 e₁_ne_zero e₂_ne_zero⟩
  have h₂ : transv (e₁ F) 1 * transv (e₁ F + e₂ F) 1 ∈ wq F :=
    ⟨mul_mem (transv_e₁_mem_Q₁ 1) (transv_e₁_add_e₂_mem_Q₁ 1),
      transv_mul_transv_mem hq2 e₁_ne_zero e₁_add_e₂_ne_zero⟩
  have hcomm : commutator (Sp4 F) ≤ H.map (MulAut.conj (yEl F)).toMonoidHom := by
    refine (commutator_le_sup_w2 hq2 h₁ h₂).trans (sup_le (sup_le ?_ ?_) ?_)
    · rw [← wq_map_conj_eq hc3, ← map_conj_map_conj']
      exact Subgroup.map_mono (S59.map_conj_le_of_mem (hWZ.trans le_sup_right) hmH)
    · have e := wq_map_conj_eq (F := F) hc1
      rw [map_conj_one] at e
      rw [← e]
      exact Subgroup.map_mono (hWZ.trans le_sup_right)
    · rw [← wq_map_conj_eq hc2, ← map_conj_map_conj']
      exact Subgroup.map_mono ((Subgroup.map_mono hWR).trans le_sup_left)
  have hcH : commutator (Sp4 F) ≤ H := commutator_le_of_map_conj (yEl F) hcomm
  have hmo : t * nuE 1 * t⁻¹ ∉ commutator (Sp4 F) := fun h => nuE_one_not_mem_commutator hq2 (by
    have := (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ h t⁻¹
    convert this using 1
    group)
  refine eq_top_iff.2 fun x _ => ?_
  by_cases hx : x ∈ commutator (Sp4 F)
  · exact hcH hx
  · have hxm := mul_mem_commutator_of_not hq2 hx hmo
    have := mul_mem (hcH hxm) (inv_mem hmH)
    rwa [mul_inv_cancel_right] at this

theorem wq_le_of_xAlt_not_mem (hq2 : Nat.card F = 2) {R A₀ Z : Subgroup (Sp4 F)}
    (hR : IsPGroup 2 R) (hRl : R ≤ MSP.stab (ln₀ F)) (hRe : ∀ r ∈ R, mat r *ᵥ e₁ F = e₁ F)
    (hA₀ : A₀ = Q₁ F ⊓ R) (hA₀c : Nat.card F ^ 2 ≤ Nat.card A₀)
    (h51 : ∀ p₁ p₂ : Submodule F (V4 F), IsPoint p₁ → IsPoint p₂ → A₀ ≠ xPoint p₁ ⊔ xPoint p₂)
    (hodd : ¬ R ≤ commutator (Sp4 F)) (hRQ : ¬ R ≤ Q₁ F) (hZR : Z ≤ R)
    (hZ : (∃ c : Submodule F (V4 F), IsPoint c ∧ Z = xPoint c) ∨
      (Nat.card F ^ 2 ≤ Nat.card Z ∧ commSp Z ≤ fixSp Z ∧ Module.finrank F (fixSp Z) ≤ 2) ∨
      (Nat.card F = 2 ∧ ∃ v₁ v₂ : V4 F, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧ form F v₁ v₂ = 0 ∧
        transv v₁ 1 ∈ R ∧ transv v₂ 1 ∈ R ∧
        (transv v₁ 1 ∈ Z ∨ transv v₂ 1 ∈ Z ∨ transv v₁ 1 * transv v₂ 1 ∈ Z)))
    (hxA : xAlt F ∉ A₀) : wq F ≤ R ∧ nuE 1 ∈ R ∧ wq F ≤ Z := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h01 := eq_zero_or_eq_one_of_card_two hq2
  have hRt : ∀ r ∈ R, mat r (.inl 1) (.inl 1) = 1 := fun r hr => by
    obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
    exact entry_e₂_eq_one (hRl hr) (hRe r hr) (by simpa using congrArg Subtype.val hn)
  have hA₀Q : A₀ ≤ Q₁ F := hA₀ ▸ inf_le_left
  have hA₀R : A₀ ≤ R := hA₀ ▸ inf_le_right
  have hmemA : ∀ {k : Sp4 F}, k ∈ Q₁ F → k ∈ R → k ∈ A₀ := fun hk hkR =>
    hA₀ ▸ Subgroup.mem_inf.2 ⟨hk, hkR⟩
  have hinj : Function.Injective fun k : A₀ =>
      (mat (k : Sp4 F) (.inl 0) (.inr 0), mat (k : Sp4 F) (.inl 1) (.inr 1)) := by
    intro x y hxy
    have e1 := congrArg Prod.fst hxy
    have e2 := congrArg Prod.snd hxy
    simp only at e1 e2
    have hk : (x : Sp4 F) * (y : Sp4 F)⁻¹ ∈ A₀ := mul_mem x.2 (inv_mem y.2)
    have hb : mat ((x : Sp4 F) * (y : Sp4 F)⁻¹) (.inl 0) (.inr 0) = 0 := by
      rw [entry_mul_inv_of_mem_Q₁ (hA₀Q x.2) (hA₀Q y.2), e1, sub_self]
    have hd : mat ((x : Sp4 F) * (y : Sp4 F)⁻¹) (.inl 1) (.inr 1) = 0 := by
      rw [entry_mul_inv_of_mem_Q₁ (hA₀Q x.2) (hA₀Q y.2), e2, sub_self]
    rcases eq_one_or_eq_xAlt hq2 (hA₀Q hk) hb hd with h | h
    · exact Subtype.ext (mul_inv_eq_one.1 h)
    · exact absurd (h ▸ hk) hxA
  have hc4 : Nat.card A₀ = Nat.card F ^ 2 := le_antisymm (by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod, ← sq] at this) hA₀c
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hc4, sq])
  obtain ⟨⟨k₁, hk₁⟩, hk₁e⟩ := hbij.2 (1, 0)
  obtain ⟨⟨k₂, hk₂⟩, hk₂e⟩ := hbij.2 (0, 1)
  simp only [Prod.mk.injEq] at hk₁e hk₂e
  have hk₁Q := hA₀Q hk₁
  have hk₂Q := hA₀Q hk₂
  obtain ⟨r₀, hr₀, hr₀Q⟩ := Set.not_subset.1 hRQ
  have ha₀ : mat r₀ (.inl 0) (.inl 1) = 1 := (h01 _).resolve_left fun h =>
    hr₀Q ((mem_Q₁_iff_of_stab (hRl hr₀) (hRe r₀ hr₀) (hRt r₀ hr₀)).2 h)
  have hcq := q1c_conj_of_stab (hRl hr₀) (hRe r₀ hr₀) (hRt r₀ hr₀) hk₂Q
  rw [ha₀] at hcq
  simp only [q1c, Prod.mk.injEq] at hcq
  have hck : r₀ * k₂ * r₀⁻¹ ∈ A₀ :=
    hmemA (conj_mem_Q₁ (hRl hr₀) hk₂Q) (R.mul_mem (R.mul_mem hr₀ (hA₀R hk₂)) (R.inv_mem hr₀))
  have hkk : k₁ * k₂ ∈ A₀ := mul_mem hk₁ hk₂
  have heq : (⟨r₀ * k₂ * r₀⁻¹, hck⟩ : A₀) = ⟨k₁ * k₂, hkk⟩ := by
    refine hinj (Prod.ext ?_ ?_)
    · simp only
      rw [hcq.1, entry_mul_of_mem_Q₁ hk₁Q hk₂Q, hk₁e.1, hk₂e.1, hk₂e.2]
      ring
    · simp only
      rw [hcq.2.2, entry_mul_of_mem_Q₁ hk₁Q hk₂Q, hk₁e.2, hk₂e.2]
      ring
  have hc₁ : mat k₁ (.inl 0) (.inr 1) = 1 := by
    have := congrArg (fun k : A₀ => mat (k : Sp4 F) (.inl 0) (.inr 1)) heq
    simp only at this
    rw [hcq.2.1, entry_mul_of_mem_Q₁ hk₁Q hk₂Q, hk₂e.2] at this
    linear_combination -this
  obtain ⟨g00, g01, g02⟩ := entry_transv_gv (0 : F) 1
  obtain ⟨g10, g11, g12⟩ := entry_transv_gv (1 : F) 1
  have hT0 := transv_gv_mem_Q₁ (0 : F) 1
  have hT1 := transv_gv_mem_Q₁ (1 : F) 1
  have hk₁t : k₁ = transv (gv 0) 1 * transv (gv 1) 1 := by
    refine eq_of_mem_Q₁ hk₁Q (mul_mem hT0 hT1) ?_ ?_ ?_ <;>
      rw [entry_mul_of_mem_Q₁ hT0 hT1]
    · rw [hk₁e.1, g00, g10]; ring
    · rw [hc₁, g01, g11]; ring
    · rw [hk₁e.2, g02, g12]; linear_combination -h2
  have hc₂ : mat k₂ (.inl 0) (.inr 1) = 1 := by
    rcases h01 (mat k₂ (.inl 0) (.inr 1)) with hc | hc
    · exfalso
      have hk₂t : k₂ = transv (gv 0) 1 := eq_of_mem_Q₁ hk₂Q hT0 (by rw [hk₂e.1, g00]; ring)
        (by rw [hc, g01]; ring) (by rw [hk₂e.2, g02])
      have ht1 : transv (gv 1) 1 ∈ A₀ := by
        have := mul_mem hk₂ hk₁
        rwa [hk₂t, hk₁t, ← mul_assoc, transv_mul, CharTwo.add_self_eq_zero, transv_zero,
          one_mul] at this
      have hX0 := xPoint_span_le_of_card_two hq2 (gv_ne_zero (0 : F)) (hk₂t ▸ hk₂)
      have hX1 := xPoint_span_le_of_card_two hq2 (gv_ne_zero (1 : F)) ht1
      have hne : (F ∙ gv (0 : F)) ≠ F ∙ gv 1 := fun h => zero_ne_one (span_gv_inj h)
      have hcard := card_xPoint_sup (isPoint_gv 0) (isPoint_gv 1) hne (span_gv_le_perp 0 1)
      exact h51 _ _ (isPoint_gv 0) (isPoint_gv 1)
        (Subgroup.eq_of_le_of_card_ge (sup_le hX0 hX1) (by rw [hc4]; exact hcard)).symm
    · exact hc
  have hTe := transv_e₁_mem_Q₁ (F := F) 1
  have hk₂t : k₂ = transv (e₁ F) 1 * transv (gv 1) 1 := by
    have he := q1c_transv_e₁ (F := F) 1
    simp only [q1c, Prod.mk.injEq] at he
    refine eq_of_mem_Q₁ hk₂Q (mul_mem hTe hT1) ?_ ?_ ?_ <;>
      rw [entry_mul_of_mem_Q₁ hTe hT1]
    · rw [hk₂e.1, he.1, g10]; linear_combination -h2
    · rw [hc₂, he.2.1, g11]; ring
    · rw [hk₂e.2, he.2.2, g12]; ring
  have hcomm₁ : k₁ ∈ commutator (Sp4 F) := hk₁t ▸ transv_mul_transv_mem hq2 (gv_ne_zero 0)
    (gv_ne_zero 1)
  have hcomm₂ : k₂ ∈ commutator (Sp4 F) := hk₂t ▸ transv_mul_transv_mem hq2 e₁_ne_zero
    (gv_ne_zero 1)
  have hA₀W : A₀ ≤ wq F := by
    intro a ha
    refine ⟨hA₀Q ha, ?_⟩
    have hval : ∀ (k : A₀), (mat (k : Sp4 F) (.inl 0) (.inr 0), mat (k : Sp4 F) (.inl 1) (.inr 1))
        = (mat (a : Sp4 F) (.inl 0) (.inr 0), mat a (.inl 1) (.inr 1)) → (k : Sp4 F) = a :=
      fun k hk => congrArg Subtype.val (hinj (a₁ := k) (a₂ := ⟨a, ha⟩) hk)
    have e11 : (mat (k₁ * k₂) (.inl 0) (.inr 0), mat (k₁ * k₂) (.inl 1) (.inr 1)) = (1, 1) := by
      rw [entry_mul_of_mem_Q₁ hk₁Q hk₂Q, entry_mul_of_mem_Q₁ hk₁Q hk₂Q, hk₁e.1, hk₁e.2, hk₂e.1,
        hk₂e.2]
      simp
    rcases h01 (mat a (.inl 0) (.inr 0)) with hb | hb <;>
      rcases h01 (mat a (.inl 1) (.inr 1)) with hd | hd
    · have := hval ⟨1, one_mem _⟩ (by simp [entry_one, hb, hd])
      rw [← this]
      exact one_mem _
    · have := hval ⟨k₂, hk₂⟩ (by simp [hk₂e.1, hk₂e.2, hb, hd])
      rw [← this]
      exact hcomm₂
    · have := hval ⟨k₁, hk₁⟩ (by simp [hk₁e.1, hk₁e.2, hb, hd])
      rw [← this]
      exact hcomm₁
    · have := hval ⟨k₁ * k₂, hkk⟩ (by rw [e11, hb, hd])
      rw [← this]
      exact mul_mem hcomm₁ hcomm₂
  have hWc : Nat.card (wq F) ≤ Nat.card F ^ 2 := by
    have hlt : wq F < Q₁ F := lt_of_le_of_ne inf_le_left fun h =>
      transv_one_not_mem hq2 e₁_ne_zero ((h ▸ transv_e₁_mem_Q₁ 1 : transv (e₁ F) 1 ∈ wq F).2)
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2' := Subgroup.card_dvd_of_le hlt.le
    rw [card_Q₁, hq2] at h1 h2'
    rw [hq2]
    obtain ⟨m, hm⟩ := h2'
    rcases m with _ | _ | m
    · omega
    · omega
    · nlinarith
  have hA₀eq : A₀ = wq F := Subgroup.eq_of_le_of_card_ge hA₀W (by rw [hc4]; exact hWc)
  have hnR : nuE 1 ∈ R := by
    obtain ⟨r₁, hr₁, hr₁c⟩ := Set.not_subset.1 hodd
    have hr₁Q : r₁ ∉ Q₁ F := fun h => hr₁c (hA₀W (hmemA h hr₁)).2
    have ha₁ : mat r₁ (.inl 0) (.inl 1) = 1 := (h01 _).resolve_left fun h =>
      hr₁Q ((mem_Q₁_iff_of_stab (hRl hr₁) (hRe r₁ hr₁) (hRt r₁ hr₁)).2 h)
    have hk := nuE_mul_mem_Q₁ (hRl hr₁) (hRe r₁ hr₁) (hRt r₁ hr₁)
    rw [ha₁] at hk
    have hkc := mul_mem_commutator_of_not hq2 (nuE_one_not_mem_commutator hq2) hr₁c
    have hkR : nuE 1 * r₁ ∈ R := hA₀R (hA₀eq ▸ (⟨hk, hkc⟩ : nuE 1 * r₁ ∈ wq F))
    have := R.mul_mem hkR (R.inv_mem hr₁)
    rwa [mul_inv_cancel_right] at this
  refine ⟨hA₀eq ▸ hA₀R, hnR, ?_⟩
  have hnot : ∀ {v : V4 F}, v ≠ 0 → transv v 1 ∈ R → False := fun hv hvR => by
    have hvl := mem_ln₀_of_transv_mem_stab hv (hRl hvR) (hRe _ hvR)
    have := hA₀W (hmemA (transv_mem_qLine isLine_ln₀ hvl 1) hvR)
    exact transv_one_not_mem hq2 hv this.2
  have hXnot : ∀ {c : Submodule F (V4 F)}, IsPoint c → ¬ xPoint c ≤ R := fun hc hcR => by
    obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_isPoint hc
    exact hnot hv (hcR (transv_mem_xPoint v 1))
  rcases hZ with hZ | hZ | ⟨-, v₁, -, h₁, -, -, -, hR₁, -, -⟩
  · obtain ⟨c, hc, rfl⟩ := hZ
    exact absurd hZR (hXnot hc)
  · rcases xPoint_le_or_le_Q₁ hR hRl hRe hZR (Or.inr hZ) with ⟨c, hc, -, hcZ⟩ | ⟨hZQ, hZc⟩
    · exact absurd (hcZ.trans hZR) (hXnot hc)
    · have hZA : Z ≤ A₀ := fun z hz => hmemA (hZQ hz) (hZR hz)
      have heqZ : Z = A₀ := Subgroup.eq_of_le_of_card_ge hZA (by rw [hc4]; exact hZc)
      rw [heqZ, hA₀eq]
  · exact (hnot h₁ hR₁).elim

theorem exists_top_of_card_two (hq2 : Nat.card F = 2) {R A₀ D Z : Subgroup (Sp4 F)}
    (hR : IsPGroup 2 R) (hA : candMax R = {A₀}) (hRl : R ≤ MSP.stab (ln₀ F))
    (hRe : ∀ r ∈ R, mat r *ᵥ e₁ F = e₁ F) (hA₀ : A₀ = Q₁ F ⊓ R)
    (hA₀c : Nat.card F ^ 2 ≤ Nat.card A₀)
    (h51 : ∀ p₁ p₂ : Submodule F (V4 F), IsPoint p₁ → IsPoint p₂ → A₀ ≠ xPoint p₁ ⊔ xPoint p₂)
    (hodd : ¬ R ≤ commutator (Sp4 F)) (hDR : D ≤ R)
    (hDn : R ≤ Subgroup.normalizer (D : Set (Sp4 F))) (hAD : Nat.card A₀ ≤ Nat.card D)
    (hDQ : ¬ D ≤ Q₁ F) (hZR : Z ≤ R)
    (hZ : (∃ c : Submodule F (V4 F), IsPoint c ∧ Z = xPoint c) ∨
      (Nat.card F ^ 2 ≤ Nat.card Z ∧ commSp Z ≤ fixSp Z ∧ Module.finrank F (fixSp Z) ≤ 2) ∨
      (Nat.card F = 2 ∧ ∃ v₁ v₂ : V4 F, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧ form F v₁ v₂ = 0 ∧
        transv v₁ 1 ∈ R ∧ transv v₂ 1 ∈ R ∧
        (transv v₁ 1 ∈ Z ∨ transv v₂ 1 ∈ Z ∨ transv v₁ 1 * transv v₂ 1 ∈ Z))) :
    ∃ g : Sp4 F, pt₀ F ⊓ (ln₀ F).map (mulVecLin (mat g⁻¹)) = ⊥ ∧
      R.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z = ⊤ := by
  by_cases hxA : xAlt F ∈ A₀
  · obtain ⟨ν, hZν⟩ := exists_lam_shape_two hq2 hR hRl hRe hZR hZ
    exact ⟨gEl ν ν, pt₀_inf_map_gEl ν ν,
      top_of_xAlt_mem hq2 hR hA hRl hRe hA₀ hA₀c hDR hDn hAD hDQ hZν hxA⟩
  · obtain ⟨hWR, hnR, hWZ⟩ := wq_le_of_xAlt_not_mem hq2 hR hRl hRe hA₀ hA₀c h51 hodd
      (fun h => hDQ (hDR.trans h)) hZR hZ hxA
    exact ⟨gEl 0 0, pt₀_inf_map_gEl 0 0, top_of_wq hq2 hWR hnR hWZ⟩

theorem sp4Case55Std_of_card_two (hq2 : Nat.card F = 2) [Fintype F] : Sp4Case55Std F := by
  intro R A₀ D Z hR hA hRl hRe hA₀ hA₀c h51 hodd hDR hDn hAD _ hDQ hZR hZ
  obtain ⟨g, hg, htop⟩ := exists_top_of_card_two hq2 hR hA hRl hRe hA₀ hA₀c h51 (hodd hq2) hDR
    hDn hAD hDQ hZR hZ
  refine ⟨g, hg, ?_⟩
  by_cases hDR' : D = R
  · left
    subst hDR'
    rw [htop]
    exact le_top
  · right
    have hRt : ∀ r ∈ R, mat r (.inl 1) (.inl 1) = 1 := fun r hr => by
      obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
      exact entry_e₂_eq_one (hRl hr) (hRe r hr) (by simpa using congrArg Subtype.val hn)
    have hRle := card_le_card_inf_Q₁_mul fun r hr =>
      (⟨hRl hr, hRe r hr, hRt r hr⟩ :
        r ∈ MSP.stab (ln₀ F) ∧ mat r *ᵥ e₁ F = e₁ F ∧ mat r (.inl 1) (.inl 1) = 1)
    rw [inf_comm, ← hA₀, hq2] at hRle
    have hDlt : D < R := lt_of_le_of_ne hDR hDR'
    have hcD := Subgroup.card_lt_of_lt hDlt
    have hdD := Subgroup.card_dvd_of_le hDR
    have hD : Nat.card D = Nat.card A₀ := by
      refine le_antisymm ?_ hAD
      obtain ⟨m, hm⟩ := hdD
      rcases m with _ | _ | m
      · omega
      · omega
      · nlinarith
    refine ⟨htop, hD, ?_⟩
    have hDA : D ⊓ A₀ ≤ D ⊓ Q₁ F := inf_le_inf_left _ (hA₀ ▸ inf_le_left)
    have hlt : D ⊓ Q₁ F < D := lt_of_le_of_ne inf_le_left fun h => hDQ (h ▸ inf_le_right)
    have hc1 := Subgroup.card_lt_of_lt hlt
    have hd1 := Subgroup.card_dvd_of_le (inf_le_left : D ⊓ Q₁ F ≤ D)
    have hA8 : Nat.card A₀ ≤ Nat.card F ^ 3 := by
      rw [← card_Q₁]
      exact Subgroup.card_le_of_le (hA₀ ▸ inf_le_left)
    have hle : 2 * Nat.card ↥(D ⊓ Q₁ F) ≤ Nat.card D := by
      obtain ⟨m, hm⟩ := hd1
      rcases m with _ | _ | m
      · omega
      · omega
      · nlinarith
    rw [hq2] at hA8 ⊢
    have := Subgroup.card_le_of_le hDA
    omega

theorem sp4Case55_holds : Sp4Case55 := by
  intro F _ _ _ R A₀ D Z l hR hA hl hRl hA₀l hA₀c h51 hodd hDR hDn hAD hDnc hZR hZ
  have hstd : Sp4Case55Std F := by
    rcases card_eq_two_or_four_le (F := F) with h2 | h4
    · exact sp4Case55Std_of_card_two h2
    · exact sp4Case55Std_of_two_lt (by omega)
  exact sp4Case55_of_std hstd R A₀ D Z l hR hA hl hRl hA₀l hA₀c h51 hodd hDR hDn hAD hDnc hZR hZ

end CFSG.Quasithin.MS93.S5
