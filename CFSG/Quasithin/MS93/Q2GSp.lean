module

public import CFSG.Quasithin.MS93.S5Q2Par

public section

namespace CFSG.Quasithin.MS93.Q2G

open CFSG.Quasithin.MS93.MSP
open scoped Matrix

variable {K : Type} [Field K]

theorem finrank_fixSp_le (A : Subgroup (Sp4 K)) : Module.finrank K (fixSp A) ≤ 4 := by
  have := Submodule.finrank_le (fixSp A)
  simpa using this

theorem mem_fixSp_zpowers {g : Sp4 K} {v : V4 K} :
    v ∈ fixSp (Subgroup.zpowers g) ↔ mat g *ᵥ v = v := by
  refine ⟨fun h => h g (Subgroup.mem_zpowers g), fun h => ?_⟩
  have hle : Subgroup.zpowers g ≤ fixer (K ∙ v) := by
    rw [Subgroup.zpowers_le]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [Matrix.mulVec_smul, h]
  exact (le_fixer_iff.1 hle) (Submodule.mem_span_singleton_self v)

theorem eq_zero_or_eq_one (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  obtain ⟨φ⟩ := nonempty_ringEquiv_of_card_two hK
  exact eq_zero_or_eq_one_of_ringEquiv φ c

theorem two_le_card_zpowers (hK : Nat.card K = 2) {g : Sp4 K} (hg : g ≠ 1) :
    Nat.card K ≤ Nat.card (Subgroup.zpowers g) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  rw [hK]
  have hne : Subgroup.zpowers g ≠ ⊥ := fun h =>
    hg (by rw [← Subgroup.mem_bot, ← h]; exact Subgroup.mem_zpowers g)
  have := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  omega

theorem fixSp_zpowers_eq_of_mem (hK : Nat.card K = 2) {l : Submodule K (V4 K)} (hl : IsLine l)
    {e : Sp4 K} (he : e ∈ qLine l ⊓ commutator (Sp4 K)) (he1 : e ≠ 1) :
    fixSp (Subgroup.zpowers e) = l := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hle : l ≤ fixSp (Subgroup.zpowers e) :=
    calc l = fixSp (qLine l) := (fixSp_qLine hl).symm
      _ ≤ _ := fixSp_antitone ((Subgroup.zpowers_le).2 he.1)
  have h2 : Module.finrank K l = 2 := hl.1
  have hfr : 2 ≤ Module.finrank K (fixSp (Subgroup.zpowers e)) := by
    have := Submodule.finrank_mono hle
    omega
  have h4 := finrank_fixSp_le (Subgroup.zpowers e)
  rcases (show Module.finrank K (fixSp (Subgroup.zpowers e)) = 2 ∨
      Module.finrank K (fixSp (Subgroup.zpowers e)) = 3 ∨
      Module.finrank K (fixSp (Subgroup.zpowers e)) = 4 by omega) with h | h | h
  · exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, h])).symm
  · exfalso
    obtain ⟨p, hp, hpE⟩ := eq_xPoint_of_finrank_fixSp_three h (two_le_card_zpowers hK he1)
    exact xPoint_not_le_commutator hK hp (hpE ▸ (Subgroup.zpowers_le).2 he.2)
  · exfalso
    have htop : fixSp (Subgroup.zpowers e) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h]; simp)
    have hbot := fixSp_eq_top_iff.1 htop
    exact he1 (by rw [← Subgroup.mem_bot, ← hbot]; exact Subgroup.mem_zpowers e)

theorem exists_ne_one (hK : Nat.card K = 2) {l : Submodule K (V4 K)} (hl : IsLine l) :
    ∃ e ∈ qLine l ⊓ commutator (Sp4 K), e ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : qLine l ⊓ commutator (Sp4 K) = ⊥ := eq_bot_iff.2 fun e he =>
    Subgroup.mem_bot.2 (hcon e he)
  have h4 := card_qLine_inf_commutator hK hl
  rw [hbot, Subgroup.card_bot] at h4
  omega

theorem fixSp_qLine_inf_commutator (hK : Nat.card K = 2) {l : Submodule K (V4 K)}
    (hl : IsLine l) : fixSp (qLine l ⊓ commutator (Sp4 K)) = l := by
  obtain ⟨e, he, he1⟩ := exists_ne_one hK hl
  refine le_antisymm ?_ ?_
  · calc fixSp (qLine l ⊓ commutator (Sp4 K)) ≤ fixSp (Subgroup.zpowers e) :=
          fixSp_antitone ((Subgroup.zpowers_le).2 he)
      _ = l := fixSp_zpowers_eq_of_mem hK hl he he1
  · calc l = fixSp (qLine l) := (fixSp_qLine hl).symm
      _ ≤ _ := fixSp_antitone inf_le_left

private theorem sub_mulVec_comm {t e : Sp4 K} (hte : t * e = e * t) (v : V4 K) :
    mat e *ᵥ (mat t *ᵥ v) - mat t *ᵥ v = mat t *ᵥ (mat e *ᵥ v - v) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mat_mul, ← mat_mul, hte]

theorem mem_qLine_of_commute (hK : Nat.card K = 2) {l : Submodule K (V4 K)} (hl : IsLine l)
    {t e e' : Sp4 K} (ht : t ∈ MSP.stab l) {p : V4 K} (hpl : p ∈ l) (hp0 : p ≠ 0)
    (htp : mat t *ᵥ p = p) (he : e ∈ qLine l) (he' : e' ∈ qLine l)
    (hfe : fixSp (Subgroup.zpowers e) = l) (hfe' : fixSp (Subgroup.zpowers e') = l)
    (hfee : fixSp (Subgroup.zpowers (e⁻¹ * e')) = l)
    (hte : t * e = e * t) (hte' : t * e' = e' * t) : t ∈ qLine l := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hP3 : Module.finrank K (perp (K ∙ p)) = 3 := by
    have h1 := finrank_perp (K ∙ p)
    rw [finrank_span_singleton hp0] at h1
    omega
  have hlP : l ≤ perp (K ∙ p) := fun v hv => mem_perp_span.2 (hl.2 p hpl v hv)
  obtain ⟨w, hwP, hwl⟩ : ∃ w ∈ perp (K ∙ p), w ∉ l := by
    by_contra hcon
    push Not at hcon
    have h1 := Submodule.finrank_mono (show perp (K ∙ p) ≤ l from hcon)
    have h2 : Module.finrank K l = 2 := hl.1
    rw [hP3, h2] at h1
    omega
  have htw : mat t *ᵥ w ∈ perp (K ∙ p) := by
    rw [mem_perp_span, ← htp, form_mat]
    exact mem_perp_span.1 hwP
  have hsup : l ⊔ (K ∙ w) = perp (K ∙ p) := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hlP
      ((Submodule.span_singleton_le_iff_mem w (perp (K ∙ p))).2 hwP)) ?_
    have hdisj : l ⊓ (K ∙ w) = ⊥ := by
      refine eq_bot_iff.2 fun v hv => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv.2
      rcases eq_zero_or_eq_one hK c with rfl | rfl
      · simp
      · exact absurd (by simpa using hv.1) hwl
    have hw0 : w ≠ 0 := fun h0 => hwl (h0 ▸ l.zero_mem)
    have h := Submodule.finrank_sup_add_finrank_inf_eq l (K ∙ w)
    rw [hdisj, finrank_bot, finrank_span_singleton hw0, hl.1] at h
    rw [hP3]
    omega
  have htwl : mat t *ᵥ w - w ∈ l := by
    rw [← hsup] at htw
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 htw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rcases eq_zero_or_eq_one hK c with rfl | rfl
    · exfalso
      rw [zero_smul, add_zero] at hxy
      have h1 : mat t⁻¹ *ᵥ (mat t *ᵥ w) ∈ l := mulVec_mem_of_mem_stab (inv_mem ht) (hxy ▸ hx)
      rw [mat_inv_mulVec] at h1
      exact hwl h1
    · rw [one_smul] at hxy
      rw [← hxy, add_sub_cancel_right]
      exact hx
  have hel : ∀ {f : Sp4 K}, f ∈ qLine l → ∀ v ∈ l, mat f *ᵥ v = v := fun hf v hv => hf v hv
  have hfix : ∀ {f : Sp4 K}, f ∈ qLine l → t * f = f * t →
      mat t *ᵥ (mat f *ᵥ w - w) = mat f *ᵥ w - w := by
    intro f hf htf
    rw [← sub_mulVec_comm htf]
    have hd : mat t *ᵥ w = w + (mat t *ᵥ w - w) := by abel
    rw [hd, Matrix.mulVec_add, hel hf _ htwl]
    abel
  have hmem : ∀ {f : Sp4 K}, f ∈ qLine l → mat f *ᵥ w - w ∈ l := by
    intro f hf
    have hf' : f ∈ fixer (perp l) := by rw [hl.perp_eq]; exact hf
    exact sub_mem_of_mem_fixer_perp hf' w
  have hne0 : ∀ {f : Sp4 K}, fixSp (Subgroup.zpowers f) = l → mat f *ᵥ w - w ≠ 0 := by
    intro f hf h0
    apply hwl
    rw [← hf, mem_fixSp_zpowers]
    exact sub_eq_zero.1 h0
  have hxy : mat e' *ᵥ w - w ∉ K ∙ (mat e *ᵥ w - w) := by
    intro hyx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hyx
    rcases eq_zero_or_eq_one hK c with rfl | rfl
    · exact hne0 hfe' (by rw [← hc, zero_smul])
    · rw [one_smul] at hc
      apply hwl
      rw [← hfee, mem_fixSp_zpowers, mat_mul, ← Matrix.mulVec_mulVec]
      have h1 : mat e' *ᵥ w = mat e *ᵥ w := by
        have := congrArg (· + w) hc
        simp only [sub_add_cancel] at this
        exact this.symm
      rw [h1, mat_inv_mulVec]
  have hspan : Submodule.span K {mat e *ᵥ w - w, mat e' *ᵥ w - w} = l := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact hmem he
      · exact hmem he'
    · rw [finrank_span_pair (hne0 hfe) hxy, hl.1]
  have htl : ∀ v ∈ l, mat t *ᵥ v = v := by
    rw [← hspan]
    intro v hv
    refine Submodule.span_induction (p := fun v _ => mat t *ᵥ v = v) ?_ ?_ ?_ ?_ hv
    · rintro _ (rfl | rfl)
      · exact hfix he hte
      · exact hfix he' hte'
    · exact Matrix.mulVec_zero _
    · intro u v _ _ hu hv
      rw [Matrix.mulVec_add, hu, hv]
    · intro c u _ hu
      rw [Matrix.mulVec_smul, hu]
  exact htl

theorem mem_qLine_of_centralizer (hK : Nat.card K = 2) {l : Submodule K (V4 K)} (hl : IsLine l)
    {t : Sp4 K} (ht : t ∈ MSP.stab l) {p : V4 K} (hpl : p ∈ l) (hp0 : p ≠ 0)
    (htp : mat t *ᵥ p = p)
    (htE : ∀ e ∈ qLine l ⊓ commutator (Sp4 K), t * e = e * t) : t ∈ qLine l := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set E := qLine l ⊓ commutator (Sp4 K) with hE
  obtain ⟨e, he, he1⟩ := exists_ne_one hK hl
  obtain ⟨e', he', he'1, he'e⟩ : ∃ e' ∈ E, e' ≠ 1 ∧ e' ≠ e := by
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set (Sp4 K)) ⊆ {1, e} := fun f hf => by
      by_cases hf1 : f = 1
      · exact Or.inl hf1
      · exact Or.inr (hcon f hf hf1)
    have h4 : Nat.card E = 4 := card_qLine_inf_commutator hK hl
    have hle : Nat.card E ≤ 2 := by
      have h1 : Nat.card E = (E : Set (Sp4 K)).ncard := Nat.card_coe_set_eq _
      rw [h1]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      rw [Set.ncard_pair (Ne.symm he1)]
    omega
  have hee : e⁻¹ * e' ∈ E := E.mul_mem (E.inv_mem he) he'
  have hee1 : e⁻¹ * e' ≠ 1 := fun h => he'e (by
    rw [inv_mul_eq_one] at h
    exact h.symm)
  exact mem_qLine_of_commute hK hl ht hpl hp0 htp he.1 he'.1
    (fixSp_zpowers_eq_of_mem hK hl he he1) (fixSp_zpowers_eq_of_mem hK hl he' he'1)
    (fixSp_zpowers_eq_of_mem hK hl hee hee1) (htE e he) (htE e' he')

end CFSG.Quasithin.MS93.Q2G
