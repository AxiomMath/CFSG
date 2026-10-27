module

public import CFSG.Quasithin.MS93.MSPBT
public import CFSG.Quasithin.MS93.MSPGen

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

theorem finrank_span_pair {x w : V4 F} (hx : x ≠ 0) (hw : w ∉ F ∙ x) :
    Module.finrank F (Submodule.span F {x, w}) = 2 := by
  have hli : LinearIndependent F ![x, w] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hx, rfl⟩
    · refine absurd ?_ hw
      have : w = (-(s / t)) • x := by
        have h := congrArg (fun v => t⁻¹ • v) hst
        simp only [smul_add, smul_smul, smul_zero] at h
        rw [inv_mul_cancel₀ ht, one_smul] at h
        rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, div_eq_inv_mul, add_comm]
        exact h
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have h := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h
  rwa [Matrix.range_cons_cons_empty] at h

theorem form_span_pair {x w : V4 F} (hxw : form F x w = 0) :
    IsTotallyIsotropic (form F) (Submodule.span F {x, w}) := by
  intro u hu v hv
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hu
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hv
  have hwx : form F w x = 0 := by rw [form_swap, hxw, neg_zero]
  simp [hxw, hwx, form_self]

theorem exists_not_mem_span_of_one_lt {W : Submodule F (V4 F)} (hW : 1 < Module.finrank F W)
    (x : V4 F) : ∃ w ∈ W, w ∉ F ∙ x := by
  by_contra h
  push Not at h
  have := Submodule.finrank_mono (show W ≤ F ∙ x from fun w hw => h w hw)
  have h1 : Module.finrank F (F ∙ x) ≤ 1 := by
    by_cases hx : x = 0
    · rw [hx, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]
      omega
    · rw [finrank_span_singleton hx]
  omega

theorem isTotallyIsotropic_of_finrank_two {C : Submodule F (V4 F)}
    (hC : Module.finrank F C = 2) {x : V4 F} (hx : x ∈ C) (hx0 : x ≠ 0) (hxp : x ∈ perp C) :
    IsTotallyIsotropic (form F) C := by
  obtain ⟨w, hw, hwx⟩ := exists_not_mem_span_of_one_lt (W := C) (by omega) x
  have hspan : Submodule.span F {x, w} = C := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      exacts [hx, hw]
    · rw [finrank_span_pair hx0 hwx, hC]
  rw [← hspan]
  exact form_span_pair (by rw [form_swap, mem_perp.1 hxp w hw, neg_zero])

theorem exists_isLine_ge {p : Submodule F (V4 F)} (hp : IsPoint p) :
    ∃ l : Submodule F (V4 F), IsLine l ∧ p ≤ l := by
  obtain ⟨x, hx0, rfl⟩ := exists_eq_span_of_isPoint hp
  have h3 : Module.finrank F (perp (F ∙ x)) = 3 := by
    have := finrank_perp (F ∙ x)
    rw [hp] at this
    omega
  obtain ⟨y, hy, hyx⟩ := exists_not_mem_span_of_one_lt (W := perp (F ∙ x)) (by omega) x
  refine ⟨Submodule.span F {x, y}, ⟨finrank_span_pair hx0 hyx,
    form_span_pair (mem_perp_span.1 hy)⟩, ?_⟩
  rw [Submodule.span_singleton_le_iff_mem]
  exact Submodule.subset_span (Set.mem_insert x _)

theorem exists_map_ln₀_eq {l : Submodule F (V4 F)} (hl : IsLine l) :
    ∃ g : Sp4 F, (ln₀ F).map (mulVecLin (mat g)) = l :=
  exists_statedSp_map_eq isLine_ln₀.2 hl.2 (by rw [isLine_ln₀.1, hl.1])

theorem commSp_map_conj (g : Sp4 F) (A : Subgroup (Sp4 F)) :
    commSp (A.map (MulAut.conj g).toMonoidHom) = (commSp A).map (mulVecLin (mat g)) := by
  refine le_antisymm (commSp_le_iff.2 fun b hb v => ?_) ?_
  · rw [mem_map_conj] at hb
    have h := sub_mem_commSp hb (mat g⁻¹ *ᵥ v)
    refine mem_map_mulVecLin.2 ?_
    rw [mulVec_sub]
    convert h using 2
    rw [mat_mul_mulVec, mat_mul_mulVec, mat_mulVec_inv]
  · rw [Submodule.map_le_iff_le_comap, commSp_le_iff]
    intro a ha v
    rw [Submodule.mem_comap, mulVecLin_apply, mulVec_sub]
    have h := sub_mem_commSp (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
      (mat g *ᵥ v)
    convert h using 1
    change mat g *ᵥ (mat a *ᵥ v) - mat g *ᵥ v = mat (g * a * g⁻¹) *ᵥ (mat g *ᵥ v) - mat g *ᵥ v
    rw [mat_mul_mulVec, mat_mul_mulVec, mat_inv_mulVec]

theorem qLine_map_eq (g : Sp4 F) :
    qLine ((ln₀ F).map (mulVecLin (mat g))) = (Q₁ F).map (MulAut.conj g).toMonoidHom :=
  (fixer_map_conj g _).symm

theorem qPoint_map_eq (g : Sp4 F) :
    qPoint ((pt₀ F).map (mulVecLin (mat g))) = (Q₂ F).map (MulAut.conj g).toMonoidHom :=
  (qPoint_map_conj g _).symm

theorem card_map_conj (g : Sp4 F) (A : Subgroup (Sp4 F)) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_qLine [Finite F] {l : Submodule F (V4 F)} (hl : IsLine l) :
    Nat.card (qLine l) = Nat.card F ^ 3 := by
  obtain ⟨g, rfl⟩ := exists_map_ln₀_eq hl
  rw [qLine_map_eq, card_map_conj, card_Q₁]

theorem fixSp_qLine {l : Submodule F (V4 F)} (hl : IsLine l) : fixSp (qLine l) = l := by
  obtain ⟨g, rfl⟩ := exists_map_ln₀_eq hl
  rw [qLine_map_eq, fixSp_map_conj, fixSp_Q₁]

theorem commSp_qLine {l : Submodule F (V4 F)} (hl : IsLine l) : commSp (qLine l) = l := by
  obtain ⟨g, rfl⟩ := exists_map_ln₀_eq hl
  rw [qLine_map_eq, commSp_map_conj, commSp_Q₁]

theorem card_qPoint [Finite F] {p : Submodule F (V4 F)} (hp : IsPoint p) :
    Nat.card (qPoint p) = Nat.card F ^ 3 := by
  obtain ⟨g, rfl⟩ := exists_map_pt₀_eq hp
  rw [qPoint_map_eq, card_map_conj, card_Q₂]

theorem fixSp_qPoint {p : Submodule F (V4 F)} (hp : IsPoint p) : fixSp (qPoint p) = p := by
  obtain ⟨g, rfl⟩ := exists_map_pt₀_eq hp
  rw [qPoint_map_eq, fixSp_map_conj, fixSp_Q₂]

theorem card_xPoint [Finite F] {p : Submodule F (V4 F)} (hp : IsPoint p) :
    Nat.card (xPoint p) = Nat.card F := by
  obtain ⟨g, rfl⟩ := exists_map_pt₀_eq hp
  rw [← X₂_map_conj, card_map_conj, card_X₂]

theorem le_perp_of_isPoint {p : Submodule F (V4 F)} (hp : IsPoint p) : p ≤ perp p := by
  obtain ⟨x, -, rfl⟩ := exists_eq_span_of_isPoint hp
  exact fun v hv => mem_perp.2 fun w hw => isTotallyIsotropic_span x w hw v hv

theorem xPoint_le_qPoint {p : Submodule F (V4 F)} (hp : IsPoint p) : xPoint p ≤ qPoint p :=
  fun _ hg => ⟨fun v hv => hg v (le_perp_of_isPoint hp hv), fun v _ =>
    sub_mem_of_mem_fixer_perp hg v⟩

theorem xPoint_le_qLine {p l : Submodule F (V4 F)} (hl : IsLine l) (hpl : p ≤ l) :
    xPoint p ≤ qLine l := by
  refine fixer_antitone ?_
  rw [← hl.perp_eq]
  exact perp_antitone hpl

theorem le_of_xPoint_le_stab {p l : Submodule F (V4 F)} (hp : IsPoint p) (hl : IsLine l)
    (h : xPoint p ≤ stab l) : p ≤ l := by
  obtain ⟨x, hx0, rfl⟩ := exists_eq_span_of_isPoint hp
  rw [Submodule.span_singleton_le_iff_mem]
  by_contra hxl
  have hperp : l ≤ perp (F ∙ x) := fun w hw => by
    rw [mem_perp_span]
    have h1 := mulVec_mem_of_mem_stab (h (transv_mem_xPoint x 1)) hw
    rw [transv_mulVec, one_mul] at h1
    by_contra hne
    refine hxl ?_
    have h2 := l.sub_mem h1 hw
    rw [add_sub_cancel_left] at h2
    have := l.smul_mem (form F x w)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  refine hxl ?_
  rw [← hl.perp_eq]
  exact mem_perp.2 fun w hw => by
    rw [form_swap, mem_perp_span.1 (hperp hw), neg_zero]

theorem xPoint_le_qLine_iff {p l : Submodule F (V4 F)} (hp : IsPoint p) (hl : IsLine l) :
    xPoint p ≤ qLine l ↔ p ≤ l :=
  ⟨fun h => le_of_xPoint_le_stab hp hl (h.trans (fixer_le_stab l)), xPoint_le_qLine hl⟩

theorem xPoint_le_stab_iff {p l : Submodule F (V4 F)} (hp : IsPoint p) (hl : IsLine l) :
    xPoint p ≤ stab l ↔ p ≤ l :=
  ⟨le_of_xPoint_le_stab hp hl, fun h => (xPoint_le_qLine hl h).trans (fixer_le_stab l)⟩

theorem card_V4 [Finite F] : Nat.card (V4 F) = Nat.card F ^ 4 := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp

theorem card_fixSp [Finite F] (E : Subgroup (Sp4 F)) :
    Nat.card (fixSp E) = Nat.card F ^ Module.finrank F (fixSp E) :=
  Module.natCard_eq_pow_finrank (K := F)

theorem exists_point_of_finrank_fixSp_three {E : Subgroup (Sp4 F)}
    (h : Module.finrank F (fixSp E) = 3) :
    ∃ p : Submodule F (V4 F), IsPoint p ∧ fixSp E = perp p ∧ E ≤ xPoint p := by
  refine ⟨perp (fixSp E), ?_, (perp_perp _).symm, ?_⟩
  · have := finrank_perp (fixSp E)
    change Module.finrank F (perp (fixSp E)) = 1
    omega
  · change E ≤ fixer (perp (perp (fixSp E)))
    rw [perp_perp]
    exact le_fixer_iff.2 le_rfl

theorem eq_xPoint_of_finrank_fixSp_three [Finite F] {E : Subgroup (Sp4 F)}
    (h : Module.finrank F (fixSp E) = 3) (hcard : Nat.card F ≤ Nat.card E) :
    ∃ p : Submodule F (V4 F), IsPoint p ∧ E = xPoint p := by
  obtain ⟨p, hp, -, hE⟩ := exists_point_of_finrank_fixSp_three h
  refine ⟨p, hp, Subgroup.eq_of_le_of_card_ge hE ?_⟩
  rw [card_xPoint hp]
  exact hcard

variable [Finite F] [CharP F 2]

theorem isLine_fixSp_of_finrank_two {E : Subgroup (Sp4 F)} (hE : IsPGroup 2 E)
    (h : Module.finrank F (fixSp E) = 2) : IsLine (fixSp E) ∧ E ≤ qLine (fixSp E) := by
  refine ⟨⟨h, ?_⟩, le_fixer_iff.2 le_rfl⟩
  have hp0 : perp (fixSp E) ≠ ⊥ := fun h0 => by
    have := finrank_perp (fixSp E)
    rw [h0, finrank_bot] at this
    omega
  obtain ⟨x, hx, hx0, hxfix⟩ := exists_fixed_ne_zero hE hp0 fun e he w hw =>
    mulVec_mem_of_mem_stab (stab_le_stab_perp _ (fixer_le_stab _ (le_fixer_iff.2 le_rfl he))) hw
  exact isTotallyIsotropic_of_finrank_two h (mem_fixSp.2 hxfix) hx0 hx

theorem exists_line_of_two_le_finrank_fixSp {E : Subgroup (Sp4 F)} (hE : IsPGroup 2 E)
    (hE1 : E ≠ ⊥) (h : 2 ≤ Module.finrank F (fixSp E)) :
    ∃ l : Submodule F (V4 F), IsLine l ∧ l ≤ fixSp E ∧ E ≤ qLine l := by
  have h4 : Module.finrank F (fixSp E) ≤ 4 := by
    have := Submodule.finrank_le (fixSp E)
    simpa using this
  have hne4 : Module.finrank F (fixSp E) ≠ 4 := fun h' => by
    refine hE1 (fixSp_eq_top_iff.1 (Submodule.eq_top_of_finrank_eq ?_))
    rw [h']
    simp
  rcases (show Module.finrank F (fixSp E) = 2 ∨ Module.finrank F (fixSp E) = 3 by omega)
    with h2 | h3
  · obtain ⟨hl, hEl⟩ := isLine_fixSp_of_finrank_two hE h2
    exact ⟨_, hl, le_rfl, hEl⟩
  · obtain ⟨p, hp, hfix, -⟩ := exists_point_of_finrank_fixSp_three h3
    obtain ⟨l, hl, hpl⟩ := exists_isLine_ge hp
    have hlf : l ≤ fixSp E := by
      rw [hfix, ← hl.perp_eq]
      exact perp_antitone hpl
    exact ⟨l, hl, hlf, (le_fixer_iff.2 le_rfl).trans (fixer_antitone hlf)⟩

end CFSG.Quasithin.MS93.MSP
