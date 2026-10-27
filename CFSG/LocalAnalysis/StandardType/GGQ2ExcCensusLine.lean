module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusMain
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcLine
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcRefl

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open CFSG CFSG.Assembly Module

variable {m : Fin 6} {T : Chk.Tabs}

theorem censusCasesVx_of_scanLineN (hT : Chk.tabsOK m T = true) {X : Chk.CSearch} {vx : V m}
    (h : Chk.scanLineN T m true false X.S (Chk.bodyCC T m X) (code m vx) = true) :
    CensusCasesVx (excRaw m) vx := by
  intro hvx ℓ hℓ hocc hcent hout U hU hxU j hj hjocc hjcent _ _
  have hL : LineHyp m true false vx ℓ :=
    ⟨hvx, hℓ, fun h => absurd h (by decide), hocc, hcent, iff_of_false hout (by decide)⟩
  have hP : PlaneHyp m U j := ⟨hj, hjocc, hjcent⟩
  obtain ⟨cv, cy, hcv, hcy, rfl, hy, rfl, rfl, rfl, hbody⟩ := scanLineN_sound hT h hL hU hxU hP
  simp only [Chk.bodyCC, Bool.or_eq_true] at hbody
  rcases hbody with ((h1 | h2) | h3) | h4
  · simp only [labelOf_eq hT, twoNodeN_encL] at h1
    exact Or.inr (Or.inr (Or.inl h1))
  · cases hX : X.twoNode cv cy with
    | none => simp [hX] at h2
    | some t =>
      obtain ⟨a, b, rows, B, φ⟩ := t
      simp only [hX, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨⟨⟨-, hb⟩, hc⟩, ho⟩, htw⟩ := h2
      simp only [labelOf_eq hT, twoNodeN_encL] at htw
      refine Or.inr (Or.inl ⟨_, vec_combN_mem cv cy a b, ?_, _,
        candidate_of_candOK hT hcv hc hP (vec_combN_mem cv cy a b), outOK_sound hT ho, htw⟩)
      rw [vec_combN]
      exact comb_not_mem_span hy hb
  · cases hX : X.common cv cy with
    | none => simp [hX] at h3
    | some t =>
      obtain ⟨a, b, rows, B, W⟩ := t
      simp only [hX, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h3
      obtain ⟨⟨⟨-, hb⟩, hc⟩, hW⟩ := h3
      refine Or.inl ⟨_, vec_combN_mem cv cy a b, ?_, _,
        candidate_of_candOK hT hcv hc hP (vec_combN_mem cv cy a b),
        commonWitness_of_commonOK hT hW⟩
      rw [vec_combN]
      exact comb_not_mem_span hy hb
  · refine Or.inr (Or.inr (Or.inr fun z hz hzx k hk _ => ?_))
    obtain ⟨a, b, -, -, rfl, rfl, hab⟩ :=
      candScanN_sound hT h4 hcv hcy hz hzx (candHyp_of_candidate hk)
    simp only [Bool.or_eq_true] at hab
    rcases hab with htw | hamb
    · simp only [labelOf_eq hT, twoNodeN_encL] at htw
      exact Or.inl htw
    · right
      cases hX : X.amb cv (Chk.combN (dim m) cv cy a b) with
      | none => simp [hX] at hamb
      | some t =>
        obtain ⟨W, B, B'⟩ := t
        simp only [hX] at hamb
        exact ambientWitness_of_ambientOK hT hamb

theorem censusCasesVx_reflection (hT : Chk.tabsOK m T = true) (u : Root m) {vx : V m}
    (h : CensusCasesVx (excRaw m) vx) : CensusCasesVx (excRaw m) (reflection m u vx) :=
  (reflFrameAut hT u).censusCasesVx_map h

theorem inLCommonCasesVx_reflection (hT : Chk.tabsOK m T = true) (u : Root m) {vx : V m}
    (h : InLCommonCasesVx (excRaw m) vx) : InLCommonCasesVx (excRaw m) (reflection m u vx) :=
  (reflFrameAut hT u).inLCommonCasesVx_map h

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
