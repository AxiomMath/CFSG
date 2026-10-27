module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_cG_of_hc (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hc : ∀ T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      T ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
        normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
      (∀ g ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
        normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _),
          ∀ x ∈ T, g * x * g⁻¹ ∈ T) →
      (∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) →
      (∃ f ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
        normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _),
          ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
          f ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
            fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∧
          f ^ r ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
            fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) →
      T ≤ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    ∀ K : Subgroup G, K ≤ nBar D.M ⊥ V h.hyp151.isElemAbelian L →
      (∀ g ∈ nBar D.M ⊥ V h.hyp151.isElemAbelian L, ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
      (∀ k ∈ K, ∃ n : ℕ, k ^ 2 ^ n ∈
        centralizer ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G) :
          Subgroup G) : Set G)) →
      (∃ f ∈ nBar D.M ⊥ V h.hyp151.isElemAbelian L, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
        f ∉ centralizer ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G) :
          Subgroup G) : Set G) ∧
        f ^ r ∈ centralizer ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G) :
          Subgroup G) : Set G)) →
      K ≤ centralizer ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G) :
        Subgroup G) : Set G) := by
  intro K hK hKn hK2 hf
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  let Zt : Subgroup (Vtil ⊥ V hV) :=
    commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)
  have hZ : (wSub ⊥ V hV L ⊓ centralizer (L : Set G) : Subgroup G) =
      preTil ⊥ V hV Zt :=
    s16h_wSub_inf_centralizer_eq_preTil D h
  have key : ∀ {g : G} (hg : g ∈ D.M),
      g ∈ centralizer ((wSub ⊥ V hV L ⊓ centralizer (L : Set G) : Subgroup G) : Set G) ↔
        actTil ⊥ V hV ⟨g, hMs hg⟩ ∈ centSub Zt := by
    intro g hg
    rw [hZ]
    exact s16h_mem_centralizer_preTil_iff hV hMs Zt hg
  have hnBarM : nBar D.M ⊥ V hV L ≤ D.M := inf_le_left
  let T : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV K
  have hT_le : T ≤ Mbar D.M ⊥ V hV ⊓
      normalizer ((lBar ⊥ V hV L : Subgroup _) : Set _) := by
    intro φ hφ
    obtain ⟨g, hgK, rfl⟩ := (mem_barSub ⊥ V hV K φ).1 hφ
    obtain ⟨hgM, hgs, hgnorm⟩ := (mem_preBarSub D.M ⊥ V hV _).1 (hK hgK)
    exact ⟨actTil_mem_barSub ⊥ V hV hgM (hMs hgM), hgnorm⟩
  have hT_norm : ∀ g ∈ Mbar D.M ⊥ V hV ⊓
      normalizer ((lBar ⊥ V hV L : Subgroup _) : Set _),
      ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g₀ hg₀ x hx
    obtain ⟨g, hgM, hgeq⟩ := (mem_barSub ⊥ V hV D.M g₀).1 (Subgroup.mem_inf.1 hg₀).1
    obtain ⟨k, hkK, hkeq⟩ := (mem_barSub ⊥ V hV K x).1 hx
    have hgn : (g : G) ∈ nBar D.M ⊥ V hV L := by
      refine (mem_preBarSub D.M ⊥ V hV _).2 ⟨hgM, g.2, ?_⟩
      have hg₀n : actTil ⊥ V hV g ∈
          normalizer ((lBar ⊥ V hV L : Subgroup _) : Set _) := by
        rw [hgeq]
        exact (Subgroup.mem_inf.1 hg₀).2
      exact hg₀n
    rw [← hgeq, ← hkeq]
    have hmem : actTil ⊥ V hV (g * k * g⁻¹) ∈ barSub ⊥ V hV K :=
      actTil_mem_barSub ⊥ V hV (by
        show (g : G) * (k : G) * (g : G)⁻¹ ∈ K
        exact hKn (g : G) hgn (k : G) hkK) (g * k * g⁻¹).2
    rw [show actTil ⊥ V hV (g * k * g⁻¹) =
        actTil ⊥ V hV g * actTil ⊥ V hV k * (actTil ⊥ V hV g)⁻¹ from by
      rw [map_mul, map_mul, map_inv]] at hmem
    exact hmem
  have hT_pow : ∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n ∈ centSub Zt := by
    intro x hx
    obtain ⟨k, hkK, hkeq⟩ := (mem_barSub ⊥ V hV K x).1 hx
    obtain ⟨n, hn⟩ := hK2 (k : G) hkK
    refine ⟨n, ?_⟩
    have hkM : (k : G) ∈ D.M := hnBarM (hK hkK)
    have hkpow : (k : G) ^ 2 ^ n ∈ D.M := D.M.pow_mem hkM (2 ^ n)
    have hxpow : x ^ 2 ^ n = actTil ⊥ V hV ⟨(k : G) ^ 2 ^ n, hMs hkpow⟩ := by
      rw [← hkeq, ← map_pow]
      rfl
    rw [hxpow]
    exact (key hkpow).1 hn
  obtain ⟨f, hfn, r, hr, hfr_ne, hfne, hfr⟩ := hf
  have hfM : f ∈ D.M := hnBarM hfn
  obtain ⟨_, hfs, hfnorm⟩ := (mem_preBarSub D.M ⊥ V hV _).1 hfn
  have hfbar_mem : actTil ⊥ V hV ⟨f, hMs hfM⟩ ∈ Mbar D.M ⊥ V hV ⊓
      normalizer ((lBar ⊥ V hV L : Subgroup _) : Set _) :=
    ⟨actTil_mem_barSub ⊥ V hV hfM (hMs hfM), hfnorm⟩
  have hfbar_ne : actTil ⊥ V hV ⟨f, hMs hfM⟩ ∉ centSub Zt := by
    intro hfc
    exact hfne ((key hfM).2 hfc)
  have hfrM : f ^ r ∈ D.M := D.M.pow_mem hfM r
  have hfbar_r : (actTil ⊥ V hV ⟨f, hMs hfM⟩) ^ r ∈ centSub Zt := by
    have h1 : (actTil ⊥ V hV ⟨f, hMs hfM⟩) ^ r =
        actTil ⊥ V hV ⟨f ^ r, hMs hfrM⟩ := by
      rw [← map_pow]
      rfl
    rw [h1]
    exact (key hfrM).mp hfr
  have hTle : T ≤ centSub Zt :=
    hc T hT_le hT_norm hT_pow
      ⟨actTil ⊥ V hV ⟨f, hMs hfM⟩, hfbar_mem, r, hr, hfr_ne, hfbar_ne, hfbar_r⟩
  intro k hkK
  have hkM : k ∈ D.M := hnBarM (hK hkK)
  exact (key hkM).2 (hTle (actTil_mem_barSub ⊥ V hV hkK (hMs hkM)))

theorem s16h_v1Sub_ne_V (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hL : barSub ⊥ V h.hyp151.isElemAbelian L ≠ ⊥) :
    v1Sub D.M ⊥ V h.hyp151.isElemAbelian L ≠ V := by
  have hV := h.hyp151.isElemAbelian
  intro hV₁
  have himg : imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) = ⊤ := by
    rw [hV₁]
    exact s15_Infra_imgTil_top ⊥ V hV
  have hle := s15_Core_imgTil_v1Sub_le_fixV (D := D) (V₀ := ⊥) (V := V) (L := L)
    h.hyp151 (m := 1) D.M.one_mem
  rw [conjSubgroup_one] at hle
  have hfix : fixV (barSub ⊥ V hV L) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← himg]
    exact hle
  have hbot : barSub ⊥ V hV L = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).2
    intro φ hφ
    refine MulEquiv.ext fun q => ?_
    have hq : q ∈ fixV (barSub ⊥ V hV L) := by rw [hfix]; trivial
    simpa using (mem_fixV.1 hq) φ hφ
  exact hL hbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
