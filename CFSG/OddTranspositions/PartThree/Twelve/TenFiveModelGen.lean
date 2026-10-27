module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelWalk
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelBridge
public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import CFSG.Mathlib.QuadraticFormReflectionFix
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

set_option backward.isDefEq.respectTransparency false

private instance : Invertible (2 : ZMod 5) :=
  invertibleOfNonzero (show (2 : ZMod 5) ≠ 0 by decide)

theorem nondegenerate_restrict_span_singleton {k : ℕ} (ε : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : fiveForm k ε c c ≠ 0) :
    ((fiveQ k ε).restrict (Submodule.span (ZMod 5) {c})).Nondegenerate := by
  apply QuadraticMap.nondegenerate_polar_iff.mp
  apply CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict
  intro x hx hx0
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  have h := hx0 c (Submodule.subset_span (by simp))
  rw [fiveQ_polar, fiveForm_smul_left] at h
  have h' : a * fiveForm k ε c c = 0 := (mul_eq_zero.mp h).resolve_left (by decide)
  rcases mul_eq_zero.mp h' with ha | hB
  · rw [ha, zero_smul]
  · exact absurd hB hc

theorem nondegenerate_restrict_span_hypPair {k : ℕ} (ε : Bool)
    {c d : Fin (k + 1) → ZMod 5} (hcc : fiveForm k ε c c = 0) (hdd : fiveForm k ε d d = 0)
    (hcd : fiveForm k ε c d = 1) :
    ((fiveQ k ε).restrict (Submodule.span (ZMod 5) {c, d})).Nondegenerate := by
  apply QuadraticMap.nondegenerate_polar_iff.mp
  apply CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict
  intro x hx hx0
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨a, b, rfl⟩ := hx
  have hc : polar (fiveQ k ε) (a • c + b • d) c = 0 :=
    hx0 c (Submodule.subset_span (by simp))
  have hd : polar (fiveQ k ε) (a • c + b • d) d = 0 :=
    hx0 d (Submodule.subset_span (by simp))
  rw [fiveQ_polar, fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left,
    fiveForm_comm k ε d c, hcc, hcd, mul_zero, mul_one, zero_add] at hc
  rw [fiveQ_polar, fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left,
    hcd, hdd, mul_one, mul_zero, add_zero] at hd
  have hb : b = 0 := (mul_eq_zero.mp hc).resolve_left (by decide)
  have ha : a = 0 := (mul_eq_zero.mp hd).resolve_left (by decide)
  rw [ha, hb, zero_smul, zero_smul, add_zero]

theorem exists_fiveReflOf_list_prod_of_isometry_fix {k : ℕ} (hk : 4 ≤ k) (ε : Bool)
    (P : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5))
    (hP : ((fiveQ k ε).restrict P).Nondegenerate)
    {g : GL (Fin (k + 1)) (ZMod 5)}
    (hg : ∀ x y, fiveForm k ε (g *ᵥ x) (g *ᵥ y) = fiveForm k ε x y)
    (hfix : ∀ p ∈ P, g *ᵥ p = p) :
    ∃ l : List (Fin (k + 1) → ZMod 5),
      (∀ w ∈ l, w ∈ LinearMap.BilinForm.orthogonal (polarBilin (fiveQ k ε)) P ∧
        fiveForm k ε w w ≠ 0) ∧
      g = (l.map (fiveReflOf k ε)).prod := by
  classical
  have hQ : (fiveQ k ε).Nondegenerate := fiveQ_nondegenerate k ε
  let g' : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5) := fiveGLIso k g
  have hg' : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [show g' x = g *ᵥ x from fiveGLIso_apply k g x, fiveQ_apply, fiveQ_apply]
    exact hg x x
  have hfix' : ∀ p ∈ P, g' p = p := by
    intro p hp
    rw [show g' p = g *ᵥ p from fiveGLIso_apply k g p]
    exact hfix p hp
  obtain ⟨l, hl, hprod⟩ :=
    exists_list_reflect_of_fix (fiveQ k ε) hQ P hP g' hg' hfix'
  refine ⟨l, ?_, ?_⟩
  · intro w hw
    obtain ⟨hworth, hwQ⟩ := hl w hw
    refine ⟨hworth, ?_⟩
    rwa [fiveQ_apply] at hwQ
  · have hmap : ∀ w, (fiveGLIso k).symm
        (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) w) = fiveReflOf k ε w := by
      intro w
      apply (fiveGLIso k).injective
      rw [MulEquiv.apply_symm_apply, fiveGLIso_fiveReflOf]
      rfl
    calc g = (fiveGLIso k).symm g' := by
          rw [show g' = fiveGLIso k g from rfl, MulEquiv.symm_apply_apply]
      _ = (fiveGLIso k).symm
            ((l.map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε))).prod) := by rw [hprod]
      _ = ((l.map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε))).map
            (fiveGLIso k).symm).prod := by rw [map_list_prod]
      _ = (l.map (fun w => (fiveGLIso k).symm
            (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) w))).prod := by
            rw [List.map_map]; rfl
      _ = (l.map (fiveReflOf k ε)).prod := by
            congr 1
            exact List.map_congr_left (fun w _ => hmap w)

theorem reflect_sub_apply_eq_of_map_eq_fiveQ {k : ℕ} (ε : Bool)
    {x y : Fin (k + 1) → ZMod 5} (hxy : (fiveQ k ε) x = (fiveQ k ε) y)
    (h : fiveForm k ε (x - y) (x - y) ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) (x - y) x = y := by
  letI : Invertible ((fiveQ k ε) (x - y)) := invertibleOfNonzero (by rw [fiveQ_apply]; exact h)
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
  exact TauCeti.QuadraticMap.reflection_sub_apply_eq_of_map_eq (fiveQ k ε) x y hxy

theorem eq_of_mem_span_pair_of_map_eq {k : ℕ}
    {f : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5)}
    {c d : Fin (k + 1) → ZMod 5} (hc : f c = c) (hd : f d = d)
    {p : Fin (k + 1) → ZMod 5} (hp : p ∈ Submodule.span (ZMod 5) {c, d}) : f p = p := by
  rw [Submodule.mem_span_pair] at hp
  obtain ⟨a, b, rfl⟩ := hp
  rw [map_add, map_smul, map_smul, hc, hd]

theorem inv_prod_map_reflect_fiveQ {k : ℕ} (ε : Bool) (l : List (Fin (k + 1) → ZMod 5)) :
    ((l.map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε))).prod)⁻¹ =
      ((l.reverse).map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε))).prod := by
  induction l with
  | nil => simp
  | cons w l ih =>
    rw [List.map_cons, List.prod_cons, _root_.mul_inv_rev, ih,
      CFSG.ClassicalGroups.Orthogonal.reflect_inv, List.reverse_cons, List.map_append,
      List.prod_append, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]

set_option maxHeartbeats 400000 in
theorem exists_list_reflect_fiveQ_of_mulVec_eq {k : ℕ} (hk : 4 ≤ k) (ε : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0)
    {g : GL (Fin (k + 1)) (ZMod 5)}
    (hg : ∀ x y, fiveForm k ε (g *ᵥ x) (g *ᵥ y) = fiveForm k ε x y)
    (hfix : g *ᵥ c = c) :
    ∃ l : List (Fin (k + 1) → ZMod 5),
      (∀ w ∈ l, fiveForm k ε w c = 0 ∧ fiveForm k ε w w ≠ 0) ∧
      fiveGLIso k g = (l.map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε))).prod := by
  classical
  let g' : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5) := fiveGLIso k g
  have hg' : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [show g' x = g *ᵥ x from fiveGLIso_apply k g x, fiveQ_apply, fiveQ_apply]
    exact hg x x
  have hfix' : g' c = c := by
    rw [show g' c = g *ᵥ c from fiveGLIso_apply k g c]; exact hfix
  by_cases hQc : fiveForm k ε c c = 0
  ·
    have hQc' : fiveQ k ε c = 0 := by rw [fiveQ_apply]; exact hQc
    have hBnd : (polarBilin (fiveQ k ε)).Nondegenerate :=
      (QuadraticMap.nondegenerate_polar_iff).mpr (fiveQ_nondegenerate k ε)
    obtain ⟨P, hPe⟩ := CFSG.ClassicalGroups.Orthogonal.exists_hypPair hBnd hQc' hc
    set d : Fin (k + 1) → ZMod 5 := (2 : ZMod 5) • P.f with hddef
    have hQd : fiveQ k ε d = 0 := by
      rw [hddef, fiveQ_apply, fiveForm_smul_left, fiveForm_smul_right]
      have h := P.Q_f
      rw [show fiveQ k ε P.f = fiveForm k ε P.f P.f from fiveQ_apply k ε P.f] at h
      rw [h]; ring
    have hdd : fiveForm k ε d d = 0 := by rw [← fiveQ_apply]; exact hQd
    have hcd : fiveForm k ε c d = 1 := by
      have hp : polar (fiveQ k ε) c P.f = 1 := by rw [← hPe]; exact P.polar_ef
      have h2 : polar (fiveQ k ε) c d = 2 := by
        rw [hddef, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hp, mul_one]
      rw [fiveQ_polar] at h2
      exact mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0) (by rw [h2, mul_one])
    set u : Fin (k + 1) → ZMod 5 := g *ᵥ d - d with hudef
    have hg'd : g' d = g *ᵥ d := fiveGLIso_apply k g d
    have hQgd : fiveQ k ε (g *ᵥ d) = 0 := by
      rw [← hg'd, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg' d, hQd]
    have hgdc : fiveForm k ε (g *ᵥ d) c = 1 := by
      have h := hg d c
      rw [hfix, fiveForm_comm k ε d c, hcd] at h
      exact h
    have huc : fiveForm k ε u c = 0 := by
      rw [hudef, fiveForm_sub_left, hgdc, fiveForm_comm k ε d c, hcd, sub_self]
    have assemble : ∀ lh : List (Fin (k + 1) → ZMod 5),
        (∀ w ∈ lh, fiveForm k ε w c = 0 ∧ fiveForm k ε w w ≠ 0) →
        (∀ p ∈ Submodule.span (ZMod 5) {c, d},
          ((lh.map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε))).prod * g') p = p) →
        ∃ l : List (Fin (k + 1) → ZMod 5),
          (∀ w ∈ l, fiveForm k ε w c = 0 ∧ fiveForm k ε w w ≠ 0) ∧
          g' = (l.map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε))).prod := by
      intro lh hlh hfixp
      set g'' : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5) :=
        (lh.map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε))).prod * g' with hg''
      have hg''O : g'' ∈ TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε) := by
        rw [hg'']
        refine Subgroup.mul_mem _ ?_ hg'
        apply Subgroup.list_prod_mem
        intro r hr
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
        exact CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (fiveQ k ε) w
      have hfixp' : ∀ p ∈ Submodule.span (ZMod 5) {c, d}, g'' p = p := by
        intro p hp
        rw [hg'']
        exact hfixp p hp
      obtain ⟨l', hl', hprod'⟩ := exists_list_reflect_of_fix (fiveQ k ε) (fiveQ_nondegenerate k ε)
        (Submodule.span (ZMod 5) {c, d}) (nondegenerate_restrict_span_hypPair ε hQc hdd hcd)
        g'' hg''O hfixp'
      refine ⟨lh.reverse ++ l', ?_, ?_⟩
      · intro w hw
        rw [List.mem_append] at hw
        rcases hw with hw | hw
        · exact hlh w (List.mem_reverse.mp hw)
        · obtain ⟨hwo, hwQ⟩ := hl' w hw
          refine ⟨?_, by rwa [fiveQ_apply] at hwQ⟩
          have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hwo) c
            (Submodule.subset_span (by simp))
          rw [QuadraticMap.polarBilin_apply_apply, fiveQ_polar] at h
          have hbc : fiveForm k ε c w = 0 := (mul_eq_zero.mp h).resolve_left (by decide)
          rwa [fiveForm_comm]
      · have hg'inv : g' =
            ((lh.map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε))).prod)⁻¹ * g'' := by
          rw [hg'']; group
        rw [hg'inv, hprod', inv_prod_map_reflect_fiveQ, List.map_append, List.prod_append]
    by_cases hu : fiveQ k ε u = 0
    · by_cases hue : u = 0
      · refine assemble [] (by simp) ?_
        intro p hp
        rw [List.map_nil, List.prod_nil, one_mul]
        have hgd : g *ᵥ d = d := by
          have h := hue
          rw [hudef] at h
          exact sub_eq_zero.mp h
        exact eq_of_mem_span_pair_of_map_eq hfix' (by rw [hg'd, hgd]) hp
      ·
        have hQuadd : fiveForm k ε (c + d) (c + d) ≠ 0 := by
          rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right,
            fiveForm_comm k ε d c, hQc, hdd, hcd]
          decide
        obtain ⟨e, he_cd, he_cd', hee⟩ :=
          exists_fiveForm_orth_eq (k := k) (a := c + d) (d := 1) hk ε hQuadd (c - d)
            (by decide : (1 : ZMod 5) ≠ 0)
        have hec : fiveForm k ε e c = 0 := by
          have h1 : fiveForm k ε e c + fiveForm k ε e d = 0 := by
            simpa [fiveForm_add_right] using he_cd
          have h2 : fiveForm k ε e c - fiveForm k ε e d = 0 := by
            simpa [fiveForm_sub_right] using he_cd'
          have hb1 : fiveForm k ε e d = -fiveForm k ε e c := by
            rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
          have hb2 : fiveForm k ε e d = fiveForm k ε e c := (sub_eq_zero.mp h2).symm
          have ha : fiveForm k ε e c = -fiveForm k ε e c := hb2.symm.trans hb1
          have hsum : fiveForm k ε e c + fiveForm k ε e c = 0 := by
            nth_rewrite 1 [ha]; exact neg_add_cancel (fiveForm k ε e c)
          have h2a : (2 : ZMod 5) * fiveForm k ε e c = 0 := by rw [two_mul]; exact hsum
          exact (mul_eq_zero.mp h2a).resolve_left (by decide)
        have hed : fiveForm k ε e d = 0 := by
          have h1 : fiveForm k ε e c + fiveForm k ε e d = 0 := by
            simpa [fiveForm_add_right] using he_cd
          rw [hec, zero_add] at h1; exact h1
        have hchoose : ∃ e' : Fin (k + 1) → ZMod 5,
            fiveForm k ε e' c = 0 ∧ fiveForm k ε e' d = 0 ∧
            fiveForm k ε e' e' ≠ 0 ∧
            fiveForm k ε e' e' - 2 * fiveForm k ε u e' ≠ 0 := by
          by_cases hcond : fiveForm k ε e e - 2 * fiveForm k ε u e = 0
          · refine ⟨(2 : ZMod 5) • e, ?_, ?_, ?_, ?_⟩
            · rw [fiveForm_smul_left, hec, mul_zero]
            · rw [fiveForm_smul_left, hed, mul_zero]
            · rw [fiveForm_smul_left, fiveForm_smul_right, hee]; decide
            · rw [fiveForm_smul_left, fiveForm_smul_right, fiveForm_smul_right]
              have harith : ∀ x y : ZMod 5, x ≠ 0 → x - 2 * y = 0 →
                  2 * (2 * x) - 2 * (2 * y) ≠ 0 := by decide
              exact harith _ _ (by rw [hee]; decide) hcond
          · exact ⟨e, hec, hed, by rw [hee]; decide, hcond⟩
        obtain ⟨e', he'c, he'd, he'Q, he'u⟩ := hchoose
        let lam : ZMod 5 := -(fiveForm k ε e' e') / 2
        set dp : Fin (k + 1) → ZMod 5 := d + lam • c + e' with hdpdef
        have hBdc : fiveForm k ε d c = 1 := by rw [fiveForm_comm]; exact hcd
        have hBce : fiveForm k ε c e' = 0 := by rw [fiveForm_comm]; exact he'c
        have hBde : fiveForm k ε d e' = 0 := by rw [fiveForm_comm]; exact he'd
        have huu0 : fiveForm k ε u u = 0 := by rw [← fiveQ_apply]; exact hu
        have hsub : dp - d = lam • c + e' := by
          rw [hdpdef]; abel
        have hval : fiveForm k ε (lam • c + e') (lam • c + e') = fiveForm k ε e' e' := by
          simp only [fiveForm_add_left, fiveForm_add_right, fiveForm_smul_left,
            fiveForm_smul_right, hQc, he'c, hBce, mul_zero, zero_mul, add_zero, zero_add]
        have hdpd : fiveForm k ε (dp - d) (dp - d) ≠ 0 := by
          rw [hsub, hval]; exact he'Q
        have hdpQ : fiveQ k ε dp = 0 := by
          rw [hdpdef, fiveQ_apply]
          simp only [fiveForm_add_left, fiveForm_add_right, fiveForm_smul_left,
            fiveForm_smul_right, hQc, hdd, hcd, hBdc, he'c, he'd, hBce, hBde, mul_zero, zero_mul,
            add_zero, zero_add]
          have hlam : lam * (2 : ZMod 5) = -fiveForm k ε e' e' := by
            rw [show lam = -(fiveForm k ε e' e') / 2 from rfl]
            field_simp
          rw [show lam * 1 + lam * 1 = lam * 2 by ring, hlam]; ring
        have hsub2 : g *ᵥ d - dp = u - (lam • c + e') := by
          rw [hdpdef, hudef]
          abel
        have hgddp : fiveForm k ε (g *ᵥ d - dp) (g *ᵥ d - dp) ≠ 0 := by
          rw [hsub2]
          have hval2 : fiveForm k ε (u - (lam • c + e')) (u - (lam • c + e')) =
              fiveForm k ε e' e' - 2 * fiveForm k ε u e' := by
            simp only [fiveForm_sub_left, fiveForm_sub_right, fiveForm_add_left,
              fiveForm_add_right, fiveForm_smul_left, fiveForm_smul_right, hQc, huu0, huc,
              he'c, he'd, hBce, hBde, fiveForm_comm k ε c u, fiveForm_comm k ε e' u,
              mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub]
            ring
          rw [hval2]; exact he'u
        have hdpc : fiveForm k ε (dp - d) c = 0 := by
          rw [hsub, fiveForm_add_left, fiveForm_smul_left, he'c, hQc, mul_zero, add_zero]
        have hgddpc : fiveForm k ε (g *ᵥ d - dp) c = 0 := by
          rw [hsub2, fiveForm_sub_left, fiveForm_add_left, fiveForm_smul_left, he'c, huc, hQc,
            mul_zero, add_zero, sub_zero]
        have href_dp : CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) (dp - d) dp = d :=
          reflect_sub_apply_eq_of_map_eq_fiveQ ε
            (by rw [hdpQ, fiveQ_apply]; exact hdd.symm) hdpd
        have href_gd : CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) (g *ᵥ d - dp)
            (g *ᵥ d) = dp :=
          reflect_sub_apply_eq_of_map_eq_fiveQ ε (by rw [hQgd, hdpQ]) hgddp
        have hc_ref : ∀ x : Fin (k + 1) → ZMod 5, fiveForm k ε x c = 0 →
            CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) x c = c := by
          intro x hx
          apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
          rw [fiveQ_polar, hx, mul_zero]
        refine assemble [dp - d, g *ᵥ d - dp] ?_ ?_
        · intro w hw
          rw [List.mem_cons, List.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact ⟨hdpc, hdpd⟩
          · exact ⟨hgddpc, hgddp⟩
        · intro p hp
          rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_nil,
            List.prod_nil, mul_one]
          have hAc : CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) (dp - d) c = c := by
            apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
            rw [fiveQ_polar, hdpc, mul_zero]
          have hBc : CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) (g *ᵥ d - dp) c = c := by
            apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
            rw [fiveQ_polar, hgddpc, mul_zero]
          exact eq_of_mem_span_pair_of_map_eq (p := p)
            (by rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix', hBc, hAc])
            (by rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg'd, href_gd, href_dp])
            hp
    ·
      have hQu : fiveQ k ε u ≠ 0 := hu
      have huu : fiveForm k ε u u ≠ 0 := by rwa [← fiveQ_apply]
      have huc' : polar (fiveQ k ε) u c = 0 := by rw [fiveQ_polar, huc, mul_zero]
      have hgd_eq : fiveQ k ε (g *ᵥ d) = fiveQ k ε d := by
        rw [← hg'd, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg' d]
      have href_ud : CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) u (g *ᵥ d) = d := by
        have := reflect_sub_apply_eq_of_map_eq_fiveQ ε (x := g *ᵥ d) (y := d)
          (by rw [hgd_eq, hQd]) (by rw [show (g *ᵥ d) - d = u from rfl]; exact huu)
        rwa [show (g *ᵥ d) - d = u from rfl] at this
      refine assemble [u] ?_ ?_
      · intro w hw
        rw [List.mem_singleton] at hw; subst hw
        exact ⟨huc, huu⟩
      · intro p hp
        rw [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
        rw [Submodule.mem_span_pair] at hp
        obtain ⟨a, b, rfl⟩ := hp
        rw [LinearEquiv.mul_apply, map_add, map_smul, map_smul, hfix', hg'd]
        rw [map_add, map_smul, map_smul,
          CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (Q := fiveQ k ε) huc',
          href_ud]
  ·
    have hspan_fix : ∀ p ∈ Submodule.span (ZMod 5) {c}, g' p = p := by
      intro p hp
      rw [Submodule.mem_span_singleton] at hp
      obtain ⟨a, ha⟩ := hp
      rw [← ha, map_smul, hfix']
    obtain ⟨l, hl, hprod⟩ := exists_fiveReflOf_list_prod_of_isometry_fix hk ε
      (Submodule.span (ZMod 5) {c}) (nondegenerate_restrict_span_singleton ε hQc) hg hspan_fix
    refine ⟨l, ?_, ?_⟩
    · intro w hw
      obtain ⟨hwo, hwQ⟩ := hl w hw
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hwo) c (Submodule.subset_span (by simp))
      rw [QuadraticMap.polarBilin_apply_apply, fiveQ_polar] at h
      refine ⟨?_, hwQ⟩
      have hbc : fiveForm k ε c w = 0 := (mul_eq_zero.mp h).resolve_left (by decide)
      rwa [fiveForm_comm]
    · have hmap2 : ∀ w, fiveGLIso k (fiveReflOf k ε w) =
          CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε) w := by
        intro w; rw [fiveGLIso_fiveReflOf]; rfl
      rw [hprod, map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left (fun w _ => hmap2 w)

theorem exists_fiveReflOf_list_prod_of_mulVec_eq {k : ℕ} (hk : 4 ≤ k) (ε : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0)
    {g : GL (Fin (k + 1)) (ZMod 5)}
    (hg : ∀ x y, fiveForm k ε (g *ᵥ x) (g *ᵥ y) = fiveForm k ε x y)
    (hfix : g *ᵥ c = c) :
    ∃ l : List (Fin (k + 1) → ZMod 5),
      (∀ w ∈ l, fiveForm k ε w c = 0 ∧ fiveForm k ε w w ≠ 0) ∧
      g = (l.map (fiveReflOf k ε)).prod := by
  obtain ⟨l, hl, hprod⟩ := exists_list_reflect_fiveQ_of_mulVec_eq hk ε hc hg hfix
  refine ⟨l, hl, ?_⟩
  have hmap : (l.map (fiveReflOf k ε)).map (fiveGLIso k) =
      l.map (CFSG.ClassicalGroups.Orthogonal.reflect (fiveQ k ε)) := by
    rw [List.map_map]
    congr 1
    funext w
    rw [Function.comp_apply, fiveGLIso_fiveReflOf]
    rfl
  apply (fiveGLIso k).injective
  rw [map_list_prod, hmap, ← hprod]

end CFSG.OddTranspositions.PartThree
