module

public import CFSG.LocalAnalysis.StandardType.GGWAutOrthOdd
import CFSG.LocalAnalysis.StandardType.GGWitOrthCrAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private lemma ggWAutN_det_omega (Q : QuadraticForm (ZMod 3) V) :
    ∀ ω ∈ ggOmega Q, LinearEquiv.det ω = 1 := by
  intro ω hω
  have hker : ggOmega Q ≤ (LinearEquiv.det : (V ≃ₗ[ZMod 3] V) →* (ZMod 3)ˣ).ker := by
    rw [ggOmega]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨g, h, hg, hh, rfl⟩ := hx
    exact MonoidHom.mem_ker.mpr (by
      apply Units.ext
      simp only [Units.val_mul, Units.val_one, map_mul, map_inv, Units.val_inv_eq_inv_val]
      have hg : ((LinearEquiv.det g : (ZMod 3)ˣ) : ZMod 3) ≠ 0 := (LinearEquiv.det g).ne_zero
      have hh : ((LinearEquiv.det h : (ZMod 3)ˣ) : ZMod 3) ≠ 0 := (LinearEquiv.det h).ne_zero
      field_simp)
  exact MonoidHom.mem_ker.mp (hker hω)

private lemma ggWAutN_det_refl [Module.Finite (ZMod 3) V] {t : V ≃ₗ[ZMod 3] V} (h : IsReflLin t) :
    LinearEquiv.det t = -1 := by
  obtain ⟨c, φ, hc, rfl⟩ := h
  exact Module.det_reflection hc

theorem ggWAut_orth_norm [Module.Finite (ZMod 3) V] (hn : 2 ≤ Module.finrank (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r}) (hO : GGOrthType R)
    (hneg : ∀ r ∈ R, ¬ ∀ v, r v = -v)
    {a : V ≃ₗ[ZMod 3] V} (ha : a ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V))) :
    ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  classical
  obtain ⟨Q, hQ, hRQ, hcomm⟩ := hO
  have hΩ : ggOmega Q ≤ R := by
    rw [ggOmega]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨g, h, hg, hh, rfl⟩ := hx
    exact hcomm g h hg hh
  have hR1 : R ≠ ⊥ := by
    intro hbot
    have : Nontrivial V := Module.finrank_pos_iff (R := ZMod 3) (M := V) |>.mp (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) ({v} : Set V)
    have hWfin : Module.finrank (ZMod 3) W = 1 := finrank_span_singleton hv
    have hWinv : ∀ b ∈ R, ∀ w ∈ W, b w ∈ W := by
      intro b hb w hw
      have hb1 : b = 1 := by
        have : b ∈ (⊥ : Subgroup (V ≃ₗ[ZMod 3] V)) := by rwa [← hbot]
        exact Subgroup.mem_bot.mp this
      rw [hb1]
      simpa using hw
    rcases habs.1 W hWinv with hW | hW
    · have hvW : v ∈ W := Submodule.subset_span (by simp)
      rw [hW] at hvW
      exact hv (by simpa using hvW)
    · have : Module.finrank (ZMod 3) V = 1 := by
        rw [← hWfin, hW, finrank_top]
      omega
  obtain ⟨s, hsR, hsrefl⟩ : ∃ s ∈ R, GGLinRefl s := by
    by_contra h
    have h' : ∀ r, r ∈ R → ¬ GGLinRefl r := fun r hr hr' => h ⟨r, hr, hr'⟩
    have hbot : R = ⊥ := by
      rw [hgen]
      have hset : {r : V ≃ₗ[ZMod 3] V | r ∈ R ∧ GGLinRefl r} = ∅ := by
        ext r
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        exact ⟨fun hh => h' r hh.1 hh.2, fun hf => hf.elim⟩
      rw [hset, Subgroup.closure_empty]
    exact hR1 hbot
  have hsRefl : IsReflLin s := (ggLinRefl_iff_isReflLin s).mp hsrefl
  have hsisom : ZS.IsIsom 3 Q s := hRQ s hsR
  set Q' : QuadraticForm (ZMod 3) V := Q.comp (a : V →ₗ[ZMod 3] V) with hQ'def
  have hR' : ∀ g ∈ R, ZS.IsIsom 3 Q' g := by
    intro g hg v
    have hconj : a * g * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp ha g).mp hg
    have h1 : a (g v) = (a * g * a⁻¹) (a v) := by
      simp [mul_assoc]
    show Q (a (g v)) = Q (a v)
    rw [h1]
    exact hRQ _ hconj _
  set B : LinearMap.BilinForm (ZMod 3) V := QuadraticMap.polarBilin Q with hBdef
  have hB'form : ∀ x y : V, QuadraticMap.polarBilin Q' x y = B (a x) (a y) := by
    intro x y
    rw [hQ'def, QuadraticMap.polarBilin_comp, hBdef]
    rfl
  have hQ' : (QuadraticMap.polarBilin Q').Nondegenerate := by
    constructor
    · intro x hx
      have hx' : a x = 0 := hQ.1 (a x) (fun z => by
        have h := hx (a.symm z)
        rwa [hB'form x (a.symm z), LinearEquiv.apply_symm_apply] at h)
      exact a.injective (by simpa using hx')
    · intro y hy
      have hy' : a y = 0 := hQ.2 (a y) (fun z => by
        have h := hy (a.symm z)
        rwa [hB'form (a.symm z) y, LinearEquiv.apply_symm_apply] at h)
      exact a.injective (by simpa using hy')
  obtain ⟨c, hc0, hcQ⟩ := ggWAut_form_unique R habs Q Q' hQ hQ' hRQ hR'
  have hQa : ∀ v : V, Q (a v) = c * Q v := fun v => hcQ v
  have hc : c = 1 ∨ c = -1 :=
    (by decide : ∀ y : ZMod 3, y ≠ 0 → y = 1 ∨ y = -1) c hc0
  let m : V ≃ₗ[ZMod 3] V := LinearEquiv.neg (ZMod 3)
  have hm_apply : ∀ v, m v = -v := fun v => by simp [m]
  have hm_isom : ZS.IsIsom 3 Q m := fun v => by
    rw [hm_apply v]
    exact QuadraticMap.map_neg Q v
  have hm_notin : m ∉ R := fun hmR => hneg m hmR hm_apply
  obtain ⟨t₁, t₂, ⟨hrefl₁, hisom₁⟩, ⟨hrefl₂, hisom₂⟩, hdec⟩ :=
    ggWAut_orth_cosets Q hQ (by omega : 1 ≤ Module.finrank (ZMod 3) V)
  rcases hc with hc1 | hcneg
  ·
    have haIsom : ZS.IsIsom 3 Q a := fun v => by rw [hQa v, hc1, one_mul]
    have hdetOm : ∀ ω ∈ ggOmega Q, LinearEquiv.det ω = 1 := ggWAutN_det_omega Q
    have hdet₁ : LinearEquiv.det t₁ = -1 := ggWAutN_det_refl hrefl₁
    have hdet₂ : LinearEquiv.det t₂ = -1 := ggWAutN_det_refl hrefl₂
    have hdet_s : LinearEquiv.det s = -1 := ggWAutN_det_refl hsRefl
    have hone : (1 : (ZMod 3)ˣ) ≠ -1 := by decide
    have hnegmul : (-1 : (ZMod 3)ˣ) * (-1) = 1 := by
      apply Units.ext
      simp
    have finish : ∀ t : V ≃ₗ[ZMod 3] V,
        (∀ g, ZS.IsIsom 3 Q g → g ∈ R ∨ ∃ r ∈ R, g = r * t) →
        ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
      intro t hcover
      rcases hcover m hm_isom with hmR | ⟨r₀, hr₀R, hr₀⟩
      · exact absurd hmR hm_notin
      · have ht_eq : t = r₀⁻¹ * m := by rw [hr₀]; group
        rcases hcover a haIsom with haR | ⟨r, hrR, hr⟩
        · exact ⟨a, haR, Or.inl fun v => rfl⟩
        · refine ⟨r * r₀⁻¹, R.mul_mem hrR (R.inv_mem hr₀R), Or.inr fun v => ?_⟩
          have haeq : a = (r * r₀⁻¹) * m := by rw [hr, ht_eq]; group
          calc a v = (r * r₀⁻¹) (m v) := by rw [haeq, LinearEquiv.mul_apply]
            _ = (r * r₀⁻¹) (-v) := by rw [hm_apply]
            _ = -((r * r₀⁻¹) v) := map_neg _ v
    have hs_class : t₁ ∈ R ∨ t₂ ∈ R := by
      obtain ⟨ω, hω, h'⟩ := hdec s hsisom
      have hωdet : LinearEquiv.det ω = 1 := hdetOm ω hω
      have hωR : ω ∈ R := hΩ hω
      rcases h' with h | h | h | h
      · exfalso
        rw [h, hωdet] at hdet_s
        exact hone hdet_s
      · left
        have h1 : t₁ = ω⁻¹ * s := by rw [h]; group
        rw [h1]
        exact R.mul_mem (R.inv_mem hωR) hsR
      · right
        have h1 : t₂ = ω⁻¹ * s := by rw [h]; group
        rw [h1]
        exact R.mul_mem (R.inv_mem hωR) hsR
      · exfalso
        have hdet : LinearEquiv.det (ω * (t₁ * t₂)) = 1 := by
          rw [map_mul, map_mul, hωdet, hdet₁, hdet₂]
          simp [hnegmul]
        rw [h, hdet] at hdet_s
        exact hone hdet_s
    rcases hs_class with ht1R | ht2R
    ·
      refine finish t₂ ?_
      intro g hg
      obtain ⟨ω, hω, h'⟩ := hdec g hg
      have hωR : ω ∈ R := hΩ hω
      rcases h' with h | h | h | h
      · exact Or.inl (by rw [h]; exact hωR)
      · exact Or.inl (by rw [h]; exact R.mul_mem hωR ht1R)
      · exact Or.inr ⟨ω, hωR, h⟩
      · exact Or.inr ⟨ω * t₁, R.mul_mem hωR ht1R, by rw [h]; group⟩
    ·
      refine finish t₁ ?_
      intro g hg
      obtain ⟨ω, hω, h'⟩ := hdec g hg
      have hωR : ω ∈ R := hΩ hω
      rcases h' with h | h | h | h
      · exact Or.inl (by rw [h]; exact hωR)
      · exact Or.inr ⟨ω, hωR, h⟩
      · exact Or.inl (by rw [h]; exact R.mul_mem hωR ht2R)
      · refine Or.inr ⟨ω * (t₁ * t₂ * t₁⁻¹ * t₂⁻¹) * t₂, ?_, ?_⟩
        · exact R.mul_mem (R.mul_mem hωR (hΩ (Subgroup.subset_closure
            ⟨t₁, t₂, hisom₁, hisom₂, rfl⟩))) ht2R
        · rw [h]; group
  ·
    exfalso
    have htwo : (2 : ZMod 3) ≠ 0 := by decide
    obtain ⟨u, hu, hsu⟩ := ZS.owCr_refl_form Q hQ htwo hsrefl.1 hsrefl.2 hsisom
    have hau : Q (a u) ≠ 0 := by
      rw [hQa u, hcneg]
      simpa using neg_ne_zero.mpr hu
    have hpolar : ∀ x y : V, QuadraticMap.polarBilin Q (a x) (a y) =
        c * QuadraticMap.polarBilin Q x y := by
      intro x y
      simp only [QuadraticMap.polarBilin_apply_apply]
      rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hQa (x + y), hQa x, hQa y]
      ring
    have hcoef : ∀ v : V, QuadraticMap.polarBilin Q (a.symm v) u / Q u =
        QuadraticMap.polarBilin Q v (a u) / Q (a u) := by
      intro v
      have h1 : QuadraticMap.polarBilin Q v (a u) =
          c * QuadraticMap.polarBilin Q (a.symm v) u := by
        rw [← hpolar (a.symm v) u, LinearEquiv.apply_symm_apply]
      rw [h1, hQa u, mul_div_mul_left _ _ hc0]
    have hconj : a * s * a⁻¹ = ZS.owCr_orthRefl Q (a u) hau := by
      refine LinearEquiv.ext fun v => ?_
      calc (a * s * a⁻¹) v = a (s (a.symm v)) := by
              simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
        _ = a (ZS.owCr_orthRefl Q u hu (a.symm v)) := by rw [hsu]
        _ = a (a.symm v - (QuadraticMap.polarBilin Q (a.symm v) u / Q u) • u) := by
              rw [ZS.owCr_orthRefl_apply]
        _ = v - (QuadraticMap.polarBilin Q (a.symm v) u / Q u) • (a u) := by
              rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]
        _ = v - (QuadraticMap.polarBilin Q v (a u) / Q (a u)) • (a u) := by rw [hcoef v]
        _ = ZS.owCr_orthRefl Q (a u) hau v := by rw [ZS.owCr_orthRefl_apply]
    have hsauR : a * s * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp ha s).mp hsR
    have hrefl_mem : ∀ t : V ≃ₗ[ZMod 3] V, IsReflLin t → ZS.IsIsom 3 Q t → t ∈ R := by
      intro t htRefl htIsom
      have htGG : GGLinRefl t := (ggLinRefl_iff_isReflLin t).mpr htRefl
      obtain ⟨v, hv, htv⟩ := ZS.owCr_refl_form Q hQ htwo htGG.1 htGG.2 htIsom
      have hkey : ∀ x y z : ZMod 3, x ≠ 0 → y ≠ 0 → z = -y → x = y ∨ x = z := by decide
      have hcases : Q v = Q u ∨ Q v = Q (a u) :=
        hkey (Q v) (Q u) (Q (a u)) hv hu (by rw [hQa u, hcneg]; ring)
      rcases hcases with hq | hq
      · obtain ⟨g, hgO, hgu⟩ :=
          CFSG.LocalAnalysis.ComponentInitial.exists_mem_orthogonalGroup_apply_eq htwo hq.symm hv
        have hgIsom : ZS.IsIsom 3 Q g := fun x =>
          CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO x
        have hguQ : Q (g u) ≠ 0 := by rw [hgIsom u]; exact hu
        have hcw : g * ZS.owCr_orthRefl Q u hu * g⁻¹ = ZS.owCr_orthRefl Q v hv := by
          have h1 := ZS.owCr_orthRefl_conj Q g hgIsom u hu hguQ
          simpa [hgu] using h1
        have hswR : ZS.owCr_orthRefl Q u hu ∈ R := by rw [← hsu]; exact hsR
        have hcommut : g * ZS.owCr_orthRefl Q u hu * g⁻¹ *
            (ZS.owCr_orthRefl Q u hu)⁻¹ ∈ R :=
          hcomm g _ hgIsom (ZS.owCr_orthRefl_isIsom Q u hu)
        have ht : t = (g * ZS.owCr_orthRefl Q u hu * g⁻¹ *
            (ZS.owCr_orthRefl Q u hu)⁻¹) * ZS.owCr_orthRefl Q u hu := by
          rw [htv, ← hcw]
          group
        rw [ht]
        exact R.mul_mem hcommut hswR
      · obtain ⟨g, hgO, hgau⟩ :=
          CFSG.LocalAnalysis.ComponentInitial.exists_mem_orthogonalGroup_apply_eq htwo hq.symm hv
        have hgIsom : ZS.IsIsom 3 Q g := fun x =>
          CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO x
        have hgauQ : Q (g (a u)) ≠ 0 := by rw [hgIsom (a u)]; exact hau
        have hcw : g * ZS.owCr_orthRefl Q (a u) hau * g⁻¹ = ZS.owCr_orthRefl Q v hv := by
          have h1 := ZS.owCr_orthRefl_conj Q g hgIsom (a u) hau hgauQ
          simpa [hgau] using h1
        have hswR : ZS.owCr_orthRefl Q (a u) hau ∈ R := by rw [← hconj]; exact hsauR
        have hcommut : g * ZS.owCr_orthRefl Q (a u) hau * g⁻¹ *
            (ZS.owCr_orthRefl Q (a u) hau)⁻¹ ∈ R :=
          hcomm g _ hgIsom (ZS.owCr_orthRefl_isIsom Q (a u) hau)
        have ht : t = (g * ZS.owCr_orthRefl Q (a u) hau * g⁻¹ *
            (ZS.owCr_orthRefl Q (a u) hau)⁻¹) * ZS.owCr_orthRefl Q (a u) hau := by
          rw [htv, ← hcw]
          group
        rw [ht]
        exact R.mul_mem hcommut hswR
    have ht1R : t₁ ∈ R := hrefl_mem t₁ hrefl₁ hisom₁
    have ht2R : t₂ ∈ R := hrefl_mem t₂ hrefl₂ hisom₂
    have hall : ∀ g : V ≃ₗ[ZMod 3] V, ZS.IsIsom 3 Q g → g ∈ R := by
      intro g hg
      obtain ⟨ω, hω, h'⟩ := hdec g hg
      have hωR : ω ∈ R := hΩ hω
      rcases h' with h | h | h | h
      · rw [h]; exact hωR
      · rw [h]; exact R.mul_mem hωR ht1R
      · rw [h]; exact R.mul_mem hωR ht2R
      · rw [h]; exact R.mul_mem hωR (R.mul_mem ht1R ht2R)
    exact hneg m (hall m hm_isom) hm_apply

end CFSG.StandardType

end
