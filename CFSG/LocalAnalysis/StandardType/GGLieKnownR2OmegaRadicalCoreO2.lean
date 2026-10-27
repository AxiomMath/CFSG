module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalCore
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalFlag

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open CFSG.Open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.PCoreSection
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.StandardType.ClassicalPosition
open scoped commutatorElement

private theorem o2_neg_eq_self {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 2] (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul K v, CharTwo.two_eq_zero, zero_smul]

private theorem o2_add_self_eq_zero {K : Type} [Field K] [CharP K 2] (a : K) :
    a + a = 0 := by
  rw [← two_mul, CharTwo.two_eq_zero, zero_mul]

private theorem o2_add_add_self {K : Type} [Field K] [CharP K 2] (a b : K) :
    a + (a + b) = b := by
  rw [← add_assoc, o2_add_self_eq_zero a, zero_add]

private theorem o2_add_add_self' {K : Type} [Field K] [CharP K 2] (a b : K) :
    a + (b + a) = b := by
  rw [add_comm b a, o2_add_add_self]

private theorem o2_eichler_ef_Pe {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    eichler Q P.e P'.f P.e = P.e := by
  rw [eichler_apply P.Q_e h.ef]
  simp only [P.polar_ee, h.ef, P'.Q_f, mul_zero, zero_smul, add_zero, sub_zero]

private theorem o2_eichler_ef_Pe' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    eichler Q P.e P'.f P'.e = P.e + P'.e := by
  rw [eichler_apply P.Q_e h.ef]
  rw [polar_comm Q P'.e P.e, h.ee, P'.polar_ef, P'.Q_f]
  simp only [mul_zero, mul_one, zero_smul, one_smul, add_zero]
  rw [sub_eq_add_neg, o2_neg_eq_self (K := K) P.e, add_comm]

private theorem o2_eichler_fe_Pe {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    eichler Q P'.e P.f P.e = P.e + P'.e := by
  rw [eichler_apply P'.Q_e (by rw [polar_comm]; exact h.fe)]
  rw [h.ee, P.polar_ef, P.Q_f]
  simp only [mul_zero, mul_one, zero_smul, one_smul, add_zero]
  rw [sub_eq_add_neg, o2_neg_eq_self (K := K) P'.e]

private theorem o2_eichler_fe_Pe' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    eichler Q P'.e P.f P'.e = P'.e := by
  rw [eichler_apply P'.Q_e (by rw [polar_comm]; exact h.fe)]
  rw [polar_comm Q P'.e P.f, h.fe, P'.polar_ee, P.Q_f]
  simp only [mul_zero, zero_smul, add_zero, sub_zero]

private theorem o2_eichler_ef_apply {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] (γ δ : K) :
    eichler Q P.e P'.f (γ • P.e + δ • P'.e) = (γ + δ) • P.e + δ • P'.e := by
  rw [map_add, map_smul, map_smul, o2_eichler_ef_Pe h, o2_eichler_ef_Pe' h]
  module

private theorem o2_eichler_fe_apply {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] (γ δ : K) :
    eichler Q P'.e P.f (γ • P.e + δ • P'.e) = γ • P.e + (γ + δ) • P'.e := by
  rw [map_add, map_smul, map_smul, o2_eichler_fe_Pe h, o2_eichler_fe_Pe' h]
  module

private theorem o2_eichler_ef_maps_siegelY {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] {v : V}
    (hv : v ∈ siegelY K P.e P'.e) : eichler Q P.e P'.f v ∈ siegelY K P.e P'.e := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [o2_eichler_ef_Pe h]
        exact Submodule.subset_span (by simp)
      · rw [o2_eichler_ef_Pe' h]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

private theorem o2_eichler_fe_maps_siegelY {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] {v : V}
    (hv : v ∈ siegelY K P.e P'.e) : eichler Q P'.e P.f v ∈ siegelY K P.e P'.e := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [o2_eichler_fe_Pe h]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
      · rw [o2_eichler_fe_Pe' h]
        exact Submodule.subset_span (by simp)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

private theorem o2_mem_siegelY_sup_siegelW {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {v : V}
    (hv : polar Q P.e v = 0 ∧ polar Q P'.e v = 0) :
    v ∈ siegelY K P.e P'.e ⊔ siegelW Q P.e P'.e P.f P'.f := by
  have hw : v - polar Q v P.f • P.e - polar Q v P'.f • P'.e ∈
      siegelW Q P.e P'.e P.f P'.f := by
    rw [siegelW, LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [polarBilin_apply_apply]
    induction hx using Submodule.span_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
            hv.1, P.polar_ee, h.ee, mul_zero, mul_zero, sub_zero, sub_zero]
        · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
            hv.2, P'.polar_ee, polar_comm Q P'.e P.e, h.ee, mul_zero, mul_zero, sub_zero,
            sub_zero]
        · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
            P.polar_fe, mul_one, h.fe, mul_zero, sub_zero, polar_comm Q P.f v, sub_self]
        · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
            polar_comm Q P'.f P.e, h.ef, mul_zero, P'.polar_fe, mul_one, sub_zero,
            polar_comm Q P'.f v, sub_self]
    | zero => rw [polar_zero_left]
    | add x z _ _ hx hz => rw [polar_add_left, hx, hz, add_zero]
    | smul c x _ hx => rw [polar_smul_left_eq, hx, mul_zero]
  have hdecomp : v = (v - polar Q v P.f • P.e - polar Q v P'.f • P'.e) +
      (polar Q v P.f • P.e + polar Q v P'.f • P'.e) := by abel
  rw [hdecomp]
  exact Submodule.mem_sup.mpr ⟨polar Q v P.f • P.e + polar Q v P'.f • P'.e,
    Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))),
    v - polar Q v P.f • P.e - polar Q v P'.f • P'.e, hw, by abel⟩

theorem siegelO2_le_orthSiegelCore {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hS : SpinOmegaData Q) {P P' : HypPair Q} (h : P.Orth P')
    [CharP K 2] [Finite K] [FiniteDimensional K V]
    (hV : 6 ≤ Module.finrank K V)
    (hW : ∀ X : Submodule K V, X ≤ siegelW Q P.e P'.e P.f P'.f →
      (∀ g ∈ elementaryGroup Q, (∀ v ∈ Submodule.span K {P.e, P'.e, P.f, P'.f}, g v = v) →
        ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW Q P.e P'.e P.f P'.f) :
    pCoreOf 2 (Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q))) ≤
      orthSiegelCore Q P.e P'.e := by
  intro t ht
  haveI : Finite V := Module.finite_of_finite K
  let S : Subgroup (spinGroup Q) := Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q))
  let Y : Submodule K V := siegelY K P.e P'.e
  let Yperp : Submodule K V := LinearMap.BilinForm.orthogonal (polarBilin Q) Y
  have hact : IsLinearAction K (fun (g : spinGroup Q) (v : V) => spinAction Q g v) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      simp
    · intro g h v
      simp
    · intro g x y
      exact map_add (spinAction Q g) x y
    · intro g c x
      exact map_smul (spinAction Q g) c x
  have hspan_le : Submodule.span K {P.e, P'.e} ≤ Submodule.span K {P.e, P'.e, P.f, P'.f} :=
    Submodule.span_mono (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have hYperp_mem : ∀ {v : V}, v ∈ Yperp ↔ ∀ x ∈ Y, polar Q x v = 0 := by
    intro v
    dsimp only [Yperp, Y]
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor <;> intro h x hx
    · have := h x hx; rwa [polarBilin_apply_apply] at this
    · rw [polarBilin_apply_apply]; exact h x hx
  have hSY : ∀ s ∈ S, ∀ x ∈ Y, spinAction Q s x ∈ Y :=
    fun s hs x hx => normalizer_siegelRoot_le_stab hS h hs x hx
  have hSYperp : ∀ s ∈ S, ∀ x ∈ Yperp, spinAction Q s x ∈ Yperp := by
    intro s hs x hx
    rw [hYperp_mem] at hx ⊢
    intro y hy
    have hsy : spinAction Q s⁻¹ y ∈ Y := hSY s⁻¹ (S.inv_mem hs) y hy
    have hss : spinAction Q s (spinAction Q s⁻¹ y) = y := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      simp
    have key : polar Q y (spinAction Q s x) = polar Q (spinAction Q s⁻¹ y) x := by
      have h1 := polar_spinAction (Q := Q) s (spinAction Q s⁻¹ y) x
      rwa [hss] at h1
    rw [key]
    exact hx _ hsy
  have hYleYperp : Y ≤ Yperp := by
    intro y hy
    rw [hYperp_mem]
    intro x hx
    dsimp only [Y] at hx hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [polar_add_left, polar_smul_left, polar_add_right, polar_smul_right, P.polar_ee,
      P'.polar_ee, polar_comm Q P'.e P.e, h.ee]
    ring
  obtain ⟨s₁, hs₁⟩ : ∃ s : spinGroup Q, spinAction Q s = eichler Q P.e P'.f := by
    have hmem : eichler Q P.e P'.f ∈ (spinAction Q).range := by
      rw [hS.range_eq]
      exact eichler_mem_elementaryGroup Q _ _
    exact hmem
  have hs₁S : s₁ ∈ S := by
    apply stab_le_normalizer_siegelRoot h
    intro v hv
    rw [hs₁]
    exact o2_eichler_ef_maps_siegelY h hv
  obtain ⟨s₂, hs₂⟩ : ∃ s : spinGroup Q, spinAction Q s = eichler Q P'.e P.f := by
    have hmem : eichler Q P'.e P.f ∈ (spinAction Q).range := by
      rw [hS.range_eq]
      exact eichler_mem_elementaryGroup Q _ _
    exact hmem
  have hs₂S : s₂ ∈ S := by
    apply stab_le_normalizer_siegelRoot h
    intro v hv
    rw [hs₂]
    exact o2_eichler_fe_maps_siegelY h hv
  have hirrY : ∀ X : Submodule K V, ⊥ ≤ X → X ≤ Y →
      (∀ s ∈ S, ∀ x ∈ X, spinAction Q s x ∈ X) → X = ⊥ ∨ X = Y := by
    intro X _ hXY hXinv
    by_cases hbot : X = ⊥
    · exact Or.inl hbot
    · right
      refine le_antisymm hXY ?_
      obtain ⟨x, hxX, hxne⟩ : ∃ x ∈ X, x ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hbot ((Submodule.eq_bot_iff X).mpr hcon)
      have hxY : x ∈ Y := hXY hxX
      dsimp only [Y] at hxY
      obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hxY
      have hγδ : γ ≠ 0 ∨ δ ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hxne (by rw [hcon.1, hcon.2, zero_smul, zero_smul, add_zero])
      have hδPe : δ • P.e ∈ X := by
        have h1 : spinAction Q s₁ (γ • P.e + δ • P'.e) ∈ X := hXinv s₁ hs₁S _ hxX
        rw [hs₁, o2_eichler_ef_apply h γ δ] at h1
        have h2 : (γ • P.e + δ • P'.e) + ((γ + δ) • P.e + δ • P'.e) = δ • P.e := by
          rw [show (γ • P.e + δ • P'.e) + ((γ + δ) • P.e + δ • P'.e) =
              (γ • P.e + (γ + δ) • P.e) + (δ • P'.e + δ • P'.e) by abel]
          rw [← add_smul, ← add_smul, o2_add_add_self, o2_add_self_eq_zero, zero_smul,
            add_zero]
        rw [← h2]
        exact X.add_mem hxX h1
      have hγPe' : γ • P'.e ∈ X := by
        have h1 : spinAction Q s₂ (γ • P.e + δ • P'.e) ∈ X := hXinv s₂ hs₂S _ hxX
        rw [hs₂, o2_eichler_fe_apply h γ δ] at h1
        have h2 : (γ • P.e + δ • P'.e) + (γ • P.e + (γ + δ) • P'.e) = γ • P'.e := by
          rw [show (γ • P.e + δ • P'.e) + (γ • P.e + (γ + δ) • P'.e) =
              (γ • P.e + γ • P.e) + (δ • P'.e + (γ + δ) • P'.e) by abel]
          rw [← add_smul, ← add_smul, o2_add_self_eq_zero, zero_smul, zero_add,
            o2_add_add_self']
        rw [← h2]
        exact X.add_mem hxX h1
      obtain ⟨hPe, hPe'⟩ : P.e ∈ X ∧ P'.e ∈ X := by
        rcases hγδ with hγ | hδ
        · have hPe' : P'.e ∈ X := by
            have hh := X.smul_mem γ⁻¹ hγPe'
            rwa [smul_smul, inv_mul_cancel₀ hγ, one_smul] at hh
          have h1 : spinAction Q s₁ P'.e ∈ X := hXinv s₁ hs₁S _ hPe'
          rw [hs₁, o2_eichler_ef_Pe' h] at h1
          have h2 : P'.e + (P.e + P'.e) = P.e := by
            have hv2 : P'.e + P'.e = 0 := by rw [← two_smul K P'.e, CharTwo.two_eq_zero, zero_smul]
            rw [show P'.e + (P.e + P'.e) = (P'.e + P'.e) + P.e by abel, hv2, zero_add]
          exact ⟨by rw [← h2]; exact X.add_mem hPe' h1, hPe'⟩
        · have hPe : P.e ∈ X := by
            have hh := X.smul_mem δ⁻¹ hδPe
            rwa [smul_smul, inv_mul_cancel₀ hδ, one_smul] at hh
          have h1 : spinAction Q s₂ P.e ∈ X := hXinv s₂ hs₂S _ hPe
          rw [hs₂, o2_eichler_fe_Pe h] at h1
          have h2 : P.e + (P.e + P'.e) = P'.e := by
            have hv2 : P.e + P.e = 0 := by rw [← two_smul K P.e, CharTwo.two_eq_zero, zero_smul]
            rw [show P.e + (P.e + P'.e) = (P.e + P.e) + P'.e by abel, hv2, zero_add]
          exact ⟨hPe, by rw [← h2]; exact X.add_mem hPe h1⟩
      intro v hv
      dsimp only [Y] at hv
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
      exact X.add_mem (X.smul_mem a hPe) (X.smul_mem b hPe')
  have hYfix : ∀ t ∈ pCoreOf 2 S, ∀ x ∈ Y, spinAction Q t x = x := by
    intro t ht x hx
    have h := apply_sub_mem_of_isPGroup (K := K) (V := V) (G := spinGroup Q)
      (app := fun (g : spinGroup Q) (v : V) => spinAction Q g v) hact
      (S := S) (T := pCoreOf 2 S) (L := ⊥) (P := Y)
      (pCoreOf_le 2 S) (isPGroup_pCoreOf 2 S) (fun s hs t ht => conj_mem_pCoreOf hs ht) bot_le
      (fun s hs x hx => hSY s hs x hx) (fun s hs x hx => by simpa using hx) hirrY t ht x hx
    exact sub_eq_zero.mp (by simpa using h)
  have hirrYperp : ∀ X : Submodule K V, Y ≤ X → X ≤ Yperp →
      (∀ s ∈ S, ∀ x ∈ X, spinAction Q s x ∈ X) → X = Y ∨ X = Yperp := by
    intro X hYX hXYperp hXinv
    let XW : Submodule K V :=
      { carrier := {w : V | w ∈ siegelW Q P.e P'.e P.f P'.f ∧ ∃ y ∈ Y, y + w ∈ X}
        zero_mem' := ⟨(siegelW Q P.e P'.e P.f P'.f).zero_mem, 0, Y.zero_mem, by
          simpa using X.zero_mem⟩
        add_mem' := by
          rintro w₁ w₂ ⟨hw₁W, y₁, hy₁, hy₁X⟩ ⟨hw₂W, y₂, hy₂, hy₂X⟩
          refine ⟨(siegelW Q P.e P'.e P.f P'.f).add_mem hw₁W hw₂W, y₁ + y₂,
            Y.add_mem hy₁ hy₂, ?_⟩
          have h := X.add_mem hy₁X hy₂X
          convert h using 1 <;> abel
        smul_mem' := by
          rintro c w ⟨hwW, y, hy, hyX⟩
          refine ⟨(siegelW Q P.e P'.e P.f P'.f).smul_mem c hwW, c • y, Y.smul_mem c hy, ?_⟩
          have h := X.smul_mem c hyX
          rwa [smul_add] at h }
    have hXW_leW : XW ≤ siegelW Q P.e P'.e P.f P'.f := fun w hw => hw.1
    have hXW_inv : ∀ g ∈ elementaryGroup Q,
        (∀ v ∈ Submodule.span K {P.e, P'.e, P.f, P'.f}, g v = v) →
        ∀ x ∈ XW, g x ∈ XW := by
      intro g hgE hgfix x hxW
      obtain ⟨hxW, y, hyY, hyxX⟩ := hxW
      have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        elementaryGroup_le_orthogonalGroup Q hgE
      obtain ⟨s, hs⟩ : ∃ s : spinGroup Q, spinAction Q s = g := by
        have hmem : g ∈ (spinAction Q).range := by rwa [hS.range_eq]
        exact hmem
      have hsS : s ∈ S := by
        apply stab_le_normalizer_siegelRoot h
        intro v hv
        rw [hs]
        rw [hgfix v (hspan_le hv)]
        exact hv
      have hgxW : g x ∈ siegelW Q P.e P'.e P.f P'.f := by
        rw [siegelW, LinearMap.BilinForm.mem_orthogonal_iff]
        intro u hu
        rw [polarBilin_apply_apply]
        have hgu : g⁻¹ u = u := by
          have := hgfix u hu
          calc g⁻¹ u = g⁻¹ (g u) := by rw [this]
            _ = u := by rw [LinearEquiv.inv_apply_apply']
        rw [show u = g (g⁻¹ u) from (LinearEquiv.apply_inv_apply' g u).symm,
          polar_map_of_mem hgO, hgu]
        have hx0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hxW) u hu
        rwa [polarBilin_apply_apply] at hx0
      have hygxX : y + g x ∈ X := by
        have h1 : spinAction Q s (y + x) ∈ X := hXinv s hsS (y + x) hyxX
        rw [hs, map_add] at h1
        have hgy : g y = y := hgfix y (hspan_le hyY)
        rwa [hgy] at h1
      exact ⟨hgxW, y, hyY, hygxX⟩
    rcases hW XW hXW_leW hXW_inv with hbot | htop
    · left
      refine le_antisymm ?_ hYX
      intro v hv
      have hv' : v ∈ Yperp := hXYperp hv
      obtain ⟨hv1, hv2⟩ : polar Q P.e v = 0 ∧ polar Q P'.e v = 0 :=
        ⟨(hYperp_mem.mp hv') P.e (by exact Submodule.subset_span (by simp)),
         (hYperp_mem.mp hv') P'.e (by exact Submodule.subset_span (by simp))⟩
      have hv'' : v ∈ Y ⊔ siegelW Q P.e P'.e P.f P'.f :=
        o2_mem_siegelY_sup_siegelW h ⟨hv1, hv2⟩
      rw [Submodule.mem_sup] at hv''
      obtain ⟨y, hyY, w, hwW, hsum⟩ := hv''
      have hwXW : w ∈ XW := ⟨hwW, y, hyY, by rw [hsum]; exact hv⟩
      rw [hbot] at hwXW
      have hw0 : w = 0 := by simpa using hwXW
      rw [← hsum, hw0, add_zero]
      exact hyY
    · right
      refine le_antisymm hXYperp ?_
      intro v hv
      obtain ⟨hv1, hv2⟩ : polar Q P.e v = 0 ∧ polar Q P'.e v = 0 :=
        ⟨(hYperp_mem.mp hv) P.e (by exact Submodule.subset_span (by simp)),
         (hYperp_mem.mp hv) P'.e (by exact Submodule.subset_span (by simp))⟩
      have hv'' : v ∈ Y ⊔ siegelW Q P.e P'.e P.f P'.f :=
        o2_mem_siegelY_sup_siegelW h ⟨hv1, hv2⟩
      rw [Submodule.mem_sup] at hv''
      obtain ⟨y, hyY, w, hwW, hsum⟩ := hv''
      have hwX : w ∈ X := by
        have hwXW : w ∈ XW := by rw [htop]; exact hwW
        obtain ⟨_, y', hy'Y, hy'wX⟩ := hwXW
        have hy'X : y' ∈ X := hYX hy'Y
        have h := X.sub_mem hy'wX hy'X
        simpa using h
      rw [← hsum]
      exact X.add_mem (hYX hyY) hwX
  have hYmoves : ∀ t ∈ pCoreOf 2 S, ∀ x ∈ Yperp, spinAction Q t x - x ∈ Y :=
    apply_sub_mem_of_isPGroup (K := K) (V := V) (G := spinGroup Q)
      (app := fun (g : spinGroup Q) (v : V) => spinAction Q g v) hact
      (S := S) (T := pCoreOf 2 S) (L := Y) (P := Yperp)
      (pCoreOf_le 2 S) (isPGroup_pCoreOf 2 S) (fun s hs t ht => conj_mem_pCoreOf hs ht)
      hYleYperp (fun s hs x hx => hSYperp s hs x hx) (fun s hs x hx => hSY s hs x hx) hirrYperp
  change t ∈ orthSiegelCore Q P.e P'.e
  rw [orthSiegelCore, Subgroup.mem_comap]
  exact mem_axisRadical_of_flag hS.nondeg h hV (map_spinAction Q t)
    (fun v hv => hYfix t ht v hv)
    (fun v hv => hYmoves t ht v (by
      rw [hYperp_mem]
      intro x hx
      rw [polar_comm]
      exact hv x hx))

private theorem o2_linearIndependent_apply {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    LinearIndependent K ![P.e, P'.e] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (polar Q P.f) hst
  have h2 := congrArg (polar Q P'.f) hst
  simp only [polar_add_right, polar_smul_right_eq, P.polar_fe, h.fe, polar_comm Q P'.f P.e,
    h.ef, P'.polar_fe, polar_zero_right] at h1 h2
  exact ⟨by linear_combination h1, by linear_combination h2⟩

private theorem o2_orthSiegelLevi_fixed_on_siegelY {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] {x : V}
    (hx : x ∈ siegelY K P.e P'.e) (hfix : orthSiegelLevi Q P P' x = x) : x = 0 := by
  rw [siegelY] at hx
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  have hli : LinearIndependent K ![P.e, P'.e] := o2_linearIndependent_apply h
  have hxy : orthSiegelLevi Q P P' (α • P.e + β • P'.e) = α • P.e + β • P'.e := hfix
  rw [map_add, map_smul, map_smul, (orthSiegelLevi_apply_e h).1, (orthSiegelLevi_apply_e h).2]
    at hxy
  have h0 : (β - α) • P.e + α • P'.e = 0 := by
    have hsub : α • P'.e + β • (P.e + P'.e) - (α • P.e + β • P'.e) = 0 := sub_eq_zero.mpr hxy
    have heq : (β - α) • P.e + α • P'.e =
        α • P'.e + β • (P.e + P'.e) - (α • P.e + β • P'.e) := by module
    rw [heq, hsub]
  have hzero := (LinearIndependent.pair_iff.mp hli (β - α) α) h0
  obtain ⟨h1, h2⟩ := hzero
  rw [h2, sub_zero] at h1
  rw [h2, h1, zero_smul, zero_smul, add_zero]

theorem orthSiegelCore_centralizer_levi_le_siegelRoot {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (hS : SpinOmegaData Q) {P P' : HypPair Q} (h : P.Orth P')
    [CharP K 2] (hV : 6 ≤ Module.finrank K V) {h : spinGroup Q}
    (hh : spinAction Q h = orthSiegelLevi Q P P') {y : spinGroup Q}
    (hy : y ∈ orthSiegelCore Q P.e P'.e) (hcomm : h * y = y * h) :
    y ∈ siegelRoot Q P.e P'.e := by
  haveI : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  have hOrth : P.Orth P' := by assumption
  have hfixW : ∀ w ∈ siegelW Q P.e P'.e P.f P'.f, spinAction Q y w = w := by
    intro w hw
    have hφ : spinAction Q y w - w ∈ siegelY K P.e P'.e := by
      apply orthSiegelCore_sub_mem_Y hOrth hy w
      intro x hx
      have hx' : x ∈ Submodule.span K {P.e, P'.e, P.f, P'.f} :=
        Submodule.span_mono (by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
          tauto) hx
      have horth := (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) x hx'
      rw [polar_comm]
      rwa [polarBilin_apply_apply] at horth
    have hfix_phi : orthSiegelLevi Q P P' (spinAction Q y w - w) = spinAction Q y w - w := by
      have hcomm_action : spinAction Q h * spinAction Q y = spinAction Q y * spinAction Q h := by
        rw [← map_mul, ← map_mul, hcomm]
      have h1 : orthSiegelLevi Q P P' (spinAction Q y w) =
          spinAction Q y (orthSiegelLevi Q P P' w) := by
        have := congrArg (fun f : V ≃ₗ[K] V => f w) hcomm_action
        simpa only [LinearEquiv.mul_apply, hh] using this
      rw [orthSiegelLevi_fixes_W hOrth hw] at h1
      have hw_decomp : spinAction Q y w = w + (spinAction Q y w - w) := by abel
      rw [hw_decomp, map_add, orthSiegelLevi_fixes_W hOrth hw] at h1
      exact add_left_cancel h1
    have hphi_zero : spinAction Q y w - w = 0 :=
      o2_orthSiegelLevi_fixed_on_siegelY hOrth hφ hfix_phi
    exact sub_eq_zero.mp hphi_zero
  have hfixYperp : ∀ v, polar Q P.e v = 0 → polar Q P'.e v = 0 → spinAction Q y v = v := by
    intro v hv1 hv2
    obtain ⟨y1, hy1, w, hw, hsum⟩ :=
      Submodule.mem_sup.mp (o2_mem_siegelY_sup_siegelW hOrth ⟨hv1, hv2⟩)
    rw [← hsum, map_add, orthSiegelCore_fixes_Y hOrth hy y1 hy1, hfixW w hw]
  have hTy_elem : spinAction Q y ∈ elementaryGroup Q := by
    rw [← hS.range_eq]
    exact ⟨y, rfl⟩
  have hTyO : spinAction Q y ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hTy_elem
  have hcent : spinAction Q y ∈
      Subgroup.centralizer (axisRadical Q P.e P'.e : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨u, w, hu, hw1, hw2, rfl⟩ := hx
        have hTu : spinAction Q y u = u := orthSiegelCore_fixes_Y hOrth hy u hu
        have hTw : spinAction Q y w = w := hfixYperp w hw1 hw2
        have hconj := eichler_conj hTyO u w
        rw [hTu, hTw] at hconj
        have h2 : spinAction Q y * eichler Q u w = eichler Q u w * spinAction Q y := by
          have h3 : (spinAction Q y * eichler Q u w * (spinAction Q y)⁻¹) * spinAction Q y =
              eichler Q u w * spinAction Q y := congrArg (· * spinAction Q y) hconj
          rwa [mul_assoc, inv_mul_cancel, mul_one] at h3
        exact h2.symm
    | one => rw [one_mul, mul_one]
    | mul x z _ _ hx hz =>
        calc (x * z) * spinAction Q y = x * (z * spinAction Q y) := by rw [mul_assoc]
          _ = x * (spinAction Q y * z) := by rw [hz]
          _ = (x * spinAction Q y) * z := by rw [mul_assoc]
          _ = (spinAction Q y * x) * z := by rw [hx]
          _ = spinAction Q y * (x * z) := by rw [mul_assoc]
    | inv x _ hx =>
        have h := congrArg (fun z => x⁻¹ * z * x⁻¹) hx.symm
        simpa [mul_assoc] using h
  have hC : spinAction Q y ∈
      (Subgroup.centralizer (axisRadical Q P.e P'.e : Set (V ≃ₗ[K] V)) ⊓ elementaryGroup Q :
        Subgroup (V ≃ₗ[K] V)) := Subgroup.mem_inf.mpr ⟨hcent, hTy_elem⟩
  have hC' : spinAction Q y ∈
      (((Subgroup.centralizer (axisRadical Q P.e P'.e : Set (V ≃ₗ[K] V)) ⊓ elementaryGroup Q :
        Subgroup (V ≃ₗ[K] V))) : Set (V ≃ₗ[K] V)) := hC
  rw [centralizer_axisRadical_inf_eq hS.nondeg hOrth hV] at hC'
  obtain ⟨c, hc⟩ := hC'
  change spinAction Q y ∈ siegelGroup Q P.e P'.e
  rw [← hc]
  exact Subgroup.subset_closure ⟨c, rfl⟩

private theorem o2_orthSiegelLevi_maps_siegelY {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] {v : V}
    (hv : v ∈ siegelY K P.e P'.e) : orthSiegelLevi Q P P' v ∈ siegelY K P.e P'.e := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [(orthSiegelLevi_apply_e h).1]
        exact Submodule.subset_span (by simp)
      · rw [(orthSiegelLevi_apply_e h).2]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem exists_spin_lift_orthSiegelLevi {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hS : SpinOmegaData Q) {P P' : HypPair Q} (h : P.Orth P') [CharP K 2] :
    ∃ h : spinGroup Q, spinAction Q h = orthSiegelLevi Q P P' ∧ orderOf h = 3 ∧
      h ∈ Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q)) := by
  have hmem : orthSiegelLevi Q P P' ∈ (spinAction Q).range := by
    rw [hS.range_eq]
    exact orthSiegelLevi_mem_elementary h
  obtain ⟨g, hg⟩ := hmem
  have hinj : Function.Injective (spinAction Q) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hS.ker_eq_bot
  refine ⟨g, hg, ?_, ?_⟩
  · rw [← orderOf_injective (spinAction Q) hinj g, hg]
    exact orthSiegelLevi_orderOf h
  · refine stab_le_normalizer_siegelRoot h ?_
    intro v hv
    rw [hg]
    exact o2_orthSiegelLevi_maps_siegelY h hv

end CFSG.StandardType.LieKnownR2.POmega.Radical
