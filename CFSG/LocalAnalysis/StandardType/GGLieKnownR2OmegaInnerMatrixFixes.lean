module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerMatrixFrameAux

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.LieKnownR2.POmega.Radical
open CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.PCoreSection
open QuadraticMap
open Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

private theorem imat_stabilizes_siegelY {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q)
    {P P' : HypPair Q} (h : P.Orth P')
    {y : MulAut ↥(spinGroup Q)} (htriv : GGTrivialOnNormalizer (siegelRoot Q P.e P'.e) y)
    {A' : (ι → F) ≃ₗ[F] (ι → F)}
    (hact : ∀ x : ↥(spinGroup Q), spinAction Q (y x) = A' * spinAction Q x * A'⁻¹) :
    ∀ x ∈ siegelY F P.e P'.e, A' x ∈ siegelY F P.e P'.e := by
  have hsub : siegelGroup Q P.e P'.e ≤ (spinAction Q).range := by
    rw [hS.range_eq, siegelGroup, Subgroup.closure_le]
    rintro g ⟨c, rfl⟩
    exact eichler_mem_elementaryGroup Q _ _
  have hgen : ∀ w ∈ ({w : ι → F | ∃ g ∈ siegelGroup Q P.e P'.e, ∃ v, g v - v = w} :
      Set (ι → F)), A' w ∈ Submodule.span F {w : ι → F |
        ∃ g ∈ siegelGroup Q P.e P'.e, ∃ v, g v - v = w} := by
    rintro w ⟨g, hg, v, rfl⟩
    obtain ⟨n, hn_eq⟩ : ∃ n : spinGroup Q, spinAction Q n = g := hsub hg
    have hn : n ∈ siegelRoot Q P.e P'.e := by
      show spinAction Q n ∈ siegelGroup Q P.e P'.e
      rw [hn_eq]; exact hg
    have hyn : y n ∈ siegelRoot Q P.e P'.e := by
      rw [← htriv.1]
      exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have hmem : A' * g * A'⁻¹ ∈ siegelGroup Q P.e P'.e := by
      have h1 : A' * g * A'⁻¹ = spinAction Q (y n) := by
        rw [← hn_eq]; exact (hact n).symm
      rw [h1]; exact hyn
    have hcomp : (A' * g * A'⁻¹) (A' v) = A' (g v) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      congr 1
      congr 1
      exact imat_symm_apply_apply A' v
    have heq : A' (g v - v) = (A' * g * A'⁻¹) (A' v) - A' v := by
      rw [map_sub, hcomp]
    rw [heq]
    exact Submodule.subset_span ⟨A' * g * A'⁻¹, hmem, A' v, rfl⟩
  have hmap : Submodule.map (A' : (ι → F) →ₗ[F] (ι → F))
      (Submodule.span F {w : ι → F | ∃ g ∈ siegelGroup Q P.e P'.e, ∃ v, g v - v = w}) ≤
      Submodule.span F {w : ι → F | ∃ g ∈ siegelGroup Q P.e P'.e, ∃ v, g v - v = w} := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    exact hgen
  intro x hx
  have hx' : x ∈ Submodule.span F {w : ι → F | ∃ g ∈ siegelGroup Q P.e P'.e,
      ∃ v, g v - v = w} := by
    rw [siegelMovedSpace_eq h]; exact hx
  have hx'' : A' x ∈ Submodule.map (A' : (ι → F) →ₗ[F] (ι → F))
      (Submodule.span F {w : ι → F | ∃ g ∈ siegelGroup Q P.e P'.e, ∃ v, g v - v = w}) :=
    Submodule.mem_map_of_mem hx'
  have hthis := hmap hx''
  rwa [siegelMovedSpace_eq h] at hthis

private theorem imat_fixes_siegelY {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q)
    {P P' : HypPair Q} (h : P.Orth P') (hV : 6 ≤ Module.finrank F (ι → F))
    (hW : GGSiegelWIrreducible Q P P')
    {y : MulAut ↥(spinGroup Q)} (htriv : GGTrivialOnNormalizer (siegelRoot Q P.e P'.e) y)
    (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1)
    {A' : (ι → F) ≃ₗ[F] (ι → F)} (hA' : ∀ v, Q (A' v) = Q v)
    (hact : ∀ x : ↥(spinGroup Q), spinAction Q (y x) = A' * spinAction Q x * A'⁻¹) :
    ∀ v ∈ siegelY F P.e P'.e, A' v = v := by
  obtain ⟨k, hkA'⟩ := imat_pow_two_eq_one (P := P) hS hV hy2 hA' hact
  have hstabY := imat_stabilizes_siegelY hS h htriv hact
  have hStabY : A' ∈ imat_stabilizer (siegelY F P.e P'.e) := hstabY
  have hT : IsPGroup 2 (Subgroup.zpowers A') := by
    obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hkA')
    exact IsPGroup.of_card (n := l) (by rw [Nat.card_zpowers, hl])
  have hlin : IsLinearAction F (fun (g : (ι → F) ≃ₗ[F] (ι → F)) (x : ι → F) => g x) :=
    ⟨fun x => rfl, fun g h x => rfl, fun g x y => map_add g x y, fun g c x => map_smul g c x⟩
  have hstabE1 : ∀ v ∈ siegelY F P.e P'.e, eichler Q P.e P'.f v ∈ siegelY F P.e P'.e := by
    intro v hv
    have hsubv := imat_tau1_sub h hv
    have : eichler Q P.e P'.f v = v - polar Q v P'.f • P.e := by rw [← hsubv]; abel
    rw [this]
    exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hstabE2 : ∀ v ∈ siegelY F P.e P'.e, eichler Q P'.e P.f v ∈ siegelY F P.e P'.e := by
    intro v hv
    have hsubv := imat_tau2_sub h hv
    have : eichler Q P'.e P.f v = v - polar Q v P.f • P'.e := by rw [← hsubv]; abel
    rw [this]
    exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨s1, hs1⟩ : ∃ s1 : spinGroup Q, spinAction Q s1 = eichler Q P.e P'.f := by
    change eichler Q P.e P'.f ∈ (spinAction Q).range
    rw [hS.range_eq]; exact eichler_mem_elementaryGroup Q P.e P'.f
  obtain ⟨s2, hs2⟩ : ∃ s2 : spinGroup Q, spinAction Q s2 = eichler Q P'.e P.f := by
    change eichler Q P'.e P.f ∈ (spinAction Q).range
    rw [hS.range_eq]; exact eichler_mem_elementaryGroup Q P'.e P.f
  have hs1N : s1 ∈ Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q)) :=
    stab_le_normalizer_siegelRoot h (by rw [hs1]; exact hstabE1)
  have hs2N : s2 ∈ Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q)) :=
    stab_le_normalizer_siegelRoot h (by rw [hs2]; exact hstabE2)
  have hcomm1 : ∀ x ∈ siegelY F P.e P'.e,
      A' (eichler Q P.e P'.f x) = eichler Q P.e P'.f (A' x) := by
    have hc := imat_commutes_on_Y hS h hV hW htriv hact hstabY hs1N
    intro x hx
    rw [← hs1]
    exact hc x hx
  have hcomm2 : ∀ x ∈ siegelY F P.e P'.e,
      A' (eichler Q P'.e P.f x) = eichler Q P'.e P.f (A' x) := by
    have hc := imat_commutes_on_Y hS h hV hW htriv hact hstabY hs2N
    intro x hx
    rw [← hs2]
    exact hc x hx
  have hYne : (⊥ : Submodule F (ι → F)) ≠ siegelY F P.e P'.e := by
    intro hbot
    have hmem : P.e ∈ (⊥ : Submodule F (ι → F)) := by
      rw [hbot]; exact Submodule.subset_span (by simp)
    exact P.e_ne_zero (imat_mem_bot_eq_zero hmem)
  obtain ⟨x0, hx0Y, hx00, hx0fix⟩ := exists_fixed_mem_of_isPGroup hlin hT (bot_le)
    (fun t ht => Subgroup.zpowers_le.mpr hStabY ht)
    (fun t ht x hx => by
      have hx0 : x = 0 := imat_mem_bot_eq_zero hx
      rw [Submodule.mem_bot, hx0, map_zero])
    hYne
  have hx0A' : A' x0 = x0 := by
    have h1 : (A' : (ι → F) →ₗ[F] (ι → F)) x0 - x0 ∈ (⊥ : Submodule F (ι → F)) :=
      hx0fix A' (Subgroup.mem_zpowers A')
    have h2 : (A' : (ι → F) →ₗ[F] (ι → F)) x0 - x0 = 0 := imat_mem_bot_eq_zero h1
    simpa only [LinearEquiv.coe_coe] using sub_eq_zero.mp h2
  let X : Submodule F (ι → F) :=
    LinearMap.ker ((A' : (ι → F) →ₗ[F] (ι → F)) - LinearMap.id) ⊓ siegelY F P.e P'.e
  have hXle : X ≤ siegelY F P.e P'.e := inf_le_right
  have hx0X : x0 ∈ X := by
    refine ⟨LinearMap.mem_ker.mpr ?_, hx0Y⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    simp only [LinearEquiv.coe_coe]
    rw [hx0A', sub_self]
  have hXne : X ≠ ⊥ := by
    intro hbot
    have : x0 ∈ (⊥ : Submodule F (ι → F)) := hbot ▸ hx0X
    exact hx00 (imat_mem_bot_eq_zero this)
  have hX1 : ∀ x ∈ X, eichler Q P.e P'.f x ∈ X := by
    intro x hx
    have hxA' : A' x = x := by
      have h2 := imat_mem_ker_eq_zero hx.1
      have h3 : (A' : (ι → F) →ₗ[F] (ι → F)) x - x = 0 := by
        rwa [LinearMap.sub_apply, LinearMap.id_apply] at h2
      simpa only [LinearEquiv.coe_coe] using sub_eq_zero.mp h3
    refine ⟨LinearMap.mem_ker.mpr ?_, hstabE1 x hx.2⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    simp only [LinearEquiv.coe_coe]
    rw [hcomm1 x hx.2, hxA', sub_self]
  have hX2 : ∀ x ∈ X, eichler Q P'.e P.f x ∈ X := by
    intro x hx
    have hxA' : A' x = x := by
      have h2 := imat_mem_ker_eq_zero hx.1
      have h3 : (A' : (ι → F) →ₗ[F] (ι → F)) x - x = 0 := by
        rwa [LinearMap.sub_apply, LinearMap.id_apply] at h2
      simpa only [LinearEquiv.coe_coe] using sub_eq_zero.mp h3
    refine ⟨LinearMap.mem_ker.mpr ?_, hstabE2 x hx.2⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    simp only [LinearEquiv.coe_coe]
    rw [hcomm2 x hx.2, hxA', sub_self]
  have hXY : X = siegelY F P.e P'.e := by
    rcases imat_submodule_eq_bot_or_siegelY h hXle hX1 hX2 with hbot | htop
    · exact absurd hbot hXne
    · exact htop
  intro y hy
  have hyX : y ∈ X := by rw [hXY]; exact hy
  have h2 := imat_mem_ker_eq_zero hyX.1
  have h3 : (A' : (ι → F) →ₗ[F] (ι → F)) y - y = 0 := by
    rwa [LinearMap.sub_apply, LinearMap.id_apply] at h2
  simpa only [LinearEquiv.coe_coe] using sub_eq_zero.mp h3

private theorem imat_moves_Yperp_into_siegelY {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q)
    {P P' : HypPair Q} (h : P.Orth P') (hV : 6 ≤ Module.finrank F (ι → F))
    (hW : GGSiegelWIrreducible Q P P')
    {y : MulAut ↥(spinGroup Q)} (htriv : GGTrivialOnNormalizer (siegelRoot Q P.e P'.e) y)
    (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1)
    {A' : (ι → F) ≃ₗ[F] (ι → F)} (hA' : ∀ v, Q (A' v) = Q v)
    (hact : ∀ x : ↥(spinGroup Q), spinAction Q (y x) = A' * spinAction Q x * A'⁻¹) :
    ∀ v, (∀ x ∈ siegelY F P.e P'.e, polar Q v x = 0) → A' v - v ∈ siegelY F P.e P'.e := by
  have hfixY := imat_fixes_siegelY hS h hV hW htriv hy2 hA' hact
  obtain ⟨k, hkA'⟩ := imat_pow_two_eq_one (P := P) hS hV hy2 hA' hact
  have hstabY := imat_stabilizes_siegelY hS h htriv hact
  have hStabY : A' ∈ imat_stabilizer (siegelY F P.e P'.e) := hstabY
  have hA'orth : A' ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hA'
  let f : (ι → F) →ₗ[F] (ι → F) := (A' : (ι → F) →ₗ[F] (ι → F)) - LinearMap.id
  have hf_apply : ∀ x : ι → F, f x = A' x - x := by
    intro x
    change (A' : (ι → F) →ₗ[F] (ι → F)) x - x = A' x - x
    rfl
  have hYle_span : siegelY F P.e P'.e ≤
      Submodule.span F ({P.e, P'.e, P.f, P'.f} : Set (ι → F)) := by
    rw [siegelY, Submodule.span_le]
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  have hmapY : Submodule.map (A' : (ι → F) →ₗ[F] (ι → F)) (siegelY F P.e P'.e) =
      siegelY F P.e P'.e := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      exact hstabY y hy
    · exact LinearEquiv.finrank_map_eq A' _
  have hinvY : ∀ y ∈ siegelY F P.e P'.e, A'⁻¹ y ∈ siegelY F P.e P'.e := by
    intro y hy
    have hy' : y ∈ Submodule.map (A' : (ι → F) →ₗ[F] (ι → F)) (siegelY F P.e P'.e) := by
      rw [hmapY]; exact hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy'
    have hzy' : A'⁻¹ y = z := by rw [← hzy]; simp
    rw [hzy']; exact hz
  have hStabYperp : A' ∈ imat_stabilizer
      (LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY F P.e P'.e)) := by
    intro x hx
    rw [mem_orth_iff] at hx ⊢
    intro y hy
    have h1 : polar Q y (A' x) = polar Q (A'⁻¹ y) x := by
      rw [← polar_map_of_mem hA'orth (A'⁻¹ y) x, imat_apply_symm_apply A' y]
    rw [h1]
    exact hx (A'⁻¹ y) (hinvY y hy)
  have hT : IsPGroup 2 (Subgroup.zpowers A') := by
    obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hkA')
    exact IsPGroup.of_card (n := l) (by rw [Nat.card_zpowers, hl])
  have hlin : IsLinearAction F (fun (g : (ι → F) ≃ₗ[F] (ι → F)) (x : ι → F) => g x) :=
    ⟨fun x => rfl, fun g h x => rfl, fun g x y => map_add g x y, fun g c x => map_smul g c x⟩
  have hYle : siegelY F P.e P'.e ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY F P.e P'.e) := by
    intro y hy
    rw [mem_orth_iff]
    intro z hz
    exact imat_polar_eq_zero_of_mem_siegelY h hz hy
  have hYperp_ne : siegelY F P.e P'.e ≠
      LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY F P.e P'.e) := by
    obtain ⟨m, hm, hQm, -⟩ := exists_nonsingular_of_finrank hS.nondeg
      (finrank_span_pair_le P.e P'.e) (by omega : 5 ≤ Module.finrank F (ι → F))
    have hmnotY : m ∉ siegelY F P.e P'.e := fun hmY => hQm (imat_Q_eq_zero_of_mem_siegelY h hmY)
    intro heq
    have hm' : m ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY F P.e P'.e) := hm
    rw [← heq] at hm'
    exact hmnotY hm'
  obtain ⟨x1, hx1P, hx1notL, hx1fix⟩ := exists_fixed_mem_of_isPGroup hlin hT hYle
    (fun t ht => Subgroup.zpowers_le.mpr hStabYperp ht)
    (fun t ht => Subgroup.zpowers_le.mpr hStabY ht) hYperp_ne
  let Yperp : Submodule F (ι → F) :=
    LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY F P.e P'.e)
  let X' : Submodule F (ι → F) := Submodule.comap f (siegelY F P.e P'.e) ⊓ Yperp
  have hx1X' : x1 ∈ X' := by
    refine ⟨Submodule.mem_comap.mpr ?_, hx1P⟩
    have h1 := hx1fix A' (Subgroup.mem_zpowers A')
    rw [hf_apply]
    simpa only [LinearEquiv.coe_coe] using h1
  have hX'ne : X' ≠ siegelY F P.e P'.e := by
    intro heq
    have : x1 ∈ siegelY F P.e P'.e := by rw [← heq]; exact hx1X'
    exact hx1notL this
  let π : (ι → F) →ₗ[F] (ι → F) := (imat_projLin P').comp (imat_projLin P)
  let Z : Submodule F (ι → F) := Submodule.map π X'
  have hZle : Z ≤ siegelW Q P.e P'.e P.f P'.f := by
    rintro z ⟨x, hx, rfl⟩
    exact imat_pi_mem_siegelW h x
  have hZinv : ∀ g ∈ elementaryGroup Q,
      (∀ v ∈ Submodule.span F {P.e, P'.e, P.f, P'.f}, g v = v) → ∀ z ∈ Z, g z ∈ Z := by
    rintro g hg hgfix z ⟨x, hxX', rfl⟩
    have hgorth : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      elementaryGroup_le_orthogonalGroup Q hg
    obtain ⟨s, hs⟩ : ∃ s : spinGroup Q, spinAction Q s = g := by
      change g ∈ (spinAction Q).range
      rw [hS.range_eq]; exact hg
    have hge : g P.e = P.e := hgfix P.e (Submodule.subset_span (by simp))
    have hgf : g P.f = P.f := hgfix P.f (Submodule.subset_span (by simp))
    have hge' : g P'.e = P'.e := hgfix P'.e (Submodule.subset_span (by simp))
    have hgf' : g P'.f = P'.f := hgfix P'.f (Submodule.subset_span (by simp))
    have hgp : ∀ x ∈ Yperp, g x ∈ Yperp := by
      intro x hx
      rw [mem_orth_iff] at hx ⊢
      intro y hy
      have h1 : polar Q y (g x) = polar Q (g⁻¹ y) x := by
        rw [← polar_map_of_mem hgorth (g⁻¹ y) x, imat_apply_symm_apply g y]
      rw [h1]
      have h2 : g⁻¹ y = y := by
        have hgy : g y = y := hgfix y (hYle_span hy)
        conv_lhs => rw [← hgy]
        exact imat_symm_apply_apply g y
      rw [h2]
      exact hx y hy
    have hsN : s ∈ Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q)) := by
      refine stab_le_normalizer_siegelRoot h ?_
      intro v hv
      rw [hs, hgfix v (hYle_span hv)]
      exact hv
    have hgxX' : g x ∈ X' := by
      refine ⟨Submodule.mem_comap.mpr ?_, hgp x hxX'.2⟩
      obtain ⟨q, hq, hc⟩ := imat_commutator_orthSiegelCore hS h hV hW htriv hact hsN
      have hc' : A' * g * A'⁻¹ * g⁻¹ = spinAction Q q := by simpa [hs] using hc
      have h1 : A' * g = spinAction Q q * g * A' := by
        calc A' * g = (A' * g * A'⁻¹ * g⁻¹) * (g * A') := by group
          _ = spinAction Q q * g * A' := by rw [hc']; group
      have hA'xperp : A' x ∈ Yperp := hStabYperp x hxX'.2
      have hgA'xperp : g (A' x) ∈ Yperp := hgp (A' x) hA'xperp
      have hgA'xperp' : ∀ u ∈ siegelY F P.e P'.e, polar Q (g (A' x)) u = 0 := by
        intro u hu
        rw [polar_comm]
        exact (mem_orth_iff.mp hgA'xperp) u hu
      have hqY : spinAction Q q (g (A' x)) - g (A' x) ∈ siegelY F P.e P'.e :=
        orthSiegelCore_sub_mem_Y h hq (g (A' x)) hgA'xperp'
      have hx1x : A' x - x ∈ siegelY F P.e P'.e := by
        have h := imat_mem_comap_apply hxX'.1
        rw [hf_apply] at h
        simpa only [LinearEquiv.coe_coe] using h
      have hgsub : g (A' x) - g x = A' x - x := by
        rw [← map_sub]
        exact hgfix (A' x - x) (hYle_span hx1x)
      have hAgx : A' (g x) = spinAction Q q (g (A' x)) := by
        rw [← LinearEquiv.mul_apply, h1, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      have hmem : A' (g x) - g x ∈ siegelY F P.e P'.e := by
        rw [hAgx]
        have h2 : spinAction Q q (g (A' x)) - g x =
            (spinAction Q q (g (A' x)) - g (A' x)) + (g (A' x) - g x) := by abel
        rw [h2, hgsub]
        exact Submodule.add_mem _ hqY hx1x
      rw [hf_apply]
      simpa only [LinearEquiv.coe_coe] using hmem
    refine ⟨g x, hgxX', ?_⟩
    exact imat_pi_equivariant hgorth hge hgf hge' hgf' x
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hπx1 : π x1 ≠ 0 := by
      intro h0
      have h0' : imat_projLin P' (imat_projLin P x1) = 0 := h0
      exact hx1notL (imat_pi_eq_zero_mem_siegelY h hx1P h0')
    have : π x1 ∈ (⊥ : Submodule F (ι → F)) :=
      hbot ▸ (Submodule.mem_map.mpr ⟨x1, hx1X', rfl⟩)
    exact hπx1 (imat_mem_bot_eq_zero this)
  have hZeq : Z = siegelW Q P.e P'.e P.f P'.f := by
    rcases hW Z hZle hZinv with h | h
    · exact absurd h hZne
    · exact h
  have hX'eq : X' = Yperp := by
    refine le_antisymm inf_le_right ?_
    intro v hv
    have hvZ : π v ∈ Z := by rw [hZeq]; exact imat_pi_mem_siegelW h v
    obtain ⟨x', hx'X', hx'eq⟩ := Submodule.mem_map.mp hvZ
    have hx'eq' : imat_projLin P' (imat_projLin P x') =
        imat_projLin P' (imat_projLin P v) := hx'eq
    have hvx' : v - x' ∈ Yperp := Submodule.sub_mem _ hv hx'X'.2
    have hmem : v - x' ∈ siegelY F P.e P'.e := by
      refine imat_pi_eq_zero_mem_siegelY h hvx' ?_
      rw [map_sub, map_sub, hx'eq', sub_self]
    have hfx' : f x' ∈ siegelY F P.e P'.e := imat_mem_comap_apply hx'X'.1
    have hfvdiff : f (v - x') = 0 := by
      rw [hf_apply, hfixY (v - x') hmem, sub_self]
    refine ⟨Submodule.mem_comap.mpr ?_, hv⟩
    have hvdecomp : v = x' + (v - x') := by abel
    rw [hvdecomp, map_add]
    exact Submodule.add_mem _ hfx' (by rw [hfvdiff]; exact Submodule.zero_mem _)
  intro v hv
  have hvv : v ∈ Yperp := by
    rw [mem_orth_iff]
    intro x hx
    rw [polar_comm]
    exact hv x hx
  have hvX' : v ∈ X' := by rw [hX'eq]; exact hvv
  have hmem := imat_mem_comap_apply hvX'.1
  rw [hf_apply] at hmem
  simpa only [LinearEquiv.coe_coe] using hmem

theorem isometry_fixes_siegelY_of_trivial {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q)
    {P P' : HypPair Q} (h : P.Orth P') (hV : 6 ≤ Module.finrank F (ι → F))
    (hW : GGSiegelWIrreducible Q P P')
    {y : MulAut ↥(spinGroup Q)}
    (htriv : GGTrivialOnNormalizer (siegelRoot Q P.e P'.e) y)
    (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1)
    {A' : (ι → F) ≃ₗ[F] (ι → F)} (hA' : ∀ v, Q (A' v) = Q v)
    (hact : ∀ x : ↥(spinGroup Q), spinAction Q (y x) = A' * spinAction Q x * A'⁻¹) :
    (∀ v ∈ siegelY F P.e P'.e, A' v = v) ∧
      (∀ v, (∀ x ∈ siegelY F P.e P'.e, polar Q v x = 0) →
A' v - v ∈ siegelY F P.e P'.e) := by
  exact ⟨imat_fixes_siegelY hS h hV hW htriv hy2 hA' hact,
    imat_moves_Yperp_into_siegelY hS h hV hW htriv hy2 hA' hact⟩

end CFSG.StandardType.LieKnownR2.POmega.Inner
