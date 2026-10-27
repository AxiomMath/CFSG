module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.C3AlgebraicPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2Finite
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3PinnedPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.B3Algebraic

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Symplectic CFSG.Open CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.StandardType.F4ExplicitPos.FiniteAction CFSG.StandardType.F4ExplicitPos.B3Pinned
  CFSG.StandardType.F4ExplicitPos.B3Exact CFSG.StandardType.F4ExplicitPos.B3Faithful
  CFSG.StandardType.F4ExplicitPos.B3Unconditional
  C3Range C3Algebraic B2Finite
  CFSG.Timmesfeld.LieEmbed

theorem short_fixes_of_bcGL_short_fixes
    {t : ReeTag} {E L : Type} [Field E] [Field L]
    (f : E →+* L) (g : ModGL t.tag E)
    (h : ∀ v ∈ t.shortModule L,
      ((bcGL (τ := t.tag) f g : ModGL t.tag L) : Module.End L (RootModule t.tag L)) v = v) :
    ∀ v ∈ t.shortModule E, (g : Module.End E (RootModule t.tag E)) v = v := by
  have hb : ∀ b : t.shortLabels,
      (g : Module.End E (RootModule t.tag E)) (t.shortBasis E b) = t.shortBasis E b := by
    intro b
    have h1 := h ((t.shortBasis L b : t.shortModule L) : RootModule t.tag L)
      (t.shortBasis L b).2
    rw [ReeTag.coe_shortBasis, bcGL_apply_single] at h1
    have h2 : (g : Module.End E (RootModule t.tag E)) (Finsupp.single b.1 1) =
        Finsupp.single b.1 1 := by
      refine Finsupp.mapRange_injective f f.map_zero (RingHom.injective f) ?_
      rw [h1, Finsupp.mapRange_single, map_one]
    rw [ReeTag.coe_shortBasis (t := t) (R := E) b]
    exact h2
  have hmap : (g : Module.End E (RootModule t.tag E)).comp (t.shortModule E).subtype =
      (t.shortModule E).subtype := by
    apply (t.shortBasis E).ext
    intro b
    exact hb b
  intro v hv
  exact congrArg (fun (φ : t.shortModule E →ₗ[E] RootModule t.tag E) => φ ⟨v, hv⟩) hmap

theorem rootSpanOver_eq_map_rootSpan_narrow
    {K : Type} [Field K] (F : Subfield K)
    (Ψ : Set (Fin (Tag.rank .F4) → ℤ)) :
    rootSpanOver K F Ψ = (rootSpan .F4 F Ψ).map (bcGL (τ := .F4) F.subtype) := by
  refine le_antisymm ?_ ?_
  · rw [rootSpanOver, Subgroup.closure_le]
    rintro x ⟨α, hα, c, rfl⟩
    exact Subgroup.mem_map.2 ⟨pinnedX .F4 F α c, by
      rw [rootSpan]
      exact Subgroup.mem_iSup_of_mem α
        (Subgroup.mem_iSup_of_mem hα (Subgroup.subset_closure ⟨c, rfl⟩)),
      bcGL_pinnedX F.subtype α c⟩
  · rw [rootSpanOver, Subgroup.map_le_iff_le_comap, rootSpan]
    refine iSup_le fun α => iSup_le fun hα => ?_
    rw [← Subgroup.map_le_iff_le_comap, rootSubgroup, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro x ⟨c, hc, rfl⟩
    obtain ⟨d, rfl⟩ := hc
    rw [bcGL_pinnedX]
    exact Subgroup.subset_closure ⟨α, hα, d, rfl⟩

theorem adjointGroup_le_rootSpan_isRoot
    (K : Type) [Field K] :
    adjointGroup .F4 K ≤ rootSpan .F4 K {α | IsRoot .F4 α} := by
  rw [CFSG.Blueprint.Chevalley.adjointGroup, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · have hgi : g = xUnit .F4 K i c := Units.ext (hg.trans (coe_xUnit i c).symm)
    rw [hgi, ← pinnedX_single (τ := .F4) (R := K) i c]
    exact CFSG.LieType.Chevalley.pinnedX_mem_rootSpan (isRoot_single .F4 i) c
  · have hgi : g = yUnit .F4 K i c := Units.ext (hg.trans (coe_yUnit i c).symm)
    rw [hgi, ← pinnedX_neg_single (τ := .F4) (R := K) i c]
    exact CFSG.LieType.Chevalley.pinnedX_mem_rootSpan
      (CFSG.LieType.Steinberg.TagRoots.isRoot_neg (isRoot_single .F4 i)) c

theorem exists_frobFixed_of_finset (Ω : Type) [Field Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    (S : Finset Ω) {k₀ : ℕ} (hk₀ : k₀ ≠ 0) :
    ∃ k, k ≠ 0 ∧ k₀ ∣ k ∧ ∀ x ∈ S, x ∈ TauCeti.frobeniusFixedSubfield Ω 2 k := by
  classical
  choose n hn hx using fun x : Ω => TauCeti.exists_mem_frobeniusFixedSubfield Ω 2 x
  refine ⟨k₀ * ∏ x ∈ S, n x, mul_ne_zero hk₀ (Finset.prod_ne_zero_iff.2 fun x _ => hn x),
    dvd_mul_right _ _, fun x hxS => ?_⟩
  exact TauCeti.frobeniusFixedSubfield_le_of_dvd
    (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem n hxS) _) (hx x)

theorem f4_exists_finite_subfield_preimage
    (Ω : Type) [Field Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    (g : adjointGroup .F4 Ω) :
    ∃ k, k ≠ 0 ∧ ∃ gE : adjointGroup .F4 (TauCeti.frobeniusFixedSubfield Ω 2 k),
      j (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype gE = g := by
  classical
  have hg : (g : ModGL .F4 Ω) ∈ rootSpan .F4 Ω {α | IsRoot .F4 α} :=
    adjointGroup_le_rootSpan_isRoot Ω g.2
  obtain ⟨T, hT⟩ := CFSG.StandardType.F4ExplicitPos.FiniteAction.exists_finset_coefficients Ω hg
  obtain ⟨k, hk, _hdiv, hmem⟩ := exists_frobFixed_of_finset Ω T (k₀ := 1) one_ne_zero
  have : Finite ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) :=
    TauCeti.finite_frobeniusFixedSubfield Ω 2 k hk
  have : CharP ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) 2 :=
    Subfield.charP (TauCeti.frobeniusFixedSubfield Ω 2 k) 2
  have hmemRoot : (g : ModGL .F4 Ω) ∈ CFSG.StandardType.F4ExplicitPos.FiniteAction.rootSpanOver Ω
      (TauCeti.frobeniusFixedSubfield Ω 2 k) {α | IsRoot .F4 α} := hT _ hmem
  rw [rootSpanOver_eq_map_rootSpan_narrow] at hmemRoot
  obtain ⟨gE, hgE, hgEeq⟩ := Subgroup.mem_map.mp hmemRoot
  refine ⟨k, hk, ⟨gE, (ReeTag.rootSpan_le_adjointGroup (t := ReeTag.F4)
    (S := {α : Fin F4.tag.rank → ℤ | IsRoot F4.tag α})) hgE⟩, ?_⟩
  refine Subtype.ext ?_
  rw [j_apply]
  exact hgEeq

theorem f4_shortFaithful_algebraic
    (Ω : Type) [Field Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω] :
    ReeTag.F4.ShortFaithful Ω := by
  have hmain : ∀ g ∈ adjointGroup .F4 Ω,
      (∀ v ∈ ReeTag.F4.shortModule Ω,
        (g : Module.End Ω (RootModule .F4 Ω)) v = v) → g = 1 := by
    intro g hg hfix
    obtain ⟨k, hk, gE, hgE⟩ := f4_exists_finite_subfield_preimage Ω ⟨g, hg⟩
    have : Finite ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) :=
      TauCeti.finite_frobeniusFixedSubfield Ω 2 k hk
    have : CharP ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) 2 :=
      Subfield.charP (TauCeti.frobeniusFixedSubfield Ω 2 k) 2
    have hbc : bcGL (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype
        (gE : ModGL .F4 (TauCeti.frobeniusFixedSubfield Ω 2 k)) = g := by
      have h1 := congrArg (fun x : adjointGroup .F4 Ω => (x : ModGL .F4 Ω)) hgE
      rwa [j_apply] at h1
    have hfixE : ∀ v ∈ ReeTag.F4.shortModule (TauCeti.frobeniusFixedSubfield Ω 2 k),
        ((gE : ModGL .F4 (TauCeti.frobeniusFixedSubfield Ω 2 k)) :
          Module.End (TauCeti.frobeniusFixedSubfield Ω 2 k)
            (RootModule .F4 (TauCeti.frobeniusFixedSubfield Ω 2 k))) v = v :=
      short_fixes_of_bcGL_short_fixes (t := ReeTag.F4)
        (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype
        (gE : ModGL .F4 (TauCeti.frobeniusFixedSubfield Ω 2 k))
        (fun v hv => by
          change ((bcGL (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype
            (gE : ModGL .F4 (TauCeti.frobeniusFixedSubfield Ω 2 k))) :
              Module.End Ω (RootModule .F4 Ω)) v = v
          rw [hbc]
          exact hfix v hv)
    have hmod : (gE : ModGL .F4 (TauCeti.frobeniusFixedSubfield Ω 2 k)) = 1 :=
      CFSG.StandardType.F4ExplicitPos.B3Faithful.f4_shortFaithful _
        (gE : ModGL .F4 (TauCeti.frobeniusFixedSubfield Ω 2 k)) gE.2 hfixE
    have hEq : (⟨g, hg⟩ : adjointGroup .F4 Ω) = 1 := by
      rw [← hgE]
      rw [show gE = 1 from Subtype.ext hmod, map_one]
    exact congrArg Subtype.val hEq
  intro g hg hfix
  exact hmain g hg hfix

section Algebraic

variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

abbrev sigmaΩ
    : adjointGroup F4.tag Ω →* adjointGroup F4.tag Ω :=
  CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exceptionalEndoNarrow (t := ReeTag.F4) Ω
    (B3Exact.Narrow.F4_prime_cast_eq_zero Ω) (f4_shortFaithful_algebraic Ω)

theorem j_xElement
    {E : Type} [Field E] [CharP E 2] (f : E →+* Ω)
    (i : Fin F4.tag.rank) (c : E) :
    j (τ := F4.tag) f (xElement i c) = xElement i (f c) := by
  refine Subtype.ext ?_
  rw [j_apply]
  change bcGL (τ := F4.tag) f (xUnit F4.tag E i c) = xUnit F4.tag Ω i (f c)
  rw [bcGL_xUnit]

theorem j_yElement
    {E : Type} [Field E] [CharP E 2] (f : E →+* Ω)
    (i : Fin F4.tag.rank) (c : E) :
    j (τ := F4.tag) f (yElement i c) = yElement i (f c) := by
  refine Subtype.ext ?_
  rw [j_apply]
  change bcGL (τ := F4.tag) f (yUnit F4.tag E i c) = yUnit F4.tag Ω i (f c)
  rw [bcGL_yUnit]

theorem f4Endo_natural
    {E : Type} [Field E] [CharP E 2] [Finite E] (f : E →+* Ω)
    (g : adjointGroup F4.tag E) :
    j (τ := F4.tag) f (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo E g) =
      (sigmaΩ Ω) (j (τ := F4.tag) f g) := by
  let S : Set (adjointGroup F4.tag E) := {g | ∃ i c, g = xElement i c ∨ g = yElement i c}
  let Φ : adjointGroup F4.tag E →* adjointGroup F4.tag Ω :=
    (j (τ := F4.tag) f).comp (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo E)
  let Ψ : adjointGroup F4.tag E →* adjointGroup F4.tag Ω :=
    (sigmaΩ Ω).comp (j (τ := F4.tag) f)
  have hle : Subgroup.closure S ≤ MonoidHom.eqLocus Φ Ψ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    · show Φ (xElement i c) = Ψ (xElement i c)
      change j (τ := F4.tag) f
          (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo E (xElement i c)) =
        (sigmaΩ Ω) (j (τ := F4.tag) f (xElement i c))
      rw [B3Pinned.f4_exceptionalEndo_xElement, j_xElement, j_xElement]
      have h2 : (sigmaΩ Ω) (xElement i (f c)) =
          xElement (F4.perm i) ((f c) ^ F4.exponent i) :=
        CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exceptionalEndoNarrow_xElement
          (CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.F4_prime_cast_eq_zero Ω)
          (f4_shortFaithful_algebraic Ω) i (f c)
      rw [h2, map_pow]
    · show Φ (yElement i c) = Ψ (yElement i c)
      change j (τ := F4.tag) f
          (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo E (yElement i c)) =
        (sigmaΩ Ω) (j (τ := F4.tag) f (yElement i c))
      rw [B3Pinned.f4_exceptionalEndo_yElement, j_yElement, j_yElement]
      have h2 : (sigmaΩ Ω) (yElement i (f c)) =
          yElement (F4.perm i) ((f c) ^ F4.exponent i) :=
        CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exceptionalEndoNarrow_yElement
          (CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.F4_prime_cast_eq_zero Ω)
          (f4_shortFaithful_algebraic Ω) i (f c)
      rw [h2, map_pow]
  have hgen := B3Exact.Narrow.closure_xElement_yElement_narrow (τ := F4.tag) (K := E)
  have hg : g ∈ Subgroup.closure S := hgen.symm ▸ Subgroup.mem_top g
  exact hle hg

end Algebraic
end CFSG.StandardType.F4ExplicitPos.B3Algebraic
end

end
