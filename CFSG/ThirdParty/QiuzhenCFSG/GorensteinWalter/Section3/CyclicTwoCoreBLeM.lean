module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBInterM
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# `B ≤ M` in the cyclic first-case A₇ layer model — normalizer-equality leg

The paper derives `B ⊆ M` (p. 223) by applying its Lemma 2.9 corollary to
the normal subgroup `X = B ∩ PP^g` of `C_U(t₁)`.  The `P ∩ P^g` normality/
triviality steps behind that witness are a known source gap (see
`tasks/gw-section3.md`), so the witness is replaced with `X = B ∩ M`
itself.  This module contains the fully proved normalizer-equality leg
and the conditional public theorem:

* `P₂ ≤ B ∩ M` and `P₂ ≠ 1` make `B ∩ M` nontrivial (the FourData/
  normalizer setup, i.e. `N_G(P₂) ≤ M`);
* `B ∩ M = O₂'(M)` (landed equality) makes `B ∩ M` normal in the coatom
  `M`;
* `normalizer_eq_of_nontrivial_normal_in_coatom` forces
  `N_G(B ∩ M) = M`, so `B ≤ M` is equivalent to the single leg
  `hBnorm : B ≤ N_G(B ∩ M)`; the public theorem below states exactly this
  reduction.

The route audit (Route A's Frattini factorization modulo `C ∩ M ⊴ C`,
the Theorem-C bypass, the maximality alternative, and the proposed
direct A₇ order-four contradiction with its concrete counterexample) is
recorded in `/tmp/s3-b-le-m-report.md`; `hBnorm` is the one missing leg.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The replacement witness `P₂ ≤ B ∩ M` from the normalizer setup. -/
private theorem firstCase_cyclic_P2_le_B_inter_M
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M) :
    sylowCarrier (firstCase_P2_sylow c od hU Q) ≤ od.d.bg.B ⊓ M := by
  intro x hx
  exact Subgroup.mem_inf.mpr
    ⟨firstCase_cyclic_P2_le_B c od hU Q x hx, hMN (Subgroup.le_normalizer hx)⟩

/-- In the A₇ layer model the intersection `B ∩ M` is nontrivial, since it
contains the nontrivial Sylow `p`-subgroup `P₂` of `B`. -/
private theorem firstCase_cyclic_B_inter_M_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (M : Subgroup G)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M) :
    od.d.bg.B ⊓ M ≠ ⊥ := by
  let P2 : Subgroup G := sylowCarrier (firstCase_P2_sylow c od hU Q)
  have hP2ne : P2 ≠ ⊥ := firstCase_P2_ne_one hmin c od hfirst hHhat hU Q
  have hP2leBM : P2 ≤ od.d.bg.B ⊓ M :=
    firstCase_cyclic_P2_le_B_inter_M c od M hU Q hMN
  intro hbot
  apply hP2ne
  apply le_antisymm
  · intro x hx
    have hxBM : x ∈ od.d.bg.B ⊓ M := hP2leBM hx
    rwa [hbot] at hxBM
  · exact bot_le

/-- In the A₇ layer model `B ∩ M` is the odd core of `M`, hence normal in
the coatom `M`. -/
private theorem firstCase_cyclic_B_inter_M_normal_in_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B) :
    ((od.d.bg.B ⊓ M).subgroupOf M).Normal := by
  let O : Subgroup G := (pPrimeCore 2 M).map M.subtype
  have hBMeqO : od.d.bg.B ⊓ M = O :=
    firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer
      hmin c od M hMmax hSM fd hV2 hA7 hU
  have hOleM : O ≤ M := by
    simpa [O] using (Subgroup.map_subtype_le (H := M) (pPrimeCore 2 M))
  have hOnorm : IsNormalIn O M := by
    refine ⟨hOleM, ?_⟩
    intro m hm o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(⟨m, hm⟩ : M) * o0 * (⟨m, hm⟩ : M)⁻¹, ?_, rfl⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥M)).conj_mem o0 ho0 ⟨m, hm⟩
  have hOnormalM : (O.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := O)
      (le_normalizer_of_isNormalIn hOnorm)
  simpa [hBMeqO] using hOnormalM

/-- Ambient normalizer control: in the A₇ layer model the normalizer of
`B ∩ M` is exactly the maximal overgroup `M`. -/
private theorem firstCase_cyclic_normalizer_B_inter_M_eq_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M) :
    Subgroup.normalizer ((od.d.bg.B ⊓ M : Subgroup G) : Set G) = M := by
  let O : Subgroup G := (pPrimeCore 2 M).map M.subtype
  have hBMeqO : od.d.bg.B ⊓ M = O :=
    firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer
      hmin c od M hMmax hSM fd hV2 hA7 hU
  have hBMne : od.d.bg.B ⊓ M ≠ ⊥ :=
    firstCase_cyclic_B_inter_M_ne_bot hmin c od hfirst hHhat M hU Q hMN
  have hOne : O ≠ ⊥ := by
    intro hbot
    apply hBMne
    rwa [← hBMeqO] at hbot
  have hOleM : O ≤ M := by
    simpa [O] using (Subgroup.map_subtype_le (H := M) (pPrimeCore 2 M))
  have hOnorm : IsNormalIn O M := by
    refine ⟨hOleM, ?_⟩
    intro m hm o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(⟨m, hm⟩ : M) * o0 * (⟨m, hm⟩ : M)⁻¹, ?_, rfl⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥M)).conj_mem o0 ho0 ⟨m, hm⟩
  have hOnormalM : (O.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := O)
      (le_normalizer_of_isNormalIn hOnorm)
  have hNOM : Subgroup.normalizer (O : Set G) = M :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) hMmax hOleM hOne hOnormalM
  simpa [hBMeqO] using hNOM

/-- In the cyclic first-case A₇ layer model, the common centralizer
`B = C_U(S)` lies in the maximal overgroup `M`, modulo the single exact
remaining leg that `B` normalizes its intersection with `M`.

The paper's witness `X = B ∩ PP^g` for this leg is invalid (known source
gap), so the leg is stated explicitly as `hBnorm`; all other steps
(nontriviality of `B ∩ M` via `P₂`, the landed equality
`B ∩ M = O₂'(M)`, and the coatom normalizer control `N_G(B ∩ M) = M`)
are proved in this module. -/
public theorem firstCase_cyclic_B_le_M_of_a7_layer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hBnorm : od.d.bg.B ≤ Subgroup.normalizer
      ((od.d.bg.B ⊓ M : Subgroup G) : Set G)) :
    od.d.bg.B ≤ M := by
  have hNOM : Subgroup.normalizer ((od.d.bg.B ⊓ M : Subgroup G) : Set G) = M :=
    firstCase_cyclic_normalizer_B_inter_M_eq_M
      hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 hU Q hMN
  intro b hb
  exact hNOM ▸ hBnorm hb

end CFSG.GorensteinWalter
