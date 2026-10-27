module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9: the focal-subgroup squeeze

This file formalizes the focal-subgroup mechanism in source Lemma 9.2.  If a
subgroup `E` contains a Sylow `p`-subgroup `P` of `G`, controls `G`-fusion in
`P`, and `p` divides the order of `E / E'`, then Hall's `p`-residual of `G` is
proper.  Since `E` contains `P`, it also supplements that residual.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement

universe u

/-- The elementwise fusion-control condition needed by the focal subgroup
theorem: ambient-conjugate elements of `P` are already conjugate by `E`. -/
public def ControlsFusionIn {G : Type u} [Group G]
    (E P : Subgroup G) : Prop :=
  ∀ {x y : G}, x ∈ P → y ∈ P → IsConj x y →
    ∃ e : E, (e : G) * x * (e : G)⁻¹ = y

/-- Construct fusion control from the elementwise conjugator condition. -/
public theorem ControlsFusionIn.of_conjugators
    {G : Type u} [Group G] {E P : Subgroup G}
    (h : ∀ {x y : G}, x ∈ P → y ∈ P → IsConj x y →
      ∃ e : E, (e : G) * x * (e : G)⁻¹ = y) :
    ControlsFusionIn E P :=
  h

/-- Apply elementwise fusion control without unfolding its private-by-default
definition downstream. -/
public theorem ControlsFusionIn.exists_conjugator
    {G : Type u} [Group G] {E P : Subgroup G}
    (hfusion : ControlsFusionIn E P)
    {x y : G} (hxP : x ∈ P) (hyP : y ∈ P) (hxy : IsConj x y) :
    ∃ e : E, (e : G) * x * (e : G)⁻¹ = y :=
  hfusion hxP hyP hxy

/-- Fusion control puts the ambient focal subgroup of `P` inside the image of
the commutator subgroup of `E`. -/
public theorem focalSubgroup_le_map_commutator_of_controlsFusionIn
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (E : Subgroup G) (P : Sylow p G) (hP : (P : Subgroup G) ≤ E)
    (hfusion : ControlsFusionIn E (P : Subgroup G)) :
    (P : Subgroup G).feitThompsonFocalSubgroup ≤
      (commutator E).map E.subtype := by
  rw [Subgroup.feitThompsonFocalSubgroup_def, Subgroup.closure_le]
  rintro z ⟨x, hxP, y, hyP, hxy, rfl⟩
  obtain ⟨e, he⟩ := hfusion.exists_conjugator hxP hyP hxy
  let xE : E := ⟨x, hP hxP⟩
  have hecomm : ⁅xE⁻¹, e⁆ ∈ commutator E :=
    Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup E))
      (H₂ := (⊤ : Subgroup E)) (by simp) (by simp)
  refine Subgroup.mem_map.mpr ⟨⁅xE⁻¹, e⁆, hecomm, ?_⟩
  have hmul := congrArg (fun z : G => x⁻¹ * z) he
  simpa [Subgroup.coe_subtype, commutatorElement_def, xE, mul_assoc] using hmul

/-- Fusion control identifies the intersection of every subgroup of the
ambient Sylow subgroup with the ambient commutator and with the commutator of
the fusion-controlling subgroup.  This is the focal-subgroup equality used in
source `(10B)`. -/
public theorem inf_commutator_eq_inf_map_commutator_of_controlsFusionIn
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (E U : Subgroup G) (P : Sylow p G)
    (hP : (P : Subgroup G) ≤ E)
    (hU : U ≤ (P : Subgroup G))
    (hfusion : ControlsFusionIn E (P : Subgroup G)) :
    U ⊓ commutator G =
      U ⊓ (commutator E).map E.subtype := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hxFocal : x ∈ (P : Subgroup G).feitThompsonFocalSubgroup := by
      rw [← Subgroup.commutator_inf_eq_feitThompsonFocalSubgroup P]
      exact ⟨hx.2, hU hx.1⟩
    exact focalSubgroup_le_map_commutator_of_controlsFusionIn
      E P hP hfusion hxFocal
  · intro x hx
    refine ⟨hx.1, ?_⟩
    rw [Subgroup.map_subtype_commutator] at hx
    exact Subgroup.commutator_mono le_top le_top hx.2

/-- If `p` occurs in `E / E'`, fusion control forces the focal subgroup of the
ambient Sylow subgroup to be proper. -/
public theorem focalSubgroup_lt_of_dvd_abelianization_of_controlsFusionIn
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (E : Subgroup G) (P : Sylow p G) (hP : (P : Subgroup G) ≤ E)
    (hfusion : ControlsFusionIn E (P : Subgroup G))
    (hp : p ∣ Nat.card (E ⧸ derivedSubgroup E)) :
    (P : Subgroup G).feitThompsonFocalSubgroup < (P : Subgroup G) := by
  have hpcomm : p ∣ Nat.card (E ⧸ commutator E) := by
    simpa only [derivedSubgroup, derivedSeries_one] using hp
  have hPnot : ¬ (P : Subgroup G) ≤ (commutator E).map E.subtype := by
    intro hPcomm
    let PE : Sylow p E := P.subtype hP
    have hPEcomm : (PE : Subgroup E) ≤ commutator E := by
      intro x hx
      have hxP : (x : G) ∈ (P : Subgroup G) := by
        simpa [PE, Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hx
      have hxmap : (x : G) ∈ (commutator E).map E.subtype := hPcomm hxP
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
      have hyeq : y = x := Subtype.ext hyx
      simpa [hyeq] using hy
    have hpindex : p ∣ (commutator E).index := by
      simpa [Subgroup.index_eq_card] using hpcomm
    have hindexdvd : (commutator E).index ∣ (PE : Subgroup E).index :=
      Subgroup.index_dvd_of_le hPEcomm
    exact PE.not_dvd_index (hpindex.trans hindexdvd)
  have hfocalmap : (P : Subgroup G).feitThompsonFocalSubgroup ≤
      (commutator E).map E.subtype :=
    focalSubgroup_le_map_commutator_of_controlsFusionIn E P hP hfusion
  refine lt_of_le_of_ne (P : Subgroup G).feitThompsonFocalSubgroup_le ?_
  intro heq
  exact hPnot (heq ▸ hfocalmap)

/-- Source Lemma 9.2's focal endpoint: the Hall `p`-residual is proper.  The
proof uses focal transfer to a nontrivial quotient of the Sylow subgroup. -/
public theorem hallPResidual_lt_top_of_dvd_abelianization_of_controlsFusionIn
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (E : Subgroup G) (P : Sylow p G) (hP : (P : Subgroup G) ≤ E)
    (hfusion : ControlsFusionIn E (P : Subgroup G))
    (hp : p ∣ Nat.card (E ⧸ derivedSubgroup E)) :
    External.hallPResidual p G < ⊤ := by
  have hfocal_lt : (P : Subgroup G).feitThompsonFocalSubgroup < (P : Subgroup G) :=
    focalSubgroup_lt_of_dvd_abelianization_of_controlsFusionIn
      E P hP hfusion hp
  let V : G →* ((P : Subgroup G) ⧸ (P : Subgroup G).feitThompsonFocalSubgroupOf) :=
    (P : Subgroup G).feitThompsonTransferFocal
  have htarget :
      IsPGroup p ((P : Subgroup G) ⧸ (P : Subgroup G).feitThompsonFocalSubgroupOf) :=
    P.isPGroup'.to_quotient (P : Subgroup G).feitThompsonFocalSubgroupOf
  have hresker : External.hallPResidual p G ≤ V.ker :=
    External.hallPResidual_le_ker_of_isPGroup V htarget
  have hkerlt : V.ker < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hker
    have hPeq : (P : Subgroup G) = (P : Subgroup G).feitThompsonFocalSubgroup := by
      calc
        (P : Subgroup G) = (⊤ : Subgroup G) ⊓ (P : Subgroup G) := by simp
        _ = V.ker ⊓ (P : Subgroup G) := by rw [hker]
        _ = (P : Subgroup G).feitThompsonFocalSubgroup := by
          simpa [V] using
            (Subgroup.ker_feitThompsonTransferFocal_inf_eq_feitThompsonFocalSubgroup (P := P))
    exact hfocal_lt.ne hPeq.symm
  exact lt_of_le_of_lt hresker hkerlt

/-- The complete source factorization behind Lemma 9.2: the proper Hall
`p`-residual, together with `E`, generates the whole ambient group. -/
public theorem hallPResidual_factorization_of_dvd_abelianization_of_controlsFusionIn
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (E : Subgroup G) (P : Sylow p G) (hP : (P : Subgroup G) ≤ E)
    (hfusion : ControlsFusionIn E (P : Subgroup G))
    (hp : p ∣ Nat.card (E ⧸ derivedSubgroup E)) :
    External.hallPResidual p G < ⊤ ∧
      E ⊔ External.hallPResidual p G = ⊤ := by
  refine ⟨?_, External.hall_sup_hallPResidual_eq_top_of_sylow_le p P E hP⟩
  exact hallPResidual_lt_top_of_dvd_abelianization_of_controlsFusionIn
    E P hP hfusion hp

end CFSG.BenderSuzuki
