module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordSpec
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4InnerAction
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootCores
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIModel

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LieType.Steinberg.TwistedD4 CFSG.StandardType.LieKnownR2.TriD4.Bridge
  CFSG.StandardType.LieKnownR2.TriD4HighRootParabolic
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.HighestRoot
  CFSG.LieType.TitsSimplicity CFSG.SeitzReduction CFSG.StandardType.RootCentExc
open scoped commutatorElement

private theorem rckTriC_coord_one
    (τ : Tag) (K : Type) [Field K] {coord : ModGL τ K → (Fin τ.rank → ℤ) → K}
    (h : HeisCoordSpec τ K coord) : coord 1 = 0 := by
  have h1 := h.mul (1 : ModGL τ K) ((Qθ τ K).one_mem) 1
    ((Qθ τ K).one_mem)
  rw [one_mul] at h1
  exact add_left_cancel (a := coord 1) (by rw [add_zero]; exact h1.symm)

private theorem rckTriC_coord_inv
    (τ : Tag) (K : Type) [Field K] {coord : ModGL τ K → (Fin τ.rank → ℤ) → K}
    (h : HeisCoordSpec τ K coord) {q : ModGL τ K} (hq : q ∈ Qθ τ K) :
    coord q⁻¹ = -coord q := by
  have h1 := h.mul q hq q⁻¹ ((Qθ τ K).inv_mem hq)
  rw [mul_inv_cancel] at h1
  rw [rckTriC_coord_one τ K h] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

theorem rckTriC_commutator_Qθ_le_Uθ
    (τ : Tag) (K : Type) [Field K] : ⁅Qθ τ K, Qθ τ K⁆ ≤ Uθ τ K := by
  obtain ⟨coord, hspec⟩ := exists_heisCoord (τ := τ) (K := K)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : a * b ∈ Qθ τ K := (Qθ τ K).mul_mem ha hb
  have ha' : a⁻¹ ∈ Qθ τ K := (Qθ τ K).inv_mem ha
  have hb' : b⁻¹ ∈ Qθ τ K := (Qθ τ K).inv_mem hb
  have hmem : ⁅a, b⁆ ∈ Qθ τ K := by
    rw [commutatorElement_def]
    exact (Qθ τ K).mul_mem ((Qθ τ K).mul_mem ((Qθ τ K).mul_mem ha hb)
      ((Qθ τ K).inv_mem ha)) ((Qθ τ K).inv_mem hb)
  rw [← hspec.eq_zero_iff ⁅a, b⁆ hmem]
  change coord (a * b * a⁻¹ * b⁻¹) = 0
  have h1 := hspec.mul (a * b) hab a⁻¹ ha'
  have h2 := hspec.mul a ha b hb
  have h5 := hspec.mul (a * b * a⁻¹) ((Qθ τ K).mul_mem hab ha') b⁻¹ hb'
  rw [h5, h1, h2, rckTriC_coord_inv τ K hspec ha, rckTriC_coord_inv τ K hspec hb]
  abel

theorem rckTriC_pcore_normalizer_C0
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K →+* K) :
    pCoreOf 2 (Subgroup.normalizer (triD4C0HighRoot K σ :
        Set (graphFixedRootGroup TwistTag.D4 K σ))) =
      (graphFixedParabolicRadical TwistTag.D4 K σ
        ({(0 : Fin 2)} : Set (Fin TwistTag.D4.foldedTag.rank))).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ) := by
  classical
  let σ' : K ≃+* K := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : σ'.toRingHom = σ := rfl
  have hθ : IsRoot d4 (highRoot d4) := isRoot_highRoot d4
  let G : Subgroup (ModGL d4 K) := graphFixedRootGroup TwistTag.D4 K σ
  let H : Subgroup (ModGL d4 K) := rootSubgroup d4 K (highRoot d4) ⊓
    twistedFixedGroup TwistTag.D4 K σ
  let P : Subgroup (ModGL d4 K) := graphFixedParabolic TwistTag.D4 K σ
    ({(0 : Fin 2)} : Set (Fin 2))
  let QA : Subgroup (ModGL d4 K) := graphFixedParabolicRadical TwistTag.D4 K σ
    ({(0 : Fin 2)} : Set (Fin 2))
  have hPG : P ≤ G := graphFixedParabolic_le TwistTag.D4 K σ _
  have hHleG : H ≤ G := by
    have hroot_pos : rootSubgroup d4 K (highRoot d4) ≤ posUnipotent d4 K :=
      le_iSup₂_of_le (highRoot d4) ⟨hθ, height_highRoot_pos d4⟩ le_rfl
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hroot_pos hx1, hx2⟩)
  have hX : triD4C0HighRoot K σ = H.subgroupOf G := rfl
  have hN : Subgroup.normalizer (triD4C0HighRoot K σ : Set G) = P.subgroupOf G := by
    rw [hX, ← Subgroup.subgroupOf_normalizer_eq hHleG]
    have hkey : G ⊓ Subgroup.normalizer (H : Set (ModGL d4 K)) = P := by
      have h := graphFixedRootGroup_inf_normalizer_highRootFixed_D4 K σ'
      rw [hσ'] at h
      exact h
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (hkey ▸ ⟨x.2, hx⟩ : (x : ModGL d4 K) ∈ P)
    · intro hx
      exact (hkey ▸ hx : (x : ModGL d4 K) ∈ G ⊓ Subgroup.normalizer (H : Set (ModGL d4 K))).2
  have hpCore_sub : pCoreOf 2 (P.subgroupOf G) = (pCoreOf 2 P).subgroupOf G := by
    apply Subgroup.map_injective (f := G.subtype) G.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans hPG)]
    rw [pCoreOf, Subgroup.map_map]
    rw [show G.subtype.comp (P.subgroupOf G).subtype =
        P.subtype.comp (Subgroup.subgroupOfEquivOfLe hPG).toMonoidHom from by ext x; rfl]
    rw [← Subgroup.map_map]
    rw [CFSG.pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hPG)]
    rw [pCoreOf]
  have hcoreP : pCoreOf 2 P = QA := by
    have h := pCore_graphFixedParabolic_D4 K σ'
    rw [hσ', ringChar.eq K 2] at h
    exact h
  rw [hN, hpCore_sub, hcoreP]
  rfl

theorem rckTriC_commutator_pcore_C0
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K →+* K) :
    ⁅pCoreOf 2 (Subgroup.normalizer (triD4C0HighRoot K σ :
          Set (graphFixedRootGroup TwistTag.D4 K σ))),
        pCoreOf 2 (Subgroup.normalizer (triD4C0HighRoot K σ :
          Set (graphFixedRootGroup TwistTag.D4 K σ)))⁆ ≤ triD4C0HighRoot K σ := by
  classical
  let G : Subgroup (ModGL d4 K) := graphFixedRootGroup TwistTag.D4 K σ
  let H : Subgroup (ModGL d4 K) := rootSubgroup d4 K (highRoot d4) ⊓
    twistedFixedGroup TwistTag.D4 K σ
  let QA : Subgroup (ModGL d4 K) := graphFixedParabolicRadical TwistTag.D4 K σ
    ({(0 : Fin 2)} : Set (Fin 2))
  have hX : triD4C0HighRoot K σ = H.subgroupOf G := rfl
  have hJ : TwistTag.D4.orbitUnion ({(0 : Fin TwistTag.D4.foldedTag.rank)} :
      Set (Fin TwistTag.D4.foldedTag.rank)) = Jθ d4 := by
    ext i
    rw [mem_orbitUnion_iff_orbitIndex]
    exact (show ∀ i : Fin 4, (![0, 0, 1, 0] : Fin 4 → Fin 2) i = 0 ↔ i ≠ 2 by decide) i
  have hQ : graphFixedParabolicRadical TwistTag.D4 K σ
      ({(0 : Fin 2)} : Set (Fin 2)) ≤ parabolicRadical d4 K (Jθ d4) := by
    show parabolicRadical d4 K (TwistTag.D4.orbitUnion
      ({(0 : Fin TwistTag.D4.foldedTag.rank)} : Set (Fin TwistTag.D4.foldedTag.rank))) ⊓
      twistedFixedGroup TwistTag.D4 K σ ≤ parabolicRadical d4 K (Jθ d4)
    rw [hJ]
    exact inf_le_left
  have hQH : graphFixedParabolicRadical TwistTag.D4 K σ
      ({(0 : Fin 2)} : Set (Fin 2)) ≤ twistedFixedGroup TwistTag.D4 K σ :=
    inf_le_right
  have hcomm : ⁅parabolicRadical d4 K (Jθ d4), parabolicRadical d4 K (Jθ d4)⁆ ≤
      rootSubgroup d4 K (highRoot d4) := rckTriC_commutator_Qθ_le_Uθ d4 K
  rw [rckTriC_pcore_normalizer_C0 σ, hX]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have haQ : (a : ModGL d4 K) ∈ parabolicRadical d4 K (Jθ d4) := hQ (Subgroup.mem_subgroupOf.1 ha)
    have hbQ : (b : ModGL d4 K) ∈ parabolicRadical d4 K (Jθ d4) := hQ (Subgroup.mem_subgroupOf.1 hb)
    have hmem : ⁅(a : ModGL d4 K), (b : ModGL d4 K)⁆ ∈
        ⁅parabolicRadical d4 K (Jθ d4), parabolicRadical d4 K (Jθ d4)⁆ :=
      Subgroup.commutator_mem_commutator haQ hbQ
    change ⁅(a : ModGL d4 K), (b : ModGL d4 K)⁆ ∈ rootSubgroup d4 K (highRoot d4)
    exact hcomm hmem
  · have haF : (a : ModGL d4 K) ∈ twistedFixedGroup TwistTag.D4 K σ :=
      hQH (Subgroup.mem_subgroupOf.1 ha)
    have hbF : (b : ModGL d4 K) ∈ twistedFixedGroup TwistTag.D4 K σ :=
      hQH (Subgroup.mem_subgroupOf.1 hb)
    exact (Subgroup.commutator_le.mpr fun x hx y hy =>
      (twistedFixedGroup TwistTag.D4 K σ).mul_mem
        ((twistedFixedGroup TwistTag.D4 K σ).mul_mem
          ((twistedFixedGroup TwistTag.D4 K σ).mul_mem hx hy)
          ((twistedFixedGroup TwistTag.D4 K σ).inv_mem hx))
        ((twistedFixedGroup TwistTag.D4 K σ).inv_mem hy))
      (Subgroup.commutator_mem_commutator haF hbF)

theorem rckTriC_hQ
    {F : Type} [Field F] [Finite F] (σ : F →+* F) {g : ℕ} (hF : TriField F σ g) :
    ⁅pCoreOf 2 (Subgroup.normalizer
          ((twistedDatum σ).rootGroup (highRoot .G2) : Set (twistedGroup σ))),
        pCoreOf 2 (Subgroup.normalizer
          ((twistedDatum σ).rootGroup (highRoot .G2) : Set (twistedGroup σ)))⁆ ≤
      (twistedDatum σ).rootGroup (highRoot .G2) := by
  haveI hchar : CharP F 2 := by
    haveI : Fintype F := Fintype.ofFinite F
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hF.2.1, ← pow_mul] at h0
    rw [Nat.cast_pow, Nat.cast_ofNat] at h0
    have hg : g * 3 ≠ 0 := by have := hF.1; omega
    exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (pow_eq_zero_iff hg |>.mp h0)
  let e : twistedGroup σ ≃* graphFixedRootGroup TwistTag.D4 F σ :=
    triD4BridgeEquiv σ hF.1 hF.2.1 hF.2.2
  have hH := triD4BridgeEquiv_twistedRootGroup_highRoot σ hF.1 hF.2.1 hF.2.2
  have hmap := CFSG.StandardType.LieKnownR2.map_pCoreOf_normalizer_mulEquiv e
    ((twistedDatum σ).rootGroup (highRoot .G2))
  rw [hH] at hmap
  have hC0 := rckTriC_commutator_pcore_C0 (K := F) σ
  rw [← hmap, ← hH] at hC0
  refine (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp ?_
  rw [Subgroup.map_commutator]
  exact hC0

end CFSG.StandardType.RCKK1II
