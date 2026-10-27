module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeIso
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4HighRootParabolic
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LinkTriD4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2FixedPointOdd

public section

namespace CFSG.StandardType.LieKnownR2.TriD4.NC

open CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.StandardType.LieKnownR2.TriD4HighRootParabolic CFSG.SeitzReduction
open scoped commutatorElement

private theorem tnc_highRootFixed_le_graphFixedRootGroup
    {K : Type} [Field K] (σ : K →+* K) :
    (rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ) ≤
      graphFixedRootGroup TwistTag.D4 K σ := by
  have hle : rootSubgroup d4 K (highRoot d4) ≤ posUnipotent d4 K :=
    le_iSup₂_of_le (highRoot d4) ⟨isRoot_highRoot _, height_highRoot_pos _⟩ le_rfl
  exact le_trans (inf_le_inf_right (twistedFixedGroup TwistTag.D4 K σ) hle)
    (graphFixedPosUnipotent_le_graphFixedRootGroup (t := TwistTag.D4) K σ)

private theorem tnc_pCoreOf_subgroupOf_map_le
    {M : Type} [Group M] {C0 P Q : Subgroup M} (hPC : P ≤ C0)
    (hQ : (CFSG.pCore 2 P).map P.subtype = Q) :
    ((CFSG.Open.pCoreOf 2 (P.subgroupOf C0)).map C0.subtype) ≤ Q := by
  let e : P.subgroupOf C0 ≃* P := Subgroup.subgroupOfEquivOfLe hPC
  have hpc : (CFSG.pCore 2 (P.subgroupOf C0)).map e.toMonoidHom = CFSG.pCore 2 P :=
    CFSG.pCore_map_iso 2 e
  change (((CFSG.pCore 2 (P.subgroupOf C0)).map (P.subgroupOf C0).subtype).map C0.subtype) ≤ Q
  rw [Subgroup.map_map]
  rw [show C0.subtype.comp (P.subgroupOf C0).subtype = P.subtype.comp e.toMonoidHom from
    MonoidHom.ext fun n => rfl]
  rw [← Subgroup.map_map, hpc, hQ]

private theorem tnc_pCoreOf_normalizer_le
    {M : Type} [Group M] {C0 H P Q : Subgroup M}
    (hHle : H ≤ C0) (hPC : P ≤ C0)
    (hN : C0 ⊓ Subgroup.normalizer (H : Set M) = P)
    (hQ : (CFSG.pCore 2 P).map P.subtype = Q) :
    ((CFSG.Open.pCoreOf 2 (Subgroup.normalizer (H.subgroupOf C0))).map C0.subtype) ≤ Q := by
  rw [← Subgroup.subgroupOf_normalizer_eq hHle]
  rw [← Subgroup.inf_subgroupOf_left, hN]
  exact tnc_pCoreOf_subgroupOf_map_le hPC hQ

private theorem tnc_mem_normalizer_subgroupOf
    {M : Type} [Group M] {C0 H : Subgroup M} (hHle : H ≤ C0) {h₀ : M} (hhC : h₀ ∈ C0)
    (hh : h₀ ∈ Subgroup.normalizer (H : Set M)) :
    (⟨h₀, hhC⟩ : C0) ∈ Subgroup.normalizer (H.subgroupOf C0) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hHle]
  exact hh

theorem triD4_C0_exists_odd_fpf
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ∃ h : graphFixedRootGroup TwistTag.D4 K σ,
      h ∈ (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)) ⊓
          Subgroup.normalizer (Bridge.triD4C0HighRoot K σ :
            Set (graphFixedRootGroup TwistTag.D4 K σ)) ∧
        Odd (orderOf h) ∧
        ∀ y ∈ pCoreOf 2 ((⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)) ⊓
            Subgroup.normalizer (Bridge.triD4C0HighRoot K σ :
              Set (graphFixedRootGroup TwistTag.D4 K σ))),
          h * y = y * h → y ∈ Bridge.triD4C0HighRoot K σ := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, Nat.mul_comm f 3]
  haveI hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK3
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  let σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσ' : σ'.toRingHom = σ := rfl
  obtain ⟨h₀ : ModGL (TwistTag.D4.tag) K, hh₀, hodd₀, hfpf₀⟩ :=
    CFSG.StandardType.LieKnownR2.LinkTriD4.triD4_exists_odd_fpf_of_card K f hK3 σ
  have hJ : TwistTag.D4.orbitUnion ({(0 : Fin TwistTag.D4.foldedTag.rank)} :
      Set (Fin TwistTag.D4.foldedTag.rank)) = Jθ d4 := by
    ext i
    rw [mem_orbitUnion_iff_orbitIndex]
    have key : ∀ i : Fin 4, (![0, 0, 1, 0] : Fin 4 → Fin 2) i = 0 ↔ i ≠ 2 := by decide
    exact key i
  have hP := (diagram_fixed_parabolic_intersection TwistTag.D4 K σ'
    ({(0 : Fin TwistTag.D4.foldedTag.rank)} : Set (Fin TwistTag.D4.foldedTag.rank))).2.1
  rw [hJ] at hP
  rw [hσ'] at hP
  have hN := graphFixedRootGroup_inf_normalizer_highRootFixed_D4 K σ'
  rw [hσ'] at hN
  let C0 : Subgroup (ModGL d4 K) := graphFixedRootGroup TwistTag.D4 K σ
  let H : Subgroup (ModGL d4 K) := rootSubgroup d4 K (highRoot d4) ⊓
    twistedFixedGroup TwistTag.D4 K σ
  let P : Subgroup (ModGL d4 K) := graphFixedParabolic TwistTag.D4 K σ'
    ({(0 : Fin TwistTag.D4.foldedTag.rank)} : Set (Fin TwistTag.D4.foldedTag.rank))
  let Q : Subgroup (ModGL d4 K) := graphFixedParabolicRadical TwistTag.D4 K σ'
    ({(0 : Fin TwistTag.D4.foldedTag.rank)} : Set (Fin TwistTag.D4.foldedTag.rank))
  have hHle : H ≤ C0 := tnc_highRootFixed_le_graphFixedRootGroup σ
  have hPC : P ≤ C0 := graphFixedParabolic_le TwistTag.D4 K σ' _
  have hN' : C0 ⊓ Subgroup.normalizer (H : Set (ModGL d4 K)) = P := hN
  have hQeq : (CFSG.pCore 2 P).map P.subtype = Q := by
    have := pCore_graphFixedParabolic_D4 K σ'
    rw [hring] at this
    exact this
  have hbound : ((CFSG.Open.pCoreOf 2 (Subgroup.normalizer (H.subgroupOf C0))).map
      C0.subtype) ≤ Q := tnc_pCoreOf_normalizer_le hHle hPC hN' hQeq
  have hhC : (h₀ : ModGL d4 K) ∈ C0 := (Subgroup.mem_inf.1 hh₀).2
  have hhP : (h₀ : ModGL d4 K) ∈ P := by
    change (h₀ : ModGL d4 K) ∈ graphFixedParabolic TwistTag.D4 K σ
      ({(0 : Fin TwistTag.D4.foldedTag.rank)} : Set (Fin TwistTag.D4.foldedTag.rank))
    rw [← hP]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hh₀).1, (Subgroup.mem_inf.1 hh₀).2⟩
  have hhNormH : (h₀ : ModGL d4 K) ∈ Subgroup.normalizer (H : Set (ModGL d4 K)) := by
    have h1 : (h₀ : ModGL d4 K) ∈ C0 ⊓ Subgroup.normalizer (H : Set (ModGL d4 K)) := by
      rw [hN']
      exact hhP
    exact (Subgroup.mem_inf.1 h1).2
  refine ⟨⟨(h₀ : ModGL d4 K), hhC⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩, ?_, ?_⟩
  · exact tnc_mem_normalizer_subgroupOf hHle hhC hhNormH
  · rw [Subgroup.orderOf_mk]
    exact hodd₀
  · intro y hy hcomm
    rw [top_inf_eq] at hy
    have hyQ : (y : ModGL d4 K) ∈ Q := hbound (Subgroup.mem_map_of_mem C0.subtype hy)
    have hyQθ : (y : ModGL d4 K) ∈ Qθ d4 K := by
      have h1 : (y : ModGL d4 K) ∈ graphFixedParabolicRadical TwistTag.D4 K σ'
          ({(0 : Fin TwistTag.D4.foldedTag.rank)} :
            Set (Fin TwistTag.D4.foldedTag.rank)) := hyQ
      have h3 : (y : ModGL d4 K) ∈ parabolicRadical d4 K
          (TwistTag.D4.orbitUnion
            ({(0 : Fin TwistTag.D4.foldedTag.rank)} : Set (Fin TwistTag.D4.foldedTag.rank))) :=
        (Subgroup.mem_inf.1 h1).1
      rwa [hJ] at h3
    have hmem : (h₀ : ModGL d4 K) * (y : ModGL d4 K) * (h₀ : ModGL d4 K)⁻¹ *
        (y : ModGL d4 K)⁻¹ ∈ Uθ d4 K := by
      have h1 : (⟨(h₀ : ModGL d4 K), hhC⟩ : C0) * y = y * ⟨(h₀ : ModGL d4 K), hhC⟩ := hcomm
      have h2 : (h₀ : ModGL d4 K) * (y : ModGL d4 K) =
          (y : ModGL d4 K) * (h₀ : ModGL d4 K) := by
        simpa using congrArg (fun z : C0 => (z : ModGL d4 K)) h1
      have h3 : (h₀ : ModGL d4 K) * (y : ModGL d4 K) * (h₀ : ModGL d4 K)⁻¹ *
          (y : ModGL d4 K)⁻¹ = 1 := by
        rw [h2]; group
      rw [h3]
      exact (Uθ d4 K).one_mem
    have hU : (y : ModGL d4 K) ∈ Uθ d4 K := hfpf₀ _ hyQθ hmem
    have hΓ : (y : ModGL d4 K) ∈ twistedFixedGroup TwistTag.D4 K σ :=
      graphFixedRootGroup_le _ K σ y.2
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.2 ⟨hU, hΓ⟩)

theorem triD4_noCentral_C0
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    GGRootNoCentralAt (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ))
      (Bridge.triD4C0HighRoot K σ) := by
  obtain ⟨h, hhN, hodd, hfix⟩ := triD4_C0_exists_odd_fpf σ hf hK hσ
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ) :=
    Finite.of_injective (Subtype.val : graphFixedRootGroup TwistTag.D4 K σ → ModGL d4 K)
      Subtype.val_injective
  exact noCentral_of_fixedPoint_odd hodd hhN hfix

end CFSG.StandardType.LieKnownR2.TriD4.NC
