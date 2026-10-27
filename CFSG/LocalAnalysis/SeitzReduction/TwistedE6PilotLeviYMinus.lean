module

public import CFSG.ClassicalGroups.Orthogonal.PointedPlane
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYDescent
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYGroupAction
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYSplit

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog (semilinCentralizer mem_semilinCentralizer
  descentField mem_descentField fixSpace mem_fixSpace descentForm)

section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def omegaMinusLevi (σ : K →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  subsystemGroup TwistTag.E6.tag K setD ⊓ graphFixedRootGroup TwistTag.E6 K σ

theorem omegaMinusLevi_le_graphFixedRootGroup (σ : K →+* K) :
    omegaMinusLevi σ ≤ graphFixedRootGroup TwistTag.E6 K σ :=
  inf_le_right

noncomputable abbrev d4Gamma (σ : K →+* K) : Subgroup (ModGL Tag.E6 K) :=
  twistedFixedGroup TwistTag.E6 K σ

noncomputable abbrev d4C0 (σ : K →+* K) : Subgroup (ModGL Tag.E6 K) :=
  graphFixedRootGroup TwistTag.E6 K σ

end Defs

section Iso


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
  (hσσ : ∀ c, σ (σ c) = c)
include hσσ

theorem d4Psi_mem_centralizer (g : ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K))) :
    d4Psi K ⟨g, g.2.1⟩ ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ) :=
  ⟨elementaryGroup_le_orthogonalGroup _ (d4Psi_range_le ⟨_, rfl⟩),
    (mem_twistedFixedGroup_iff_d4Psi hσσ ⟨g, g.2.1⟩).1 g.2.2⟩

@[expose] noncomputable def d4FixedPsi :
    ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K)) →*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ)) :=
  ((d4Psi K).comp (Subgroup.inclusion (inf_le_left : d4Levi K ⊓ d4Gamma (σ : K →+* K) ≤
    d4Levi K))).codRestrict _ (d4Psi_mem_centralizer hσσ)

theorem coe_d4FixedPsi (g : ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K))) :
    (d4FixedPsi hσσ g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) = d4Psi K ⟨g, g.2.1⟩ :=
  rfl

theorem d4FixedPsi_injective : Function.Injective (d4FixedPsi hσσ) := by
  intro g h hgh
  have h1 : d4Psi K ⟨g, g.2.1⟩ = d4Psi K ⟨h, h.2.1⟩ := congrArg Subtype.val hgh
  have h2 := d4Psi_injective h1
  exact Subtype.ext (congrArg (fun x : d4Levi K => (x : ModGL Tag.E6 K)) h2)

theorem range_d4FixedPsi :
    (d4FixedPsi hσσ).range = (orthElementaryGroup (quadPlus 4 K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ)) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_subgroupOf, coe_d4FixedPsi]
    exact d4Psi_range_le ⟨_, rfl⟩
  · intro a ha
    rw [Subgroup.mem_subgroupOf, ← range_d4Psi] at ha
    obtain ⟨g, hg⟩ := ha
    have hΓ : (g : ModGL Tag.E6 K) ∈ d4Gamma (σ : K →+* K) :=
      (mem_twistedFixedGroup_iff_d4Psi hσσ g).2 (by rw [hg]; exact a.2.2)
    exact ⟨⟨g, g.2, hΓ⟩, Subtype.ext hg⟩

variable {ω : K} (hω : σ ω ≠ ω)

@[expose] noncomputable def d4FixedEquiv :
    ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K)) ≃*
      ↥(elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) :=
  ((MonoidHom.ofInjective (d4FixedPsi_injective hσσ)).trans
      (MulEquiv.subgroupCongr (range_d4FixedPsi hσσ))).trans
    ((((orthElementaryGroup (quadPlus 4 K)).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓
          semilinCentralizer (d4Tau σ))).equivMapOfInjective (d4DescentEquiv hσσ hω).toMonoidHom
        (d4DescentEquiv hσσ hω).injective).trans
      ((MulEquiv.subgroupCongr (map_d4DescentEquiv_elementary hσσ hω)).trans
        (Subgroup.subgroupOfEquivOfLe (elementaryGroup_le_orthogonalGroup _))))

include hω in
theorem isPerfect_d4Fixed : Group.IsPerfect ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K)) :=
  have : Group.IsPerfect ↥(elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω)
      (d4MinusC hσσ ω))) := (orthogonal_elementary_perfect
    (regular_quadMinus (n := 4) (K := descentField σ) (by norm_num) (d4Minus_irr hσσ hω)).1
    (regular_quadMinus (n := 4) (K := descentField σ) (by norm_num) (d4Minus_irr hσσ hω)).2).1
  Group.IsPerfect.ofSurjective (f := (d4FixedEquiv hσσ hω).symm.toMonoidHom)
    (d4FixedEquiv hσσ hω).symm.surjective

include hω in
theorem d4Fixed_le_d4C0 : d4Levi K ⊓ d4Gamma (σ : K →+* K) ≤ d4C0 (σ : K →+* K) := by
  have := isPerfect_d4Fixed hσσ hω
  rw [← Subgroup.commutator_eq_self (H := d4Levi K ⊓ d4Gamma (σ : K →+* K))]
  exact (Subgroup.commutator_mono inf_le_right inf_le_right).trans
    (commutator_twistedFixedGroup_le (t := TwistTag.E6) σ.surjective)

end Iso

section Stated

variable (k : Type) [Field k] [Finite k] [CharP k 2] (b c : k)
  (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def elementaryMinusStatedEquiv :
    elementaryGroup (quadMinus 4 k b c) ≃* StatedProj (StatedOmega (StatedQuadMinus 4 k b c)) :=
  ((elementaryGroup (quadMinus 4 k b c)).equivMapOfInjective
      (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).symm.toMonoidHom
      (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).symm.injective).trans
    ((MulEquiv.subgroupCongr (statedOmega_quadMinus_eq_map (n := 4) (K := k) (by norm_num)
        hirr).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
          (coe_quadMinus 4 k b c)
          ⟨(minusPair k b c (n := 4) ⟨0, by norm_num⟩).e + (minusPair k b c (n := 4) ⟨0, by norm_num⟩).f,
            by rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair]; exact one_ne_zero⟩)).trans
        QuotientGroup.quotientBot).symm)

end Stated

section LieModel


section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
  (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω)
include hσσ hω

theorem omegaMinusLevi_eq :
    omegaMinusLevi (σ : K →+* K) =
      subsystemGroup TwistTag.E6.tag K setD ⊓ twistedFixedGroup TwistTag.E6 K (σ : K →+* K) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (graphFixedRootGroup_le _ _ _)
  · intro g hg
    exact ⟨hg.1, d4Fixed_le_d4C0 hσσ hω hg⟩

@[expose] noncomputable def omegaMinusLeviEquiv :
    ↥(omegaMinusLevi (σ : K →+* K)) ≃*
      ↥(elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) :=
  (MulEquiv.subgroupCongr (omegaMinusLevi_eq hσσ hω)).trans (d4FixedEquiv hσσ hω)

theorem d4Iota_d4FixedEquiv_apply
    (g : ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K)))
    (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :
    d4Iota σ ω ((d4FixedEquiv hσσ hω g : _ ≃ₗ[descentField σ] _) v) =
      d4Psi K ⟨g.1, g.2.1⟩ (d4Iota σ ω v) := by
  change d4Iota σ ω
      ((d4DescentEquiv hσσ hω (d4FixedPsi hσσ g) : _ ≃ₗ[descentField σ] _) v) =
    d4Psi K ⟨g.1, g.2.1⟩ (d4Iota σ ω v)
  rw [d4Iota_d4DescentEquiv, coe_d4FixedPsi]

theorem d4Iota_omegaMinusLeviEquiv_apply
    (g : ↥(omegaMinusLevi (σ : K →+* K)))
    (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :
    d4Iota σ ω ((omegaMinusLeviEquiv hσσ hω g : _ ≃ₗ[descentField σ] _) v) =
      d4Psi K
        ⟨(MulEquiv.subgroupCongr (G := ModGL Tag.E6 K) (omegaMinusLevi_eq hσσ hω) g).1,
          (MulEquiv.subgroupCongr (G := ModGL Tag.E6 K) (omegaMinusLevi_eq hσσ hω) g).2.1⟩
        (d4Iota σ ω v) :=
  d4Iota_d4FixedEquiv_apply hσσ hω
    (MulEquiv.subgroupCongr (G := ModGL Tag.E6 K) (omegaMinusLevi_eq hσσ hω) g) v

theorem exists_omegaMinusLevi_conj_rootD_product
    (T : ↥(elementaryGroup (quadMinus 4 (descentField σ)
      (d4MinusB hσσ ω) (d4MinusC hσσ ω)))) :
    ∃ g : ↥(omegaMinusLevi (σ : K →+* K)),
      ∀ v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ,
        MulAut.conj (G := ModGL Tag.E6 K) g.1 (d4RootWord (d4Iota σ ω v)) =
          d4RootWord (d4Iota σ ω ((T :
            (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) ≃ₗ[descentField σ] _) v)) := by
  let g : ↥(omegaMinusLevi (σ : K →+* K)) := (omegaMinusLeviEquiv hσσ hω).symm T
  let g0 : ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K)) :=
    MulEquiv.subgroupCongr (G := ModGL Tag.E6 K) (omegaMinusLevi_eq hσσ hω) g
  refine ⟨g, fun v => ?_⟩
  have hT : omegaMinusLeviEquiv hσσ hω g = T := MulEquiv.apply_symm_apply _ _
  have hIota := d4Iota_omegaMinusLeviEquiv_apply hσσ hω g v
  rw [hT] at hIota
  have hgen := d4Psi_conj_rootD_product (F := K) ⟨g0.1, g0.2.1⟩
    (d4Iota σ ω v)
  rw [← hIota] at hgen
  change (g0 : ModGL Tag.E6 K) * d4RootWord (d4Iota σ ω v) *
      (g0 : ModGL Tag.E6 K)⁻¹ =
    d4RootWord (d4Iota σ ω ((T :
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) ≃ₗ[descentField σ] _) v))
  exact hgen

theorem exists_omegaMinusLevi_conj_rootD_span_pair
    (h2k : Nat.card (descentField σ) = 2)
    {r v r2 w : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ}
    (hr : quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω) r = 1)
    (hv : quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω) v = 1)
    (hr2 : quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω) r2 = 1)
    (hw : quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω) w = 1)
    (hrv : QuadraticMap.polar
      (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) r v = 1)
    (hr2w : QuadraticMap.polar
      (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) r2 w = 1) :
    ∃ g : ↥(omegaMinusLevi (σ : K →+* K)),
      MulAut.conj (G := ModGL Tag.E6 K) g.1 (d4RootWord (d4Iota σ ω r)) =
        d4RootWord (d4Iota σ ω r2) ∧
      Set.image (MulAut.conj (G := ModGL Tag.E6 K) g.1)
        ((fun x => d4RootWord (d4Iota σ ω x)) ''
          (Submodule.span (descentField σ) {r, v} : Set _)) =
      (fun x => d4RootWord (d4Iota σ ω x)) ''
        (Submodule.span (descentField σ) {r2, w} : Set _) := by
  let Q : QuadraticForm (descentField σ)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :=
    quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    (regular_quadMinus (n := 4) (K := descentField σ)
      (b := d4MinusB hσσ ω) (c := d4MinusC hσσ ω)
      (by norm_num) (d4Minus_irr hσσ hω)).1
  let P : HypPair Q := minusPair (n := 4) (K := descentField σ)
    (b := d4MinusB hσσ ω) (c := d4MinusC hσσ ω) (0 : Fin (4 - 1))
  let P' : HypPair Q := minusPair (n := 4) (K := descentField σ)
    (b := d4MinusB hσσ ω) (c := d4MinusC hσσ ω) (1 : Fin (4 - 1))
  have hP : P.Orth P' := by
    simpa [P, P'] using
      (minusPair_orth (K := descentField σ) (n := 4)
        (b := d4MinusB hσσ ω) (c := d4MinusC hσσ ω)
        (i := (0 : Fin (4 - 1))) (j := (1 : Fin (4 - 1))) (by decide))
  have hrQ : Q r = 1 := by simpa [Q] using hr
  have hvQ : Q v = 1 := by simpa [Q] using hv
  have hr2Q : Q r2 = 1 := by simpa [Q] using hr2
  have hwQ : Q w = 1 := by simpa [Q] using hw
  have hrvQ : QuadraticMap.polar Q r v = 1 := by simpa [Q] using hrv
  have hr2wQ : QuadraticMap.polar Q r2 w = 1 := by simpa [Q] using hr2w
  obtain ⟨T, hTmem, hTr, hTspan⟩ :=
    exists_mem_elementaryGroup_apply_span_pair (Q := Q) h2k hQ
      (P := P) (P' := P') hP hrQ hvQ hr2Q hwQ hrvQ hr2wQ
  let Tsub : ↥(elementaryGroup Q) := ⟨T, hTmem⟩
  obtain ⟨g, hg⟩ := exists_omegaMinusLevi_conj_rootD_product hσσ hω Tsub
  refine ⟨g, ?_, ?_⟩
  · simpa [Tsub, hTr] using hg r
  · let f : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) → ModGL Tag.E6 K :=
      fun x => d4RootWord (d4Iota σ ω x)
    let c := MulAut.conj (G := ModGL Tag.E6 K) g.1
    let S : Set (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :=
      (Submodule.span (descentField σ) {r, v} : Set _)
    let S' : Set (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :=
      (Submodule.span (descentField σ) {r2, w} : Set _)
    have hTS : (T : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) →ₗ[descentField σ]
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ)) '' S = S' := by
      dsimp [S, S']
      exact congrArg (fun L : Submodule (descentField σ)
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) =>
          (L : Set (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ))) hTspan
    change c '' (f '' S) = f '' S'
    calc
      c '' (f '' S) = (fun x => c (f x)) '' S := by rw [Set.image_image]
      _ = (fun x => f ((T : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) →ₗ[descentField σ]
            (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ)) x)) '' S := by
        apply Set.image_congr
        intro x _
        simpa [c, f, Tsub] using hg x
      _ = f '' ((T : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) →ₗ[descentField σ]
            (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ)) '' S) := by
        rw [← Set.image_image]
      _ = f '' S' := by rw [hTS]

end Fixed

theorem lieModel_omegaMinusLevi {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LieModel (omegaMinusLevi σ) .POmegaMinus 4 2 f := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := fun c => apply_apply_eq hK hσ c
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have hω' : σE ω ≠ ω := hω
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σE = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact d4_sigma_mul_self hσσ) (d4_sigma_ne_one hω')
  have hk : Nat.card (descentField σE) = 2 ^ f := by
    have h := (CFSG.RankThree.PartOne.KCSpComm.card_descentField Nat.prime_two
      (by omega : 1 ≤ 2 * f) (by rw [hK, ← pow_mul, mul_comm]) hord).2
    rwa [Nat.mul_div_cancel_left f two_pos] at h
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, hf, le_rfl⟩, descentField σE, inferInstance,
    inferInstance, hk, d4MinusB hσσ ω, d4MinusC hσσ ω, d4Minus_irr hσσ hω',
    ⟨(omegaMinusLeviEquiv hσσ hω').trans
      (elementaryMinusStatedEquiv _ _ _ (d4Minus_irr hσσ hω'))⟩⟩

theorem isSimpleGroup_omegaMinusLevi {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsSimpleGroup (omegaMinusLevi σ) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := fun c => apply_apply_eq hK hσ c
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have hω' : σE ω ≠ ω := hω
  have := isSimpleGroup_statedProj_statedOmega_quadMinus (n := 4) (K := descentField σE)
    (by norm_num) (d4Minus_irr hσσ hω')
  exact ((omegaMinusLeviEquiv hσσ hω').trans
    (elementaryMinusStatedEquiv _ _ _ (d4Minus_irr hσσ hω'))).isSimpleGroup

theorem lieModel_d4Levi_of_card {f' : ℕ} (hf' : 1 ≤ f') {K : Type} [Field K]
    (hK' : Nat.card K = 2 ^ f') : LieModel (d4Levi K) .POmegaPlus 4 2 f' := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK']; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf' hK'
  exact lieModel_d4Levi hf' hK'

theorem lieModel_d4Levi_inf_adjointGroup {f' : ℕ} (hf' : 1 ≤ f') {K : Type} [Field K]
    (hK' : Nat.card K = 2 ^ f') :
    LieModel ↥(subsystemGroup TwistTag.E6.tag K setD ⊓ adjointGroup TwistTag.E6.tag K)
      .POmegaPlus 4 2 f' := by
  have h : subsystemGroup TwistTag.E6.tag K setD ⊓ adjointGroup TwistTag.E6.tag K = d4Levi K :=
    inf_of_le_left d4Levi_le_adjointGroup
  rw [h]
  exact lieModel_d4Levi_of_card hf' hK'

theorem omegaMinusLevi_eq_of_card {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    omegaMinusLevi σ = subsystemGroup TwistTag.E6.tag K setD ⊓ twistedFixedGroup TwistTag.E6 K σ := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := fun c => apply_apply_eq hK hσ c
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  exact omegaMinusLevi_eq hσσ (ω := ω) hω

theorem xUnit_mem_omegaMinusLevi {K : Type} [Field K] {σ : K →+* K} {k : Fin 4}
    (hk : k = 0 ∨ k = 1) {c : K} (hc : σ c = c) :
    xUnit TwistTag.E6.tag K (jD k) c ∈ omegaMinusLevi σ := by
  have hρ : TwistTag.E6.perm (jD k) = jD k := by
    rw [perm_jD]
    rcases hk with rfl | rfl <;> rfl
  exact ⟨xUnit_mem_d4Levi k c, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (xUnit_mem_graphFixedPosUnipotent hρ hc)⟩

theorem yUnit_mem_omegaMinusLevi {K : Type} [Field K] {σ : K →+* K} {k : Fin 4}
    (hk : k = 0 ∨ k = 1) {c : K} (hc : σ c = c) :
    yUnit TwistTag.E6.tag K (jD k) c ∈ omegaMinusLevi σ := by
  have hρ : TwistTag.E6.perm (jD k) = jD k := by
    rw [perm_jD]
    rcases hk with rfl | rfl <;> rfl
  exact ⟨yUnit_mem_d4Levi k c, graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
    (yUnit_mem_graphFixedNegUnipotent hρ hc)⟩

end LieModel

end CFSG.SeitzReduction.TwistedE6Pilot
