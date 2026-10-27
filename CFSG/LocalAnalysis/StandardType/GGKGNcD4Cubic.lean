module

public import CFSG.LocalAnalysis.StandardType.GGKGNotCDefs

import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds2
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerTw
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.StandardType.KG

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice CFSG.RankThree.Chevalley CFSG.RankThree.E6
  CFSG.LieType.Steinberg.Adjoint CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
open CFSG CFSG.Blueprint CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL
open scoped Matrix MatrixGroups

theorem kgNotC_graphFixedRootGroup_cubic
    {ℓ : ℕ}
    {f' : ℕ}
    (hℓ : Nat.Prime ℓ)
    (hf' : 1 ≤ f')
    (K : Type)
    [Field K]
    [Finite K]
    (hK : Nat.card K = (ℓ ^ f') ^ 3)
    (σ : K ≃+* K)
    {r : ℕ}
    (hr : r = 1 ∨ r = 2)
    (hσ : ∀ (c : K), (σ : K → K) c = c ^ (ℓ ^ f') ^ r) :
    CFSG.StandardType.KG.KGNotCLieType ℓ
      ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K
        σ.toRingHom) := by
  classical
  obtain ⟨σ₁, hσ₁, ⟨e⟩⟩ : ∃ σ₁ : K ≃+* K, (∀ c, σ₁ c = c ^ (ℓ ^ f')) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := by
    rcases hr with rfl | rfl
    · exact ⟨σ, fun c => by rw [hσ, pow_one], ⟨MulEquiv.refl _⟩⟩
    · have h₁ : ∀ c, σ.symm c = c ^ (ℓ ^ f') := fun c => by
        rw [RingEquiv.symm_apply_eq, hσ, ← pow_mul,
          show ℓ ^ f' * (ℓ ^ f') ^ 2 = (ℓ ^ f') ^ 3 by ring]
        have : Fintype K := Fintype.ofFinite K
        have hq : Fintype.card K = (ℓ ^ f') ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
        rw [← hq]
        exact (FiniteField.pow_card c).symm
      exact ⟨σ.symm, h₁,
        CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_mulEquiv_graphFixedRootGroup_inv_D4
          K σ σ.symm (fun c => σ.apply_symm_apply c)⟩
  have hK' : Nat.card K = (ℓ ^ f') ^ TwistTag.D4.order := hK
  obtain ⟨ψ⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.D4 hℓ hf' K
    hK' σ₁.toRingHom (fun c => hσ₁ c)
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  let e0 : (↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸
      Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hadm : CFSG.Open.StatedLieAdmissible .trialityD4 0 ℓ f' := ⟨hℓ, hf', rfl⟩
  refine ⟨.trialityD4, 0, f', by decide, Or.inr (Or.inl ⟨rfl, by decide, hadm, ?_⟩)⟩
  exact ⟨K, inferInstance, inferInstance, hK', σ₁.toRingHom, fun c => hσ₁ c,
    ⟨(e0.trans e).trans ψ.symm⟩⟩

theorem kgNotC_tauDatum
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    {f : ℕ}
    (hf : 1 ≤ f) :
    CFSG.StandardType.KG.KGNotCLieType ℓ
      ↥(CFSG.RankThree.Lattice.GenFixedRootDatum.orbitGroup
          (CFSG.RankThree.PartOne.KD4L.tauDatum L ℓ f hf :
            CFSG.RankThree.Lattice.GenFixedRootDatum CFSG.Blueprint.Chevalley.Tag.E6 ℓ L
              (Multiplicative (Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ)))) := by
  classical
  have h1S : (1 : Fin Tag.E6.rank) ∈ d4Support := by
    change (1 : Fin Tag.E6.rank) ≠ 0 ∧ (1 : Fin Tag.E6.rank) ≠ 5
    decide
  have h2S : (2 : Fin Tag.E6.rank) ∈ d4Support := by
    change (2 : Fin Tag.E6.rank) ≠ 0 ∧ (2 : Fin Tag.E6.rank) ≠ 5
    decide
  have h3S : (3 : Fin Tag.E6.rank) ∈ d4Support := by
    change (3 : Fin Tag.E6.rank) ≠ 0 ∧ (3 : Fin Tag.E6.rank) ≠ 5
    decide
  have h4S : (4 : Fin Tag.E6.rank) ∈ d4Support := by
    change (4 : Fin Tag.E6.rank) ≠ 0 ∧ (4 : Fin Tag.E6.rank) ≠ 5
    decide
  refine ⟨.POmegaMinus, 4, _, by decide, lieModel_orbitGroup_of_datum_four (τ := Tag.E6)
    (Or.inr (Or.inl rfl)) (tauDatum L ℓ f hf) (m := 4) le_rfl
    (CompsPTwoDChainO.twoDChainRecog_all hf le_rfl) bTau bTau_root bTau_injective iform_bTau
    ?_ ?_ ?_ ?_ ?_⟩
  ·
    ext β
    constructor
    · intro hβ
      rw [GenFixedRootDatum.simpleRootsJ_eq] at hβ
      obtain ⟨j, hj, rfl⟩ := d4Aux.mem_unionSimpleRoots_iff.1 hβ
      have hjS : j ∈ d4Support := d4Aux_support ▸ hj
      rcases d4Support_cases hjS with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact single_mem_simpleRootsJ hf h1S
      · exact single_mem_simpleRootsJ hf h3S
      · exact single_mem_simpleRootsJ hf h2S
      · exact single_mem_simpleRootsJ hf h4S
  ·
    intro j hj
    fin_cases j
    · exact (theta_single_tau hf h1S).trans (by rw [gam_one]; rfl)
    · exact (theta_single_tau hf h3S).trans (by rw [gam_three]; rfl)
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  · exact (theta_single_tau hf h2S).trans (by rw [gam_two]; rfl)
  · exact (theta_single_tau hf h4S).trans (by rw [gam_four]; rfl)
  ·
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
      | (exfalso; revert hjk; decide)
      | exact exists_frame_E6 (by decide)

theorem kgNotC_fixE6_dN
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    {f : ℕ}
    (hf : 1 ≤ f) :
    CFSG.StandardType.KG.KGNotCLieType ℓ
      ↥(CFSG.RankThree.PartOne.KD4L.fixE6 ℓ f (CFSG.RankThree.PartOne.KD4L.dN L)) := by
  rw [fixE6_dN hf]
  exact kgNotC_tauDatum hf

theorem exists_fix_swap13_kgNotC
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    {f : ℕ}
    (hf : 1 ≤ f) :
    ∃ (n₂ : CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L),
      CFSG.RankThree.PartOne.KD4L.Acts n₂ (Equiv.swap 1 3) ∧
        CFSG.RankThree.PartOne.KD4L.E6Fix f n₂ ∧
          CFSG.StandardType.KG.KGNotCLieType ℓ ↥(CFSG.RankThree.PartOne.KD4L.fixE6 ℓ f n₂) := by
  exact ⟨dN L, acts_dN, E6Fix_dN hf, kgNotC_fixE6_dN hf⟩

theorem exists_fix_swap03_kgNotC
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    {f : ℕ}
    (hf : 1 ≤ f) :
    ∃ (n₂ : CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L),
      CFSG.RankThree.PartOne.KD4L.Acts n₂ (Equiv.swap 0 3) ∧
        CFSG.RankThree.PartOne.KD4L.E6Fix f n₂ ∧
          CFSG.StandardType.KG.KGNotCLieType ℓ ↥(CFSG.RankThree.PartOne.KD4L.fixE6 ℓ f n₂) := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)
  · rw [fixE6_conj map_conj_d4TrialityRep frob_d4TrialityRep]
    exact KGNotCLieType.map_conj _ (kgNotC_fixE6_dN hf)

theorem exists_fix_swap01_kgNotC
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    {f : ℕ}
    (hf : 1 ≤ f) :
    ∃ (n₂ : CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L),
      CFSG.RankThree.PartOne.KD4L.Acts n₂ (Equiv.swap 0 1) ∧
        CFSG.RankThree.PartOne.KD4L.E6Fix f n₂ ∧
          CFSG.StandardType.KG.KGNotCLieType ℓ ↥(CFSG.RankThree.PartOne.KD4L.fixE6 ℓ f n₂) := by
  have hR := map_conj_mul (L := L) map_conj_d4TrialityRep map_conj_d4TrialityRep
  have hF : Units.map (entrywiseHom (iterateFrobenius L ℓ f))
      (d4TrialityRep L * d4TrialityRep L) = d4TrialityRep L * d4TrialityRep L := by
    rw [map_mul, frob_d4TrialityRep]
  refine ⟨(d4TrialityRep L * d4TrialityRep L) * dN L * (d4TrialityRep L * d4TrialityRep L)⁻¹,
    ?_, ?_, ?_⟩
  · have h := Acts.conj ((acts_d4TrialityRep (L := L)).mul (acts_d4TrialityRep (L := L)))
      (acts_dN (L := L))
    rwa [rho_sq_conj_swap] at h
  · exact E6Fix.conj hR hF (E6Fix_dN hf)
  · rw [fixE6_conj hR hF]
    exact KGNotCLieType.map_conj _ (kgNotC_fixE6_dN hf)

theorem kgNotC_layer_swap
    {τ : CFSG.Blueprint.Chevalley.Tag}
    [hτ : CFSG.RankThree.PartOne.KD4T.E6Sub τ]
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    {f : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    {n₁ : CFSG.Blueprint.Chevalley.ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)}
    {σ : Equiv.Perm (Fin CFSG.Blueprint.Chevalley.Tag.D4.rank)}
    {n₂ : CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L}
    (hstd : CFSG.RankThree.PartOne.KD4L.StdSwap n₁ π σ)
    (h₂ : CFSG.RankThree.PartOne.KD4L.Acts n₂ σ)
    (hRL : CFSG.StandardType.KG.KGNotCLieType ℓ ↥(CFSG.RankThree.PartOne.KD4L.fixE6 ℓ f n₂))
    {n : CFSG.Blueprint.Chevalley.ModGL τ L}
    {h : CFSG.Blueprint.Chevalley.ModGL τ L}
    (hh : h ∈ CFSG.LieType.Chevalley.subsystemGroup τ L (CFSG.RankThree.PartOne.KD4T.d4Set τ))
    (hlang : ∀ (g : CFSG.Blueprint.Chevalley.ModGL τ L),
      n *
              (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)) :
                  (Module.End L (CFSG.Blueprint.Chevalley.RootModule τ L))ˣ →
                    (Module.End L (CFSG.Blueprint.Chevalley.RootModule τ L))ˣ)
                g *
            n⁻¹ =
          g ↔
        n₁ *
              (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)) :
                  (Module.End L (CFSG.Blueprint.Chevalley.RootModule τ L))ˣ →
                    (Module.End L (CFSG.Blueprint.Chevalley.RootModule τ L))ˣ)
                (h * g * h⁻¹) *
            n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (CFSG.Blueprint.Chevalley.ModGL τ L)}
    (hP : P =
      CFSG.LieType.Chevalley.subsystemGroup τ L (CFSG.RankThree.PartOne.KD4T.d4Set τ) ⊓
        CFSG.RankThree.PartOne.KE.twistedFixedPoints n
          (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)))) :
    CFSG.StandardType.KG.KGNotCLieType ℓ ↥P := by
  obtain ⟨eP⟩ := nonempty_equiv_stdLayer hh hlang hP
  exact hRL.of_mulEquiv (eP.trans (hstd.layerEquiv (ℓ := ℓ) (f := f) h₂)).symm

theorem kgNotC_layer_triality
    {τ : CFSG.Blueprint.Chevalley.Tag}
    [hτ : CFSG.RankThree.PartOne.KD4T.E6Sub τ]
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    {f : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    {n₁ : CFSG.Blueprint.Chevalley.ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)}
    {e : ℕ}
    (hf : 1 ≤ f)
    (hstd : CFSG.RankThree.PartOne.KD4L.StdTwist n₁ π e)
    {n : CFSG.Blueprint.Chevalley.ModGL τ L}
    {h : CFSG.Blueprint.Chevalley.ModGL τ L}
    (hh : h ∈ CFSG.LieType.Chevalley.subsystemGroup τ L (CFSG.RankThree.PartOne.KD4T.d4Set τ))
    (hlang : ∀ (g : CFSG.Blueprint.Chevalley.ModGL τ L),
      n *
              (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)) :
                  (Module.End L (CFSG.Blueprint.Chevalley.RootModule τ L))ˣ →
                    (Module.End L (CFSG.Blueprint.Chevalley.RootModule τ L))ˣ)
                g *
            n⁻¹ =
          g ↔
        n₁ *
              (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)) :
                  (Module.End L (CFSG.Blueprint.Chevalley.RootModule τ L))ˣ →
                    (Module.End L (CFSG.Blueprint.Chevalley.RootModule τ L))ˣ)
                (h * g * h⁻¹) *
            n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (CFSG.Blueprint.Chevalley.ModGL τ L)}
    (hP : P =
      CFSG.LieType.Chevalley.subsystemGroup τ L (CFSG.RankThree.PartOne.KD4T.d4Set τ) ⊓
        CFSG.RankThree.PartOne.KE.twistedFixedPoints n
          (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)))) :
    CFSG.StandardType.KG.KGNotCLieType ℓ ↥P := by
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨eP⟩⟩ := layer_graph_equiv_of_standard hf hstd hh hlang hP
  exact (kgNotC_graphFixedRootGroup_cubic (Fact.out : ℓ.Prime) hf K hKc σ hstd.he
    hσ).of_mulEquiv eP.symm

theorem trialityLayerKGNotC_generic
    {τ : CFSG.Blueprint.Chevalley.Tag}
    [hτ : CFSG.RankThree.PartOne.KD4T.E6Sub τ]
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    {f : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    (hf : 1 ≤ f)
    (π : Equiv.Perm (Fin τ.rank))
    (e : ℕ)
    (he : e = 1 ∨ e = 2)
    (hπe : ∀ (k : Fin CFSG.Blueprint.Chevalley.Tag.D4.rank),
      (π : Fin τ.rank → Fin τ.rank) (CFSG.RankThree.PartOne.KD4T.d4Id k) =
        CFSG.RankThree.PartOne.KD4T.d4Id (CFSG.RankThree.PartOne.KD4L.rhoE e k))
    (hπ : ∀ i ∈ CFSG.RankThree.PartOne.KD4T.d4Set τ,
      (π : Fin τ.rank → Fin τ.rank) i ∈ CFSG.RankThree.PartOne.KD4T.d4Set τ)
    (hπ' : ∀ i ∈ CFSG.RankThree.PartOne.KD4T.d4Set τ,
      (Equiv.symm π : Fin τ.rank → Fin τ.rank) i ∈ CFSG.RankThree.PartOne.KD4T.d4Set τ)
    (n : CFSG.Blueprint.Chevalley.ModGL τ L)
    (hn : n ∈ CFSG.LieType.Chevalley.monomialSubgroup τ L)
    (hact : ∃ u ∈ CFSG.LieType.Chevalley.parabolicWeylGroup τ (CFSG.RankThree.PartOne.KE.d4Nodes τ),
      ∀ α ∈ CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ),
        (CFSG.LieType.Chevalley.weylQuotientHom τ L :
                ↥(CFSG.LieType.Chevalley.monomialSubgroup τ L) → CFSG.LieType.Chevalley.WeylGroup τ)
              ⟨n, hn⟩ •
            α =
          u • CFSG.Blueprint.Chevalley.permLattice π α)
    (P : Subgroup (CFSG.Blueprint.Chevalley.ModGL τ L))
    (hP : P =
      CFSG.Blueprint.Chevalley.rootSpan τ L
          (CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ)) ⊓
        CFSG.RankThree.PartOne.KE.twistedFixedPoints n
          (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)))) :
    CFSG.StandardType.KG.KGNotCLieType ℓ ↥P := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact kgNotC_layer_triality hf hstd hh hlang hP

theorem swapLayerKGNotC_generic
    {τ : CFSG.Blueprint.Chevalley.Tag}
    [hτ : CFSG.RankThree.PartOne.KD4T.E6Sub τ]
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    {f : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    (hf : 1 ≤ f)
    (σ : Equiv.Perm (Fin CFSG.Blueprint.Chevalley.Tag.D4.rank))
    (hE : ∃ (n₂ : CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L),
      CFSG.RankThree.PartOne.KD4L.Acts n₂ σ ∧
        CFSG.RankThree.PartOne.KD4L.E6Fix f n₂ ∧
          CFSG.StandardType.KG.KGNotCLieType ℓ ↥(CFSG.RankThree.PartOne.KD4L.fixE6 ℓ f n₂))
    (π : Equiv.Perm (Fin τ.rank))
    (hπσ : ∀ (k : Fin CFSG.Blueprint.Chevalley.Tag.D4.rank),
      (π : Fin τ.rank → Fin τ.rank) (CFSG.RankThree.PartOne.KD4T.d4Id k) =
        CFSG.RankThree.PartOne.KD4T.d4Id
          ((σ : Fin CFSG.Blueprint.Chevalley.Tag.D4.rank →
              Fin CFSG.Blueprint.Chevalley.Tag.D4.rank) k))
    (hπ : ∀ i ∈ CFSG.RankThree.PartOne.KD4T.d4Set τ,
      (π : Fin τ.rank → Fin τ.rank) i ∈ CFSG.RankThree.PartOne.KD4T.d4Set τ)
    (hπ' : ∀ i ∈ CFSG.RankThree.PartOne.KD4T.d4Set τ,
      (Equiv.symm π : Fin τ.rank → Fin τ.rank) i ∈ CFSG.RankThree.PartOne.KD4T.d4Set τ)
    (n : CFSG.Blueprint.Chevalley.ModGL τ L)
    (hn : n ∈ CFSG.LieType.Chevalley.monomialSubgroup τ L)
    (hact : ∃ u ∈ CFSG.LieType.Chevalley.parabolicWeylGroup τ (CFSG.RankThree.PartOne.KE.d4Nodes τ),
      ∀ α ∈ CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ),
        (CFSG.LieType.Chevalley.weylQuotientHom τ L :
                ↥(CFSG.LieType.Chevalley.monomialSubgroup τ L) → CFSG.LieType.Chevalley.WeylGroup τ)
              ⟨n, hn⟩ •
            α =
          u • CFSG.Blueprint.Chevalley.permLattice π α)
    (P : Subgroup (CFSG.Blueprint.Chevalley.ModGL τ L))
    (hP : P =
      CFSG.Blueprint.Chevalley.rootSpan τ L
          (CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ)) ⊓
        CFSG.RankThree.PartOne.KE.twistedFixedPoints n
          (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)))) :
    CFSG.StandardType.KG.KGNotCLieType ℓ ↥P := by
  obtain ⟨n₂, h₂, -, hRL⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact kgNotC_layer_swap hstd h₂ hRL hh hlang hP

end CFSG.StandardType.KG
