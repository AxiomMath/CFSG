module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_9_CalT
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_15
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection11.PFsection11_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_5_to_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.9), Delta correction
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

public theorem section14_theorem_14_9_late_type_T1_active_sigma_mem_active_omegaSigma
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p q : ℕ}
    (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ) :
    ∀ ξ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup ξ →
        σ ξ ∈ (Finset.univ.image fun ij : Fin q × Fin p => σ (ω ij.1 ij.2)) := by
  classical
  rcases hNotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωNat⟩
  intro ξ hξ
  rcases hωFin.all_irreducibles ξ hξ with ⟨i, j, hξeq⟩
  refine Finset.mem_image.mpr ⟨(i, j), by simp, ?_⟩
  calc
    σ (ω i j) = σ (ωFin i j) := by rw [hωNat i j i.2 j.2]
    _ = σ ξ := by rw [← hξeq]

/-- Endpoint threading for the PF `(14.9)` use of Hypothesis `(5.2)`.

Once a PF `(3.9)` transport equality identifies each global `σ ξ` with the
T-side Section `(4.6)` map applied to the transported character, the Section 8
full `(5.2)` table supplies the required finite omega-sigma image membership.
-/
public theorem section14_theorem_14_9_late_type_T1_fullData_omegaSigma_mem_of_transport_eq
    {G : Type u} [Group G] [Finite G]
    {Tmax Ms W1 W2 : Subgroup G}
    {A : Set G}
    (d52 : Section8.section8Hypothesis52FullData Tmax Ms W1 W2 A)
    {Wsrc : Subgroup G}
    (σsrc : Section1.ClassFunction Wsrc →ₗ[ℂ] Section1.ClassFunction G)
    (e : Wsrc ≃* d52.W)
    (hσeq : ∀ ξ : Section1.ClassFunction Wsrc,
      Section1.IsIrreducibleCharacterOnGroup ξ →
        σsrc ξ =
          d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)) :
    letI : Fintype d52.I := d52.instFintypeI
    letI : Fintype d52.J := d52.instFintypeJ
    letI : DecidableEq d52.I := d52.instDecidableEqI
    letI : DecidableEq d52.J := d52.instDecidableEqJ
    ∀ ξ : Section1.ClassFunction Wsrc,
      Section1.IsIrreducibleCharacterOnGroup ξ →
        σsrc ξ ∈
          (Finset.univ.image fun p : d52.I × d52.J =>
            d52.sigma (d52.omega p.1 p.2)) := by
  classical
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  rcases d52.fullHypothesis with
    ⟨_h46, _hW2K, _h31, _hIsoFull, _hVirtFull, _hClassFull, _hPrinFull,
      _h22A, hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc,
      _hTauA0, _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  intro ξ hξ
  have htransportIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section6.theorem_6_8_transportClassFunction_irreducible e hξ
  rcases hω.all_irreducibles
      (Section6.theorem_6_8_transportClassFunction e ξ)
      htransportIrr with
    ⟨i, j, htransport_eq⟩
  refine Finset.mem_image.mpr ⟨(i, j), by simp, ?_⟩
  calc
    d52.sigma (d52.omega i j) =
        d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) := by
          rw [← htransport_eq]
    _ = σsrc ξ := (hσeq ξ hξ).symm

/-- The concrete subgroup equivalence behind the PF `(14.9)` T-side table.

Case B supplies `W = W1 ⊔ W2` in `G`, the T-Type-P data places both factors
inside `Tmax`, and the Section 8 full data identifies its table subgroup with
`(W2 ⊔ W1).subgroupOf Tmax`.  This packages those equalities as the
transport equivalence used before invoking PF `(3.9)`. -/
public theorem section14_theorem_14_9_late_type_T1_fullData_global_to_local_equiv
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (d52 : Section8.section8Hypothesis52FullData Tmax (Q ⊔ V) W2 W1
      (Section8.section8CentralizerUnion
        (ambientDerivedSubgroup Tmax) (Q ⊔ V))) :
    ∃ e : W ≃* d52.W,
      ∀ x : W, (((e x : d52.W) : Tmax) : G) = (x : G) := by
  classical
  have hsource := hctx.1
  unfold Section13.hypothesis_13_1_sourceData at hsource
  rcases hsource with
    ⟨hcaseB, _hSTypeP, _hTtypePsrc, _hp_card, _hq_card, _hC, _hD,
      _hc, _hd, _hu, _hv, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hChar, _hDiff, _hZero, _hConj, _hConjTau, _hChoice,
      _hmin, _hFourSixS, _hFourSixT⟩
  have hprod : section12InternalDirectProduct W1 W2 W := hcaseB.1
  have hW_eq : W = W1 ⊔ W2 := hprod.2.2.1
  have hW_swap : W = W2 ⊔ W1 := by
    simp [hW_eq, sup_comm]
  rcases hTtypeP with
    ⟨_hQMF, _hW2cyc, _hW2ne, hW2Hall, _hTcomp, _hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit, _hFitLe,
      hW1leQSecond, _hW1cyc, _hW1ne, _hCentralizer, _hNormalizer⟩
  have hQleT : Q ≤ Tmax :=
    hDerComp.1.trans (section12_ambientDerivedSubgroup_le (G := G) (E := Tmax))
  have hW2leT : W2 ≤ Tmax := hW2Hall.1
  have hW1leT : W1 ≤ Tmax :=
    ((le_inf_iff.mp hW1leQSecond).1).trans hQleT
  have hWsupT : W2 ⊔ W1 ≤ Tmax := sup_le hW2leT hW1leT
  let eSup : W ≃* (W2 ⊔ W1 : Subgroup G) :=
    MulEquiv.subgroupCongr hW_swap
  let eSub : (W2 ⊔ W1 : Subgroup G) ≃* ((W2 ⊔ W1).subgroupOf Tmax) :=
    (Subgroup.subgroupOfEquivOfLe (H := W2 ⊔ W1) (K := Tmax) hWsupT).symm
  let eLoc : ((W2 ⊔ W1).subgroupOf Tmax) ≃* d52.W :=
    MulEquiv.subgroupCongr d52.W_eq.symm
  let e : W ≃* d52.W := (eSup.trans eSub).trans eLoc
  have he_apply : ∀ x : W, (((e x : d52.W) : Tmax) : G) = (x : G) := by
    intro x
    simp [e, eSup, eSub, eLoc, Subgroup.subgroupOfEquivOfLe,
      MulEquiv.subgroupCongr_apply]
  exact ⟨e, he_apply⟩

/-- PF `(3.9)(a)` bridge for the Section 8 full T-side table.

If the T-side image of the transported irreducible agrees pointwise with the
original irreducible on the global cyclic-TI set, then PF `(3.9)(a)` identifies
it with the global Section 13 Dade image.  This isolates the remaining
textbook `cycTIisoC` work to a pointwise agreement statement. -/
public theorem section14_theorem_14_9_late_type_T1_fullData_transport_eq_of_cyclicTI_agreement
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p q : ℕ}
    (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    {Ms : Subgroup G} {A : Set G}
    (d52 : Section8.section8Hypothesis52FullData Tmax Ms W2 W1 A)
    (e : W ≃* d52.W)
    {ξ : Section1.ClassFunction W}
    (hξ : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hVagree :
      ∀ x : G, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) x =
          ξ ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) :
    σ ξ = d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) := by
  classical
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  rcases hNotation with
    ⟨hωData, hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨h31, h0q, h0p, ωFin, hωFin, _hωNat⟩
  rcases Section3.pf35_data_of_theorem_3_2_map_statement hωFin σ hσmap with
    ⟨χ, horth, hsigned, h00, hInd, hσω⟩
  have hσ_eq : σ = Section3.sigmaOfPF35 ωFin χ :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, h0q⟩) (j0 := ⟨0, h0p⟩)
      (ω := ωFin) (χ := χ) h31 hωFin hσω
  rcases d52.fullHypothesis with
    ⟨_h46, _hW2K, _h31local, hIsoFull, hVirtFull, _hClassFull, _hPrinFull,
      _h22A, _hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc,
      _hTauA0, _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  have htransportIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section6.theorem_6_8_transportClassFunction_irreducible e hξ
  have hξ_class : Section1.IsClassFunction ξ := by
    rcases hξ with ⟨_n, ρ, _hρirr, hξeq⟩
    rw [hξeq]
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have htransportClass :
      Section1.IsClassFunction
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section6.theorem_6_8_transportClassFunction_isClass e hξ_class
  have htransportVirt :
      Theory.Character.IsVirtualCharacter
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup htransportIrr
  have hImageVirt :
      Theory.Character.IsVirtualCharacter
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)) :=
    hVirtFull _ htransportVirt
  have hselfW : Section1.scalarProduct W ξ ξ = 1 :=
    Section1.scalarProduct_irreducibleCharacter_self hξ
  have hself :
      Section1.scalarProduct G
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ))
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)) = 1 := by
    calc
      Section1.scalarProduct G
          (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ))
          (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)) =
        Section1.scalarProduct d52.W
          (Section6.theorem_6_8_transportClassFunction e ξ)
          (Section6.theorem_6_8_transportClassFunction e ξ) :=
          hIsoFull _ _ htransportClass htransportClass
      _ = Section1.scalarProduct W ξ ξ :=
          Section6.theorem_6_8_scalarProduct_transportClassFunction e ξ ξ
      _ = 1 := hselfW
  have hXsigned :
      Section3.IsSignedIrreducibleCharacter
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hImageVirt hself
  have hXeq :
      d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) =
        Section3.sigmaOfPF35 ωFin χ ξ :=
    Section3.proposition_3_9_a_uniqueness_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, h0q⟩) (j0 := ⟨0, h0p⟩)
      (ω := ωFin) (χ := χ) h31 hωFin horth hsigned h00 hInd
      hξ hXsigned hVagree
  calc
    σ ξ = Section3.sigmaOfPF35 ωFin χ ξ := by rw [hσ_eq]
    _ = d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) := hXeq.symm


public theorem section14_theorem_14_9_late_type_T1_active_sigma_mem_local_omegaSigma_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_ : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_ : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    (d52 : Section8.section8Hypothesis52FullData Tmax (Q ⊔ V) W2 W1
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Tmax) (Q ⊔ V)))
    (_ : d52.tau = τT)
    (hCompat :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      letI : DecidableEq d52.I := d52.instDecidableEqI
      letI : DecidableEq d52.J := d52.instDecidableEqJ
      ∀ ξ : Section1.ClassFunction W,
        Section1.IsIrreducibleCharacterOnGroup ξ →
          σ ξ ∈
            (Finset.univ.image fun p : d52.I × d52.J =>
              d52.sigma (d52.omega p.1 p.2))) :
    letI : Fintype d52.I := d52.instFintypeI
    letI : Fintype d52.J := d52.instFintypeJ
    letI : DecidableEq d52.I := d52.instDecidableEqI
    letI : DecidableEq d52.J := d52.instDecidableEqJ
    ∀ ξ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup ξ →
        σ ξ ∈
          (Finset.univ.image fun p : d52.I × d52.J =>
            d52.sigma (d52.omega p.1 p.2)) := by
  classical
  simpa using hCompat

public theorem section14_theorem_14_9_late_type_T1_calt1_hypothesis52_fullData_omegaSigma_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ) :
    ∃ d52 : Section8.section8Hypothesis52FullData Tmax (Q ⊔ V) W2 W1
        (Section8.section8CentralizerUnion
          (ambientDerivedSubgroup Tmax) (Q ⊔ V)),
      d52.tau = τT ∧
        letI : Fintype d52.I := d52.instFintypeI
        letI : Fintype d52.J := d52.instFintypeJ
        letI : DecidableEq d52.I := d52.instDecidableEqI
        letI : DecidableEq d52.J := d52.instDecidableEqJ
        ∀ ξ : Section1.ClassFunction W,
          Section1.IsIrreducibleCharacterOnGroup ξ →
            σ ξ ∈
              (Finset.univ.image fun p : d52.I × d52.J =>
                d52.sigma (d52.omega p.1 p.2)) := by
  classical
  rcases
      section14_theorem_14_9_late_type_T1_calt1_hypothesis52_fullData_source_bridge
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP with
    ⟨d52, hd52τ, hSigmaAgree⟩
  refine ⟨d52, hd52τ, ?_⟩
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  have hΩactive :
      ∀ ξ : Section1.ClassFunction W,
        Section1.IsIrreducibleCharacterOnGroup ξ →
          σ ξ ∈
            (Finset.univ.image fun ij : Fin q × Fin p => σ (ω ij.1 ij.2)) :=
    section14_theorem_14_9_late_type_T1_active_sigma_mem_active_omegaSigma
      hNotation
  rcases
      section14_theorem_14_9_late_type_T1_fullData_global_to_local_equiv
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hctx hTtypeP d52 with
    ⟨e, he⟩
  have hσeq :
      ∀ ξ : Section1.ClassFunction W,
        Section1.IsIrreducibleCharacterOnGroup ξ →
          σ ξ =
            d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) := by
    intro ξ hξ
    have _hΩactive_mem := hΩactive ξ hξ
    have hVagree :
        ∀ x : G, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
          d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) x =
            ξ ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
      intro x hx
      let xW : W := ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
      let y : d52.W := e xW
      have hyG : (((y : d52.W) : Tmax) : G) = x := by
        simpa [xW, y] using he xW
      have hyLocal :
          ((y : d52.W) : Tmax) ∈
            Section3.cyclicTISet (W2.subgroupOf Tmax) (W1.subgroupOf Tmax)
              d52.W := by
        rw [Section3.cyclicTISet_mem_iff]
        refine ⟨y.2, ?_, ?_⟩
        · intro hyW2
          have hxW2 : x ∈ (W2 : Set G) := by
            have hyW2G : (((y : d52.W) : Tmax) : G) ∈ (W2 : Set G) :=
              Subgroup.mem_subgroupOf.mp hyW2
            simpa [hyG] using hyW2G
          exact Section3.cyclicTISet_not_mem_right W1 W2 W hx hxW2
        · intro hyW1
          have hxW1 : x ∈ (W1 : Set G) := by
            have hyW1G : (((y : d52.W) : Tmax) : G) ∈ (W1 : Set G) :=
              Subgroup.mem_subgroupOf.mp hyW1
            simpa [hyG] using hyW1G
          exact Section3.cyclicTISet_not_mem_left W1 W2 W hx hxW1
      have htransportClass :
          Section1.IsClassFunction
            (Section6.theorem_6_8_transportClassFunction e ξ) := by
        have hξClass : Section1.IsClassFunction ξ := by
          rcases hξ with ⟨_n, ρ, _hρirr, hξeq⟩
          rw [hξeq]
          intro x g
          simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
        exact Section6.theorem_6_8_transportClassFunction_isClass e hξClass
      have hlocal :=
        hSigmaAgree
          (Section6.theorem_6_8_transportClassFunction e ξ)
          htransportClass y hyLocal
      have hright :
          Section6.theorem_6_8_transportClassFunction e ξ
              ⟨(y : Tmax), Section3.cyclicTISet_subset
                (W2.subgroupOf Tmax) (W1.subgroupOf Tmax) d52.W hyLocal⟩ =
            ξ xW := by
        change ξ (e.symm
          ⟨(y : Tmax), Section3.cyclicTISet_subset
            (W2.subgroupOf Tmax) (W1.subgroupOf Tmax) d52.W hyLocal⟩) = ξ xW
        congr 1
        simp [xW, y]
      calc
        d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) x =
            d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)
              (((y : d52.W) : Tmax) : G) := by
                rw [hyG]
        _ =
            Section6.theorem_6_8_transportClassFunction e ξ
              ⟨(y : Tmax), Section3.cyclicTISet_subset
                (W2.subgroupOf Tmax) (W1.subgroupOf Tmax) d52.W hyLocal⟩ := hlocal
        _ = ξ xW := hright
    exact
      section14_theorem_14_9_late_type_T1_fullData_transport_eq_of_cyclicTI_agreement
        hNotation d52 e hξ hVagree
  exact
    section14_theorem_14_9_late_type_T1_fullData_omegaSigma_mem_of_transport_eq
      d52 σ e hσeq


public theorem section14_principalInducedCharacter_sub_irreducible_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G} {ζ : Section1.ClassFunction L}
    (hζ : Section1.IsIrreducibleCharacterOnGroup ζ) :
    Theory.Character.IsVirtualCharacter (Section7.principalInducedCharacter L H - ζ) := by
  have hprincipalVirt :
      Theory.Character.IsVirtualCharacter (Section7.principalInducedCharacter L H) := by
    unfold Section7.principalInducedCharacter
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      (H.subgroupOf L) Section3.isVirtualCharacter_principalCharacter
  exact Section3.isVirtualCharacter_sub hprincipalVirt
    (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hζ)

public theorem section14_isClassFunction_of_irreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨_n, ρ, _hirr, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

public theorem section14_theorem_14_9_late_type_T1_tauT1_mem_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    {Tmax : Subgroup G}
    {T1T : Finset (Section1.ClassFunction Tmax)}
    {τT τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    (hcoh : Section6.coherentExtension T1T τT τT1)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    Theory.Character.IsVirtualCharacter (τT1 ζ) :=
  hcoh.2.1 ζ (Section5.integerSpan_of_mem T1T hζ)

public theorem section14_theorem_14_9_late_type_T1_delta_isVirtualCharacter_of_betaT0
    {G : Type u} [Group G] [Finite G]
    {Tmax : Subgroup G}
    {τT τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {βT0 ζ : Section1.ClassFunction Tmax}
    (hβT0 : Theory.Character.IsVirtualCharacter (τT βT0))
    (hζ : Theory.Character.IsVirtualCharacter (τT1 ζ)) :
    Theory.Character.IsVirtualCharacter
      (τT βT0 - Section1.principalCharacter G + τT1 ζ) := by
    exact Section3.isVirtualCharacter_add
      (Section3.isVirtualCharacter_sub hβT0
        Section3.isVirtualCharacter_principalCharacter) hζ


public theorem section14_theorem_14_9_late_type_T1_book_AZero_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1) :
    ∃ A0book : Set G, ∃ H_A0 : G → Subgroup G,
      ∃ hA0M : Section2.Hypothesis2 A0book Tmax H_A0,
        (∀ l : Tmax,
          (l : G) ∈ section16NonidentityElements ((Q ⊔ V : Subgroup G) : Set G) →
            (l : G) ∈ A0book) ∧
        ∀ α : Section1.ClassFunction Tmax,
          τT α = Section2.dadeTransform H_A0 hA0M.subset_L α := by
  classical
  have hFourSixT : Section13.typePFourSixTauSourceData Tmax Q V W2 W1 τT := by
    have hsource := hctx.1
    unfold Section13.hypothesis_13_1_sourceData at hsource
    tauto
  rcases hFourSixT with
    ⟨I, instI, decI, J, instJ, decJ, W46, A, A0, i0, j0, μ, δSign, ω, σ,
      _hNotation, _hSigmaAgree, hCyclicSource⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hCyclicSource with
    ⟨_Hcyclic, _hCyclic, _hTauCyclic, hBookSource⟩
  rcases hBookSource with
    ⟨Ms, _Abook, A0book, _A1book, H_A0, hA0M, h810, _hAbook, _hA0book,
      _hQleMs, hMsSharp, hτDade⟩
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := by
    rcases hTtypeP with
      ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
        _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
    exact hDerComp.2.2.1
  have hMs : Ms = Q ⊔ V :=
    (Section8.notation_8_10_source_data_ms_eq_ambientDerived_of_late
      h810 hLateType).trans hDerEq
  refine ⟨A0book, H_A0, hA0M, ?_, hτDade⟩
  intro l hlQVsharp
  exact hMsSharp l (by simpa [hMs] using hlQVsharp)

public theorem section14_theorem_14_9_late_type_T1_betaT0_CFOn_book_AZero
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    ∃ A0book : Set G, ∃ H_A0 : G → Subgroup G,
      ∃ hA0M : Section2.Hypothesis2 A0book Tmax H_A0,
        Section2.CFOn Tmax A0book
          (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) ∧
        ∀ α : Section1.ClassFunction Tmax,
          τT α = Section2.dadeTransform H_A0 hA0M.subset_L α := by
  classical
  rcases
      section14_theorem_14_9_late_type_T1_book_AZero_source_bridge
        (hctx := hctx) (hLateType := hLateType) (hTtypeP := hTtypeP) with
    ⟨A0book, H_A0, hA0M, hQVsharpA0, hτDade⟩
  have hCalT1src := hCalT1
  rcases hCalT1 with ⟨_hQle, _hKle, hCalT1mem⟩
  rcases (hCalT1mem ζ).mp hζ with
    ⟨θζ, _hθζIrr, _hθζNotKer, _hθζKer, hζeq⟩
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := by
    rcases hTtypeP with
      ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
        _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
    exact hDerComp.2.2.1
  haveI : ((Q ⊔ V).subgroupOf Tmax).Normal := by
    have hDerNormal :
        ((ambientDerivedSubgroup Tmax).subgroupOf Tmax).Normal :=
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)).2
    simpa [hDerEq] using hDerNormal
  have hβclass :
      Section1.IsClassFunction
        (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) := by
    have hprincipalClass :
        Section1.IsClassFunction (Section7.principalInducedCharacter Tmax (Q ⊔ V)) := by
      unfold Section7.principalInducedCharacter
      exact Section1.inducedCF_isClassFunction ((Q ⊔ V).subgroupOf Tmax)
        (Section1.principalCharacter ((Q ⊔ V).subgroupOf Tmax))
    have hζclass : Section1.IsClassFunction ζ := by
      rw [hζeq]
      exact Section1.inducedCF_isClassFunction ((Q ⊔ V).subgroupOf Tmax) θζ
    intro x g
    simp [Pi.sub_apply, hprincipalClass x g, hζclass x g]
  have hQnormal : (Q.subgroupOf Tmax).Normal := by
    rcases hTtypeP with
      ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, _hDerComp, _hQnoncyc, _hSecond, _hFit,
        _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
    exact Section12.section16MFSubgroup_subgroupOf_normal hQMF
  have hS6 :
      Section6.inducedKernelFamily ((Q ⊔ V).subgroupOf Tmax) (Q.subgroupOf Tmax) T1T := by
    exact section14_inducedKernelFamily_of_kernelInducedFamily_self
      (M := Tmax) (N := Q ⊔ V) (Y := Q) hCalT1src
  rcases
      section14_theorem_14_9_late_type_T1_calt_core_source_inputs_bridge
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP hQnormal T1T hCalT1src with
    ⟨_hcard, _h52b, hquotComm, _hfrobQuot⟩
  have hζdeg :
      Section1.degree ζ = ((Q ⊔ V).relIndex Tmax : ℂ) := by
    have hζdegTop :=
      Section6.inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
        hS6 hQnormal hquotComm hζ
    have hrel :
        ((Q ⊔ V).subgroupOf Tmax).relIndex (⊤ : Subgroup Tmax) =
          (Q ⊔ V).relIndex Tmax := by
      simpa using
        (Subgroup.relIndex_subgroupOf (H := Q ⊔ V) (K := Tmax) (L := Tmax) le_rfl)
    simpa [hrel] using hζdegTop
  have hsupp :
      ∀ l : Tmax, (l : G) ∉ A0book →
        (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) l = 0 := by
    intro l hlA0book
    have hprincipal_degree :
        Section1.degree (Section7.principalInducedCharacter Tmax (Q ⊔ V)) =
          ((Q ⊔ V).relIndex Tmax : ℂ) := by
      unfold Section7.principalInducedCharacter
      rw [Section1.degree_inducedClassFunction]
      simp [Section1.degree, Section1.principalCharacter, Subgroup.relIndex]
    have hprincipal_one :
        Section7.principalInducedCharacter Tmax (Q ⊔ V) (1 : Tmax) =
          ((Q ⊔ V).relIndex Tmax : ℂ) := by
      simpa [Section1.degree_apply] using hprincipal_degree
    have hζ_one : ζ 1 = ((Q ⊔ V).relIndex Tmax : ℂ) := by
      simpa [Section1.degree_apply] using hζdeg
    have hβ_one :
        (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) (1 : Tmax) = 0 := by
      simp [Pi.sub_apply, hprincipal_one, hζ_one]
    by_cases hl_one : l = 1
    · simpa [hl_one] using hβ_one
    · have hl_ne_oneG : (l : G) ≠ 1 := by
        intro hG
        apply hl_one
        ext
        exact hG
      have hlnotQV : (l : G) ∉ Q ⊔ V := by
        intro hlQV
        exact hlA0book (hQVsharpA0 l ⟨hlQV, hl_ne_oneG⟩)
      have hlnotKsub : l ∉ (Q ⊔ V).subgroupOf Tmax := by
        intro hlK
        exact hlnotQV (Subgroup.mem_subgroupOf.mp hlK)
      have hprincipal_zero : Section7.principalInducedCharacter Tmax (Q ⊔ V) l = 0 := by
        unfold Section7.principalInducedCharacter
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          ((Q ⊔ V).subgroupOf Tmax)
          (Section1.principalCharacter ((Q ⊔ V).subgroupOf Tmax)) hlnotKsub
      have hζ_zero : ζ l = 0 := by
        rw [hζeq]
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          ((Q ⊔ V).subgroupOf Tmax) θζ hlnotKsub
      simp [Pi.sub_apply, hprincipal_zero, hζ_zero]
  exact ⟨A0book, H_A0, hA0M, ⟨hβclass, hsupp⟩, hτDade⟩

public theorem section14_theorem_14_9_late_type_T1_betaT0_supportedOn_QVsharp
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    Section1.supportedOn
      (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)
      (Section13.subgroupSetPreimage Tmax
        (section16NonidentityElements ((Q ⊔ V : Subgroup G) : Set G))) := by
  classical
  have hCalT1src := hCalT1
  rcases hCalT1 with ⟨_hQle, _hKle, hCalT1mem⟩
  rcases (hCalT1mem ζ).mp hζ with
    ⟨θζ, _hθζIrr, _hθζNotKer, _hθζKer, hζeq⟩
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := by
    rcases hTtypeP with
      ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
        _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
    exact hDerComp.2.2.1
  haveI : ((Q ⊔ V).subgroupOf Tmax).Normal := by
    have hDerNormal :
        ((ambientDerivedSubgroup Tmax).subgroupOf Tmax).Normal :=
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)).2
    simpa [hDerEq] using hDerNormal
  have hQnormal : (Q.subgroupOf Tmax).Normal := by
    rcases hTtypeP with
      ⟨hQMF, _hW2cyc, _hW2ne, _hW2hall, _hcompMW1, _hVleD,
        _hVnil, _hW2normV, _hDerComp, _hQnotCyc, _hSecond, _hFitEq,
        _hFitLeD, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNormHatW⟩
    exact Section12.section16MFSubgroup_subgroupOf_normal hQMF
  have hS6 :
      Section6.inducedKernelFamily ((Q ⊔ V).subgroupOf Tmax) (Q.subgroupOf Tmax) T1T := by
    exact section14_inducedKernelFamily_of_kernelInducedFamily_self
      (M := Tmax) (N := Q ⊔ V) (Y := Q) hCalT1src
  rcases
      section14_theorem_14_9_late_type_T1_calt_core_source_inputs_bridge
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP hQnormal T1T hCalT1src with
    ⟨_hcard, _h52b, hquotComm, _hfrobQuot⟩
  have hζdeg :
      Section1.degree ζ = ((Q ⊔ V).relIndex Tmax : ℂ) := by
    have hζdegTop :=
      Section6.inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
        hS6 hQnormal hquotComm hζ
    have hrel :
        ((Q ⊔ V).subgroupOf Tmax).relIndex (⊤ : Subgroup Tmax) =
          (Q ⊔ V).relIndex Tmax := by
      simpa using
        (Subgroup.relIndex_subgroupOf (H := Q ⊔ V) (K := Tmax) (L := Tmax) le_rfl)
    simpa [hrel] using hζdegTop
  have hprincipal_degree :
      Section1.degree (Section7.principalInducedCharacter Tmax (Q ⊔ V)) =
        ((Q ⊔ V).relIndex Tmax : ℂ) := by
    unfold Section7.principalInducedCharacter
    rw [Section1.degree_inducedClassFunction]
    simp [Section1.degree, Section1.principalCharacter, Subgroup.relIndex]
  have hprincipal_one :
      Section7.principalInducedCharacter Tmax (Q ⊔ V) (1 : Tmax) =
        ((Q ⊔ V).relIndex Tmax : ℂ) := by
    simpa [Section1.degree_apply] using hprincipal_degree
  have hζ_one : ζ 1 = ((Q ⊔ V).relIndex Tmax : ℂ) := by
    simpa [Section1.degree_apply] using hζdeg
  rw [Section1.supportedOn_iff]
  intro l hlQVsharp
  by_cases hl_one : l = 1
  · simp [Pi.sub_apply, hl_one, hprincipal_one, hζ_one]
  · have hl_ne_oneG : (l : G) ≠ 1 := by
      intro hG
      apply hl_one
      ext
      exact hG
    have hlnotQV : (l : G) ∉ Q ⊔ V := by
      intro hlQV
      exact hlQVsharp (by
        simpa [Section13.subgroupSetPreimage] using
          (show (l : G) ∈
            section16NonidentityElements ((Q ⊔ V : Subgroup G) : Set G) from
            ⟨hlQV, hl_ne_oneG⟩))
    have hlnotKsub : l ∉ (Q ⊔ V).subgroupOf Tmax := by
      intro hlK
      exact hlnotQV (Subgroup.mem_subgroupOf.mp hlK)
    have hprincipal_zero : Section7.principalInducedCharacter Tmax (Q ⊔ V) l = 0 := by
      unfold Section7.principalInducedCharacter
      exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
        ((Q ⊔ V).subgroupOf Tmax)
        (Section1.principalCharacter ((Q ⊔ V).subgroupOf Tmax)) hlnotKsub
    have hζ_zero : ζ l = 0 := by
      rw [hζeq]
      exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
        ((Q ⊔ V).subgroupOf Tmax) θζ hlnotKsub
    simp [Pi.sub_apply, hprincipal_zero, hζ_zero]

public theorem section14_theorem_14_9_late_type_T1_betaT0_CFOn_of_QVsharp_subset
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T)
    {A0book : Set G}
    (hQVsharpA0 : ∀ l : Tmax,
      (l : G) ∈ section16NonidentityElements ((Q ⊔ V : Subgroup G) : Set G) →
        (l : G) ∈ A0book) :
    Section2.CFOn Tmax A0book
      (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) := by
  classical
  rcases
      section14_theorem_14_9_late_type_T1_betaT0_CFOn_book_AZero
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP hCalT1 hζ with
    ⟨_A0book, _H_A0, _hA0M, hβT0Book, _hτDade⟩
  have hβT0QV :
      Section1.supportedOn
        (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)
        (Section13.subgroupSetPreimage Tmax
          (section16NonidentityElements ((Q ⊔ V : Subgroup G) : Set G))) :=
    section14_theorem_14_9_late_type_T1_betaT0_supportedOn_QVsharp
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP hCalT1 hζ
  refine ⟨hβT0Book.1, ?_⟩
  intro l hlA0book
  exact (Section1.supportedOn_iff.mp hβT0QV) l (by
    intro hlQVsharp
    exact hlA0book
      (hQVsharpA0 l (by
        simpa [Section13.subgroupSetPreimage] using hlQVsharp)))

public theorem section14_theorem_14_9_late_type_T1_tauT_isVirtualCharacter_of_book_AZero
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T)
    (hβT0Virt :
      Theory.Character.IsVirtualCharacter
        (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)) :
    Theory.Character.IsVirtualCharacter
      (τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)) := by
  classical
  rcases
      section14_theorem_14_9_late_type_T1_betaT0_CFOn_book_AZero
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP hCalT1 hζ with
    ⟨A0book, H_A0, hA0M, hβT0A0, hτDade⟩
  have hβT0VirtOn :
      Section2.virtualCharacterOn Tmax A0book
        (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) :=
    ⟨hβT0Virt, hβT0A0.2⟩
  have hτβ :
      τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) =
        Section2.dadeTransform H_A0 hA0M.subset_L
          (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) :=
    hτDade (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)
  rw [hτβ]
  exact (Section2.theorem_2_6 A0book Tmax H_A0 hA0M hA0M.subset_L).2
    (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) hβT0VirtOn

public theorem section14_kernelInducedFamily_self_member_principal_orthogonal
    {G : Type u} [Group G] [Finite G]
    {M N Y : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hS : Section9.kernelInducedFamily M N N Y S)
    {χ : Section1.ClassFunction M} (hχ : χ ∈ S) :
    Section1.scalarProduct M χ (Section1.principalCharacter M) = 0 := by
  classical
  rcases hS with ⟨_hYN, _hNN, hmem⟩
  rcases (hmem χ).mp hχ with
    ⟨θ, hθirr, hθnotker, _hθker, hχeq⟩
  have hθne : θ ≠ Section1.principalCharacter (N.subgroupOf M) :=
    Section9.ne_principalCharacter_of_not_subgroupInKernel'_sec9 hθnotker
  rw [hχeq]
  have hclass : Section1.IsClassFunction (Section1.principalCharacter M) := by
    intro x g
    simp [Section1.principalCharacter]
  rw [Section1.scalarProduct_inducedCF_left (N.subgroupOf M) θ
    (Section1.principalCharacter M) hclass]
  have hres :
      Section1.subgroupRestriction (N.subgroupOf M)
          (Section1.principalCharacter M) =
        Section1.principalCharacter (N.subgroupOf M) := by
    ext x
    simp [Section1.subgroupRestriction, Section1.principalCharacter]
  rw [hres]
  exact Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
    hθirr hθne

public theorem section14_theorem_14_9_late_type_T1_tauT_betaT0_principal_scalar_book_AZero
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    Section1.scalarProduct G
      (τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ))
      (Section1.principalCharacter G) = 1 := by
  classical
  let βT0 : Section1.ClassFunction Tmax :=
    Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ
  rcases
      section14_theorem_14_9_late_type_T1_betaT0_CFOn_book_AZero
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP hCalT1 hζ with
    ⟨A0book, H_A0, hA0M, hβT0A0, hτDade⟩
  have hτβ :
      τT βT0 = Section2.dadeTransform H_A0 hA0M.subset_L βT0 :=
    hτDade βT0
  have hprincipalG :
      Section1.IsClassFunction (Section1.principalCharacter G) := by
    intro x g
    simp [Section1.principalCharacter]
  have hprincipalT :
      Section1.IsClassFunction (Section1.principalCharacter Tmax) := by
    intro x g
    simp [Section1.principalCharacter]
  have hprincipalAgree :
      ∀ ⦃a : G⦄, (ha : a ∈ A0book) →
        Section1.principalCharacter Tmax ⟨a, hA0M.subset_L a ha⟩ =
          Section2.dadeAveragingFunction Tmax H_A0
            (Section1.principalCharacter G) ⟨a, hA0M.subset_L a ha⟩ := by
    intro a ha
    unfold Section2.dadeAveragingFunction
    simp only [Section1.principalCharacter, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [← (@Nat.card_eq_fintype_card
      (H_A0 (↑(⟨a, hA0M.subset_L a ha⟩ : Tmax)))
      (Fintype.ofFinite (H_A0 (↑(⟨a, hA0M.subset_L a ha⟩ : Tmax)))))]
    have hcard : (Nat.card (H_A0 a) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := H_A0 a)).ne'
    field_simp [hcard]
  have hDadeScalar :
      Section1.scalarProduct G
          (Section2.dadeTransform H_A0 hA0M.subset_L βT0)
          (Section1.principalCharacter G) =
        Section1.scalarProduct Tmax βT0 (Section1.principalCharacter Tmax) :=
    (Section2.proposition_2_7 A0book Tmax H_A0 hA0M hA0M.subset_L
      βT0 (Section1.principalCharacter G) hβT0A0 hprincipalG
      (Section1.principalCharacter Tmax) hprincipalT hprincipalAgree).1
  have hζ_principal :
      Section1.scalarProduct Tmax ζ (Section1.principalCharacter Tmax) = 0 :=
    section14_kernelInducedFamily_self_member_principal_orthogonal
      (M := Tmax) (N := Q ⊔ V) (Y := Q) hCalT1 hζ
  have hβ_principal_T :
      Section1.scalarProduct Tmax βT0 (Section1.principalCharacter Tmax) = 1 := by
    dsimp [βT0]
    rw [Section5.scalarProduct_sub_left,
      Section7.theorem_7_8_principalInduced_principal_scalar,
      hζ_principal]
    simp
  calc
    Section1.scalarProduct G
        (τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ))
        (Section1.principalCharacter G) =
        Section1.scalarProduct G (τT βT0) (Section1.principalCharacter G) := by
          rfl
    _ = Section1.scalarProduct G
        (Section2.dadeTransform H_A0 hA0M.subset_L βT0)
        (Section1.principalCharacter G) := by
          rw [hτβ]
    _ = Section1.scalarProduct Tmax βT0 (Section1.principalCharacter Tmax) :=
        hDadeScalar
    _ = 1 := hβ_principal_T

public theorem section14_theorem_14_9_late_type_T1_tauT1_principal_scalar_zero_of_sigma_orth
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p q : ℕ}
    {T1T : Finset (Section1.ClassFunction Tmax)}
    {τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    (hσorth : ∀ ζ ∈ T1T, ∀ ξ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup ξ →
        Section1.scalarProduct G (σ ξ) (τT1 ζ) = 0)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    Section1.scalarProduct G (τT1 ζ) (Section1.principalCharacter G) = 0 := by
  classical
  rcases hNotation with
    ⟨_hωData, hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hσmap with
    ⟨_hIso, _hVirt, _hInd, _hClass, hσprincipal, _hAgree, _hVanish⟩
  have hleft :
      Section1.scalarProduct G (Section1.principalCharacter G) (τT1 ζ) = 0 := by
    simpa [hσprincipal] using
      hσorth ζ hζ (Section1.principalCharacter W)
        (Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := W))
  have hstar :
      star (Section1.scalarProduct G (τT1 ζ) (Section1.principalCharacter G)) = 0 := by
    simpa [hleft] using
      (Section1.scalarProduct_star_swap (G := G)
        (Section1.principalCharacter G) (τT1 ζ))
  simpa using congrArg star hstar

public theorem section14_theorem_14_9_late_type_T1_delta_scalar_equation_of_gamma_tau
    {G : Type u} [Group G] [Finite G]
    {Γ χ τβ Δ : Section1.ClassFunction G}
    (hΔ : Δ = τβ - Section1.principalCharacter G + χ)
    (hΓone : Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0)
    (hΓτβ : Section1.scalarProduct G Γ τβ = -1) :
    (0 : ℂ) = 1 - Section1.scalarProduct G Γ χ +
      Section1.scalarProduct G Γ Δ := by
  rw [hΔ]
  rw [Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right,
    hΓone, hΓτβ]
  ring

public theorem section14_theorem_14_9_late_type_T1_gamma_tau_scalar_of_decomposition
    {G : Type u} [Group G] [Finite G]
    {Γ βτ η01 τβ : Section1.ClassFunction G}
    (hΓ : Γ = βτ - Section1.principalCharacter G + η01)
    (hβττβ : Section1.scalarProduct G βτ τβ = 0)
    (hητβ : Section1.scalarProduct G η01 τβ = 0)
    (hτβ_principal :
      Section1.scalarProduct G τβ (Section1.principalCharacter G) = 1) :
    Section1.scalarProduct G Γ τβ = -1 := by
  have hprincipal_τβ :
      Section1.scalarProduct G (Section1.principalCharacter G) τβ = 1 := by
    have hstar :
        star (Section1.scalarProduct G τβ (Section1.principalCharacter G)) =
          Section1.scalarProduct G (Section1.principalCharacter G) τβ :=
      Section1.scalarProduct_star_swap (G := G)
        (Section1.principalCharacter G) τβ
    rw [hτβ_principal] at hstar
    simpa using hstar.symm
  rw [hΓ, Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
    hβττβ, hprincipal_τβ, hητβ]
  ring

public theorem section14_principalInducedCharacter_conjugate
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G) :
    Section1.conjugateCharacter (Section7.principalInducedCharacter L H) =
      Section7.principalInducedCharacter L H := by
  classical
  ext g
  simp [Section7.principalInducedCharacter, Section1.inducedCF,
    Section1.inducedClassFunction, Section1.conjugateCharacter,
    Section1.principalCharacter]

public theorem section14_theorem_14_9_late_type_T1_coherent_conjugate_diff_agree
    {G : Type u} [Group G] [Finite G]
    {Tmax : Subgroup G}
    {T1T : Finset (Section1.ClassFunction Tmax)}
    {τT τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement T1T τT)
    (hcoh : Section6.coherentExtension T1T τT τT1)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    τT1 (ζ - Section1.conjugateCharacter ζ) =
      τT (ζ - Section1.conjugateCharacter ζ) := by
  classical
  rcases h52 with ⟨hsetup, R, h52a, _h52b, _h52c, _h52d, _h52e⟩
  let X : T1T := ⟨ζ, hζ⟩
  have hζbar :
      Section1.conjugateCharacter ζ ∈ T1T := by
    simpa [X] using (h52a X).1
  have hspan :
      Section5.integerSpan T1T (ζ - Section1.conjugateCharacter ζ) :=
    Section5.integerSpan_sub
      (Section5.integerSpan_of_mem T1T hζ)
      (Section5.integerSpan_of_mem T1T hζbar)
  have hζchar : Section1.IsCharacter ζ := by
    simpa [X] using hsetup.2 X
  have hdeg :
      Section1.degree (ζ - Section1.conjugateCharacter ζ) = 0 := by
    change Section1.degree ζ -
      Section1.degree (Section1.conjugateCharacter ζ) = 0
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hζchar]
    simp
  exact hcoh.2.2 (ζ - Section1.conjugateCharacter ζ)
    ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero
      (ζ - Section1.conjugateCharacter ζ)).2 hdeg⟩

public theorem section14_theorem_14_9_late_type_T1_tauT_betaT0_conjugate
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (ζ : Section1.ClassFunction Tmax) :
    Section1.conjugateCharacter
        (τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)) =
      τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) -
        Section1.conjugateCharacter ζ) := by
  classical
  rcases
      section14_theorem_14_9_late_type_T1_book_AZero_source_bridge
        (hctx := hctx) (hLateType := hLateType) (hTtypeP := hTtypeP) with
    ⟨A0book, H_A0, hA0M, _hQVsharpA0, hτDade⟩
  have hprincipal :
      Section1.conjugateCharacter (Section7.principalInducedCharacter Tmax (Q ⊔ V)) =
        Section7.principalInducedCharacter Tmax (Q ⊔ V) :=
    section14_principalInducedCharacter_conjugate Tmax (Q ⊔ V)
  calc
    Section1.conjugateCharacter
        (τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)) =
        Section1.conjugateCharacter
          (Section2.dadeTransform H_A0 hA0M.subset_L
            (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)) := by
          rw [hτDade]
    _ = Section2.dadeTransform H_A0 hA0M.subset_L
          (Section1.conjugateCharacter
            (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)) :=
        Section12.conjugateCharacter_dadeTransform H_A0 hA0M.subset_L
          (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)
    _ = Section2.dadeTransform H_A0 hA0M.subset_L
          (Section7.principalInducedCharacter Tmax (Q ⊔ V) -
            Section1.conjugateCharacter ζ) := by
          congr 1
          ext x
          have hx :
              star (Section7.principalInducedCharacter Tmax (Q ⊔ V) x) =
                Section7.principalInducedCharacter Tmax (Q ⊔ V) x := by
            simpa [Section1.conjugateCharacter] using congrFun hprincipal x
          simp [Section1.conjugateCharacter, hx]
    _ = τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) -
          Section1.conjugateCharacter ζ) := by
          rw [hτDade]

public theorem section14_theorem_14_9_late_type_T1_delta_real_of_conjugation
    {G : Type u} [Group G] [Finite G]
    {Tmax : Subgroup G}
    {τT τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {ν ζ : Section1.ClassFunction Tmax}
    {Δ : Section1.ClassFunction G}
    (hΔ : Δ = τT (ν - ζ) - Section1.principalCharacter G + τT1 ζ)
    (hτβ_conj :
      Section1.conjugateCharacter (τT (ν - ζ)) =
        τT (ν - Section1.conjugateCharacter ζ))
    (hτ1_conj :
      Section1.conjugateCharacter (τT1 ζ) =
        τT1 (Section1.conjugateCharacter ζ))
    (hdiff :
      τT1 (ζ - Section1.conjugateCharacter ζ) =
        τT (ζ - Section1.conjugateCharacter ζ)) :
    Δ = Section1.conjugateCharacter Δ := by
  rw [hΔ]
  ext g
  have hτβ_g :
      star ((τT (ν - ζ)) g) =
        (τT (ν - Section1.conjugateCharacter ζ)) g := by
    simpa [Section1.conjugateCharacter] using congrFun hτβ_conj g
  have hτ1_g :
      star ((τT1 ζ) g) =
        (τT1 (Section1.conjugateCharacter ζ)) g := by
    simpa [Section1.conjugateCharacter] using congrFun hτ1_conj g
  have hdiff_g :
      (τT1 ζ) g - (τT1 (Section1.conjugateCharacter ζ)) g =
        (τT ζ) g - (τT (Section1.conjugateCharacter ζ)) g := by
    simpa using congrFun hdiff g
  have hτνζ_g :
      (τT (ν - ζ)) g = (τT ν) g - (τT ζ) g := by
    exact congrFun (τT.map_sub ν ζ) g
  have hτνbar_g :
      (τT (ν - Section1.conjugateCharacter ζ)) g =
        (τT ν) g - (τT (Section1.conjugateCharacter ζ)) g := by
    exact congrFun (τT.map_sub ν (Section1.conjugateCharacter ζ)) g
  have hτ1_eq :
      (τT1 ζ) g =
        (τT1 (Section1.conjugateCharacter ζ)) g +
          ((τT ζ) g - (τT (Section1.conjugateCharacter ζ)) g) := by
    calc
      (τT1 ζ) g =
          ((τT1 ζ) g - (τT1 (Section1.conjugateCharacter ζ)) g) +
            (τT1 (Section1.conjugateCharacter ζ)) g := by ring
      _ = ((τT ζ) g - (τT (Section1.conjugateCharacter ζ)) g) +
            (τT1 (Section1.conjugateCharacter ζ)) g := by rw [hdiff_g]
      _ = (τT1 (Section1.conjugateCharacter ζ)) g +
            ((τT ζ) g - (τT (Section1.conjugateCharacter ζ)) g) := by ring
  calc
    (τT (ν - ζ) - Section1.principalCharacter G + τT1 ζ) g =
        ((τT ν) g - (τT ζ) g) - 1 + (τT1 ζ) g := by
          simp
    _ = ((τT ν) g - (τT (Section1.conjugateCharacter ζ)) g) - 1 +
          (τT1 (Section1.conjugateCharacter ζ)) g := by
          rw [hτ1_eq]
          ring
    _ = (τT (ν - Section1.conjugateCharacter ζ) -
          Section1.principalCharacter G +
          τT1 (Section1.conjugateCharacter ζ)) g := by
          simp
    _ = (Section1.conjugateCharacter
          (τT (ν - ζ) - Section1.principalCharacter G + τT1 ζ)) g := by
          change
            (τT (ν - Section1.conjugateCharacter ζ)) g -
                Section1.principalCharacter G g +
                (τT1 (Section1.conjugateCharacter ζ)) g =
              star (((τT (ν - ζ)) g - Section1.principalCharacter G g) +
                (τT1 ζ) g)
          rw [← hτβ_g, ← hτ1_g]
          simp [Section1.principalCharacter]


public theorem section14_scalarProduct_eq_zero_of_supports_disjoint
    {G : Type u} [Finite G]
    {A B : Set G} {φ ψ : Section1.ClassFunction G}
    (hAB : Disjoint A B)
    (hφ : Section1.supportedOn φ A)
    (hψ : Section1.supportedOn ψ B) :
    Section1.scalarProduct G φ ψ = 0 := by
  classical
  rw [Section1.supportedOn_iff] at hφ hψ
  have hsum : ∑ g : G, φ g * star (ψ g) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro g _hg
    by_cases hgA : g ∈ A
    · have hgB : g ∉ B := by
        intro hgB
        exact hAB.le_bot ⟨hgA, hgB⟩
      have hzero : ψ g = 0 := hψ g hgB
      simp [hzero]
    · have hzero : φ g = 0 := hφ g hgA
      simp [hzero]
  rw [Section1.scalarProduct, hsum]
  simp

public theorem section14_inducedCF_supportedOn_conjugatesOfSetBySet_univ
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H]
    {A : Set G} {φ : Section1.ClassFunction H}
    (hφ : Section1.supportedOn φ (Section13.subgroupSetPreimage H A)) :
    Section1.supportedOn (Section1.inducedCF H φ)
      (section16ConjugatesOfSetBySet A Set.univ) := by
  classical
  rw [Section1.supportedOn_iff] at hφ ⊢
  intro g hg
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      ∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then
            φ ⟨x * g * x⁻¹, hx⟩
          else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    by_cases hxH : x * g * x⁻¹ ∈ H
    · have hxA : x * g * x⁻¹ ∉ A := by
        intro hxA
        apply hg
        refine ⟨x * g * x⁻¹, hxA, x⁻¹, by simp, ?_⟩
        simp [mul_assoc]
      have hzero :
          φ ⟨x * g * x⁻¹, hxH⟩ = 0 :=
        hφ ⟨x * g * x⁻¹, hxH⟩
          (by simpa [Section13.subgroupSetPreimage] using hxA)
      simp [hxH, hzero]
    · simp [hxH]
  rw [hsum, mul_zero]

public theorem section14_theorem_14_9_betaTau_supportedOn_betaSupport_global
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {βS₁ : Section1.ClassFunction Smax}
    {βτ Γ X Y η01 : Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hGap : section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
      βS₁ βτ Γ X Y η01 p q u) :
    Section1.supportedOn βτ
      (section16ConjugatesOfSetBySet
        (Section13.theorem_13_18_betaSupportSet Smax W W1 W2 P) Set.univ) := by
  classical
  rcases hGap with
    ⟨hβSupp, hβSuppA0, hβClass, _hβNorm, hβτ, _hη01, _hΓbase, _hΓallK,
      _hΓone, _hΓreal, _hΓvirt, _hΓdecomp, _hDecomp⟩
  have hSTypeP : Section8.typePDefinitionData Smax P U W1 W2 := hctx.1.2.1
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hMF, _hType, _hTypeII, _hUcomm, _hFrob, _hPelem, _hPcard, _huBound,
      _hCoh, _hTI, hTau, _hNormU⟩
  have hβCFOn :
      Section2.CFOn Smax (Section13.typePFAZeroSet Smax W1 W2 P) βS₁ := by
    refine ⟨hβClass, ?_⟩
    intro l hl
    exact (Section1.supportedOn_iff.mp hβSuppA0) l
      (by simpa [Section13.subgroupSetPreimage] using hl)
  have hβτ_induced :
      βτ = Section1.inducedCF Smax βS₁ := by
    calc
      βτ = τS βS₁ := hβτ
      _ = Section1.inducedCFLinear Smax βS₁ :=
        hTau.2 βS₁ hβCFOn
      _ = Section1.inducedCF Smax βS₁ := Section1.inducedCFLinear_apply Smax βS₁
  rw [hβτ_induced]
  exact
    section14_inducedCF_supportedOn_conjugatesOfSetBySet_univ Smax
      (by
        simpa [Section13.theorem_13_18_betaSupportSet] using hβSupp)

public theorem section14_theorem_14_9_late_type_T1_tauT_betaT0_agreesWithInduction_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) =
      Section1.inducedCFLinear Tmax
        (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) := by
  classical
  -- `have [_ _ _ _ [_ -> //]] := FTtypeP_facts _ TtypeP`.
  -- Use the swapped Section 13 source package, so the book `A₀(T)` is the
  -- one attached to the T-side `(4.6)` notation rather than `section16AZeroSet`.
  have hsourceT :
      Section13.hypothesis_13_1_sourceData Tmax Smax W W2 W1 Q P V U D C
        Tfam Sfam τT τS q p v u d c :=
    section14_hypothesis_13_1_sourceData_swap hctx.1
  rcases
      Section13.theorem_13_2_agreesWithInductionOnBookAZero
        Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS q p v u d c
        hsourceT with
    ⟨Ms, A0book, _H_A0, _hA0M, hMsChoice, _hTI, hMsSharp,
      _hFittingSharp, _hASet, _hτDade, hτInd⟩
  have hMsEq : Ms = ambientDerivedSubgroup Tmax :=
    Section8.msChoiceSource_eq_ambientDerived_of_late hMsChoice hLateType
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := by
    rcases hTtypeP with
      ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
        _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
    exact hDerComp.2.2.1
  have hQVsharpA0 :
      ∀ l : Tmax,
        (l : G) ∈
            section16NonidentityElements (((Q ⊔ V : Subgroup G)) : Set G) →
          (l : G) ∈ A0book := by
    intro l hl
    exact hMsSharp l (by simpa [hMsEq, hDerEq] using hl)
  have hβT0A0 :
      Section2.CFOn Tmax A0book
        (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) :=
    section14_theorem_14_9_late_type_T1_betaT0_CFOn_of_QVsharp_subset
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP hCalT1 hζ hQVsharpA0
  exact hτInd
    (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) hβT0A0

public theorem section14_theorem_14_9_late_type_T1_tauT_betaT0_supportedOn_QVsharp_global
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    Section1.supportedOn
      (τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ))
      (section16ConjugatesOfSetBySet
        (section16NonidentityElements ((Q ⊔ V : Subgroup G) : Set G)) Set.univ) := by
  classical
  have hτβ :
      τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) =
        Section1.inducedCFLinear Tmax
          (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ) :=
    section14_theorem_14_9_late_type_T1_tauT_betaT0_agreesWithInduction_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP hCalT1 hζ
  rw [hτβ, Section1.inducedCFLinear_apply]
  exact
    section14_inducedCF_supportedOn_conjugatesOfSetBySet_univ Tmax
      (section14_theorem_14_9_late_type_T1_betaT0_supportedOn_QVsharp
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP hCalT1 hζ)

private theorem section14_orderOf_conj_eq
    {G : Type u} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq x

private theorem section14_order_dvd_p_of_mem_Psharp
    {G : Type u} [Group G] [Finite G]
    {P : Subgroup G} {p : ℕ}
    (hp : Nat.Prime p) (hPelem : IsElementaryAbelian p P)
    {x : G} (hx : x ∈ section16NonidentityElements ((P : Subgroup G) : Set G)) :
    p ∣ orderOf x := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsElementaryAbelian p P := hPelem
  have hxpow : x ^ p = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := P) x hx.1
  have hxord : orderOf x = p := orderOf_eq_prime hxpow hx.2
  simp [hxord]

private theorem section14_order_dvd_p_of_mem_W_diff
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G} {p : ℕ}
    (hp : Nat.Prime p) (hp_card : p = Nat.card W2)
    (hprod : section12InternalDirectProduct W1 W2 W)
    {x : G}
    (hx : x ∈ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) :
    p ∣ orderOf x := by
  classical
  let J : Subgroup G := W2 ⊔ W1
  have hW_eq : W = W1 ⊔ W2 := hprod.2.2.1
  have hxJ : x ∈ J := by
    simpa [J, ← hW_eq, sup_comm] using hx.1
  let xJ : J := ⟨x, hxJ⟩
  have hprodSwap : section12InternalDirectProduct W2 W1 W :=
    Section13.section13_section12InternalDirectProduct_swap hprod
  have hW2_norm_W1 : W2 ≤ Subgroup.normalizer (W1 : Set G) :=
    hprodSwap.2.2.2.2.trans (centralizer_le_normalizer W1)
  haveI hW1Jnormal : (W1.subgroupOf J).Normal := by
    simpa [J] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W2) (N := W1) hW2_norm_W1)
  have hcompJ : section12ComplementIn J W1 W2 :=
    ⟨le_sup_right, le_sup_left, by simp [J, sup_comm], hprod.2.2.2.1⟩
  have hcompLocal :
      (W1.subgroupOf J).IsComplement' (W2.subgroupOf J) :=
    Section12.section12ComplementIn_left_normal_isComplement'
      (M := J) (K := W1) (L := W2) hcompJ hW1Jnormal
  have hquot_card : Nat.card (J ⧸ W1.subgroupOf J) = Nat.card W2 := by
    calc
      Nat.card (J ⧸ W1.subgroupOf J) = (W1.subgroupOf J).index :=
        (Subgroup.index_eq_card (H := W1.subgroupOf J)).symm
      _ = Nat.card (W2.subgroupOf J) := hcompLocal.symm.index_eq_card
      _ = Nat.card W2 := natCard_subgroupOf_eq W2 J le_sup_left
  let π : J →* J ⧸ W1.subgroupOf J := QuotientGroup.mk' (W1.subgroupOf J)
  have hxbar_ne : π xJ ≠ 1 := by
    intro hxbar
    have hxW1J : xJ ∈ W1.subgroupOf J :=
      (QuotientGroup.eq_one_iff (N := W1.subgroupOf J) xJ).1 hxbar
    have hxW1 : x ∈ W1 := by
      simpa [xJ, Subgroup.mem_subgroupOf] using hxW1J
    exact hx.2 (Or.inl hxW1)
  have horder_dvd_p : orderOf (π xJ) ∣ p := by
    have horder_card : orderOf (π xJ) ∣ Nat.card (J ⧸ W1.subgroupOf J) :=
      orderOf_dvd_natCard (π xJ)
    rw [hquot_card, ← hp_card] at horder_card
    exact horder_card
  have horder_eq_p : orderOf (π xJ) = p := by
    rcases (Nat.dvd_prime hp).1 horder_dvd_p with horder_one | horder_p
    · exact False.elim (hxbar_ne (orderOf_eq_one_iff.mp horder_one))
    · exact horder_p
  have hmap_dvd : orderOf (π xJ) ∣ orderOf xJ :=
    orderOf_map_dvd (ψ := π) xJ
  have hp_dvd_xJ : p ∣ orderOf xJ := by
    simpa [horder_eq_p] using hmap_dvd
  simpa [xJ, Subgroup.orderOf_coe] using hp_dvd_xJ

private theorem section14_order_coprime_p_of_mem_QVsharp
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    {x : G}
    (hx : x ∈ section16NonidentityElements (((Q ⊔ V : Subgroup G)) : Set G)) :
    Nat.Coprime p (orderOf x) := by
  classical
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hTtypeP with
    ⟨_hQMF, _hW2cyc, _hW2ne, hW2Hall, hTcomp, _hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
      _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
  rcases hW2Hall with ⟨hW2leT, hW2HallT⟩
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := hDerComp.2.2.1
  have hTcompQV : section12ComplementIn Tmax (Q ⊔ V) W2 := by
    simpa [hDerEq] using hTcomp
  have hKnormal : (((Q ⊔ V : Subgroup G)).subgroupOf Tmax).Normal := by
    have hDerNormal : ((ambientDerivedSubgroup Tmax).subgroupOf Tmax).Normal :=
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)).2
    simpa [hDerEq] using hDerNormal
  have hcompLocal :
      (((Q ⊔ V : Subgroup G)).subgroupOf Tmax).IsComplement'
        (W2.subgroupOf Tmax) :=
    Section12.section12ComplementIn_left_normal_isComplement'
      (M := Tmax) (K := Q ⊔ V) (L := W2) hTcompQV hKnormal
  have hidx : (W2.subgroupOf Tmax).index =
      Nat.card (((Q ⊔ V : Subgroup G)).subgroupOf Tmax) :=
    hcompLocal.index_eq_card
  have hcop0 : Nat.Coprime (Nat.card (W2.subgroupOf Tmax))
      (W2.subgroupOf Tmax).index :=
    hW2HallT.card_coprime_index
  have hcop1 : Nat.Coprime (Nat.card (W2.subgroupOf Tmax))
      (Nat.card (((Q ⊔ V : Subgroup G)).subgroupOf Tmax)) := by
    simpa [hidx] using hcop0
  have hW2cardSub : Nat.card (W2.subgroupOf Tmax) = Nat.card W2 :=
    natCard_subgroupOf_eq W2 Tmax hW2leT
  have hQVcardSub :
      Nat.card (((Q ⊔ V : Subgroup G)).subgroupOf Tmax) =
        Nat.card (Q ⊔ V : Subgroup G) :=
    natCard_subgroupOf_eq (Q ⊔ V : Subgroup G) Tmax hTcompQV.1
  have hcopQV : Nat.Coprime (Nat.card W2) (Nat.card (Q ⊔ V : Subgroup G)) := by
    rw [hW2cardSub, hQVcardSub] at hcop1
    exact hcop1
  have hxorder : orderOf x ∣ Nat.card (Q ⊔ V : Subgroup G) :=
    Subgroup.orderOf_dvd_natCard (Q ⊔ V : Subgroup G) hx.1
  simpa [hp_card] using Nat.Coprime.of_dvd_right hxorder hcopQV

private theorem section14_order_dvd_p_of_mem_betaSupportSet
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    {x : G}
    (hx : x ∈ Section13.theorem_13_18_betaSupportSet Smax W W1 W2 P) :
    p ∣ orderOf x := by
  classical
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, _hq⟩
  rcases hctx.1 with
    ⟨hcase, _hSTypeP, _hTTypeP, hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨hprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hTypeII,
      _hStypes, _hTtypes, _hmaxclass⟩
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hSMF, _hType, _hTypeLarge, _hUcomm, _hFrob, hPelem, _hPcard,
      _huBound, _hCoh, _hTI, _hTau, _hNorm⟩
  rcases hx with hxP | hxW
  · exact section14_order_dvd_p_of_mem_Psharp hp hPelem hxP
  · rcases hxW with ⟨w, hw, s, _hs, rfl⟩
    have hw_dvd : p ∣ orderOf w :=
      section14_order_dvd_p_of_mem_W_diff hp hp_card hprod hw
    simpa [section14_orderOf_conj_eq s w] using hw_dvd

public theorem section14_theorem_14_9_betaSupport_disjoint_QVsharp_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1) :
    Disjoint
      (section16ConjugatesOfSetBySet
        (Section13.theorem_13_18_betaSupportSet Smax W W1 W2 P) Set.univ)
      (section16ConjugatesOfSetBySet
        (section16NonidentityElements ((Q ⊔ V : Subgroup G) : Set G)) Set.univ) := by
  -- prime `p` in their order, while elements of `(Q ⊔ V)#` are `p'` by the
  -- T-side Type-P semidirect/Hall complement data.
  classical
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, _hq⟩
  rw [Set.disjoint_left]
  intro z hzS hzT
  have hz_p : p ∣ orderOf z := by
    rcases hzS with ⟨x, hx, g, _hg, rfl⟩
    have hx_p : p ∣ orderOf x :=
      section14_order_dvd_p_of_mem_betaSupportSet hctx hx
    simpa [section14_orderOf_conj_eq g x] using hx_p
  have hz_cop : Nat.Coprime p (orderOf z) := by
    rcases hzT with ⟨x, hx, g, _hg, rfl⟩
    have hx_cop : Nat.Coprime p (orderOf x) :=
      section14_order_coprime_p_of_mem_QVsharp hctx hTtypeP hx
    simpa [section14_orderOf_conj_eq g x] using hx_cop
  exact ((hp.coprime_iff_not_dvd).1 hz_cop) hz_p

public theorem section14_theorem_14_9_late_type_T1_eta_tauT_betaT0_scalar_of_pf11_row_projection
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M MF H U C H0 W1 W2 : Subgroup G)
    (Wloc : Subgroup M)
    (A A0 : Set M)
    (S SHC : Finset (Section1.ClassFunction M))
    (R : Finset (Section1.ClassFunction G))
    (i0 i1 : I)
    (j0 j1 : J)
    (μloc : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ωloc : I → J → Section1.ClassFunction Wloc)
    (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ζ β : Section1.ClassFunction M)
    (η01 : Section1.ClassFunction G)
    (p q : ℕ) :
    Section11.hypothesis_11_2_data M MF H U C H0 W1 W2 S τ p q →
      Section10.section10FourSixNotationSupportedData M W1 W2 Wloc A A0 i0 j0
        μloc δSign ωloc σloc τ →
        Section11.section11Subfamily (H ⊔ C) S SHC →
          ζ ∈ SHC →
            Section11.transformedIrreducibleFamily R σloc →
              i0 ≠ i1 →
                η01 = σloc (ωloc i1 j1) →
                  β = Section10.muColumn μloc j0 - ζ →
                    Section1.scalarProduct G η01 (τ β) = 0 := by
  classical
  intro h11 hNotation10 hSHC hζ hR hi1 hη01 hβ
  have hcoeff :=
    Section11.theorem_11_9_tau_row_coefficients_of_hypothesis
      M MF H U C H0 W1 W2 Wloc A A0 S SHC R i0 j0
      μloc δSign ωloc σloc τ ζ p q
      h11 hNotation10 hSHC hζ hR
  have hforward :
      Section1.scalarProduct G (τ β) η01 = 0 := by
    rw [hη01, hβ]
    simpa [hi1] using hcoeff i1 j1
  simpa [Section1.scalarProduct_star_swap] using congrArg star hforward

public theorem section14_transformedIrreducibleFamily_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {Wloc : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μloc : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ωloc : I → J → Section1.ClassFunction Wloc}
    {σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation10 : Section10.section10FourSixNotationSupportedData M W1 W2 Wloc A A0
      i0 j0 μloc δSign ωloc σloc τ) :
    Section11.transformedIrreducibleFamily
      (Finset.univ.image fun p : I × J => σloc (ωloc p.1 p.2)) σloc := by
  classical
  rcases hNotation10 with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource, _hW, _hA0, _h46,
      hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
      _hTauA0, _hFull⟩
  intro ψ
  constructor
  · intro hψ
    rcases Finset.mem_image.mp hψ with ⟨p, _hp, hpψ⟩
    exact ⟨ωloc p.1 p.2, hω.irreducible p.1 p.2, hpψ.symm⟩
  · rintro ⟨ω', hω'irr, rfl⟩
    rcases hω.all_irreducibles ω' hω'irr with ⟨i, j, hω'⟩
    refine Finset.mem_image.mpr ⟨(i, j), by simp, ?_⟩
    rw [hω']


public theorem section14_section11Subfamily_of_mem_iff
    {G : Type u} [Group G] [Finite G]
    {M X : Subgroup G}
    {S SX : Finset (Section1.ClassFunction M)}
    (hXM : X ≤ M)
    (hSX : ∀ χ : Section1.ClassFunction M,
      χ ∈ SX ↔ χ ∈ S ∧ Section1.subgroupInKernel' χ (X.subgroupOf M)) :
    Section11.section11Subfamily X S SX :=
  ⟨hXM, hSX⟩

public theorem section14_theorem_14_9_late_type_T1_hypothesis_11_2_of_section10_and_case97_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (S : Finset (Section1.ClassFunction Tmax))
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (h10 : Section10.hypothesis_10_1_supported_data Tmax Q W2 W1
      (section16HatW W2 W1) S τT)
    (hcaseT : Section13.case_9_7_a_sourceDataForSection13
        Tmax Q V W2 W1 D q p v ∨
      Section13.case_9_7_b_sourceDataForSection13
        Tmax Q V W2 W1 D q p v) :
    Section11.hypothesis_11_2_data Tmax Q Q V D ⊥ W2 W1 S τT q p := by
  classical
  rcases section14_context_primes_of_sourceData hctx with ⟨_hpPrime, hqPrime⟩
  have hsourceCtx := hctx.1
  rcases hsourceCtx with
    ⟨hcaseCtx, _hSTypeP, _hTTypeP, hpW2, hqW1, _hCeq, hDeq, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hnotII : ¬ Section8.typeIIDefinitionData Tmax Q := by
    intro hII
    rcases hcaseCtx with
      ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, hTmax, _hSMF,
        hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
        _hTType, _hCover⟩
    rcases hLateType with hIII | hIVV
    · rcases hChoice Tmax Q hTmax hTMF (Or.inr (Or.inr (Or.inl hIII))) with
        ⟨Ms, hMs⟩
      rcases hMs with hI | hIIbranch | hIIIbranch | hIVbranch | hVbranch
      · rcases hI with ⟨_hI, hnotII, _hnotIII, _hnotIV, _hnotV, _hMs⟩
        exact hnotII hII
      · rcases hIIbranch with ⟨_hnotI, _hII, hnotIII, _hnotIV, _hnotV, _hMs⟩
        exact hnotIII hIII
      · rcases hIIIbranch with ⟨_hnotI, hnotII, _hIII, _hnotIV, _hnotV, _hMs⟩
        exact hnotII hII
      · rcases hIVbranch with ⟨_hnotI, hnotII, hnotIII, _hIV, _hnotV, _hMs⟩
        exact hnotII hII
      · rcases hVbranch with ⟨_hnotI, hnotII, hnotIII, _hnotIV, _hV, _hMs⟩
        exact hnotII hII
    · rcases hIVV with hIV | hV
      · rcases hChoice Tmax Q hTmax hTMF
            (Or.inr (Or.inr (Or.inr (Or.inl hIV)))) with
          ⟨Ms, hMs⟩
        rcases hMs with hI | hIIbranch | hIIIbranch | hIVbranch | hVbranch
        · rcases hI with ⟨_hI, hnotII, _hnotIII, _hnotIV, _hnotV, _hMs⟩
          exact hnotII hII
        · rcases hIIbranch with ⟨_hnotI, _hII, _hnotIII, hnotIV, _hnotV, _hMs⟩
          exact hnotIV hIV
        · rcases hIIIbranch with ⟨_hnotI, hnotII, _hIII, hnotIV, _hnotV, _hMs⟩
          exact hnotII hII
        · rcases hIVbranch with ⟨_hnotI, hnotII, _hnotIII, _hIV, _hnotV, _hMs⟩
          exact hnotII hII
        · rcases hVbranch with ⟨_hnotI, hnotII, _hnotIII, hnotIV, _hV, _hMs⟩
          exact hnotII hII
      · rcases hChoice Tmax Q hTmax hTMF
            (Or.inr (Or.inr (Or.inr (Or.inr hV)))) with
          ⟨Ms, hMs⟩
        rcases hMs with hI | hIIbranch | hIIIbranch | hIVbranch | hVbranch
        · rcases hI with ⟨_hI, hnotII, _hnotIII, _hnotIV, _hnotV, _hMs⟩
          exact hnotII hII
        · rcases hIIbranch with ⟨_hnotI, _hII, _hnotIII, _hnotIV, hnotV, _hMs⟩
          exact hnotV hV
        · rcases hIIIbranch with ⟨_hnotI, hnotII, _hIII, _hnotIV, hnotV, _hMs⟩
          exact hnotII hII
        · rcases hIVbranch with ⟨_hnotI, hnotII, _hnotIII, _hIV, hnotV, _hMs⟩
          exact hnotII hII
        · rcases hVbranch with ⟨_hnotI, hnotII, _hnotIII, _hnotIV, _hV, _hMs⟩
          exact hnotII hII
  have hTsource := section14_hypothesis_13_1_sourceData_swap hctx.1
  have hT13 :=
    Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c hTsource
  rcases hT13 with
    ⟨_hTMF, hTtypes, _hTtypeII_of_pq, _hVcomm, _hfrob, _hQelem, _hQcard,
      _hv, _hTfamCoh, _hTI, _hTau, _hnorm⟩
  have hTIII : Section8.typeIIIDefinitionData Tmax Q := by
    rcases hTtypes with hII | hIII
    · exact False.elim (hnotII hII)
    · exact hIII
  have hTypeIIIIV :
      section16TypeIII Tmax Q ∨ section16TypeIV Tmax Q :=
    Or.inl
      (Section13.theorem_13_2_section16TypeIII_of_source_typeIII
        Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS q p v u d c
        hTsource hTIII)
  have hOddT : Odd (Nat.card Tmax) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card Tmax)
  have hTtypePcopy := hTtypeP
  rcases hTtypePcopy with
    ⟨_hQsection16, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit, _hFitLe,
      _hW1le, _hW1cyc, _hW1ne, _hCentralizer, _hNormalizer⟩
  have hQleDer : Q ≤ ambientDerivedSubgroup Tmax := hDerComp.1
  have hcaseCore :
      Section9.hypothesis_9_2_statement Tmax Q V W2 W1 p ∧
        ∃ hp : Nat.Primes,
          hp.val = q ∧ Section9.hoReductionData Tmax Q V W1 ⊥ hp := by
    rcases hcaseT with hcaseA | hcaseB
    · rcases hcaseA with ⟨_hbar, a, hcaseAcore⟩
      exact
        ⟨Section9.case_9_7_a_hypothesis_9_2_sec9 hcaseAcore,
          Section9.case_9_7_a_hoReductionData_sec9 hcaseAcore⟩
    · exact
        ⟨Section9.case_9_7_b_hypothesis_9_2_sec9 hcaseB,
          Section9.case_9_7_b_hoReductionData_sec9 hcaseB⟩
  rcases hcaseCore with ⟨h92, hpData⟩
  rcases hpData with ⟨hpQ, hpQeq, hho⟩
  rcases hho with
    ⟨hBotQ, _hQTmax, hBotNormalT, hBotNormalQ, hBotLtQ, hElem, hTypeData⟩
  rcases hElem with ⟨hBotNormalQ', hElemAbelian⟩
  rcases hTypeData hTypeIIIIV with ⟨_hW1card, hChief, hNotCent⟩
  have hQuot :
      ∃ hH0H : ((⊥ : Subgroup G).subgroupOf Q).Normal,
        letI : ((⊥ : Subgroup G).subgroupOf Q).Normal := hH0H
        Nontrivial (Q ⧸ (⊥ : Subgroup G).subgroupOf Q) ∧
          IsElementaryAbelian q (Q ⧸ (⊥ : Subgroup G).subgroupOf Q) := by
    refine ⟨hBotNormalQ', ?_⟩
    letI : ((⊥ : Subgroup G).subgroupOf Q).Normal := hBotNormalQ'
    constructor
    · have hBotQ_ne_top : (⊥ : Subgroup G).subgroupOf Q ≠ ⊤ := by
        intro htop
        have hle : Q ≤ (⊥ : Subgroup G) :=
          (Subgroup.subgroupOf_eq_top).1 htop
        exact hBotLtQ.not_ge hle
      exact (QuotientGroup.nontrivial_iff
        (N := (⊥ : Subgroup G).subgroupOf Q)).2 hBotQ_ne_top
    · simpa [hpQeq] using hElemAbelian
  have hComm : ¬ ⁅V, Q⁆ ≤ (⊥ : Subgroup G) := by
    intro hle
    exact hNotCent ((Section9.quotientCentralizedBy_iff_commutator_le_sec9).2 hle)
  exact
    ⟨h10, rfl, hTypeIIIIV, hQleDer, hVleDer, hDeq, bot_le,
      ⟨bot_le, hBotNormalT⟩, hqPrime, hQuot, hChief, hComm, hqW1,
      hpW2, hTtypeP, hOddT, h92⟩

public theorem section14_theorem_14_9_late_type_T1_zeta_mem_base_and_kernel_of_h10_and_calt1
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    {S T1T : Finset (Section1.ClassFunction Tmax)}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (h10 : Section10.hypothesis_10_1_supported_data Tmax Q W2 W1
      (section16HatW W2 W1) S τT)
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    ζ ∈ S ∧ Section1.subgroupInKernel' ζ ((Q ⊔ D).subgroupOf Tmax) := by
  classical
  rcases hTtypeP with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit, _hFitLe,
      _hW1le, _hW1cyc, _hW1ne, _hCentralizer, _hNormalizer⟩
  have hQVsub_eq_der : (Q ⊔ V).subgroupOf Tmax = derivedSubgroup Tmax := by
    rw [← hDerComp.2.2.1]
    exact section12_ambientDerivedSubgroup_subgroupOf_eq
  have hT1Ind :
      Section6.inducedKernelFamily ((Q ⊔ V).subgroupOf Tmax)
        (Q.subgroupOf Tmax) T1T :=
    section14_inducedKernelFamily_of_kernelInducedFamily_self hCalT1
  have hSbotDer :=
    Section10.inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10
  have hSbot :
      Section6.inducedKernelFamily ((Q ⊔ V).subgroupOf Tmax) ⊥ S := by
    simpa [hQVsub_eq_der] using hSbotDer
  have hζS : ζ ∈ S :=
    Section6.inducedKernelFamily_subset_base hSbot hT1Ind hζ
  have hζKerQ : Section1.subgroupInKernel' ζ (Q.subgroupOf Tmax) := by
    rcases (hT1Ind.2 ζ).mp hζ with ⟨θ, hθirr, hθker, _hθne, hζeq⟩
    haveI : (Q.subgroupOf Tmax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hQMF
    haveI : ((Q ⊔ V).subgroupOf Tmax).Normal := by
      rw [hQVsub_eq_der]
      infer_instance
    rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
    have hρker :
        Section1.subgroupInKernel' ρ.character
          ((Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax)) := by
      simpa [hθeq] using hθker
    have hindKer :
        Section1.subgroupInKernel'
          (Section1.inducedCF ((Q ⊔ V).subgroupOf Tmax) ρ.character)
          (Q.subgroupOf Tmax) :=
      (Section1.proposition_1_6_a ((Q ⊔ V).subgroupOf Tmax)
        (Q.subgroupOf Tmax) hT1Ind.1 ρ).mp hρker
    simpa [hθeq, hζeq] using hindKer
  rcases hctx.1 with
    ⟨_hcaseCtx, _hSTypeP, _hTTypeP, _hpW2, _hqW1, _hCeq, _hDeq, _hc, hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hd_one : d = 1 :=
    Section13.theorem_13_12 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  have hDcard : Nat.card D = 1 := by
    rw [← hd, hd_one]
  have hD_bot : D = ⊥ := (Subgroup.card_eq_one (H := D)).1 hDcard
  have hQD_eq : Q ⊔ D = Q := by
    simp [hD_bot]
  exact ⟨hζS, by simpa [hQD_eq] using hζKerQ⟩

public theorem section14_inducedCF_principal_eq_of_subgroup_eq
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (h : H = K) :
    Section1.inducedCF H (Section1.principalCharacter H) =
      Section1.inducedCF K (Section1.principalCharacter K) := by
  cases h
  rfl

public theorem section14_theorem_14_9_late_type_T1_principalInducedCharacter_eq_muColumn_base
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {Tmax Q V W2 W1 : Subgroup G}
    {Wloc : Subgroup Tmax}
    {A A0 : Set Tmax}
    {i0 : I} {j0 : J}
    {μloc : I → J → Section1.ClassFunction Tmax}
    {δSign : J → ℤ}
    {ωloc : I → J → Section1.ClassFunction Wloc}
    {σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
      Wloc A A0 i0 j0 μloc δSign ωloc σloc τT) :
    Section7.principalInducedCharacter Tmax (Q ⊔ V) =
      Section10.muColumn μloc j0 := by
  classical
  rcases hTtypeP with
    ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit, _hFitLe,
      _hW1le, _hW1cyc, _hW1ne, _hCentralizer, _hNormalizer⟩
  have hQVsub_eq_der : (Q ⊔ V).subgroupOf Tmax = derivedSubgroup Tmax := by
    rw [← hDerComp.2.2.1]
    exact section12_ambientDerivedSubgroup_subgroupOf_eq
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData
      hNotation10 with
    ⟨σM, xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, _h43c, _h43d, h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have hbase :=
    Section4.proposition_4_4_base
      (W2.subgroupOf Tmax) (W1.subgroupOf Tmax) Wloc I J i0 j0
      ωloc σM μloc (fun j : J => ((δSign j : ℤ) : ℂ)) hω h43b
  have hxChar0 : xChar j0 = Section1.principalCharacter (derivedSubgroup Tmax) := by
    have hres := h45a.1 i0 j0
    rw [hbase.2] at hres
    have hprincipal :
        Section1.subgroupRestriction (derivedSubgroup Tmax)
            (Section1.principalCharacter Tmax) =
          Section1.principalCharacter (derivedSubgroup Tmax) := by
      ext x
      simp [Section1.subgroupRestriction, Section1.principalCharacter]
    exact hres.symm.trans hprincipal
  have hMuColumn_eq_indDer :
      Section10.muColumn μloc j0 =
        Section1.inducedCF (derivedSubgroup Tmax)
          (Section1.principalCharacter (derivedSubgroup Tmax)) := by
    have hind := h45a.2.2 j0
    rw [hxChar0] at hind
    simpa [Section10.muColumn, Section4Scratch.piColumn] using hind.symm
  calc
    Section7.principalInducedCharacter Tmax (Q ⊔ V)
        = Section1.inducedCF ((Q ⊔ V).subgroupOf Tmax)
            (Section1.principalCharacter ((Q ⊔ V).subgroupOf Tmax)) := rfl
    _ = Section1.inducedCF (derivedSubgroup Tmax)
          (Section1.principalCharacter (derivedSubgroup Tmax)) :=
        section14_inducedCF_principal_eq_of_subgroup_eq hQVsub_eq_der
    _ = Section10.muColumn μloc j0 := hMuColumn_eq_indDer.symm

/-- Source package needed to specialize PF `(11.9)(a)` to the T-side
`βT0 = ν_0 - ζ` line in PF `(14.9)`.

The fields intentionally expose the exact threading data: a T-side PF
`(11.2)` package, the matching Section 10 `(4.6)` notation, the Section 11
subfamily containing the chosen `ζ`, the transformed `Irr(W)` family, and the
identifications of Section 13's `η 0 1` and `ν_0` with the local row/column
notation.  For the scalar argument, PF `(11.9)` only needs `η 0 1` to lie in
a non-base local row; its local column need not be the base column. -/
@[expose] public def section14_theorem_14_9_late_type_T1PF11RowProjectionSourceData
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Tmax Q V D W2 W1 : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (η01 : Section1.ClassFunction G)
    (ζ : Section1.ClassFunction Tmax)
    (p q : ℕ) : Prop :=
  ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
    ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      letI : Fintype I := instI
      letI : DecidableEq I := decI
      letI : Fintype J := instJ
      letI : DecidableEq J := decJ
      ∃ Wloc : Subgroup Tmax, ∃ A A0 : Set Tmax,
          ∃ S SHC : Finset (Section1.ClassFunction Tmax),
            ∃ R : Finset (Section1.ClassFunction G),
            ∃ i0 i1 : I, ∃ j0 j1 : J,
              ∃ μloc : I → J → Section1.ClassFunction Tmax,
                ∃ δSign : J → ℤ,
                  ∃ ωloc : I → J → Section1.ClassFunction Wloc,
                    ∃ σloc : Section1.ClassFunction Wloc →ₗ[ℂ]
                        Section1.ClassFunction G,
                      Section11.hypothesis_11_2_data Tmax Q Q V D ⊥ W2 W1
                          S τT q p ∧
                        Section10.section10FourSixNotationSupportedData Tmax W2 W1
                          Wloc A A0 i0 j0 μloc δSign ωloc σloc τT ∧
                        Section11.section11Subfamily (Q ⊔ D) S SHC ∧
                        ζ ∈ SHC ∧
                        Section11.transformedIrreducibleFamily R σloc ∧
                        i0 ≠ i1 ∧
                        η01 = σloc (ωloc i1 j1) ∧
                          Section7.principalInducedCharacter Tmax (Q ⊔ V) =
                            Section10.muColumn μloc j0

  
  @[expose] public def section14_theorem_14_9_late_type_T1PF11FamilyCoreSourceData
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Tmax Q W2 W1 : Subgroup G)
      (Wloc : Subgroup Tmax)
      (i0 : I) (_j0 : J)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (η01 : Section1.ClassFunction G) : Prop :=
    ∃ S : Finset (Section1.ClassFunction Tmax), ∃ i1 : I, ∃ j1 : J,
      Section10.hypothesis_10_1_supported_data Tmax Q W2 W1
          (section16HatW W2 W1) S τT ∧
        i0 ≠ i1 ∧
        η01 = σloc (ωloc i1 j1)

  /-- The assembled T-side family package needed by the PF `(11.9)` adapter.

  The transformed `Irr(W)` family is not included here because it is a direct
  consequence of the Section 10 omega table; see
  `section14_transformedIrreducibleFamily_of_section10FourSixNotationData`. -/
  @[expose] public def section14_theorem_14_9_late_type_T1PF11FamilySourceData
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Tmax Q V D W2 W1 : Subgroup G)
      (Wloc : Subgroup Tmax)
      (i0 : I) (j0 : J)
      (μloc : I → J → Section1.ClassFunction Tmax)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (η01 : Section1.ClassFunction G)
      (ζ : Section1.ClassFunction Tmax)
      (_p _q : ℕ) : Prop :=
    ∃ S : Finset (Section1.ClassFunction Tmax), ∃ i1 : I, ∃ j1 : J,
      Section10.hypothesis_10_1_supported_data Tmax Q W2 W1
          (section16HatW W2 W1) S τT ∧
        ζ ∈ S ∧
        Section1.subgroupInKernel' ζ ((Q ⊔ D).subgroupOf Tmax) ∧
        i0 ≠ i1 ∧
        η01 = σloc (ωloc i1 j1) ∧
        Section7.principalInducedCharacter Tmax (Q ⊔ V) =
          Section10.muColumn μloc j0

  
  @[expose] public def section14_theorem_14_9_late_type_T1PF11Type34SourceData
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      (Tmax Q V D W2 W1 : Subgroup G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (η01 : Section1.ClassFunction G)
      (ζ : Section1.ClassFunction Tmax)
      (p q : ℕ) : Prop :=
    ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
        letI : Fintype I := instI
        letI : DecidableEq I := decI
        letI : Fintype J := instJ
        letI : DecidableEq J := decJ
        ∃ Wloc : Subgroup Tmax, ∃ A A0 : Set Tmax,
          ∃ S SHC : Finset (Section1.ClassFunction Tmax),
            ∃ R : Finset (Section1.ClassFunction G),
              ∃ i0 i1 : I, ∃ j0 j1 : J,
                ∃ μloc : I → J → Section1.ClassFunction Tmax,
                  ∃ δSign : J → ℤ,
                    ∃ ωloc : I → J → Section1.ClassFunction Wloc,
                      ∃ σloc : Section1.ClassFunction Wloc →ₗ[ℂ]
                          Section1.ClassFunction G,
                        Section11.hypothesis_11_2_data Tmax Q Q V D ⊥ W2 W1
                            S τT q p ∧
                          Section10.section10FourSixNotationSupportedData Tmax W2 W1
                            Wloc A A0 i0 j0 μloc δSign ωloc σloc τT ∧
                          Section11.section11Subfamily (Q ⊔ D) S SHC ∧
                          ζ ∈ SHC ∧
                          Section11.transformedIrreducibleFamily R σloc ∧
                          i0 ≠ i1 ∧
                          η01 = σloc (ωloc i1 j1) ∧
                          Section7.principalInducedCharacter Tmax (Q ⊔ V) =
                            Section10.muColumn μloc j0 ∧
                          Section5.orthogonalToFinset R
                            (τT (Section10.muColumn μloc j0 - ζ) -
                              Finset.sum Finset.univ
                                (fun j : J => σloc (ωloc i0 j))) ∧
                          p > q ∧
                          section16TypeIII Tmax Q

  public theorem section14_theorem_14_9_late_type_T1_pf11_type34_of_row_projection_source
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {Tmax Q V D W2 W1 : Subgroup G}
      {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
      {η01 : Section1.ClassFunction G}
      {ζ : Section1.ClassFunction Tmax}
      {p q : ℕ} :
      section14_theorem_14_9_late_type_T1PF11RowProjectionSourceData
          Tmax Q V D W2 W1 τT η01 ζ p q →
        section14_theorem_14_9_late_type_T1PF11Type34SourceData
          Tmax Q V D W2 W1 τT η01 ζ p q := by
    classical
    intro hsource
    rcases hsource with
      ⟨I, instI, decI, J, instJ, decJ, Wloc, A, A0, S, SHC, R, i0, i1, j0, j1,
        μloc, δSign, ωloc, σloc, h11, hNotation10, hSHC, hζSHC, hR, hi1,
        hη01, hPrincipal⟩
    letI : Fintype I := instI
    letI : DecidableEq I := decI
    letI : Fintype J := instJ
    letI : DecidableEq J := decJ
    rcases
        Section11.theorem_11_9
          Tmax Q Q V D ⊥ W2 W1 Wloc A A0 S SHC R i0 j0
          μloc δSign ωloc σloc τT ζ q p
          h11 hNotation10 hSHC hζSHC hR with
      ⟨hOrth, hpgtq, _hcaseB, hTypeIII⟩
    exact
      ⟨I, instI, decI, J, instJ, decJ, Wloc, A, A0, S, SHC, R, i0, i1, j0, j1,
        μloc, δSign, ωloc, σloc, h11, hNotation10, hSHC, hζSHC, hR, hi1,
        hη01, hPrincipal, hOrth, hpgtq, hTypeIII⟩

  public theorem section14_theorem_14_9_late_type_T1_pf11_row_projection_of_type34_source
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {Tmax Q V D W2 W1 : Subgroup G}
      {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
      {η01 : Section1.ClassFunction G}
      {ζ : Section1.ClassFunction Tmax}
      {p q : ℕ} :
      section14_theorem_14_9_late_type_T1PF11Type34SourceData
          Tmax Q V D W2 W1 τT η01 ζ p q →
        section14_theorem_14_9_late_type_T1PF11RowProjectionSourceData
          Tmax Q V D W2 W1 τT η01 ζ p q := by
    classical
    intro hsource
    rcases hsource with
      ⟨I, instI, decI, J, instJ, decJ, Wloc, A, A0, S, SHC, R, i0, i1, j0, j1,
        μloc, δSign, ωloc, σloc, h11, hNotation10, hSHC, hζSHC, hR, hi1,
        hη01, hPrincipal, _hOrth, _hpgtq, _hTypeIII⟩
    exact
      ⟨I, instI, decI, J, instJ, decJ, Wloc, A, A0, S, SHC, R, i0, i1, j0, j1,
        μloc, δSign, ωloc, σloc, h11, hNotation10, hSHC, hζSHC, hR, hi1,
        hη01, hPrincipal⟩

  public theorem section14_theorem_14_9_late_type_T1_hypothesis10_typeIIIIVV_source_bridge
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q)
      (_hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1) :
      Section10.typeIIIIVVData Tmax Q W2 W1 (section16HatW W2 W1) := by
    classical
    have hnotII :
        ¬ Section8.typeIIDefinitionData Tmax Q := by
      intro hII
      rcases hctx.1 with
        ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
          _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
          _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
          hChoice, _hMin, _hFourSixS, _hFourSixT⟩
      rcases hcase with
        ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, hTmax, _hSMF,
          hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
          _hTType, _hCover⟩
      rcases hLateType with hIII | hIVV
      · rcases hChoice Tmax Q hTmax hTMF (Or.inr (Or.inr (Or.inl hIII))) with
          ⟨Ms, hMs⟩
        rcases hMs with hI | hIIbranch | hIIIbranch | hIVbranch | hVbranch
        · rcases hI with ⟨_hI, hnotII, _hnotIII, _hnotIV, _hnotV, _hMs⟩
          exact hnotII hII
        · rcases hIIbranch with ⟨_hnotI, _hII, hnotIII, _hnotIV, _hnotV, _hMs⟩
          exact hnotIII hIII
        · rcases hIIIbranch with ⟨_hnotI, hnotII, _hIII, _hnotIV, _hnotV, _hMs⟩
          exact hnotII hII
        · rcases hIVbranch with ⟨_hnotI, hnotII, hnotIII, _hIV, _hnotV, _hMs⟩
          exact hnotII hII
        · rcases hVbranch with ⟨_hnotI, hnotII, hnotIII, _hnotIV, _hV, _hMs⟩
          exact hnotII hII
      · rcases hIVV with hIV | hV
        · rcases hChoice Tmax Q hTmax hTMF
              (Or.inr (Or.inr (Or.inr (Or.inl hIV)))) with
            ⟨Ms, hMs⟩
          rcases hMs with hI | hIIbranch | hIIIbranch | hIVbranch | hVbranch
          · rcases hI with ⟨_hI, hnotII, _hnotIII, _hnotIV, _hnotV, _hMs⟩
            exact hnotII hII
          · rcases hIIbranch with ⟨_hnotI, _hII, _hnotIII, hnotIV, _hnotV, _hMs⟩
            exact hnotIV hIV
          · rcases hIIIbranch with ⟨_hnotI, hnotII, _hIII, hnotIV, _hnotV, _hMs⟩
            exact hnotII hII
          · rcases hIVbranch with ⟨_hnotI, hnotII, _hnotIII, _hIV, _hnotV, _hMs⟩
            exact hnotII hII
          · rcases hVbranch with ⟨_hnotI, hnotII, _hnotIII, hnotIV, _hV, _hMs⟩
            exact hnotII hII
        · rcases hChoice Tmax Q hTmax hTMF
              (Or.inr (Or.inr (Or.inr (Or.inr hV)))) with
            ⟨Ms, hMs⟩
          rcases hMs with hI | hIIbranch | hIIIbranch | hIVbranch | hVbranch
          · rcases hI with ⟨_hI, hnotII, _hnotIII, _hnotIV, _hnotV, _hMs⟩
            exact hnotII hII
          · rcases hIIbranch with ⟨_hnotI, _hII, _hnotIII, _hnotIV, hnotV, _hMs⟩
            exact hnotV hV
          · rcases hIIIbranch with ⟨_hnotI, hnotII, _hIII, _hnotIV, hnotV, _hMs⟩
            exact hnotII hII
          · rcases hIVbranch with ⟨_hnotI, hnotII, _hnotIII, _hIV, hnotV, _hMs⟩
            exact hnotII hII
          · rcases hVbranch with ⟨_hnotI, hnotII, _hnotIII, _hnotIV, _hV, _hMs⟩
            exact hnotII hII
    have hT13 :=
      Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
        Tfam Sfam τT τS q p v u d c
        (section14_hypothesis_13_1_sourceData_swap hctx.1)
    have hIII : Section8.typeIIIDefinitionData Tmax Q := by
      rcases hT13 with
        ⟨_hTMF, hTtypes, _hTtypeII_of_pq, _hVcomm, _hfrob, _hQelem,
          _hQcard, _hv, _hTfamCoh, _hTI, _hTau, _hnorm⟩
      rcases hTtypes with hII | hIII
      · exact False.elim (hnotII hII)
      · exact hIII
    exact
      Section13.section13_theorem_13_2_typeIIIIVVData_of_sourceContext
        Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
        q p v u d c (section14_hypothesis_13_1_sourceData_swap hctx.1)
        (Or.inl hIII)

  public theorem section14_theorem_14_9_late_type_T1_hypothesis10_source_bridge
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (Wloc : Subgroup Tmax)
      (A A0 : Set Tmax)
      (i0 : I) (j0 : J)
      (μloc : I → J → Section1.ClassFunction Tmax)
      (δSign : J → ℤ)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q)
      (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
      (hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
        Wloc A A0 i0 j0 μloc δSign ωloc σloc τT) :
      ∃ S : Finset (Section1.ClassFunction Tmax),
        Section10.hypothesis_10_1_supported_data Tmax Q W2 W1
          (section16HatW W2 W1) S τT := by
    classical
    have hType :
        Section10.typeIIIIVVData Tmax Q W2 W1 (section16HatW W2 W1) :=
      section14_theorem_14_9_late_type_T1_hypothesis10_typeIIIIVV_source_bridge
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hctx hLateType hTtypeP
    rcases Section12.exists_puncturedInducedFamily (derivedSubgroup Tmax) with
      ⟨S, hSderived0⟩
    have hSderived : Section10.derivedInducedFamily Tmax S := by
      simpa [Section10.derivedInducedFamily, Section7.puncturedInducedFamily]
        using hSderived0
    rcases hctx.1 with
      ⟨hcaseCtx, _hSTypeP, _hTTypePsrc, _hpW2, _hqW1, _hCeq, _hDeq, _hc,
        _hd, _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    rcases hcaseCtx with
      ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, _hSmax, hTmaxMax,
        _hSMF, _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII,
        _hSType, _hTType, _hCover⟩
    have hTtypePcopy := hTtypeP
    rcases hTtypePcopy with
      ⟨hQMF, _hW2cyc, _hW2ne, hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit, _hFitLe,
        hW1leQSecond, _hW1cyc, _hW1ne, _hCentralizer, _hNormalizer⟩
    have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := hDerComp.2.2.1
    have hQleT : Q ≤ Tmax :=
      hDerComp.1.trans (section12_ambientDerivedSubgroup_le (G := G) (E := Tmax))
    have hW2leT : W2 ≤ Tmax := hW2Hall.1
    have hW1leT : W1 ≤ Tmax :=
      ((le_inf_iff.mp hW1leQSecond).1).trans hQleT
    have hWsupT : W2 ⊔ W1 ≤ Tmax := sup_le hW2leT hW1leT
    have hDade :
        Section10.dadeIsometryRelativeToA0SupportedSourceData Tmax Q τT := by
      rcases hNotation10 with
        ⟨MFsrc, Ms, Abook, A0book, A1book, hSource, _hWloc, _hA0,
          _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc,
          _h45, _h48, _hTauA0, _hFull⟩
      rcases hSource with ⟨_hApre, _hA0pre, h810, H_A0, hA0M, hτDade⟩
      have hMFsrc_eq : MFsrc = Q :=
        section16MFSubgroup_unique h810.2.1 hQMF
      refine ⟨Ms, Abook, A0book, A1book, H_A0, ?_, hA0M, hτDade⟩
      simpa [hMFsrc_eq] using h810
    have h46 :
        ∃ Apre : Set Tmax,
          Section4Scratch.hypothesis_4_6_statement
            (derivedSubgroup Tmax)
            (W2.subgroupOf Tmax)
            (W1.subgroupOf Tmax)
            ((W2 ⊔ W1).subgroupOf Tmax)
            (derivedSubgroup Tmax)
            Apre := by
      have hNotation10Copy := hNotation10
      rcases hNotation10Copy with
        ⟨_MFsrc, _Ms, _Abook, _A0book, _A1book, _hSource, hWloc, _hA0,
          _h46loc, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc,
          _h45, _h48, _hTauA0, _hFull⟩
      refine ⟨A, ?_⟩
      have h46derived :=
        Section10.hypothesis_4_6_derived_of_section10FourSixNotationSupportedData_of_late
          hQMF hLateType hNotation10
      rwa [hWloc] at h46derived
    have hNotation10Exists :
        ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
        ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
        ∃ W10 : Subgroup Tmax, ∃ A10 A010 : Set Tmax, ∃ i010 : I, ∃ j010 : J,
        ∃ μ10 : I → J → Section1.ClassFunction Tmax,
        ∃ δ10 : J → ℤ,
        ∃ ω10 : I → J → Section1.ClassFunction W10,
        ∃ σ10 : Section1.ClassFunction W10 →ₗ[ℂ] Section1.ClassFunction G,
          @Section10.section10FourSixNotationSupportedData G _ _ I J instI instJ decI decJ
            Tmax W2 W1 W10 A10 A010 i010 j010 μ10 δ10 ω10 σ10 τT := by
      exact ⟨I, inferInstance, inferInstance, J, inferInstance, inferInstance,
        Wloc, A, A0, i0, j0, μloc, δSign, ωloc, σloc, hNotation10⟩
    have hS8 :
        Section8.section8InducedNonkernelFamily Tmax (Q ⊔ V) S := by
      have hS8der :
          Section8.section8InducedNonkernelFamily Tmax
            (ambientDerivedSubgroup Tmax) S :=
        Section10.section8InducedNonkernelFamily_of_typeP_derivedInducedFamily
          hTtypeP hSderived
      simpa [hDerEq] using hS8der
    rcases
        section14_theorem_14_9_late_type_T1_calt1_hypothesis52_fullData_source_bridge
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          p q u v c d hctx hLateType hTtypeP with
      ⟨d52, hd52τ, _hSigmaAgree⟩
    have h52 :
        Section5.hypothesis_5_2_statement S τT := by
      have h52d :
          Section5.hypothesis_5_2_statement S d52.tau :=
        Section8.theorem_8_15_hypothesis_5_2_of_fullData
          (G := G) (M := Tmax) (Ms := Q ⊔ V) (W1 := W2) (W2 := W1)
          (A := Section8.section8CentralizerUnion
            (ambientDerivedSubgroup Tmax) (Q ⊔ V))
          (S := S) (inferInstance : IsMinCE G) d52 hS8
      rwa [hd52τ] at h52d
    exact ⟨S, hTmaxMax, hType, hSderived, hW2leT, hW1leT, hWsupT, hDade,
      h46, hNotation10Exists, h52⟩

  public theorem section14_theorem_14_9_late_type_T1_local_table_omega01_nonbase
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (Wloc : Subgroup Tmax)
      (A A0 : Set Tmax)
      (i0 : I) (j0 : J)
      (μloc : I → J → Section1.ClassFunction Tmax)
      (δSign : J → ℤ)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
      (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
        Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
      (hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
        Wloc A A0 i0 j0 μloc δSign ωloc σloc τT) :
      ∃ e : W ≃* Wloc,
        (∀ x : W, (((e x : Wloc) : Tmax) : G) = (x : G)) ∧
          ∃ i1 : I, i0 ≠ i1 ∧
            Section6.theorem_6_8_transportClassFunction e (ω 0 1) =
              ωloc i1 j0 := by
    classical
    rcases section14_context_primes_of_sourceData hctx with ⟨hp, hq⟩
    have hsource := hctx.1
    unfold Section13.hypothesis_13_1_sourceData at hsource
    rcases hsource with
      ⟨hcaseB, _hSTypeP, _hTtypePsrc, _hp_card, _hq_card, _hC, _hD,
        _hc, _hd, _hu, _hv, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hChar, _hDiff, _hZero, _hConj, _hConjTau, _hChoice,
        _hmin, _hFourSixS, _hFourSixT⟩
    have hprod : section12InternalDirectProduct W1 W2 W := hcaseB.1
    have hW_eq : W = W1 ⊔ W2 := hprod.2.2.1
    have hW_swap : W = W2 ⊔ W1 := by
      simp [hW_eq, sup_comm]
    rcases hTtypeP with
      ⟨_hQMF, _hW2cyc, _hW2ne, hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit, _hFitLe,
        hW1leQSecond, _hW1cyc, _hW1ne, _hCentralizer, _hNormalizer⟩
    have hQleT : Q ≤ Tmax :=
      hDerComp.1.trans (section12_ambientDerivedSubgroup_le (G := G) (E := Tmax))
    have hW2leT : W2 ≤ Tmax := hW2Hall.1
    have hW1leT : W1 ≤ Tmax :=
      ((le_inf_iff.mp hW1leQSecond).1).trans hQleT
    have hWsupT : W2 ⊔ W1 ≤ Tmax := sup_le hW2leT hW1leT
    rcases hNotation10 with
      ⟨_MFsrc, _Ms, _Abook, _A0book, _A1book, _hSource, hWloc, _hA0,
        _h46, hωloc, _hIso, _hVirt, _hPrin, _hσAgreeCyc,
        _h45, _h48, _hTauA0, _hFull⟩
    let eSup : W ≃* (W2 ⊔ W1 : Subgroup G) :=
      MulEquiv.subgroupCongr hW_swap
    let eSub : (W2 ⊔ W1 : Subgroup G) ≃* ((W2 ⊔ W1).subgroupOf Tmax) :=
      (Subgroup.subgroupOfEquivOfLe (H := W2 ⊔ W1) (K := Tmax) hWsupT).symm
    let eLoc : ((W2 ⊔ W1).subgroupOf Tmax) ≃* Wloc :=
      MulEquiv.subgroupCongr hWloc.symm
    let e : W ≃* Wloc := (eSup.trans eSub).trans eLoc
    have he_apply : ∀ x : W, (((e x : Wloc) : Tmax) : G) = (x : G) := by
      intro x
      simp [e, eSup, eSub, eLoc, Subgroup.subgroupOfEquivOfLe,
        MulEquiv.subgroupCongr_apply]
    refine ⟨e, he_apply, ?_⟩
    rcases hNotation with
      ⟨hωData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
        _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
        _hμsum, _hνsum⟩
    rcases hωData with ⟨_h31, hqpos, _hppos, ωFin, hωFin, hωNat⟩
    have h0q : 0 < q := hq.pos
    have h0p : 0 < p := hp.pos
    have h1p : 1 < p := hp.one_lt
    have hω01_irr : Section1.IsIrreducibleCharacterOnGroup (ω 0 1) := by
      rw [hωNat 0 1 h0q h1p]
      exact hωFin.irreducible ⟨0, h0q⟩ ⟨1, h1p⟩
    have hχloc_irr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) :=
      Section6.theorem_6_8_transportClassFunction_irreducible e hω01_irr
    have he_symm_apply :
        ∀ x : Wloc, (((e.symm x : W) : G)) = (((x : Wloc) : Tmax) : G) := by
      intro x
      have hx := he_apply (e.symm x)
      simpa using hx.symm
    have hχloc_kernel :
        Section1.subgroupInKernel'
          (Section6.theorem_6_8_transportClassFunction e (ω 0 1))
          ((W1.subgroupOf Tmax).subgroupOf Wloc) := by
      intro a
      have haW1 : (((e.symm (a : Wloc) : W) : G)) ∈ W1 := by
        have haT : (((a : Wloc) : Tmax) : G) ∈ W1 := by
          exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp a.2)
        simpa [he_symm_apply (a : Wloc)] using haT
      have hker :=
        hωFin.right_kernel ⟨1, h1p⟩
          ⟨e.symm (a : Wloc), by
            simpa [Subgroup.mem_subgroupOf] using haW1⟩
      have hkerω : (ω 0 1) (e.symm (a : Wloc)) = (ω 0 1) 1 := by
        simpa [hωNat 0 1 h0q h1p, Section1.degree] using hker
      simpa [Section6.theorem_6_8_transportClassFunction, Section1.degree] using hkerω
    rcases (hωloc.left_kernel_exact
        (Section6.theorem_6_8_transportClassFunction e (ω 0 1))
        hχloc_irr).1 hχloc_kernel with
      ⟨i1, hi1eq⟩
    have hi1_ne : i0 ≠ i1 := by
      intro hi
      have hχloc_principal :
          Section6.theorem_6_8_transportClassFunction e (ω 0 1) =
            Section1.principalCharacter Wloc := by
        have hi1eq' :
            Section6.theorem_6_8_transportClassFunction e (ω 0 1) =
              ωloc i0 j0 := by
          simpa [← hi] using hi1eq
        exact hi1eq'.trans hωloc.principal
      have hω01_principal : ω 0 1 = Section1.principalCharacter W := by
        ext x
        have hx := congrFun hχloc_principal (e x)
        simpa [Section6.theorem_6_8_transportClassFunction,
          Section1.principalCharacter] using hx
      have hω00_principal : ω 0 0 = Section1.principalCharacter W := by
        rw [hωNat 0 0 h0q h0p]
        exact hωFin.principal
      have hωeq : ωFin ⟨0, h0q⟩ ⟨1, h1p⟩ =
          ωFin ⟨0, h0q⟩ ⟨0, h0p⟩ := by
        calc
          ωFin ⟨0, h0q⟩ ⟨1, h1p⟩ = ω 0 1 := (hωNat 0 1 h0q h1p).symm
          _ = Section1.principalCharacter W := hω01_principal
          _ = ω 0 0 := hω00_principal.symm
          _ = ωFin ⟨0, h0q⟩ ⟨0, h0p⟩ := hωNat 0 0 h0q h0p
      have hfin := (hωFin.pairwise_eq hωeq).2
      have hfin_ne : (⟨1, h1p⟩ : Fin p) ≠ ⟨0, h0p⟩ := by
        intro h
        have hval := congrArg Fin.val h
        norm_num at hval
      exact hfin_ne hfin
    exact ⟨i1, hi1_ne, hi1eq⟩

  /-- Section 10 ambient images of transported irreducibles are signed
  irreducibles.

  This is the signed-character hypothesis needed before applying PF `(3.9)(a)`
  to compare the global Section 13 Dade map with the T-side Section 10 table.
  The proof uses only the Section 10 isometry/virtual-character fields and the
  transport invariance of scalar products. -/
  public theorem section14_theorem_14_9_late_type_T1_sigma_transport_irreducible_signed
      {G : Type u} [Group G] [Finite G]
      {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      {Tmax W W1 W2 : Subgroup G}
      {Wloc : Subgroup Tmax}
      {A A0 : Set Tmax}
      {i0 : I} {j0 : J}
      {μloc : I → J → Section1.ClassFunction Tmax}
      {δSign : J → ℤ}
      {ωloc : I → J → Section1.ClassFunction Wloc}
      {σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G}
      {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
      (hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
        Wloc A A0 i0 j0 μloc δSign ωloc σloc τT)
      (e : W ≃* Wloc)
      {ξ : Section1.ClassFunction W}
      (hξ : Section1.IsIrreducibleCharacterOnGroup ξ) :
      Section3.IsSignedIrreducibleCharacter
        (σloc (Section6.theorem_6_8_transportClassFunction e ξ)) := by
    classical
    have hξloc_irr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section6.theorem_6_8_transportClassFunction e ξ) :=
      Section6.theorem_6_8_transportClassFunction_irreducible e hξ
    have hξ_class : Section1.IsClassFunction ξ :=
      section14_isClassFunction_of_irreducibleCharacterOnGroup hξ
    have hξloc_class :
        Section1.IsClassFunction
          (Section6.theorem_6_8_transportClassFunction e ξ) :=
      Section6.theorem_6_8_transportClassFunction_isClass e hξ_class
    rcases hNotation10 with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource, _hW, _hA0, _h46,
        _hωloc, hIso, hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
        _hTauA0, _hFull⟩
    have hξloc_virt :
        Theory.Character.IsVirtualCharacter
          (Section6.theorem_6_8_transportClassFunction e ξ) :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξloc_irr
    have himage_virt :
        Theory.Character.IsVirtualCharacter
          (σloc (Section6.theorem_6_8_transportClassFunction e ξ)) :=
      hVirt _ hξloc_virt
    have hselfW : Section1.scalarProduct W ξ ξ = 1 :=
      Section1.scalarProduct_irreducibleCharacter_self hξ
    have hself :
        Section1.scalarProduct G
          (σloc (Section6.theorem_6_8_transportClassFunction e ξ))
          (σloc (Section6.theorem_6_8_transportClassFunction e ξ)) = 1 := by
      calc
        Section1.scalarProduct G
            (σloc (Section6.theorem_6_8_transportClassFunction e ξ))
            (σloc (Section6.theorem_6_8_transportClassFunction e ξ)) =
          Section1.scalarProduct Wloc
            (Section6.theorem_6_8_transportClassFunction e ξ)
            (Section6.theorem_6_8_transportClassFunction e ξ) :=
            hIso _ _ hξloc_class hξloc_class
        _ = Section1.scalarProduct W ξ ξ :=
            Section6.theorem_6_8_scalarProduct_transportClassFunction e ξ ξ
        _ = 1 := hselfW
    exact Section5.signed_irreducible_of_virtual_norm_one_pf59 himage_virt hself

  public theorem section14_theorem_14_9_late_type_T1_sigma_transport_omega01_signed
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (Wloc : Subgroup Tmax)
      (A A0 : Set Tmax)
      (i0 : I) (j0 : J)
      (μloc : I → J → Section1.ClassFunction Tmax)
      (δSign : J → ℤ)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
        Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
      (hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
        Wloc A A0 i0 j0 μloc δSign ωloc σloc τT)
      (e : W ≃* Wloc) :
      Section3.IsSignedIrreducibleCharacter
        (σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1))) := by
    classical
    rcases section14_context_primes_of_sourceData hctx with ⟨hp, hq⟩
    have hNotationCopy := hNotation
    rcases hNotationCopy with
      ⟨hωData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
        _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
        _hμsum, _hνsum⟩
    rcases hωData with ⟨_h31, hqpos, _hppos, ωFin, hωFin, hωNat⟩
    have h0q : 0 < q := hq.pos
    have h1p : 1 < p := hp.one_lt
    have hω01_irr : Section1.IsIrreducibleCharacterOnGroup (ω 0 1) := by
      rw [hωNat 0 1 h0q h1p]
      exact hωFin.irreducible ⟨0, h0q⟩ ⟨1, h1p⟩
    exact
      section14_theorem_14_9_late_type_T1_sigma_transport_irreducible_signed
        (hNotation10 := hNotation10) e hω01_irr

  /-- PF `(3.9)` reduction for the PF `(14.9)` `cycTIisoC` bridge.

  Once the Section 10 ambient extension is known to agree with the transported
  `ω 0 1` on the swapped cyclic-TI set, PF `(3.9)(a)` identifies it with the
  transposed PF `(3.5)` model for the global Section 13 Dade map. -/
  public theorem section14_theorem_14_9_late_type_T1_sigma_transport_omega01_of_cyclicTI_agreement
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (Wloc : Subgroup Tmax)
      (A A0 : Set Tmax)
      (i0 : I) (j0 : J)
      (μloc : I → J → Section1.ClassFunction Tmax)
      (δSign : J → ℤ)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
        Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
      (hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
        Wloc A A0 i0 j0 μloc δSign ωloc σloc τT)
      (e : W ≃* Wloc)
      (hVagree : ∀ x : G, ∀ hx : x ∈ Section3.cyclicTISet W2 W1 W,
        σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) x =
          (ω 0 1) ⟨x, Section3.cyclicTISet_subset W2 W1 W hx⟩) :
      σ (ω 0 1) =
        σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) := by
    classical
    rcases section14_context_primes_of_sourceData hctx with ⟨hp, _hq⟩
    have h1p : 1 < p := hp.one_lt
    have hNotationCopy := hNotation
    rcases hNotation with
      ⟨hωData, hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
        _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
        _hμsum, _hνsum⟩
    rcases hωData with ⟨h31, h0q, h0p, ωFin, hωFin, hωNat⟩
    rcases Section3.pf35_data_of_theorem_3_2_map_statement hωFin σ hσmap with
      ⟨χ, horth, hsigned, h00, hInd, hσeq⟩
    have hσ_eq : σ = Section3.sigmaOfPF35 ωFin χ :=
      Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
        (W1 := W1) (W2 := W2) (W := W)
        (I := Fin q) (J := Fin p) (i0 := ⟨0, h0q⟩) (j0 := ⟨0, h0p⟩)
        (ω := ωFin) (χ := χ) h31 hωFin hσeq
    have hσ01_swap :
        σ (ω 0 1) =
          Section3.sigmaOfPF35
            (fun j i => ωFin i j) (fun j i => χ i j)
            ((fun j i => ωFin i j) ⟨1, h1p⟩ ⟨0, h0q⟩) := by
      calc
        σ (ω 0 1) = σ (ωFin ⟨0, h0q⟩ ⟨1, h1p⟩) := by
          rw [hωNat 0 1 h0q h1p]
        _ = Section3.sigmaOfPF35 ωFin χ
              (ωFin ⟨0, h0q⟩ ⟨1, h1p⟩) := by
          rw [hσ_eq]
        _ = Section3.sigmaOfPF35
              (fun j i => ωFin i j) (fun j i => χ i j)
              ((fun j i => ωFin i j) ⟨1, h1p⟩ ⟨0, h0q⟩) :=
            Section3.sigmaOfPF35_swap_apply_table
              ωFin χ ⟨0, h0q⟩ ⟨1, h1p⟩
    have horth_swap :
        Section3.IsOrthonormalDoubleFamily (fun j i => χ i j) := by
      intro p q
      rcases p with ⟨j, i⟩
      rcases q with ⟨j', i'⟩
      simpa [Prod.ext_iff, Prod.mk.injEq, eq_comm, and_left_comm,
        and_assoc, and_comm] using horth (i, j) (i', j')
    have hInd_swap :
        ∀ j i, j ≠ ⟨0, h0p⟩ → i ≠ ⟨0, h0q⟩ →
          Section1.inducedCF W
              (Section3.alphaIJ W ⟨0, h0p⟩ ⟨0, h0q⟩
                (fun j i => ωFin i j) j i) =
            Section1.principalCharacter G -
              (fun j i => χ i j) j ⟨0, h0q⟩ -
              (fun j i => χ i j) ⟨0, h0p⟩ i +
              (fun j i => χ i j) j i := by
      intro j i hj hi
      rw [Section3.alphaIJ_swap_eq (W := W) (ω := ωFin) i j]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hInd i j hi hj
    have hω01_irr :
        Section1.IsIrreducibleCharacterOnGroup
          ((fun j i => ωFin i j) ⟨1, h1p⟩ ⟨0, h0q⟩) := by
      exact hωFin.irreducible ⟨0, h0q⟩ ⟨1, h1p⟩
    have hXsigned :
        Section3.IsSignedIrreducibleCharacter
          (σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1))) :=
      section14_theorem_14_9_late_type_T1_sigma_transport_omega01_signed
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        Wloc A A0 i0 j0 μloc δSign ωloc σloc
        hctx hNotationCopy hNotation10 e
    have hVagreeFin :
        ∀ x : G, ∀ hx : x ∈ Section3.cyclicTISet W2 W1 W,
          σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) x =
            ((fun j i => ωFin i j) ⟨1, h1p⟩ ⟨0, h0q⟩)
              ⟨x, Section3.cyclicTISet_subset W2 W1 W hx⟩ := by
      intro x hx
      have hω01 : ω 0 1 = ωFin ⟨0, h0q⟩ ⟨1, h1p⟩ :=
        hωNat 0 1 h0q h1p
      simpa [hω01] using hVagree x hx
    have hXeq :
        σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) =
          Section3.sigmaOfPF35
            (fun j i => ωFin i j) (fun j i => χ i j)
            ((fun j i => ωFin i j) ⟨1, h1p⟩ ⟨0, h0q⟩) :=
      Section3.proposition_3_9_a_uniqueness_of_pf35
        (W1 := W2) (W2 := W1) (W := W)
        (I := Fin p) (J := Fin q)
        (i0 := ⟨0, h0p⟩) (j0 := ⟨0, h0q⟩)
        (ω := fun j i => ωFin i j) (χ := fun j i => χ i j)
        (Section3.hypothesis_3_1_statement_swap h31)
        (Section3.notation_3_3_statement_swap hωFin)
        horth_swap (fun j i => hsigned i j) (by simpa using h00)
        hInd_swap hω01_irr hXsigned hVagreeFin
    exact hσ01_swap.trans hXeq.symm


  public theorem section14_theorem_14_9_late_type_T1_sigma_transport_omega01_source_bridge
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (Wloc : Subgroup Tmax)
      (A A0 : Set Tmax)
      (i0 : I) (j0 : J)
      (μloc : I → J → Section1.ClassFunction Tmax)
      (δSign : J → ℤ)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (_ : Section8.typePDefinitionData Tmax Q V W2 W1)
      (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
        Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
      (hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
        Wloc A A0 i0 j0 μloc δSign ωloc σloc τT)
      (e : W ≃* Wloc)
      (he : ∀ x : W, (((e x : Wloc) : Tmax) : G) = (x : G)) :
      σ (ω 0 1) =
        σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) := by
    classical
    rcases section14_context_primes_of_sourceData hctx with ⟨hp, hq⟩
    have hNotationCopy := hNotation
    rcases hNotationCopy with
      ⟨hωData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
        _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
        _hμsum, _hνsum⟩
    rcases hωData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωNat⟩
    have hω01_irr : Section1.IsIrreducibleCharacterOnGroup (ω 0 1) := by
      rw [hωNat 0 1 hq.pos hp.one_lt]
      exact hωFin.irreducible ⟨0, hq.pos⟩ ⟨1, hp.one_lt⟩
    have hω01_class : Section1.IsClassFunction (ω 0 1) :=
      section14_isClassFunction_of_irreducibleCharacterOnGroup hω01_irr
    have htransportClass :
        Section1.IsClassFunction
          (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) :=
      Section6.theorem_6_8_transportClassFunction_isClass e hω01_class
    have hVagree : ∀ x : G, ∀ hx : x ∈ Section3.cyclicTISet W2 W1 W,
        σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) x =
          (ω 0 1) ⟨x, Section3.cyclicTISet_subset W2 W1 W hx⟩ := by
      intro x hx
      let xW : W := ⟨x, Section3.cyclicTISet_subset W2 W1 W hx⟩
      let y : Wloc := e xW
      let yT : Tmax := (y : Tmax)
      have hyG : (yT : G) = x := by
        simpa [xW, y, yT] using he xW
      have hyCyc :
          yT ∈ Section3.cyclicTISet
            (W2.subgroupOf Tmax) (W1.subgroupOf Tmax) Wloc := by
        rw [Section3.cyclicTISet_mem_iff]
        refine ⟨y.2, ?_, ?_⟩
        · intro hyW2
          have hyW2G : (yT : G) ∈ (W2 : Set G) :=
            Subgroup.mem_subgroupOf.mp hyW2
          exact Section3.cyclicTISet_not_mem_left W2 W1 W hx (by
            simpa [hyG] using hyW2G)
        · intro hyW1
          have hyW1G : (yT : G) ∈ (W1 : Set G) :=
            Subgroup.mem_subgroupOf.mp hyW1
          exact Section3.cyclicTISet_not_mem_right W2 W1 W hx (by
            simpa [hyG] using hyW1G)
      have hlocal :=
        Section10.sigma_agrees_cyclicTI_of_section10FourSixNotationSupportedData
          hNotation10
          (Section6.theorem_6_8_transportClassFunction e (ω 0 1))
          htransportClass yT hyCyc
      let yCyc : Wloc :=
        ⟨yT, Section3.cyclicTISet_subset
          (W2.subgroupOf Tmax) (W1.subgroupOf Tmax) Wloc hyCyc⟩
      have hyCycEq : yCyc = y := by
        ext
        rfl
      calc
        σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) x =
            Section6.theorem_6_8_transportClassFunction e (ω 0 1) yCyc := by
              simpa [hyG, yCyc] using hlocal
        _ = Section6.theorem_6_8_transportClassFunction e (ω 0 1) y := by
              rw [hyCycEq]
        _ = (ω 0 1) xW := by
              simp [Section6.theorem_6_8_transportClassFunction, y]
    exact
      section14_theorem_14_9_late_type_T1_sigma_transport_omega01_of_cyclicTI_agreement
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        Wloc A A0 i0 j0 μloc δSign ωloc σloc
        hctx hNotation hNotation10 e hVagree

  public theorem section14_theorem_14_9_late_type_T1_pf11_type34_family_nonbase_sigma_omega_source_bridge
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q)
      (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
      (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
        Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ) :
      ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
        letI : Fintype I := instI
        letI : DecidableEq I := decI
        letI : Fintype J := instJ
        letI : DecidableEq J := decJ
        ∃ Wloc : Subgroup Tmax, ∃ A0 : Set Tmax, ∃ i0 : I, ∃ j0 : J,
          ∃ μloc : I → J → Section1.ClassFunction Tmax,
            ∃ δSign : J → ℤ,
              ∃ ωloc : I → J → Section1.ClassFunction Wloc,
                ∃ σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G,
                  Section10.section10FourSixNotationSupportedData Tmax W2 W1 Wloc
                    (Section8.section8SubgroupSetPreimage Tmax
                      (Section8.section8CentralizerUnion
                        (ambientDerivedSubgroup Tmax) (Q ⊔ V)))
                    A0 i0 j0 μloc δSign ωloc σloc τT ∧
                  ∃ i1 : I, ∃ j1 : J,
                    i0 ≠ i1 ∧ σ (ω 0 1) = σloc (ωloc i1 j1) := by
    -- `FTtype34_structure maxT TtypeP notTtype2`: choose the concrete
    -- T-side Section 10 `(4.6)` table from the Section 13 source package and
    -- identify the Section 13 `ω_01^σ` character as a non-base row entry of
    -- that same table.
    classical
    let A : Set Tmax :=
      Section8.section8SubgroupSetPreimage Tmax
        (Section8.section8CentralizerUnion
          (ambientDerivedSubgroup Tmax) (Q ⊔ V))
    have hFourSixT : Section13.typePFourSixTauSourceData Tmax Q V W2 W1 τT := by
      have hsource := hctx.1
      unfold Section13.hypothesis_13_1_sourceData at hsource
      tauto
    rcases hFourSixT with
      ⟨I, instI, decI, J, instJ, decJ, Wloc, Asel, A0, i0, j0, μloc, δSign,
        ωloc, σloc, hNotation10, _hSigmaAgree, _hBookSource⟩
    letI : Fintype I := instI
    letI : DecidableEq I := decI
    letI : Fintype J := instJ
    letI : DecidableEq J := decJ
    have hNotation10Copy := hNotation10
    rcases hNotation10Copy with
      ⟨MFsrc, Ms, Abook, _A0book, _A1book, hSource, _hWloc, _hA0,
        _h46, _h33, _hIso, _hVirt, _hPrin, _hSigmaCyclic, _h45, _h48,
        _hTauIso, _hPackage⟩
    rcases hSource with
      ⟨hAsel, _hA0sub, h810, _H_A0, _hA0M, _hTauSource⟩
    have hTtypePcopy := hTtypeP
    rcases hTtypePcopy with
      ⟨hQMF, _hW2cyclic, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit, _hFitLe,
        _hW1le, _hW1cyclic, _hW1ne, _hCentralizer, _hNormalizer⟩
    have hMFsrc : MFsrc = Q :=
      section16MFSubgroup_unique h810.2.1 hQMF
    subst MFsrc
    have hAbook :
        Abook = Section8.section8CentralizerUnion
          (ambientDerivedSubgroup Tmax) Ms :=
      Section13.section13_notation_8_10_source_data_A_eq_centralizerUnion_of_late
        h810 hLateType
    have hMs : Ms = ambientDerivedSubgroup Tmax :=
      Section8.notation_8_10_source_data_ms_eq_ambientDerived_of_late
        h810 hLateType
    have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := hDerComp.2.2.1
    have hAselEq : Asel = A := by
      simpa [A, hAbook, hMs, hDerEq] using hAsel
    have hNotation10A :
        Section10.section10FourSixNotationSupportedData Tmax W2 W1 Wloc
          A A0 i0 j0 μloc δSign ωloc σloc τT := by
      simpa [hAselEq] using hNotation10
    have hNonbase :
        ∃ i1 : I, ∃ j1 : J,
          i0 ≠ i1 ∧ σ (ω 0 1) = σloc (ωloc i1 j1) := by
      rcases
          section14_theorem_14_9_late_type_T1_local_table_omega01_nonbase
            Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
            ω η μ ν μsum νsum δ δ' σ p q u v c d
            Wloc A A0 i0 j0 μloc δSign ωloc σloc
            hctx hTtypeP hNotation hNotation10A with
        ⟨e, he, i1, hi1_ne, hωtransport⟩
      refine ⟨i1, j0, hi1_ne, ?_⟩
      calc
        σ (ω 0 1) =
            σloc (Section6.theorem_6_8_transportClassFunction e (ω 0 1)) :=
          section14_theorem_14_9_late_type_T1_sigma_transport_omega01_source_bridge
            Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
            ω η μ ν μsum νsum δ δ' σ p q u v c d
            Wloc A A0 i0 j0 μloc δSign ωloc σloc
            hctx hTtypeP hNotation hNotation10A e he
        _ = σloc (ωloc i1 j0) := by rw [hωtransport]
    exact
      ⟨I, instI, decI, J, instJ, decJ, Wloc, A0, i0, j0, μloc, δSign,
        ωloc, σloc, hNotation10A, hNonbase⟩

  public theorem section14_theorem_14_9_late_type_T1_pf11_type34_family_row_source_bridge
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (Wloc : Subgroup Tmax)
      (A A0 : Set Tmax)
      (i0 : I) (j0 : J)
      (μloc : I → J → Section1.ClassFunction Tmax)
      (δSign : J → ℤ)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (_hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q)
      (_hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
      (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
        Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
      (_hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
        Wloc A A0 i0 j0 μloc δSign ωloc σloc τT)
      (hNonbase :
        ∃ i1 : I, ∃ j1 : J, i0 ≠ i1 ∧
          σ (ω 0 1) = σloc (ωloc i1 j1)) :
      ∃ i1 : I, ∃ j1 : J, i0 ≠ i1 ∧ η 0 1 = σloc (ωloc i1 j1) := by
    classical
    rcases section14_context_primes_of_sourceData hctx with ⟨hp, hq⟩
    rcases hNotation with
      ⟨_hωData, _hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
        _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
        _hμsum, _hνsum⟩
    have hη01 : η 0 1 = σ (ω 0 1) := hη 0 1 hq.pos hp.one_lt
    rcases hNonbase with ⟨i1, j1, hi1, hω01⟩
    exact ⟨i1, j1, hi1, hη01.trans hω01⟩

  public theorem section14_theorem_14_9_late_type_T1_pf11_type34_family_core_source_bridge
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (Wloc : Subgroup Tmax)
      (A A0 : Set Tmax)
      (i0 : I) (j0 : J)
      (μloc : I → J → Section1.ClassFunction Tmax)
      (δSign : J → ℤ)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q)
      (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
      (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
        Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
      (hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
        Wloc A A0 i0 j0 μloc δSign ωloc σloc τT)
      (hNonbase :
        ∃ i1 : I, ∃ j1 : J, i0 ≠ i1 ∧
          σ (ω 0 1) = σloc (ωloc i1 j1)) :
      section14_theorem_14_9_late_type_T1PF11FamilyCoreSourceData
        Tmax Q W2 W1 Wloc i0 j0 ωloc σloc τT (η 0 1) := by
    classical
    rcases
        section14_theorem_14_9_late_type_T1_hypothesis10_source_bridge
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          p q u v c d Wloc A A0 i0 j0 μloc δSign ωloc σloc
          hctx hLateType hTtypeP hNotation10 with
      ⟨S, h10⟩
    rcases
        section14_theorem_14_9_late_type_T1_pf11_type34_family_row_source_bridge
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          ω η μ ν μsum νsum δ δ' σ p q u v c d Wloc A A0 i0 j0
          μloc δSign ωloc σloc hctx hLateType hTtypeP hNotation
          hNotation10 hNonbase with
      ⟨i1, j1, hi1, hη01⟩
    exact ⟨S, i1, j1, h10, hi1, hη01⟩

  public theorem section14_theorem_14_9_late_type_T1_pf11_type34_family_source_bridge
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (Wloc : Subgroup Tmax)
      (A A0 : Set Tmax)
      (i0 : I) (j0 : J)
      (μloc : I → J → Section1.ClassFunction Tmax)
      (δSign : J → ℤ)
      (ωloc : I → J → Section1.ClassFunction Wloc)
      (σloc : Section1.ClassFunction Wloc →ₗ[ℂ] Section1.ClassFunction G)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q)
      (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
      (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
        Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
      (hNotation10 : Section10.section10FourSixNotationSupportedData Tmax W2 W1
        Wloc A A0 i0 j0 μloc δSign ωloc σloc τT)
      (hNonbase :
        ∃ i1 : I, ∃ j1 : J, i0 ≠ i1 ∧
          σ (ω 0 1) = σloc (ωloc i1 j1))
      {T1T : Finset (Section1.ClassFunction Tmax)}
      (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
      {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
      section14_theorem_14_9_late_type_T1PF11FamilySourceData
        Tmax Q V D W2 W1 Wloc i0 j0 μloc ωloc σloc τT
          (η 0 1) ζ p q := by
    classical
    rcases
        section14_theorem_14_9_late_type_T1_pf11_type34_family_core_source_bridge
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          ω η μ ν μsum νsum δ δ' σ p q u v c d Wloc A A0 i0 j0
          μloc δSign ωloc σloc hctx hLateType hTtypeP hNotation hNotation10
          hNonbase with
      ⟨S, i1, j1, h10, hi1, hη01⟩
    rcases
        section14_theorem_14_9_late_type_T1_zeta_mem_base_and_kernel_of_h10_and_calt1
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          p q u v c d hctx hTtypeP h10 hCalT1 hζ with
      ⟨hζS, hζKer⟩
    have hPrincipal :
        Section7.principalInducedCharacter Tmax (Q ⊔ V) =
          Section10.muColumn μloc j0 :=
      section14_theorem_14_9_late_type_T1_principalInducedCharacter_eq_muColumn_base
        hTtypeP hNotation10
    exact ⟨S, i1, j1, h10, hζS, hζKer, hi1, hη01, hPrincipal⟩

  public theorem section14_theorem_14_9_late_type_T1_pf11_type34_source_bridge
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
      (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
      (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (p q u v c d : ℕ)
      (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d)
      (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q)
      (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
      (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
        Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
      {T1T : Finset (Section1.ClassFunction Tmax)}
      (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
      {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
      section14_theorem_14_9_late_type_T1PF11Type34SourceData
        Tmax Q V D W2 W1 τT (η 0 1) ζ p q := by
    classical
    let A : Set Tmax :=
      Section8.section8SubgroupSetPreimage Tmax
        (Section8.section8CentralizerUnion
          (ambientDerivedSubgroup Tmax) (Q ⊔ V))
    rcases
        section14_theorem_14_9_late_type_T1_pf11_type34_family_nonbase_sigma_omega_source_bridge
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          ω η μ ν μsum νsum δ δ' σ p q u v c d
          hctx hLateType hTtypeP hNotation with
      ⟨I, instI, decI, J, instJ, decJ, Wloc, A0, i0, j0, μloc, δSign, ωloc,
        σloc, hNotation10, hNonbase⟩
    letI : Fintype I := instI
    letI : DecidableEq I := decI
    letI : Fintype J := instJ
    letI : DecidableEq J := decJ
    have hFamily :
        section14_theorem_14_9_late_type_T1PF11FamilySourceData
          Tmax Q V D W2 W1 Wloc i0 j0 μloc ωloc σloc τT
            (η 0 1) ζ p q :=
      section14_theorem_14_9_late_type_T1_pf11_type34_family_source_bridge
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d Wloc A A0 i0 j0
        μloc δSign ωloc σloc hctx hLateType hTtypeP hNotation hNotation10
        hNonbase hCalT1 hζ
    rcases hFamily with
      ⟨S, i1, j1, h10, hζS, hζKer, hi1, hη01, hPrincipal⟩
    let SHC : Finset (Section1.ClassFunction Tmax) :=
      S.filter fun χ => Section1.subgroupInKernel' χ ((Q ⊔ D).subgroupOf Tmax)
    have hsourceCtx := hctx.1
    rcases hsourceCtx with
      ⟨_hcaseCtx, _hSTypeP, _hTTypeP, _hpW2, _hqW1, _hCeq, hDeq, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    have hTtypePcopy := hTtypeP
    rcases hTtypePcopy with
      ⟨_hQsection16, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit, _hFitLe,
        _hW1le, _hW1cyc, _hW1ne, _hCentralizer, _hNormalizer⟩
    have hQleT : Q ≤ Tmax :=
      hDerComp.1.trans (section12_ambientDerivedSubgroup_le (G := G) (E := Tmax))
    have hDleT : D ≤ Tmax := by
      rw [hDeq]
      intro x hx
      exact (hVleDer.trans
        (section12_ambientDerivedSubgroup_le (G := G) (E := Tmax))) hx.1
    have hQDT : Q ⊔ D ≤ Tmax := sup_le hQleT hDleT
    have hSHC : Section11.section11Subfamily (Q ⊔ D) S SHC := by
      refine section14_section11Subfamily_of_mem_iff
        (M := Tmax) (X := Q ⊔ D) (S := S) (SX := SHC) hQDT ?_
      intro χ
      dsimp [SHC]
      simp
    have hζSHC : ζ ∈ SHC := by
      dsimp [SHC]
      simp [hζS, hζKer]
    have hcaseT :
        Section13.case_9_7_a_sourceDataForSection13
            Tmax Q V W2 W1 D q p v ∨
          Section13.case_9_7_b_sourceDataForSection13
            Tmax Q V W2 W1 D q p v :=
      Section13.theorem_13_2_case_9_7_sourceData_of_sourceContext
        Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
        q p v u d c (section14_hypothesis_13_1_sourceData_swap hctx.1)
    have h11 :
        Section11.hypothesis_11_2_data Tmax Q Q V D ⊥ W2 W1 S τT q p :=
      section14_theorem_14_9_late_type_T1_hypothesis_11_2_of_section10_and_case97_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        S hctx hLateType hTtypeP h10 hcaseT
    let R : Finset (Section1.ClassFunction G) :=
      Finset.univ.image fun p : I × J => σloc (ωloc p.1 p.2)
    have hR : Section11.transformedIrreducibleFamily R σloc := by
      dsimp [R]
      exact
        section14_transformedIrreducibleFamily_of_section10FourSixNotationSupportedData
          hNotation10
    exact
      section14_theorem_14_9_late_type_T1_pf11_type34_of_row_projection_source
        (show section14_theorem_14_9_late_type_T1PF11RowProjectionSourceData
            Tmax Q V D W2 W1 τT (η 0 1) ζ p q from
          ⟨I, instI, decI, J, instJ, decJ, Wloc, A, A0, S, SHC, R, i0, i1, j0, j1,
            μloc, δSign, ωloc, σloc, h11, hNotation10, hSHC, hζSHC, hR, hi1,
            hη01, hPrincipal⟩)

  public theorem section14_theorem_14_9_late_type_T1_pf11_row_projection_source_bridge
      {G : Type u} [Group G] [Finite G] [IsMinCE G]
      (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
      {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
      section14_theorem_14_9_late_type_T1PF11RowProjectionSourceData
        Tmax Q V D W2 W1 τT (η 0 1) ζ p q := by
    exact
      section14_theorem_14_9_late_type_T1_pf11_row_projection_of_type34_source
        (section14_theorem_14_9_late_type_T1_pf11_type34_source_bridge
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          ω η μ ν μsum νsum δ δ' σ p q u v c d hctx hLateType hTtypeP
          hNotation hCalT1 hζ)


public theorem section14_theorem_14_9_late_type_T1_eta_tauT_betaT0_scalar_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T) :
    Section1.scalarProduct G (η 0 1)
      (τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)) = 0 := by
  classical
  rcases
      section14_theorem_14_9_late_type_T1_pf11_row_projection_source_bridge
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hctx hLateType hTtypeP
        hNotation hCalT1 hζ with
    ⟨I, instI, decI, J, instJ, decJ, Wloc, A, A0, S, SHC, R, i0, i1, j0, j1,
      μloc, δSign, ωloc, σloc, h11, hNotation10, hSHC, hζSHC, hR, hi1,
      hη01, hPrincipal⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  exact
    section14_theorem_14_9_late_type_T1_eta_tauT_betaT0_scalar_of_pf11_row_projection
      Tmax Q Q V D ⊥ W2 W1 Wloc A A0 S SHC R i0 i1 j0 j1
      μloc δSign ωloc σloc τT ζ
      (Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ)
      (η 0 1) q p
      h11 hNotation10 hSHC hζSHC hR hi1 hη01 (by
        rw [hPrincipal])

public theorem section14_signedOrthonormal_subsetSum_self_eq_card
    {G : Type u} [Group G] [Finite G]
    {R E : Finset (Section1.ClassFunction G)}
    (hR : Section5.signedOrthonormalFinset R)
    (hEsub : E ⊆ R) :
    Section1.scalarProduct G (Finset.sum E fun ψ => ψ)
        (Finset.sum E fun ψ => ψ) = (E.card : ℂ) := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert a E ha ih =>
      have hEsub' : E ⊆ R := by
        intro ψ hψ
        exact hEsub (Finset.mem_insert_of_mem hψ)
      have haR : a ∈ R := hEsub (Finset.mem_insert_self a E)
      have haSelf : Section1.scalarProduct G a a = 1 :=
        Section12.scalarProduct_self_of_isSignedIrreducibleCharacter
          (hR.1 a haR)
      have hsumE :
          (Finset.sum E fun ψ => ψ) =
            (fun g : G => ∑ ψ : E, (ψ : Section1.ClassFunction G) g) := by
        ext g
        simpa using (Finset.sum_attach E fun ψ : Section1.ClassFunction G => ψ g).symm
      have haEzero :
          Section1.scalarProduct G a (Finset.sum E fun ψ => ψ) = 0 := by
        rw [hsumE, Section1.scalarProduct_fintype_sum_right]
        refine Finset.sum_eq_zero ?_
        intro ψ _hψ
        have ha_ne_a : a ≠ ψ.val := by
          intro hEq
          apply ha
          subst hEq
          exact ψ.property
        exact hR.2 haR (hEsub' ψ.property) ha_ne_a
      have hEazero :
          Section1.scalarProduct G (Finset.sum E fun ψ => ψ) a = 0 := by
        have hstar := congrArg star haEzero
        simpa [Section1.scalarProduct_star_swap] using hstar
      rw [Finset.sum_insert ha, Section1.scalarProduct_add_left,
        Section5.scalarProduct_add_right, Section5.scalarProduct_add_right,
        haSelf, haEzero, hEazero, ih hEsub']
      rw [Finset.card_insert_of_notMem ha]
      rw [Nat.cast_add, Nat.cast_one]
      ring

public theorem section14_subsetSum_mem_of_signedOrthonormal_norm_one
    {G : Type u} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    {φ : Section1.ClassFunction G}
    (hR : Section5.signedOrthonormalFinset R)
    (hsubset : Section5.isSubsetSumOf R φ)
    (hφnorm : Section1.scalarProduct G φ φ = 1) :
    φ ∈ R := by
  classical
  rcases hsubset with ⟨E, hEsub, hφ⟩
  have hcardC : (E.card : ℂ) = 1 := by
    have hnorm :=
      section14_signedOrthonormal_subsetSum_self_eq_card
        (G := G) (R := R) (E := E) hR hEsub
    rw [← hnorm]
    simpa [hφ] using hφnorm
  have hcard : E.card = 1 := by
    exact_mod_cast hcardC
  rcases Finset.card_eq_one.mp hcard with ⟨ψ, hEeq⟩
  have hφeq : φ = ψ := by
    rw [hφ, hEeq]
    simp
  rw [hφeq]
  exact hEsub (by simp [hEeq])

public theorem section14_theorem_14_9_late_type_T1_tauT_diff_skew
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (ζ : Section1.ClassFunction Tmax) :
    Section1.conjugateCharacter
        (τT (ζ - Section1.conjugateCharacter ζ)) =
      -(τT (ζ - Section1.conjugateCharacter ζ)) := by
  classical
  let ν : Section1.ClassFunction Tmax :=
    Section7.principalInducedCharacter Tmax (Q ⊔ V)
  have hζ :
      Section1.conjugateCharacter (τT (ν - ζ)) =
        τT (ν - Section1.conjugateCharacter ζ) := by
    simpa [ν] using
      section14_theorem_14_9_late_type_T1_tauT_betaT0_conjugate
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP ζ
  have hζbar :
      Section1.conjugateCharacter
          (τT (ν - Section1.conjugateCharacter ζ)) =
        τT (ν -
          Section1.conjugateCharacter (Section1.conjugateCharacter ζ)) := by
    simpa [ν] using
      section14_theorem_14_9_late_type_T1_tauT_betaT0_conjugate
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP (Section1.conjugateCharacter ζ)
  have hdecomp :
      τT (ζ - Section1.conjugateCharacter ζ) =
        τT (ν - Section1.conjugateCharacter ζ) - τT (ν - ζ) := by
    rw [← τT.map_sub]
    congr 1
    ext x
    simp [ν]
  calc
    Section1.conjugateCharacter
        (τT (ζ - Section1.conjugateCharacter ζ)) =
        Section1.conjugateCharacter
          (τT (ν - Section1.conjugateCharacter ζ) - τT (ν - ζ)) := by
          rw [hdecomp]
    _ = Section1.conjugateCharacter (τT (ν - Section1.conjugateCharacter ζ)) -
          Section1.conjugateCharacter (τT (ν - ζ)) := by
          ext x
          simp [Section1.conjugateCharacter]
    _ = τT (ν - Section1.conjugateCharacter (Section1.conjugateCharacter ζ)) -
          τT (ν - Section1.conjugateCharacter ζ) := by
          rw [hζbar, hζ]
    _ = τT (ν - ζ) - τT (ν - Section1.conjugateCharacter ζ) := by
          rw [Section12.conjugateCharacter_involutive]
    _ = -(τT (ζ - Section1.conjugateCharacter ζ)) := by
          rw [hdecomp]
          ext x
          simp

public theorem section14_theorem_14_9_late_type_T1_tauT1_conjugate_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Tmax : Subgroup G}
    {T1T : Finset (Section1.ClassFunction Tmax)}
    {τT τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement T1T τT)
    (hcoh : Section6.coherentExtension T1T τT τT1)
    (hIrr : ∀ ζ : Section1.ClassFunction Tmax, ζ ∈ T1T →
      Section1.IsIrreducibleCharacterOnGroup ζ)
    {ζ : Section1.ClassFunction Tmax} (hζ : ζ ∈ T1T)
    (hτTdiff_skew : Section1.conjugateCharacter
        (τT (ζ - Section1.conjugateCharacter ζ)) =
      -(τT (ζ - Section1.conjugateCharacter ζ))) :
    Section1.conjugateCharacter (τT1 ζ) =
      τT1 (Section1.conjugateCharacter ζ) := by
  -- of the `calT1` members.
  classical
  letI : Fintype Tmax := Fintype.ofFinite Tmax
  rcases h52 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  let X : T1T := ⟨ζ, hζ⟩
  have hζbar : Section1.conjugateCharacter ζ ∈ T1T := by
    simpa [X] using (h52a X).1
  have hζne : ζ ≠ Section1.conjugateCharacter ζ := by
    simpa [X] using (h52a X).2
  have hpairSub :
      ({(X : Section1.ClassFunction Tmax),
        Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)} :
        Finset (Section1.ClassFunction Tmax)) ⊆ T1T := by
    intro χ hχ
    have hχ' :
        χ = (X : Section1.ClassFunction Tmax) ∨
          χ = Section1.conjugateCharacter (X : Section1.ClassFunction Tmax) := by
      simpa using hχ
    rcases hχ' with rfl | rfl
    · exact hζ
    · exact hζbar
  have hIsoPair :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction Tmax),
          Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)} :
          Finset (Section1.ClassFunction Tmax)) τT1 :=
    Section5.isCFLinearIsometryOnSpan_mono hpairSub hcoh.1
  have hVirtPair :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction Tmax),
          Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)} :
          Finset (Section1.ClassFunction Tmax)) τT1 :=
    Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSub hcoh.2.1
  have hdiffOn :
      Section5.integerSpanOn T1T Section5.puncturedSet
        (ζ - Section1.conjugateCharacter ζ) := by
    have hspan :
        Section5.integerSpan T1T
          (ζ - Section1.conjugateCharacter ζ) :=
      Section5.integerSpan_sub
        (Section5.integerSpan_of_mem T1T hζ)
        (Section5.integerSpan_of_mem T1T hζbar)
    have hζchar : Section1.IsCharacter ζ := by
      simpa [X] using hsetup.2 X
    have hdeg :
        Section1.degree (ζ - Section1.conjugateCharacter ζ) = 0 := by
      change Section1.degree ζ -
        Section1.degree (Section1.conjugateCharacter ζ) = 0
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hζchar]
      simp
    exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg⟩
  have hagree :
      τT1 (ζ - Section1.conjugateCharacter ζ) =
        τT (ζ - Section1.conjugateCharacter ζ) :=
    hcoh.2.2 _ hdiffOn
  have hsubset : Section5.isSubsetSumOf (R X) (τT1 ζ) := by
    have hsubsetX :
        Section5.isSubsetSumOf (R X)
          (τT1 (X : Section1.ClassFunction Tmax)) :=
      Section5.theorem_5_5 T1T τT R
        hsetup h52a h52b h52c h52d h52e X τT1
        hIsoPair hVirtPair hagree
    simpa [X] using hsubsetX
  have hτT1ζSigned : Section3.IsSignedIrreducibleCharacter (τT1 ζ) :=
    Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      hcoh hζ (hIrr ζ hζ)
  have hτT1ζNorm :
      Section1.scalarProduct G (τT1 ζ) (τT1 ζ) = 1 :=
    Section12.scalarProduct_self_of_isSignedIrreducibleCharacter hτT1ζSigned
  have hτT1ζ_mem_R : τT1 ζ ∈ R X :=
    section14_subsetSum_mem_of_signedOrthonormal_norm_one
      (h52d X).1 hsubset hτT1ζNorm
  have hdiff_source_norm :
      Section1.scalarProduct Tmax
          (ζ - Section1.conjugateCharacter ζ)
          (ζ - Section1.conjugateCharacter ζ) = 2 := by
    have hζself : Section1.scalarProduct Tmax ζ ζ = 1 :=
      Section12.scalarProduct_self_of_isIrreducibleCharacterOnGroup (hIrr ζ hζ)
    have hζbarself :
        Section1.scalarProduct Tmax (Section1.conjugateCharacter ζ)
          (Section1.conjugateCharacter ζ) = 1 :=
      Section12.scalarProduct_self_of_isIrreducibleCharacterOnGroup
        (hIrr (Section1.conjugateCharacter ζ) hζbar)
    have hζζbar :
        Section1.scalarProduct Tmax ζ (Section1.conjugateCharacter ζ) = 0 :=
      h52c hζ hζbar hζne
    have hζbarζ :
        Section1.scalarProduct Tmax (Section1.conjugateCharacter ζ) ζ = 0 :=
      h52c hζbar hζ hζne.symm
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, hζself, hζζbar, hζbarζ, hζbarself]
    norm_num
  have hdiff_target_norm :
      Section1.scalarProduct G
          (τT (ζ - Section1.conjugateCharacter ζ))
          (τT (ζ - Section1.conjugateCharacter ζ)) = 2 := by
    rw [h52b.1 _ _ hdiffOn hdiffOn, hdiff_source_norm]
  have hRcard : (R X).card = 2 := by
    have hRnorm :=
      section14_signedOrthonormal_subsetSum_self_eq_card
        (G := G) (R := R X) (E := R X) (h52d X).1 (by intro ψ hψ; exact hψ)
    have hRsum :
        τT (ζ - Section1.conjugateCharacter ζ) = Finset.sum (R X) fun ψ => ψ := by
      simpa [X] using (h52d X).2
    have hcardC : ((R X).card : ℂ) = 2 := by
      rw [← hRnorm]
      rw [← hRsum]
      exact hdiff_target_norm
    exact_mod_cast hcardC
  have htarget_sub :
      τT (ζ - Section1.conjugateCharacter ζ) =
        τT1 ζ - Section1.conjugateCharacter (τT1 ζ) :=
    Section12.signedOrthonormalPair_sum_eq_sub_conjugate_of_skew
      (h52d X).1 hRcard (h52d X).2 hτTdiff_skew hτT1ζ_mem_R
  have hdiff_tauT1 :
      τT1 ζ - τT1 (Section1.conjugateCharacter ζ) =
        τT (ζ - Section1.conjugateCharacter ζ) := by
    rw [← τT1.map_sub, hagree]
  have hcancel :
      τT1 ζ - τT1 (Section1.conjugateCharacter ζ) =
        τT1 ζ - Section1.conjugateCharacter (τT1 ζ) := by
    rw [hdiff_tauT1, htarget_sub]
  ext g
  have hg := congrFun hcancel g
  exact (sub_right_inj.mp hg).symm

public theorem section14_theorem_14_9_late_type_T1_delta_correction_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS₁ : Section1.ClassFunction Smax)
    (βτ Γ X Y η01 : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_ : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (hLateType : Section8.typeIIIDefinitionData Tmax Q ∨
      Section8.typeIVDefinitionData Tmax Q ∨
        Section8.typeVDefinitionData Tmax Q)
    (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    (hGap : section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
      βS₁ βτ Γ X Y η01 p q u)
    {T1T : Finset (Section1.ClassFunction Tmax)}
    {τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T)
    (h52 : Section5.hypothesis_5_2_statement T1T τT)
    (_ : ∀ ζ ξ : T1T,
      Section1.degree (ζ : Section1.ClassFunction Tmax) =
        Section1.degree (ξ : Section1.ClassFunction Tmax))
    (hcoh : Section6.coherentExtension T1T τT τT1)
    (hσorth : ∀ ζ ∈ T1T, ∀ ξ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup ξ →
        Section1.scalarProduct G (σ ξ) (τT1 ζ) = 0) :
    ∀ ζ ∈ T1T,
      ∃ Δ : Section1.ClassFunction G,
        section14_theorem_14_9_late_type_T1DeltaCorrection Γ (τT1 ζ) Δ := by
  classical
  intro ζ hζ
  have hGapData := hGap
  rcases hGap with
    ⟨_hβSupp, _hβSuppA0, hβClass, _hβNorm, hβτ, hη01, hΓbase, _hΓallK,
      hΓone, _hΓreal, _hΓvirt, _hΓdecomp, _hDecomp⟩
  have hTtypeP :
      Section8.typePDefinitionData Tmax Q V W2 W1 :=
    section14_theorem_14_9_Tmax_typePDefinitionData_of_context hctx
  rcases section14_theorem_14_9_late_type_T1_calt_facts_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP T1T hCalT1 with
    ⟨_hcardFacts, _hneFacts, _h52aFacts, _h52bFacts, hIrr, _hdegFacts⟩
  have hζIrr : Section1.IsIrreducibleCharacterOnGroup ζ := hIrr ζ hζ
  let βT0 : Section1.ClassFunction Tmax :=
    Section7.principalInducedCharacter Tmax (Q ⊔ V) - ζ
  have hβT0Virt : Theory.Character.IsVirtualCharacter βT0 := by
    simpa [βT0] using
      section14_principalInducedCharacter_sub_irreducible_isVirtualCharacter
        (L := Tmax) (H := Q ⊔ V) (ζ := ζ) hζIrr
  let Δ : Section1.ClassFunction G :=
    τT βT0 - Section1.principalCharacter G + τT1 ζ
  have hτT1ζVirt : Theory.Character.IsVirtualCharacter (τT1 ζ) :=
    section14_theorem_14_9_late_type_T1_tauT1_mem_isVirtualCharacter hcoh hζ
  have hΔVirt_of_βT0 :
      Theory.Character.IsVirtualCharacter (τT βT0) →
        Theory.Character.IsVirtualCharacter Δ := by
    intro hβT0Virt
    dsimp [Δ]
    exact section14_theorem_14_9_late_type_T1_delta_isVirtualCharacter_of_betaT0
      hβT0Virt hτT1ζVirt
  have hτTβT0Virt_book : Theory.Character.IsVirtualCharacter (τT βT0) := by
    simpa [βT0] using
      section14_theorem_14_9_late_type_T1_tauT_isVirtualCharacter_of_book_AZero
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hctx hLateType hTtypeP hCalT1 hζ (by
          simpa [βT0] using hβT0Virt)
  have hΔVirt : Theory.Character.IsVirtualCharacter Δ :=
    hΔVirt_of_βT0 hτTβT0Virt_book
  refine ⟨Δ, ?_⟩
  -- `betaT0 := nu_ 0 - zeta`;
  -- `Delta := tauT betaT0 - 1 + tau1T zeta`;
  -- then expand `Γ = betaτk - 1 + eta_ 0 k` and use the support
  -- disjointness calculation plus coherent conjugation for `tau1T`.
  refine ⟨?_, hΔVirt, ?_, ?_⟩
  · have hΓτTβT0 :
        Section1.scalarProduct G Γ (τT βT0) = -1 := by
      have hτTβT0_principal :
          Section1.scalarProduct G (τT βT0) (Section1.principalCharacter G) = 1 := by
        simpa [βT0] using
          section14_theorem_14_9_late_type_T1_tauT_betaT0_principal_scalar_book_AZero
            Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
            p q u v c d hctx hLateType hTtypeP hCalT1 hζ
      have hβτ_τTβT0 :
          Section1.scalarProduct G βτ (τT βT0) = 0 := by
        have hβτ_supp :
            Section1.supportedOn βτ
              (section16ConjugatesOfSetBySet
                (Section13.theorem_13_18_betaSupportSet Smax W W1 W2 P)
                Set.univ) :=
          section14_theorem_14_9_betaTau_supportedOn_betaSupport_global
            (hctx := hctx) hGapData
        have hτTβT0_supp :
            Section1.supportedOn (τT βT0)
              (section16ConjugatesOfSetBySet
                (section16NonidentityElements ((Q ⊔ V : Subgroup G) : Set G))
                Set.univ) := by
          simpa [βT0] using
            section14_theorem_14_9_late_type_T1_tauT_betaT0_supportedOn_QVsharp_global
              Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
              p q u v c d hctx hLateType hTtypeP hCalT1 hζ
        have hdisj :
            Disjoint
              (section16ConjugatesOfSetBySet
                (Section13.theorem_13_18_betaSupportSet Smax W W1 W2 P)
                Set.univ)
              (section16ConjugatesOfSetBySet
                (section16NonidentityElements ((Q ⊔ V : Subgroup G) : Set G))
                Set.univ) :=
          section14_theorem_14_9_betaSupport_disjoint_QVsharp_source_bridge
            (hctx := hctx) hTtypeP
        exact section14_scalarProduct_eq_zero_of_supports_disjoint
          hdisj hβτ_supp hτTβT0_supp
      have hη01_τTβT0 :
          Section1.scalarProduct G η01 (τT βT0) = 0 := by
        rw [hη01]
        simpa [βT0] using
          section14_theorem_14_9_late_type_T1_eta_tauT_betaT0_scalar_source_bridge
            Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
            ω η μ ν μsum νsum δ δ' σ p q u v c d
            hctx hLateType hTtypeP hNotation hCalT1 hζ
      exact
        section14_theorem_14_9_late_type_T1_gamma_tau_scalar_of_decomposition
          hΓbase hβτ_τTβT0 hη01_τTβT0 hτTβT0_principal
    exact
      section14_theorem_14_9_late_type_T1_delta_scalar_equation_of_gamma_tau
        (Γ := Γ) (χ := τT1 ζ) (τβ := τT βT0) (Δ := Δ)
        rfl hΓone hΓτTβT0
  · have hτβ_conj :
        Section1.conjugateCharacter (τT βT0) =
          τT (Section7.principalInducedCharacter Tmax (Q ⊔ V) -
            Section1.conjugateCharacter ζ) := by
      simpa [βT0] using
        section14_theorem_14_9_late_type_T1_tauT_betaT0_conjugate
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          p q u v c d hctx hLateType hTtypeP ζ
    have hτ1_conj :
        Section1.conjugateCharacter (τT1 ζ) =
          τT1 (Section1.conjugateCharacter ζ) :=
      have hτTdiff_skew :
          Section1.conjugateCharacter
              (τT (ζ - Section1.conjugateCharacter ζ)) =
            -(τT (ζ - Section1.conjugateCharacter ζ)) :=
        section14_theorem_14_9_late_type_T1_tauT_diff_skew
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          p q u v c d hctx hLateType hTtypeP ζ
      section14_theorem_14_9_late_type_T1_tauT1_conjugate_source_bridge
        h52 hcoh hIrr hζ hτTdiff_skew
    have hdiff :
        τT1 (ζ - Section1.conjugateCharacter ζ) =
          τT (ζ - Section1.conjugateCharacter ζ) :=
      section14_theorem_14_9_late_type_T1_coherent_conjugate_diff_agree
        h52 hcoh hζ
    exact
      section14_theorem_14_9_late_type_T1_delta_real_of_conjugation
        (Δ := Δ)
        (ν := Section7.principalInducedCharacter Tmax (Q ⊔ V))
        (ζ := ζ) rfl hτβ_conj hτ1_conj hdiff
  · have hτTβT0_principal :
        Section1.scalarProduct G (τT βT0) (Section1.principalCharacter G) = 1 := by
      simpa [βT0] using
        section14_theorem_14_9_late_type_T1_tauT_betaT0_principal_scalar_book_AZero
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          p q u v c d hctx hLateType hTtypeP hCalT1 hζ
    have hτT1ζ_principal :
        Section1.scalarProduct G (τT1 ζ) (Section1.principalCharacter G) = 0 :=
      section14_theorem_14_9_late_type_T1_tauT1_principal_scalar_zero_of_sigma_orth
        (hNotation := hNotation) hσorth hζ
    have hprincipal_self :
        Section1.scalarProduct G (Section1.principalCharacter G)
          (Section1.principalCharacter G) = 1 := by
      simp [Section1.scalarProduct, Section1.principalCharacter]
    dsimp [Δ]
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
      hτTβT0_principal, hprincipal_self, hτT1ζ_principal]
    ring

public theorem section14_theorem_14_9_late_type_T1_calt_extension_orth_delta_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS₁ : Section1.ClassFunction Smax)
    (βτ Γ X Y η01 : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        (Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q) →
          Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
            βS₁ βτ Γ X Y η01 p q u →
          ∀ T1T : Finset (Section1.ClassFunction Tmax),
            Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
              Section5.hypothesis_5_2_statement T1T τT →
                (∀ ζ ξ : T1T,
                  Section1.degree (ζ : Section1.ClassFunction Tmax) =
                    Section1.degree (ξ : Section1.ClassFunction Tmax)) →
              section14_theorem_14_9_late_type_T1CoherentExtensionOrthDeltaData
                Tmax W τT σ Γ T1T := by
  classical
  intro hctx h143 hLateType hNotation hGap T1T hCalT1 h52 hdeg
  letI : Fintype Tmax := Fintype.ofFinite Tmax
  have hTtypeP :
      Section8.typePDefinitionData Tmax Q V W2 W1 :=
    section14_theorem_14_9_Tmax_typePDefinitionData_of_context hctx
  have hTtypeP0 : Section8.typePDefinitionData Tmax Q V W2 W1 := hTtypeP
  rcases section14_theorem_14_9_late_type_T1_calt_facts_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP T1T hCalT1 with
    ⟨_hcard, hne, _h52aFacts, _h52bFacts, hIrr, _hdegFacts⟩
  rcases h52 with ⟨hsetup52, R52, h52a, h52b, h52c, h52d, h52e⟩
  have h52Full : Section5.hypothesis_5_2_statement T1T τT :=
    ⟨hsetup52, R52, h52a, h52b, h52c, h52d, h52e⟩
  rcases
      section14_theorem_14_9_late_type_T1_calt1_hypothesis52_fullData_omegaSigma_source_bridge
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        hctx hLateType hTtypeP hNotation with
    ⟨d52, hd52τ, hΩCompat⟩
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := by
    rcases hTtypeP0 with
      ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
        _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
    exact hDerComp.2.2.1
  have hH : (Q ⊔ V).subgroupOf Tmax = derivedSubgroup Tmax := by
    rw [← hDerEq]
    exact section12_ambientDerivedSubgroup_subgroupOf_eq
  have hIndT1 :
      Section5.inducedFromNonkernelFamily_statement
        (derivedSubgroup Tmax) (derivedSubgroup Tmax) T1T := by
    simpa [hH] using
      (section14_theorem_14_9_late_type_T1_inducedFromNonkernel_of_calt
        (Tmax := Tmax) (Q := Q) (V := V) (T1T := T1T) hCalT1)
  have hpackLocal :
      ∃ R : T1T → Finset (Section1.ClassFunction G),
        Section5.hypothesis_5_2_setup_statement T1T ∧
          Section5.hypothesis_5_2_a_statement T1T ∧
          Section5.hypothesis_5_2_b_statement T1T τT ∧
          Section5.hypothesis_5_2_c_statement T1T ∧
          Section5.hypothesis_5_2_d_statement T1T τT R ∧
          Section5.hypothesis_5_2_e_statement T1T R ∧
          Section5.theorem_5_3_b_extra_statement T1T R
            (Finset.univ.image fun p : d52.I × d52.J =>
              d52.sigma (d52.omega p.1 p.2)) := by
    have hsupported :
        Section4Scratch.hypothesis_4_6_supported_statement Tmax
          (derivedSubgroup Tmax) (W2.subgroupOf Tmax) (W1.subgroupOf Tmax)
          d52.W (derivedSubgroup Tmax)
          (Section8.section8SubgroupSetPreimage Tmax
            (Section8.section8CentralizerUnion
              (ambientDerivedSubgroup Tmax) (Q ⊔ V)))
          d52.i0 d52.j0 d52.omega d52.sigmaM d52.sigma d52.piChar
          d52.xChar d52.deltaSign τT d52.H_A := by
      simpa [hH, hd52τ] using d52.fullHypothesis
    exact
      Section5.theorem_5_3_b_core
        (K := derivedSubgroup Tmax)
        (W1 := W2.subgroupOf Tmax)
        (W2 := W1.subgroupOf Tmax)
        (W := d52.W)
        (H := derivedSubgroup Tmax)
        (A := Section8.section8SubgroupSetPreimage Tmax
          (Section8.section8CentralizerUnion
            (ambientDerivedSubgroup Tmax) (Q ⊔ V)))
        (i0 := d52.i0)
        (j0 := d52.j0)
        (ω := d52.omega)
        (σL := d52.sigmaM)
        (σ := d52.sigma)
        (piChar := d52.piChar)
        (xChar := d52.xChar)
        (deltaSign := d52.deltaSign)
        (τ := τT)
        (S := T1T)
        (Section5.theorem_5_3_b_core_context_of_supported_pf53 Tmax hsupported)
        hne h52a hIndT1
  have hΩ :
      ∀ ξ : Section1.ClassFunction W,
        Section1.IsIrreducibleCharacterOnGroup ξ →
          σ ξ ∈
            (Finset.univ.image fun p : d52.I × d52.J =>
              d52.sigma (d52.omega p.1 p.2)) :=
    section14_theorem_14_9_late_type_T1_active_sigma_mem_local_omegaSigma_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hctx hNotation d52 hd52τ hΩCompat
  refine ⟨?_, ?_⟩
  · intro τT1 hcoh
    exact section14_theorem_14_9_late_type_T1_sigma_orth_of_53b_extra
      hpackLocal hcoh hΩ hIrr
  · intro τT1 hcoh
    have hσorth :
        ∀ ζ ∈ T1T, ∀ ξ : Section1.ClassFunction W,
          Section1.IsIrreducibleCharacterOnGroup ξ →
            Section1.scalarProduct G (σ ξ) (τT1 ζ) = 0 :=
      section14_theorem_14_9_late_type_T1_sigma_orth_of_53b_extra
        hpackLocal hcoh hΩ hIrr
    exact section14_theorem_14_9_late_type_T1_delta_correction_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      ω η μ ν μsum νsum δ δ' σ βS₁ βτ Γ X Y η01 p q u v c d
      hctx h143 hLateType hNotation hGap hCalT1 h52Full hdeg hcoh hσorth

public theorem section14_theorem_14_9_late_type_T1_pre_extension_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS₁ : Section1.ClassFunction Smax)
    (βτ Γ X Y η01 : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        (Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q) →
          Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
            βS₁ βτ Γ X Y η01 p q u →
          section14_theorem_14_9_late_type_T1PreExtensionSourceData
            Tmax W Q V τT σ Γ p v := by
  intro hctx h143 hLateType hNotation hGap
  have hTtypeP :
      Section8.typePDefinitionData Tmax Q V W2 W1 :=
    section14_theorem_14_9_Tmax_typePDefinitionData_of_context hctx
  have hcal :
      section14_theorem_14_9_late_type_T1CalTConstructionData
        Tmax Q V τT p v :=
    section14_theorem_14_9_late_type_T1_calt_construction_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP
  exact section14_theorem_14_9_late_type_T1PreExtensionSourceData_of_calt
    hcal
    (fun T1T hCalT1 h52 hdeg =>
      section14_theorem_14_9_late_type_T1_calt_extension_orth_delta_source_bridge
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
        ω η μ ν μsum νsum δ δ' σ βS₁ βτ Γ X Y η01 p q u v c d
        hctx h143 hLateType hNotation hGap T1T hCalT1 h52 hdeg)

public theorem section14_theorem_14_9_late_type_T1_raw_image_delta_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS₁ : Section1.ClassFunction Smax)
    (βτ Γ X Y η01 : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        (Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q) →
          Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
            βS₁ βτ Γ X Y η01 p q u →
          section14_theorem_14_9_late_type_T1RawImageDeltaSourceData
            Tmax W τT σ Γ p v := by
  intro hctx h143 hLateType hNotation hGap
  exact section14_theorem_14_9_late_type_T1RawImageDeltaSourceData_of_preExtension
    (section14_theorem_14_9_late_type_T1_pre_extension_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      ω η μ ν μsum νsum δ δ' σ βS₁ βτ Γ X Y η01 p q u v c d
      hctx h143 hLateType hNotation hGap)

public theorem section14_theorem_14_9_late_type_T1_image_delta_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS₁ : Section1.ClassFunction Smax)
    (βτ Γ X Y η01 : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        (Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q) →
          Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
            βS₁ βτ Γ X Y η01 p q u →
          section14_theorem_14_9_late_type_T1ImageDeltaSourceData Tmax τT η Γ p q v := by
  intro hctx h143 hLateType hNotation hGap
  exact section14_theorem_14_9_late_type_T1ImageDeltaSourceData_of_raw
    hNotation
    (section14_theorem_14_9_late_type_T1_raw_image_delta_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT Lfam RL
      τL τL₁ φ μ01 ν10 βS βT βL ω η μ ν μsum νsum δ δ' σ
      βS₁ βτ Γ X Y η01 p q u v c d hctx h143 hLateType hNotation hGap)


end CFSG.Section14
