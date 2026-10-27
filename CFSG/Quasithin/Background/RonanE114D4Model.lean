module

public import CFSG.Quasithin.Background.RonanE114D4Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Aux
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.A312L _root_.Certificates
open scoped MatrixGroups

section Transport

variable {G : Type} [Group G] {L : Subgroup G} [L.Normal] {C : Type} [Group C] (φ : ↥L ≃* C)

@[expose] def conjAut : G →* MulAut C := (MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal

theorem conjAut_apply (t : G) (y : C) :
    conjAut φ t y = φ (MulAut.conjNormal t (φ.symm y)) := by
  simp [conjAut, MulAut.congr_apply]

theorem coe_symm_conjAut (t : G) (y : C) :
    ((φ.symm (conjAut φ t y) : ↥L) : G) = t * ((φ.symm y : ↥L) : G) * t⁻¹ := by
  rw [conjAut_apply, MulEquiv.symm_apply_apply, MulAut.conjNormal_apply]

theorem le_normalizer_map {T : Subgroup G} {X : Subgroup C}
    (hX : ∀ t ∈ T, ∀ y ∈ X, conjAut φ t y ∈ X) :
    T ≤ Subgroup.normalizer
      (((X.map (L.subtype.comp φ.symm.toMonoidHom)) : Subgroup G) : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ X.map (L.subtype.comp φ.symm.toMonoidHom),
      t * x * t⁻¹ ∈ X.map (L.subtype.comp φ.symm.toMonoidHom) := by
    rintro t ht _ ⟨y, hy, rfl⟩
    refine ⟨conjAut φ t y, hX t ht y hy, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    exact coe_symm_conjAut φ t y
  intro t ht
  refine B6.mem_normalizer_of_forall_mem (key t ht) (fun x hx => ?_)
  simpa using key t⁻¹ (T.inv_mem ht) x hx

theorem mem_iff_conjAut_mem {T : Subgroup G} {U : Subgroup C}
    (hU : ((T ⊓ L).subgroupOf L).map φ.toMonoidHom = U) {t : G} (ht : t ∈ T) (y : C) :
    y ∈ U ↔ conjAut φ t y ∈ U := by
  rw [← hU, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, coe_symm_conjAut]
  exact Subgroup.mem_normalizer_iff.mp (CFSG.Quasithin.Vol2.Ch11.SecE3.le_normalizer_inf ht) _

theorem map_conjAut_eq {T : Subgroup G} {U : Subgroup C}
    (hU : ((T ⊓ L).subgroupOf L).map φ.toMonoidHom = U) {t : G} (ht : t ∈ T) :
    U.map (conjAut φ t).toMonoidHom = U := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have := mem_iff_conjAut_mem φ hU ht ((conjAut φ t).symm x)
  rwa [MulEquiv.apply_symm_apply] at this

end Transport

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem parabolic_large (a : Fin TwistTag.D4.foldedTag.rank)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom))
    (hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom a), s.card = 4) :
    graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} ≤
        graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊔
          perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) ∧
      ∃ g : ↥(perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) →*
            SL(2, ↥(orbitField TwistTag.D4 K σ.toRingHom a)),
        Function.Surjective g ∧ IsPGroup 2 ↥g.ker := by
  classical
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  refine ⟨?_, exists_levi_hom_fixed σ a hU hL4⟩
  obtain ⟨R, hVN, hNV, hsup, hRV, hker⟩ := fixed_structure σ a
  have hperfSL : Group.IsPerfect (SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom a)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hL4
  have hMperf : ⁅R.range, R.range⁆ = R.range := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range R)
  have hRN : R.range ≤ fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a := hsup ▸ le_sup_right
  have hMP : R.range ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} :=
    hRN.trans (fixedPosWeylGroup_le_graphFixedParabolic_singleton σ.surjective a)
  have hMc : R.range ≤ perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) :=
    le_perfectCore_of_perfect hMP hMperf
  have hVB : graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a ≤
      graphFixedRootBorel TwistTag.D4 K σ.toRingHom :=
    (graphFixedSimpleComplement_le a).trans graphFixedPosUnipotent_le_graphFixedRootBorel
  have hPa : graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} =
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
        (graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a ⊔ R.range) := by
    rw [graphFixedParabolic_singleton_eq_sup σ.surjective a, ← hsup]
  refine hPa.le.trans (sup_le ?_ (sup_le ?_ ?_))
  · exact graphFixedRootTorus_le_graphFixedRootBorel.trans le_sup_left
  · exact hVB.trans le_sup_left
  · exact hMc.trans le_sup_right

theorem parabolic_small (a : Fin TwistTag.D4.foldedTag.rank)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom))
    (h2 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) = 2) :
    Group.IsSolvable ↥(graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) := by
  classical
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨R, hVN, hNV, hsup, hRV, hker⟩ := fixed_structure σ a
  have hVU : graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a ≤
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := graphFixedSimpleComplement_le a
  have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a) :=
    IsPGroup.of_injective hU (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
  have hVs : Group.IsSolvable ↥(graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a) := by
    have := hV2.isNilpotent
    infer_instance
  have hsolvSL : Group.IsSolvable (SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom a)) := by
    refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h2]
    norm_num
  have hMs : Group.IsSolvable ↥R.range :=
    Group.isSolvable_of_surjective (f := R.rangeRestrict) (MonoidHom.rangeRestrict_surjective R)
  have hNs : Group.IsSolvable ↥(fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a) :=
    isSolvable_of_levi hVN hNV hsup hVs hMs
  have hpcN : perfectCore (fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a) = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot _).mp hNs
  exact (isSolvable_iff_perfectCore_eq_bot _).mpr (by rw [fixed_perfectCore_eq σ a, hpcN])

end Levi

section Main

open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
  (triality_named_covers invariant_of_unequal_covers P0 P1 fa0 fa1 orbit_card_fa0 orbit_card_fa1)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "U₀" => graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom
local notation "B₁" => graphFixedRootBorel TwistTag.D4 K σ.toRingHom
local notation "Par[" a "]" => graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}

theorem exists_parabolic_data_of_model {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    [hLn : L.Normal] (hLT : L ⊔ T = ⊤) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (φ : ↥L ≃* ↥C₀)
    (hφU : ((T ⊓ L).subgroupOf L).map φ.toMonoidHom = (U₀).subgroupOf C₀) :
    ∃ (P J : Fin 2 → Subgroup G) (B : Subgroup G),
      P 0 ⊔ P 1 ⊔ T = ⊤ ∧ Group.IsSolvable ↥B ∧ T ≤ Subgroup.normalizer (B : Set G) ∧
      (∀ j, P j ≤ B ⊔ J j) ∧ (∀ j, T ≤ Subgroup.normalizer (J j : Set G)) ∧
      (∀ j, Group.IsSolvable ↥(J j) ∨
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (m : ℕ), Nat.card F = 2 ^ m ∧ 2 ≤ m ∧
          m ≤ 3 * f ∧ ∃ π : ↥(J j) →* SL(2, F), Function.Surjective π ∧ IsPGroup 2 ↥π.ker) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨hSylU, hcov, h0, h1, hgen, hi0, hi1⟩ := triality_named_covers hf σ hK hσ
  obtain ⟨σ', hσ', -, hcard, -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => (hσ c).trans (hσ' c).symm
  subst hσσ'
  have hUC : U₀ ≤ C₀ := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hU2 : IsPGroup 2 ↥U₀ := hSylU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hUC)
  have hcard0 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa0) = 2 ^ (3 * f) := by
    rw [hcard fa0, orbit_card_fa0, ← pow_mul, mul_comm]
  have hcard1 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) = 2 ^ f := by
    rw [hcard fa1, orbit_card_fa1, pow_one]
  set ψ : ↥C₀ →* G := L.subtype.comp φ.symm.toMonoidHom with hψ
  have hψi : Function.Injective ψ := L.subtype_injective.comp φ.symm.injective
  have hψr : ψ.range = L := by
    rw [hψ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr φ.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hne : (2 ^ f) ^ 3 + 1 ≠ 2 ^ f + 1 := by
    intro h
    have h1 : (2 ^ f) ^ 3 = 2 ^ f := Nat.add_right_cancel h
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have h2 : 2 ^ f < (2 ^ f) ^ 3 := by
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hinv : ∀ t ∈ T,
      ((P0 σ).subgroupOf C₀).map (conjAut φ t).toMonoidHom = (P0 σ).subgroupOf C₀ ∧
      ((P1 σ).subgroupOf C₀).map (conjAut φ t).toMonoidHom = (P1 σ).subgroupOf C₀ := fun t ht =>
    invariant_of_unequal_covers hcov (by rw [hi0, hi1]; exact hne) (conjAut φ t)
      (map_conjAut_eq φ hφU ht)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  have hBnorm : C₀ ⊓ Subgroup.normalizer (U₀ : Set (ModGL TwistTag.D4.tag K)) = B₁ :=
    (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1
  have hBC : B₁ ≤ C₀ := hBnorm ▸ inf_le_left
  have hNB : Subgroup.normalizer (((U₀).subgroupOf C₀ : Subgroup _) : Set _) =
      (B₁).subgroupOf C₀ := by
    rw [← Subgroup.subgroupOf_normalizer_eq hUC, ← hBnorm, Subgroup.inf_subgroupOf_left]
  have hBs : Group.IsSolvable ↥B₁ := isSolvable_graphFixedRootBorel σ.surjective
  have hsolv : ∀ (H : Subgroup (ModGL TwistTag.D4.tag K)), H ≤ C₀ → Group.IsSolvable ↥H →
      Group.IsSolvable ↥((H.subgroupOf C₀).map ψ) := fun H hHC hH => by
    haveI : Group.IsSolvable ↥(H.subgroupOf C₀) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hHC).toMonoidHom) (MulEquiv.injective _)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective _ ψ hψi).symm.toMonoidHom) (MulEquiv.injective _)
  set B : Subgroup G := (Subgroup.normalizer (((U₀).subgroupOf C₀ : Subgroup _) : Set _)).map ψ
    with hBdef
  have hBsol : Group.IsSolvable ↥B := by
    rw [hBdef, hNB]
    exact hsolv _ hBC hBs
  have hTB : T ≤ Subgroup.normalizer (B : Set G) := by
    refine le_normalizer_map φ (fun t ht y hy => ?_)
    have h := Subgroup.mem_map_of_mem (conjAut φ t).toMonoidHom hy
    rwa [Subgroup.map_equiv_normalizer_eq, map_conjAut_eq φ hφU ht] at h
  have key : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      (∀ t ∈ T, (Par[a].subgroupOf C₀).map (conjAut φ t).toMonoidHom = Par[a].subgroupOf C₀) →
      ∀ m : ℕ, m ≤ 3 * f → Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) = 2 ^ m →
      ∃ Ja : Subgroup G, (Par[a].subgroupOf C₀).map ψ ≤ B ⊔ Ja ∧
        T ≤ Subgroup.normalizer (Ja : Set G) ∧
        (Group.IsSolvable ↥Ja ∨
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (m' : ℕ), Nat.card F = 2 ^ m' ∧ 2 ≤ m' ∧
            m' ≤ 3 * f ∧ ∃ π : ↥Ja →* SL(2, F), Function.Surjective π ∧ IsPGroup 2 ↥π.ker) := by
    intro a hinva m hm3 hcm
    set Pa := (Par[a].subgroupOf C₀).map ψ with hPa
    have hPC : Par[a] ≤ C₀ := graphFixedParabolic_le _ _ _ _
    have hTP : T ≤ Subgroup.normalizer (Pa : Set G) := le_normalizer_map φ (fun t ht y hy => by
      have h := Subgroup.mem_map_of_mem (conjAut φ t).toMonoidHom hy
      rwa [hinva t ht] at h)
    by_cases h4 : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a)
    · have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom a), s.card = 4 :=
        exists_finset_card_four h4
      obtain ⟨hPB, g, hg, hgk⟩ := parabolic_large σ a hU2 hL4
      refine ⟨(perfectCore (Par[a].subgroupOf C₀)).map ψ, ?_, ?_, Or.inr ?_⟩
      · rw [hBdef, hNB, ← Subgroup.map_sup]
        refine Subgroup.map_mono ?_
        have h1 : Par[a].subgroupOf C₀ ≤ (B₁ ⊔ perfectCore Par[a]).subgroupOf C₀ :=
          Subgroup.subgroupOf_mono C₀ hPB
        rw [Subgroup.subgroupOf_sup hBC ((perfectCore_le _).trans hPC)] at h1
        have h2 : (perfectCore Par[a]).subgroupOf C₀ = perfectCore (Par[a].subgroupOf C₀) := by
          rw [← perfectCore_map_subgroupOf hPC]
          exact Subgroup.comap_map_eq_self_of_injective (C₀).subtype_injective _
        rwa [h2] at h1
      · rw [map_perfectCore ψ]
        exact hTP.trans (normalizer_le_normalizer_perfectCore Pa)
      · refine ⟨↥(orbitField TwistTag.D4 K σ.toRingHom a), inferInstance, inferInstance, m, hcm,
          ?_, hm3, ?_⟩
        · by_contra hlt
          have h1 : m ≤ 1 := by omega
          have h2 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
          omega
        · let e := Subgroup.equivMapOfInjective (perfectCore (Par[a].subgroupOf C₀)) ψ hψi
          refine ⟨g.comp e.symm.toMonoidHom, hg.comp e.symm.surjective, ?_⟩
          have : (g.comp e.symm.toMonoidHom).ker = g.ker.comap e.symm.toMonoidHom := rfl
          rw [this]
          exact IsPGroup.comap_of_injective hgk e.symm.toMonoidHom e.symm.injective
    · have hpos : 1 < Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) := Finite.one_lt_card
      have h2 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) = 2 := by
        have hm1 : m = 1 := by
          rcases Nat.lt_or_ge m 2 with h | h
          · rcases Nat.lt_or_ge m 1 with h' | h'
            · have h0 : m = 0 := by omega
              rw [h0, pow_zero] at hcm
              omega
            · omega
          · exfalso
            have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
            omega
        rw [hcm, hm1, pow_one]
      exact ⟨Pa, le_sup_right, hTP, Or.inl (hsolv _ hPC (parabolic_small σ a hU2 h2))⟩
  obtain ⟨J0, hPJ0, hTJ0, hlev0⟩ :=
    key fa0 (fun t ht => (hinv t ht).1) (3 * f) le_rfl hcard0
  obtain ⟨J1, hPJ1, hTJ1, hlev1⟩ := key fa1 (fun t ht => (hinv t ht).2) f (by omega) hcard1
  have hgenL : ((P0 σ).subgroupOf C₀).map ψ ⊔ ((P1 σ).subgroupOf C₀).map ψ = L := by
    rw [← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, hψr]
  refine ⟨![((P0 σ).subgroupOf C₀).map ψ, ((P1 σ).subgroupOf C₀).map ψ], ![J0, J1], B, ?_, hBsol,
    hTB, ?_, ?_, ?_⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hgenL]
    exact hLT
  · intro j
    fin_cases j
    · exact hPJ0
    · exact hPJ1
  · intro j
    fin_cases j
    · exact hTJ0
    · exact hTJ1
  · intro j
    fin_cases j
    · exact hlev0
    · exact hlev1

end Model

section Top


theorem exists_parabolic_data {G : Type} [Group G] [Finite G] {L T : Subgroup G} [hLn : L.Normal]
    (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤) {f : ℕ} (hf : 1 ≤ f) (hL : Is3D4 2 f ↥L) :
    ∃ (P J : Fin 2 → Subgroup G) (B : Subgroup G),
      P 0 ⊔ P 1 ⊔ T = ⊤ ∧ Group.IsSolvable ↥B ∧ T ≤ Subgroup.normalizer (B : Set G) ∧
      (∀ j, P j ≤ B ⊔ J j) ∧ (∀ j, T ≤ Subgroup.normalizer (J j : Set G)) ∧
      (∀ j, Group.IsSolvable ↥(J j) ∨
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (m : ℕ), Nat.card F = 2 ^ m ∧ 2 ≤ m ∧
          m ≤ 3 * f ∧ ∃ π : ↥(J j) →* SL(2, F), Function.Surjective π ∧ IsPGroup 2 ↥π.ker) := by
  classical
  have hTsyl : IsSylowTwoOf T ⊤ := ⟨le_top, hT.2.1, hT.2.2⟩
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTsyl le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hU : IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_subgroupOf_top hS
  obtain ⟨K, hF, hFin, σ, φ, hK, hσ, hφU, -, -⟩ := even_rank_two_residual_triality hL hU
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  exact exists_parabolic_data_of_model σ hLT hf hK hσ φ hφU

theorem nParam_le_three_mul {G : Type} [Group G] [Finite G] {L T : Subgroup G} [L.Normal]
    (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤) {f : ℕ} (hf : 1 ≤ f) (hL : Is3D4 2 f ↥L) :
    E1.nParam (⊤ : Subgroup G) ≤ ((3 * f : ℕ) : ℕ∞) := by
  obtain ⟨P, J, B, hgen, hBs, hTB, hPJ, hTJ, hJ⟩ := exists_parabolic_data hT hLT hf hL
  exact nParam_top_le_of_parabolics hT (M := 3 * f) (by omega) hgen hBs hTB hPJ hTJ hJ

end Top

end Main

end CFSG.Quasithin.RonanE114
