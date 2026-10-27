module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBTriCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootFieldTri
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4Forms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeLongRoot
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4IsoLen
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Steinberg.CentralExt.TrialityClosed
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBInner
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBTriPairAux

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.LieType.Steinberg.TwistedD4 CFSG.StandardType.LieKnownR2.TriD4.Bridge
  CFSG.StandardType.LieKnownR2.TriD4HighRootParabolic CFSG.StandardType.RootCentExc
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.HighestRoot
  CFSG.LieType.TitsSimplicity CFSG.SeitzReduction CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

private theorem rckTriP_pinnedX_ne
    (F : Type) [Field F] :
    pinnedX d4 F d4TrialityHighestRoot 1 ≠ pinnedX d4 F (Pi.single d4CentralIndex 1) 1 :=
  pinnedX_one_ne_pinnedX_one (τ := d4) (K := F)
    ⟨isRoot_d4TrialityHighestRoot, by rw [height_d4TrialityHighestRoot]; norm_num⟩
    ⟨isRoot_single d4 d4CentralIndex, by rw [height_single]; norm_num⟩
    (by decide)

theorem rckTriP_pair
    (F : Type) [Field F] [Finite F] (σ : F →+* F) (hF : TriField F σ 1) :
    ∃ (β : Fin (triD4Universal F σ).D.rank → ℤ) (x : (triD4Universal F σ).K)
        (V : Subgroup (triD4Universal F σ).K),
      β ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β ∧
      (triD4Universal F σ).D.rootGroup β = Subgroup.zpowers x ∧ x * x = 1 ∧ x ≠ 1 ∧
      RCKK1Data x V := by
  classical
  haveI hfinU : Finite (twistedGroup σ) := inferInstance
  haveI hfinAutU : Finite (MulAut (twistedGroup σ)) := inferInstance
  haveI hchar : CharP F 2 := CFSG.StandardType.RCKC1.charP_two_of_triField hF
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hσ3 : ∀ c : F, σ (σ (σ c)) = c := sigma_three_of_card hF.2.1 hF.2.2
  let C0 : Subgroup (ModGL d4 F) := graphFixedRootGroup TwistTag.D4 F σ
  let e : twistedGroup σ ≃* C0 := triD4BridgeEquiv σ hF.1 hF.2.1 hF.2.2
  let θ : Fin (Tag.rank .G2) → ℤ := highRoot .G2
  let b : Fin (Tag.rank .G2) → ℤ := Pi.single (ng 0) 1
  have hθroot : θ ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact isRoot_highRoot .G2
  have hLong_θ : GGLongRoot (twistedDatum σ) θ := by
    refine ⟨1, θ, hθroot, fun δ hδ => ?_, ?_⟩
    · rw [twistedDatum_roots] at hδ
      exact height_le_height_highRoot hδ
    · show θ = (weylAction (twistedDatum σ).isFiniteType (1 : GGWeyl (twistedDatum σ))) θ
      rw [map_one]
      rfl
  have hb_eq : weylAction (twistedDatum σ).isFiniteType
      (simple .G2 (ng 1) * simple .G2 (ng 0)) θ = b := by
    change (simple .G2 (ng 1) * simple .G2 (ng 0)) •
      (highRoot .G2 : Fin (Tag.rank .G2) → ℤ) = Pi.single (ng 0) 1
    simp only [mul_smul, simple_smul]
    decide +kernel
  have hLong_b : GGLongRoot (twistedDatum σ) b := by
    rw [← hb_eq]
    exact (CFSG.StandardType.LieKnownR2.Short.ggLongRoot_weylAction_iff (twistedDatum σ)
      (simple .G2 (ng 1) * simple .G2 (ng 0)) θ).2 hLong_θ
  have hhigh : highRoot d4 = d4TrialityHighestRoot := by decide +kernel
  let θ4 : Fin d4.rank → ℤ := d4TrialityHighestRoot
  let β4 : Fin d4.rank → ℤ := Pi.single d4CentralIndex 1
  let b4 : Fin d4.rank → ℤ := fun _ => 1
  have hθ4r : IsRoot d4 θ4 := isRoot_d4TrialityHighestRoot
  have hθ4p : 0 < height θ4 := by
    rw [show θ4 = d4TrialityHighestRoot from rfl, height_d4TrialityHighestRoot]; norm_num
  have hβ4r : IsRoot d4 β4 := isRoot_single d4 d4CentralIndex
  have hβ4p : 0 < height β4 := by
    rw [show β4 = Pi.single d4CentralIndex 1 from rfl, height_single]; norm_num
  have hb4r : IsRoot d4 b4 := by
    rw [← CFSG.Blueprint.Chevalley.StringData.memDec_iff
      (Tag.rootCertificate_check d4) (Tag.stringData_check d4)]
    decide +kernel
  have hb4p : 0 < height b4 := by decide +kernel
  have hθ4ρ : permLattice TwistTag.D4.perm θ4 = θ4 := by
    rw [show θ4 = d4TrialityHighestRoot from rfl]
    exact permLattice_d4TrialityHighestRoot
  have hβ4ρ : permLattice TwistTag.D4.perm β4 = β4 := by
    rw [show β4 = Pi.single d4CentralIndex 1 from rfl, permLattice_single,
      perm_d4CentralIndex]
  have hb4ρ : permLattice TwistTag.D4.perm b4 = b4 := by
    ext j; fin_cases j <;> rfl
  have h2notJ : d4CentralIndex ∉ TwistTag.D4.orbitUnion ({0} : Set (Fin 2)) := by
    intro h
    obtain ⟨a, ha, hia⟩ :=
      (TwistTag.mem_orbitUnion TwistTag.D4 (J := ({0} : Set (Fin 2)))).mp h
    have ha0 : a = 0 := Set.mem_singleton_iff.mp ha
    subst ha0
    exact absurd hia (by decide)
  have hθ4mem : θ4 ∈ parabolicRadicalRoots d4 (TwistTag.D4.orbitUnion ({0} : Set (Fin 2))) :=
    (mem_parabolicRadicalRoots_iff (τ := d4)
      (J := TwistTag.D4.orbitUnion ({0} : Set (Fin 2)))).2
      ⟨hθ4r, hθ4p, d4CentralIndex, h2notJ, by decide⟩
  have hβ4mem : β4 ∈ parabolicRadicalRoots d4 (TwistTag.D4.orbitUnion ({0} : Set (Fin 2))) :=
    (mem_parabolicRadicalRoots_iff (τ := d4)
      (J := TwistTag.D4.orbitUnion ({0} : Set (Fin 2)))).2
      ⟨hβ4r, hβ4p, d4CentralIndex, h2notJ, by decide⟩
  let a : C0 := ⟨pinnedX d4 F θ4 1,
    pinnedX_one_mem_graphFixedRootGroup h2 σ hθ4r hθ4p hθ4ρ⟩
  let y0 : C0 := ⟨pinnedX d4 F β4 1,
    pinnedX_one_mem_graphFixedRootGroup h2 σ hβ4r hβ4p hβ4ρ⟩
  let z0 : C0 := ⟨pinnedX d4 F b4 1,
    pinnedX_one_mem_graphFixedRootGroup h2 σ hb4r hb4p hb4ρ⟩
  have ha2 : a * a = 1 := by
    apply Subtype.ext
    exact pinnedX_one_mul_self h2 θ4
  have hy2 : y0 * y0 = 1 := by
    apply Subtype.ext
    exact pinnedX_one_mul_self h2 β4
  have hay : a * y0 = y0 * a := by
    apply Subtype.ext
    exact (commute_pinnedX_of_forall_height_le F hθ4r
      forall_height_le_d4TrialityHighestRoot hβ4r hβ4p 1 1).eq
  have ha1 : a ≠ 1 := by
    intro h
    have h' : (a : ModGL d4 F) = 1 := congrArg (fun g : C0 => (g : ModGL d4 F)) h
    exact pinnedX_one_ne_one (τ := d4) (K := F) θ4 h'
  have hy1 : y0 ≠ 1 := by
    intro h
    have h' : (y0 : ModGL d4 F) = 1 := congrArg (fun g : C0 => (g : ModGL d4 F)) h
    exact pinnedX_one_ne_one (τ := d4) (K := F) β4 h'
  have hθβ_ne : θ4 ≠ β4 := by decide
  have haney : a ≠ y0 := fun h =>
    rckTriP_pinnedX_ne F (congrArg (fun g : C0 => (g : ModGL d4 F)) h)
  have hV0rad : FourGroup.kleinFourOf a y0 ha2 hy2 hay ≤
      (graphFixedParabolicRadical TwistTag.D4 F σ ({0} : Set (Fin 2))).subgroupOf C0 := by
    refine FourGroup.kleinFourOf_le ?_ ?_
    · refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      · exact Subgroup.mem_iSup_of_mem θ4
          (Subgroup.mem_iSup_of_mem hθ4mem (Subgroup.subset_closure ⟨1, rfl⟩))
      · exact graphFixedRootGroup_le TwistTag.D4 F σ a.2
    · refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      · exact Subgroup.mem_iSup_of_mem β4
          (Subgroup.mem_iSup_of_mem hβ4mem (Subgroup.subset_closure ⟨1, rfl⟩))
      · exact graphFixedRootGroup_le TwistTag.D4 F σ y0.2
  have hV0p : FourGroup.kleinFourOf a y0 ha2 hy2 hay ≤
      pCoreOf 2 (Subgroup.normalizer (triD4C0HighRoot F σ : Set C0)) := by
    rw [rckTriC_pcore_normalizer_C0 (K := F) σ]
    exact hV0rad
  let x : twistedGroup σ := e.symm a
  let y : twistedGroup σ := e.symm y0
  let z : twistedGroup σ := e.symm z0
  have hx2 : x * x = 1 := by
    apply e.injective
    simpa [x] using ha2
  have hy2' : y * y = 1 := by
    apply e.injective
    simpa [y] using hy2
  have hxy' : x * y = y * x := by
    apply e.injective
    simpa [x, y] using hay
  have hx1 : x ≠ 1 := by
    intro h
    apply ha1
    have := congrArg e h
    simpa [x] using this
  have hy1' : y ≠ 1 := by
    intro h
    apply hy1
    have := congrArg e h
    simpa [y] using this
  have hxney : x ≠ y := by
    intro h
    apply haney
    calc a = e x := (e.apply_symm_apply a).symm
      _ = e y := by rw [h]
      _ = y0 := e.apply_symm_apply y0
  have hcardθ : Nat.card ((twistedDatum σ).rootGroup θ) = 2 := by
    obtain ⟨β0, hβ0root, hβ0long, Fq, hFieldFq, hFiniteFq, ε, hcardFq, -⟩ :=
      CFSG.StandardType.RCKK1I.rckK1I_rootField_triD4 hF
    have hcardβ0 : Nat.card ((triD4Universal F σ).D.rootGroup β0) = 2 := by
      have h1 : Nat.card ((triD4Universal F σ).D.rootGroup β0) = Nat.card Fq :=
        (Nat.card_congr ε.toEquiv).symm
      rw [h1, hcardFq, pow_one]
    obtain ⟨m, hm⟩ := triD4_longRoot_conj (β := β0) σ hσ3
      (show GGLongRoot (twistedDatum σ) β0 from hβ0long)
    have h2' : Nat.card (((twistedDatum σ).rootGroup θ).map (MulAut.conj m).toMonoidHom) =
        Nat.card ((twistedDatum σ).rootGroup θ) :=
      Subgroup.card_map_of_injective (MulAut.conj m).injective
    rw [← h2', ← hm]
    exact hcardβ0
  have hxθ : x ∈ (twistedDatum σ).rootGroup θ := by
    have ha_high : a ∈ ((twistedDatum σ).rootGroup θ).map e.toMonoidHom := by
      change a ∈ ((twistedDatum σ).rootGroup (highRoot .G2)).map e.toMonoidHom
      rw [triD4BridgeEquiv_twistedRootGroup_highRoot σ hF.1 hF.2.1 hF.2.2]
      rw [triD4C0HighRoot, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · show pinnedX d4 F θ4 1 ∈ rootSubgroup d4 F (highRoot d4)
        rw [hhigh]
        exact Subgroup.subset_closure ⟨1, rfl⟩
      · exact graphFixedRootGroup_le TwistTag.D4 F σ a.2
    obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp ha_high
    have hxg : x = g := by
      change e.symm a = g
      rw [← hge]
      exact e.symm_apply_apply g
    rw [hxg]; exact hg
  have hX_theta : (twistedDatum σ).rootGroup θ = Subgroup.zpowers x := by
    have hxord : orderOf x = 2 := rckTriP_orderOf_eq_two hx1 hx2
    have hle : Subgroup.zpowers x ≤ (twistedDatum σ).rootGroup θ :=
      Subgroup.zpowers_le.mpr hxθ
    have hcard : Nat.card ((twistedDatum σ).rootGroup θ) ≤ Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, hxord, hcardθ]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hcommF : ⁅pinnedX d4 F b4 1, pinnedX d4 F β4 1⁆ = pinnedX d4 F θ4 1 := by
    have hαβ : b4 + β4 = θ4 := by
      ext j; fin_cases j <;> decide
    have hsum : IsRoot d4 (b4 + β4) := by rw [hαβ]; exact hθ4r
    have hne : b4 ≠ β4 := by decide
    have hne' : b4 ≠ -β4 := by decide
    obtain ⟨hC1, hC2⟩ := (simply_laced_root_commutator_unit d4 (Or.inl rfl) hb4r hβ4r
      hne hne').1 hsum
    have hCeq : ((commConst d4 b4 β4 (1, 1) : ℤ) : F) = 1 := by
      rcases hC1 with h | h
      · rw [h]; norm_num
      · rw [h]
        push_cast
        exact CharTwo.neg_eq 1
    have h := hC2 F 1 1
    rw [hαβ, hCeq] at h
    simpa using h
  have hz_coe : (z : ModGL d4 F) = pinnedX d4 F b4 1 := by
    have := triD4BridgeEquiv_coe σ hF.1 hF.2.1 hF.2.2 (e.symm z0)
    simpa [z, e] using this.symm
  have hy_coe : (y : ModGL d4 F) = pinnedX d4 F β4 1 := by
    have := triD4BridgeEquiv_coe σ hF.1 hF.2.1 hF.2.2 (e.symm y0)
    simpa [y, e] using this.symm
  have hx_coe : (x : ModGL d4 F) = pinnedX d4 F θ4 1 := by
    have := triD4BridgeEquiv_coe σ hF.1 hF.2.1 hF.2.2 (e.symm a)
    simpa [x, e] using this.symm
  have hcomm_z : (z : ModGL d4 F) * (y : ModGL d4 F) * (z : ModGL d4 F)⁻¹ =
      (x : ModGL d4 F) * (y : ModGL d4 F) := by
    rw [hz_coe, hy_coe, hx_coe]
    have h1 : pinnedX d4 F b4 1 * pinnedX d4 F β4 1 * (pinnedX d4 F b4 1)⁻¹ =
        ⁅pinnedX d4 F b4 1, pinnedX d4 F β4 1⁆ * pinnedX d4 F β4 1 := by
      rw [commutatorElement_def]; group
    rw [h1, hcommF]
  have hzy : z * y * z⁻¹ = x * y := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hcomm_z
  have hyb : y ∈ (twistedDatum σ).rootGroup b := by
    have hxpar : ((xPar (rootOperatorFamily d4) β4 1 : adjointGroup d4 F) : ModGL d4 F) =
        pinnedX d4 F β4 1 := coe_xPar_eq_pinnedX h2 (rootOperatorFamily d4) hβ4r 1
    have hypar : (y : adjointGroup d4 F) = xPar (rootOperatorFamily d4) β4 1 := by
      apply Subtype.ext
      rw [hxpar, ← hy_coe]
    have hmem : xPar (rootOperatorFamily d4) β4 1 ∈ twistedRootSubgroupD4 σ b := by
      have h := xPar_two_mem (σ := σ) (s := (1 : ℤ)) (Or.inl rfl) (c := (1 : F)) (map_one σ)
      rw [one_smul, one_smul] at h
      rw [show (nd 2 : Fin d4.rank) = d4CentralIndex from Fin.ext rfl] at h
      simpa [β4, b] using h
    show y ∈ (twistedRootSubgroupD4 σ b).subgroupOf (twistedGroup σ)
    exact Subgroup.mem_subgroupOf.2 (by rw [hypar]; exact hmem)
  have hy_conj : ∃ j : twistedGroup σ, y = j * x * j⁻¹ := by
    obtain ⟨m, hm⟩ := triD4_longRoot_conj σ hσ3 hLong_b
    have hyb' : y ∈ ((twistedDatum σ).rootGroup θ).map (MulAut.conj m).toMonoidHom := by
      rw [← hm]; exact hyb
    obtain ⟨x', hx', hy_eq⟩ := Subgroup.mem_map.mp hyb'
    have hx'z : x' ∈ Subgroup.zpowers x := by
      rw [← hX_theta]; exact hx'
    have hx'1 : x' ≠ 1 := by
      intro h
      exact hy1' (by rw [← hy_eq, h, map_one])
    have hx'eq : x' = x := rckTriP_zpowers_eq_of_involution hx2 hx1 hx'z hx'1
    have hy_eq' : m * x' * m⁻¹ = y := by
      simpa [MulAut.conj_apply] using hy_eq
    exact ⟨m, by rw [← hy_eq', hx'eq]⟩
  have hxy_conj : ∃ j : twistedGroup σ, x * y = j * x * j⁻¹ := by
    obtain ⟨j, hj⟩ := hy_conj
    exact ⟨z * j, by rw [hzy.symm, hj]; group⟩
  have hconj : ∀ v ∈ FourGroup.kleinFourOf x y hx2 hy2' hxy', v ≠ 1 →
      ∃ j : twistedGroup σ, v = j * x * j⁻¹ := by
    intro v hv hv1
    rcases (FourGroup.mem_kleinFourOf).mp hv with rfl | rfl | rfl | rfl
    · exact absurd rfl hv1
    · exact ⟨1, by group⟩
    · exact hy_conj
    · exact hxy_conj
  have hmap : (pCoreOf 2 (Subgroup.normalizer ((twistedDatum σ).rootGroup θ :
        Set (twistedGroup σ)))).map e.toMonoidHom =
      pCoreOf 2 (Subgroup.normalizer (triD4C0HighRoot F σ : Set C0)) := by
    rw [CFSG.StandardType.LieKnownR2.map_pCoreOf_normalizer_mulEquiv e,
      triD4BridgeEquiv_twistedRootGroup_highRoot σ hF.1 hF.2.1 hF.2.2]
  have hVe : (FourGroup.kleinFourOf x y hx2 hy2' hxy').map e.toMonoidHom ≤
      pCoreOf 2 (Subgroup.normalizer (triD4C0HighRoot F σ : Set C0)) := by
    rintro w ⟨v, hv, rfl⟩
    rcases (FourGroup.mem_kleinFourOf).mp hv with rfl | rfl | rfl | rfl
    · rw [map_one]; exact Subgroup.one_mem _
    · have hex : e.toMonoidHom x = a := e.apply_symm_apply a
      rw [hex]
      exact hV0p FourGroup.left_mem_kleinFourOf
    · have hey : e.toMonoidHom y = y0 := e.apply_symm_apply y0
      rw [hey]
      exact hV0p FourGroup.right_mem_kleinFourOf
    · have hex : e.toMonoidHom x = a := e.apply_symm_apply a
      have hey : e.toMonoidHom y = y0 := e.apply_symm_apply y0
      rw [map_mul, hex, hey]
      exact hV0p ((FourGroup.kleinFourOf a y0 ha2 hy2 hay).mul_mem
        FourGroup.left_mem_kleinFourOf FourGroup.right_mem_kleinFourOf)
  have hVle : FourGroup.kleinFourOf x y hx2 hy2' hxy' ≤
      pCoreOf 2 (Subgroup.normalizer ((twistedDatum σ).rootGroup θ : Set (twistedGroup σ))) := by
    intro v hv
    have hv' : e v ∈ (pCoreOf 2 (Subgroup.normalizer
        ((twistedDatum σ).rootGroup θ : Set (twistedGroup σ)))).map e.toMonoidHom := by
      rw [hmap]
      exact hVe ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hv'
    rwa [e.injective hwe] at hw
  have hxord : orderOf x = 2 := rckTriP_orderOf_eq_two hx1 hx2
  have hVcentral : FourGroup.kleinFourOf x y hx2 hy2' hxy' ≤
      pCoreOf 2 (Subgroup.centralizer ({x} : Set (twistedGroup σ))) := by
    rwa [← ggNormalizer_zpowers_eq_centralizer hxord, ← hX_theta]
  have hQ : ⁅pCoreOf 2 (Subgroup.centralizer ({x} : Set (twistedGroup σ))),
      pCoreOf 2 (Subgroup.centralizer ({x} : Set (twistedGroup σ)))⁆ ≤ Subgroup.zpowers x := by
    have h := rckTriC_hQ σ hF
    rwa [hX_theta, ggNormalizer_zpowers_eq_centralizer hxord] at h
  have hI : GGRootInnerAt (MulAut.conj : twistedGroup σ →* MulAut (twistedGroup σ)).range
      ((Subgroup.zpowers x).map (MulAut.conj : twistedGroup σ →* MulAut (twistedGroup σ))) := by
    have hker : (MulAut.conj : twistedGroup σ →* MulAut (twistedGroup σ)).ker ≤
        Subgroup.center (twistedGroup σ) := by rw [rckTriP_ker_conj]
    have h := CFSG.StandardType.LieKnownR2.TriD4.ggRootInnerAt_triD4 hF
      (MulAut.conj : twistedGroup σ →* MulAut (twistedGroup σ)) hker hLong_θ 1
    have hgg : ggRootSub (twistedDatum σ)
        (MulAut.conj : twistedGroup σ →* MulAut (twistedGroup σ)) θ 1 =
        (Subgroup.zpowers x).map (MulAut.conj : twistedGroup σ →* MulAut (twistedGroup σ)) := by
      simp only [ggRootSub, map_one]
      rw [show MulEquiv.toMonoidHom (1 : MulAut (twistedGroup σ)) = MonoidHom.id (twistedGroup σ)
          from rfl, Subgroup.map_id, hX_theta]
    have h' : GGRootInnerAt (MulAut.conj : twistedGroup σ →* MulAut (twistedGroup σ)).range
        (ggRootSub (twistedDatum σ)
          (MulAut.conj : twistedGroup σ →* MulAut (twistedGroup σ)) θ 1) := h
    rwa [hgg] at h'
  haveI hEA : CFSG.IsElementaryAbelian 2 (FourGroup.kleinFourOf x y hx2 hy2' hxy') :=
    FourGroup.isElementaryAbelian_kleinFourOf
  have hK1b : K1Lift.K1b x (FourGroup.kleinFourOf x y hx2 hy2' hxy') :=
    rckK1b_of_inner
      (by
        change Subgroup.center (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ) = ⊥
        exact CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
          (q := 2) (by norm_num) (by rw [hF.2.1]; norm_num) (fun c => by simpa using hF.2.2 c))
      x hx2 hI hQ (FourGroup.kleinFourOf x y hx2 hy2' hxy') hVcentral
  refine ⟨θ, x, FourGroup.kleinFourOf x y hx2 hy2' hxy', hθroot, hLong_θ, hX_theta, hx2, hx1,
    FourGroup.left_mem_kleinFourOf, hx1,
    (CFSG.Open.isElemAbelian_of_isElementaryAbelian
      (E := FourGroup.kleinFourOf x y hx2 hy2' hxy')),
    FourGroup.card_kleinFourOf hx1 hy1' hxney, hconj, hK1b⟩

end CFSG.StandardType.RCKK1II
