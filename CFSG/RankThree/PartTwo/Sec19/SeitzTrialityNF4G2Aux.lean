module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTau
public import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LieType.HighestRoot

namespace CFSG.RankThree.PartTwo.Sec19

section Aux


variable {n : ℕ} {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

@[expose] noncomputable def g2RootSL2 (i : Fin (Tag.rank .G2)) (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup Tag.G2 K :=
  (simpleRootSL2 Tag.G2 K i).codRestrict (adjointGroup Tag.G2 K)
    (fun A => simpleRootSL2_mem_adjointGroup i A)

@[expose] noncomputable def g2WeylRep (K : Type) [Field K] : adjointGroup Tag.G2 K :=
  ⟨canonicalRep (coxeterSystem Tag.G2) K (simple Tag.G2 g2s * simple Tag.G2 g2l),
    canonicalRep_mem_adjointGroup _ K _⟩

theorem short_conj_mem (K : Type) [Field K] (g : adjointGroup Tag.G2 K)
    (hg : g ∈ KS11Lie4Proof.g2ShortSL2 K) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) K,
      MulAut.conj (g2WeylRep K)⁻¹ g = g2RootSL2 g2s K x := by
  have hmem : (g : ModGL Tag.G2 K) ∈
      rootSubgroup Tag.G2 K g2δ ⊔ rootSubgroup Tag.G2 K (-g2δ) := hg
  rw [← map_conj_canonicalRep_closure_xUnit_yUnit g2_w_smul, Subgroup.mem_map] at hmem
  obtain ⟨h, hh, hgh⟩ := hmem
  rw [← range_simpleRootSL2] at hh
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hh
  refine ⟨x, ?_⟩
  have hcoe : ((g2RootSL2 g2s K x : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) = h := hx
  have hgeq : g = g2WeylRep K * g2RootSL2 g2s K x * (g2WeylRep K)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe]
    exact hgh.symm
  rw [hgeq, MulAut.conj_apply]
  group

theorem long_conj_mem (K : Type) [Field K] (g : adjointGroup Tag.G2 K)
    (hg : g ∈ KS11Lie4Proof.g2LongSL2 K) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) K, g = g2RootSL2 g2l K x := by
  have hmem : (g : ModGL Tag.G2 K) ∈
      rootSubgroup Tag.G2 K g2e0 ⊔ rootSubgroup Tag.G2 K (-g2e0) := hg
  rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2] at hmem
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hmem
  exact ⟨x, Subtype.ext hx.symm⟩

theorem coe_trialityFixIncl_g2Upper (c : fixSubfield σ) :
    ((trialityFixIncl σ ⟨g2OrbitXUnit (fixSubfield σ) g2s c, g2OrbitXUnit_mem g2s c⟩ : C0 σ) :
        ModGL TwistTag.D4.tag X) = g2OrbitXUnit X g2s (c : X) := by
  rw [coe_trialityFixIncl]
  exact baseChangeGL_g2OrbitXUnit (fixSubfield σ).subtype g2s c

theorem coe_trialityFixIncl_g2Lower (c : fixSubfield σ) :
    ((trialityFixIncl σ ⟨g2OrbitYUnit (fixSubfield σ) g2s c, g2OrbitYUnit_mem g2s c⟩ : C0 σ) :
        ModGL TwistTag.D4.tag X) = g2OrbitYUnit X g2s (c : X) := by
  rw [coe_trialityFixIncl]
  exact baseChangeGL_g2OrbitYUnit (fixSubfield σ).subtype g2s c

theorem g2OrbitXUnit_eq_orbitX_d4Outer (P : D4Par n X σ) (c : fixSubfield σ) :
    g2OrbitXUnit X g2s (c : X) = (orbitX TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        ⟨(c : X), KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three (c : X)⟩ :
          ModGL TwistTag.D4.tag X) :=
  g2OrbitXUnit_eq_orbitX_of_fixed ((mem_fixSubfield σ).1 c.2) g2s

theorem g2OrbitYUnit_eq_orbitY_d4Outer (P : D4Par n X σ) (c : fixSubfield σ) :
    g2OrbitYUnit X g2s (c : X) = (orbitY TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        ⟨(c : X), KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three (c : X)⟩ :
          ModGL TwistTag.D4.tag X) :=
  g2OrbitYUnit_eq_orbitY_of_fixed ((mem_fixSubfield σ).1 c.2) g2s

theorem coe_iotaA_sl2Upper_outer (P : D4Par n X σ) (c : fixSubfield σ) :
    ((iotaA P (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
        (CFSG.LieType.Steinberg.sl2Upper c)) : C0 σ) : ModGL TwistTag.D4.tag X) =
      (orbitX TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        ⟨(c : X), KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three (c : X)⟩ :
          ModGL TwistTag.D4.tag X) := by
  have e : Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
      (CFSG.LieType.Steinberg.sl2Upper c) = CFSG.LieType.Steinberg.sl2Upper (c : X) :=
    map_uSL (f := (fixSubfield σ).subtype) c
  rw [e, coe_iotaA P (CFSG.LieType.Steinberg.sl2Upper (c : X)), slShort_upper_eq_orbit P (c : X),
    orbitRankOneHom_uSL]

theorem coe_iotaA_sl2Lower_outer (P : D4Par n X σ) (c : fixSubfield σ) :
    ((iotaA P (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
        (CFSG.LieType.Steinberg.sl2Lower c)) : C0 σ) : ModGL TwistTag.D4.tag X) =
      (orbitY TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        ⟨(c : X), KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three (c : X)⟩ :
          ModGL TwistTag.D4.tag X) := by
  have e : Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
      (CFSG.LieType.Steinberg.sl2Lower c) = CFSG.LieType.Steinberg.sl2Lower (c : X) :=
    map_vSL (f := (fixSubfield σ).subtype) c
  rw [e, coe_iotaA P (CFSG.LieType.Steinberg.sl2Lower (c : X)), slShort_lower_eq_orbit P (c : X),
    orbitRankOneHom_vSL]

theorem g2RootSL2_short_upper_incl (P : D4Par n X σ) (hK : ringChar X = 2)
    (c : fixSubfield σ) :
    KFacts.trialityG2Incl σ hK (g2RootSL2 g2s (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Upper c)) =
      iotaA P (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
        (CFSG.LieType.Steinberg.sl2Upper c)) := by
  have h2 : (2 : fixSubfield σ) = 0 := two_eq_zero_fixSubfield σ hK
  have hz : g2RootSL2 g2s (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Upper c) =
      d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitXUnit (fixSubfield σ) g2s c, g2OrbitXUnit_mem g2s c⟩ := by
    apply Subtype.ext
    exact (simpleRootSL2_uSL g2s c).trans (d4FixedToG2_g2OrbitXUnit h2 g2s c).symm
  have hI : KFacts.trialityG2Incl σ hK
      (d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitXUnit (fixSubfield σ) g2s c, g2OrbitXUnit_mem g2s c⟩) =
      trialityFixIncl σ ⟨g2OrbitXUnit (fixSubfield σ) g2s c, g2OrbitXUnit_mem g2s c⟩ := by
    change trialityFixIncl σ ((d4FixedG2Equiv (fixSubfield σ) h2).symm
      (d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitXUnit (fixSubfield σ) g2s c, g2OrbitXUnit_mem g2s c⟩)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [hz, hI]
  apply Subtype.ext
  exact (coe_trialityFixIncl_g2Upper σ c).trans
    ((g2OrbitXUnit_eq_orbitX_d4Outer σ P c).trans (coe_iotaA_sl2Upper_outer σ P c).symm)

theorem g2RootSL2_short_lower_incl (P : D4Par n X σ) (hK : ringChar X = 2)
    (c : fixSubfield σ) :
    KFacts.trialityG2Incl σ hK (g2RootSL2 g2s (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Lower c)) =
      iotaA P (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
        (CFSG.LieType.Steinberg.sl2Lower c)) := by
  have h2 : (2 : fixSubfield σ) = 0 := two_eq_zero_fixSubfield σ hK
  have hz : g2RootSL2 g2s (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Lower c) =
      d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitYUnit (fixSubfield σ) g2s c, g2OrbitYUnit_mem g2s c⟩ := by
    apply Subtype.ext
    exact (simpleRootSL2_vSL g2s c).trans (d4FixedToG2_g2OrbitYUnit h2 g2s c).symm
  have hI : KFacts.trialityG2Incl σ hK
      (d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitYUnit (fixSubfield σ) g2s c, g2OrbitYUnit_mem g2s c⟩) =
      trialityFixIncl σ ⟨g2OrbitYUnit (fixSubfield σ) g2s c, g2OrbitYUnit_mem g2s c⟩ := by
    change trialityFixIncl σ ((d4FixedG2Equiv (fixSubfield σ) h2).symm
      (d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitYUnit (fixSubfield σ) g2s c, g2OrbitYUnit_mem g2s c⟩)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [hz, hI]
  apply Subtype.ext
  exact (coe_trialityFixIncl_g2Lower σ c).trans
    ((g2OrbitYUnit_eq_orbitY_d4Outer σ P c).trans (coe_iotaA_sl2Lower_outer σ P c).symm)

theorem g2RootSL2_short_hom_eq (P : D4Par n X σ) (hK : ringChar X = 2) :
    (KFacts.trialityG2Incl σ hK).comp (g2RootSL2 g2s (fixSubfield σ)) =
      (iotaA P).comp (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype) := by
  refine MonoidHom.eq_of_eqOn_dense
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixSubfield σ)) ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact g2RootSL2_short_upper_incl σ P hK c
  · exact g2RootSL2_short_lower_incl σ P hK c

theorem g2RootSL2_short_le_A0 (P : D4Par n X σ) (hK : ringChar X = 2)
    (x : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) :
    KFacts.trialityG2Incl σ hK (g2RootSL2 g2s (fixSubfield σ) x) ∈ A0sub σ := by
  rw [mem_A0sub_iff P]
  exact ⟨x, DFunLike.congr_fun (g2RootSL2_short_hom_eq σ P hK) x⟩


theorem bridge_coe_fixIncl_X (j : Fin Tag.G2.rank) (c : fixSubfield σ) :
    ((trialityFixIncl σ ⟨g2OrbitXUnit (fixSubfield σ) j c, g2OrbitXUnit_mem j c⟩ : C0 σ) :
        ModGL TwistTag.D4.tag X) = g2OrbitXUnit X j (c : X) := by
  rw [coe_trialityFixIncl]
  exact baseChangeGL_g2OrbitXUnit (fixSubfield σ).subtype j c

theorem bridge_coe_fixIncl_Y (j : Fin Tag.G2.rank) (c : fixSubfield σ) :
    ((trialityFixIncl σ ⟨g2OrbitYUnit (fixSubfield σ) j c, g2OrbitYUnit_mem j c⟩ : C0 σ) :
        ModGL TwistTag.D4.tag X) = g2OrbitYUnit X j (c : X) := by
  rw [coe_trialityFixIncl]
  exact baseChangeGL_g2OrbitYUnit (fixSubfield σ).subtype j c

theorem bridge_coe_incl_upper (hK : ringChar X = 2) (j : Fin Tag.G2.rank) (c : fixSubfield σ) :
    ((KFacts.trialityG2Incl σ hK (g2RootSL2 j (fixSubfield σ)
        (CFSG.LieType.Steinberg.sl2Upper c)) : C0 σ) : ModGL TwistTag.D4.tag X) =
      g2OrbitXUnit X j (c : X) := by
  have h2 : (2 : fixSubfield σ) = 0 := two_eq_zero_fixSubfield σ hK
  have hz : g2RootSL2 j (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Upper c) =
      d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitXUnit (fixSubfield σ) j c, g2OrbitXUnit_mem j c⟩ := by
    apply Subtype.ext
    exact (simpleRootSL2_uSL j c).trans (d4FixedToG2_g2OrbitXUnit h2 j c).symm
  have hI : KFacts.trialityG2Incl σ hK
      (d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitXUnit (fixSubfield σ) j c, g2OrbitXUnit_mem j c⟩) =
      trialityFixIncl σ ⟨g2OrbitXUnit (fixSubfield σ) j c, g2OrbitXUnit_mem j c⟩ := by
    change trialityFixIncl σ ((d4FixedG2Equiv (fixSubfield σ) h2).symm
      (d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitXUnit (fixSubfield σ) j c, g2OrbitXUnit_mem j c⟩)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [hz, hI]
  exact bridge_coe_fixIncl_X σ j c

theorem bridge_coe_incl_lower (hK : ringChar X = 2) (j : Fin Tag.G2.rank) (c : fixSubfield σ) :
    ((KFacts.trialityG2Incl σ hK (g2RootSL2 j (fixSubfield σ)
        (CFSG.LieType.Steinberg.sl2Lower c)) : C0 σ) : ModGL TwistTag.D4.tag X) =
      g2OrbitYUnit X j (c : X) := by
  have h2 : (2 : fixSubfield σ) = 0 := two_eq_zero_fixSubfield σ hK
  have hz : g2RootSL2 j (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Lower c) =
      d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitYUnit (fixSubfield σ) j c, g2OrbitYUnit_mem j c⟩ := by
    apply Subtype.ext
    exact (simpleRootSL2_vSL j c).trans (d4FixedToG2_g2OrbitYUnit h2 j c).symm
  have hI : KFacts.trialityG2Incl σ hK
      (d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitYUnit (fixSubfield σ) j c, g2OrbitYUnit_mem j c⟩) =
      trialityFixIncl σ ⟨g2OrbitYUnit (fixSubfield σ) j c, g2OrbitYUnit_mem j c⟩ := by
    change trialityFixIncl σ ((d4FixedG2Equiv (fixSubfield σ) h2).symm
      (d4FixedG2Equiv (fixSubfield σ) h2
        ⟨g2OrbitYUnit (fixSubfield σ) j c, g2OrbitYUnit_mem j c⟩)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [hz, hI]
  exact bridge_coe_fixIncl_Y σ j c

theorem bridge_g2OrbitXUnit_long (c : X) :
    g2OrbitXUnit X g2l c = xUnit TwistTag.D4.tag X (CFSG.LieType.Steinberg.TwistedD4.nd 2) c := by
  have h : TwistTag.D4.orbitWord (KFacts.g2FoldedIndex g2l) =
      [CFSG.LieType.Steinberg.TwistedD4.nd 2] := by decide
  rw [g2OrbitXUnit, h]
  simp

theorem bridge_g2OrbitYUnit_long (c : X) :
    g2OrbitYUnit X g2l c = yUnit TwistTag.D4.tag X (CFSG.LieType.Steinberg.TwistedD4.nd 2) c := by
  have h : TwistTag.D4.orbitWord (KFacts.g2FoldedIndex g2l) =
      [CFSG.LieType.Steinberg.TwistedD4.nd 2] := by decide
  rw [g2OrbitYUnit, h]
  simp

theorem bridge_coe_eC_symm (P : D4Par n X σ)
    (y : CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) :
    (((eC P).symm y : C0 σ) : ModGL TwistTag.D4.tag X) =
      ((y : adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
        ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) := by
  have h1 := coe_eC P ((eC P).symm y)
  rw [(eC P).apply_symm_apply] at h1
  exact h1.symm

theorem bridge_coe_slLong_upper (P : D4Par n X σ) (c : fixSubfield σ) :
    (((CFSG.LieType.Steinberg.TwistedD4.slLong σ.toRingHom P.sigma_cube_hom
        (CFSG.LieType.Steinberg.sl2Upper c) :
        CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) :
          adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
            ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) =
      xUnit TwistTag.D4.tag X (CFSG.LieType.Steinberg.TwistedD4.nd 2) (c : X) := by
  rw [CFSG.LieType.Steinberg.TwistedD4.slLong_val,
    CFSG.LieType.Steinberg.TwistedD4.slLongE_upper]
  have e : CFSG.LieType.Steinberg.Adjoint.xPar
      (rootOperatorFamily CFSG.LieType.Steinberg.TwistedD4.d4)
      (Pi.single (CFSG.LieType.Steinberg.TwistedD4.nd 2) 1) (c : X) =
      CFSG.RankThree.PartOne.SEITZ7.xd 2 (c : X) := by
    simp only [CFSG.RankThree.PartOne.SEITZ7.xd,
      CFSG.RankThree.PartOne.SEITZ7.d4Root_dict.1]
  rw [e]
  exact xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ7.d4Root_dict.1 (c : X)

theorem bridge_coe_slLong_lower (P : D4Par n X σ) (c : fixSubfield σ) :
    (((CFSG.LieType.Steinberg.TwistedD4.slLong σ.toRingHom P.sigma_cube_hom
        (CFSG.LieType.Steinberg.sl2Lower c) :
        CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) :
          adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
            ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) =
      yUnit TwistTag.D4.tag X (CFSG.LieType.Steinberg.TwistedD4.nd 2) (c : X) := by
  rw [CFSG.LieType.Steinberg.TwistedD4.slLong_val,
    CFSG.LieType.Steinberg.TwistedD4.slLongE_lower]
  have e : CFSG.LieType.Steinberg.Adjoint.xPar
      (rootOperatorFamily CFSG.LieType.Steinberg.TwistedD4.d4)
      (-Pi.single (CFSG.LieType.Steinberg.TwistedD4.nd 2) 1) (c : X) =
      CFSG.RankThree.PartOne.SEITZ7.xd 8 (c : X) := by
    simp only [CFSG.RankThree.PartOne.SEITZ7.xd,
      CFSG.RankThree.PartOne.SEITZ7.d4Root_dict.2.1]
  rw [e]
  exact xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ7.d4Root_dict.2.1 (c : X)

theorem bridge_long_hom (P : D4Par n X σ) (hK : ringChar X = 2) :
    (KFacts.trialityG2Incl σ hK).comp (g2RootSL2 g2l (fixSubfield σ)) =
      (eC P).symm.toMonoidHom.comp
        (CFSG.LieType.Steinberg.TwistedD4.slLong σ.toRingHom P.sigma_cube_hom) := by
  refine MonoidHom.eq_of_eqOn_dense
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixSubfield σ)) ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · apply Subtype.ext
    show ((KFacts.trialityG2Incl σ hK (g2RootSL2 g2l (fixSubfield σ)
        (CFSG.LieType.Steinberg.sl2Upper c)) : C0 σ) : ModGL TwistTag.D4.tag X) =
      (((eC P).symm (CFSG.LieType.Steinberg.TwistedD4.slLong σ.toRingHom P.sigma_cube_hom
        (CFSG.LieType.Steinberg.sl2Upper c)) : C0 σ) : ModGL TwistTag.D4.tag X)
    rw [bridge_coe_incl_upper σ hK g2l c, bridge_g2OrbitXUnit_long, bridge_coe_eC_symm σ P,
      bridge_coe_slLong_upper σ P c]
  · apply Subtype.ext
    show ((KFacts.trialityG2Incl σ hK (g2RootSL2 g2l (fixSubfield σ)
        (CFSG.LieType.Steinberg.sl2Lower c)) : C0 σ) : ModGL TwistTag.D4.tag X) =
      (((eC P).symm (CFSG.LieType.Steinberg.TwistedD4.slLong σ.toRingHom P.sigma_cube_hom
        (CFSG.LieType.Steinberg.sl2Lower c)) : C0 σ) : ModGL TwistTag.D4.tag X)
    rw [bridge_coe_incl_lower σ hK g2l c, bridge_g2OrbitYUnit_long, bridge_coe_eC_symm σ P,
      bridge_coe_slLong_lower σ P c]

theorem bridge_length_w :
    (coxeterSystem Tag.G2).length (simple Tag.G2 g2s * simple Tag.G2 g2l) =
      (coxeterSystem Tag.G2).length (simple Tag.G2 g2l) + 1 := by
  rcases (coxeterSystem Tag.G2).length_simple_mul (simple Tag.G2 g2l) g2s with h | h
  · exact h
  · exfalso
    have h1 : (coxeterSystem Tag.G2).length (simple Tag.G2 g2l) = 1 :=
      (coxeterSystem Tag.G2).length_simple g2l
    have h0 : (coxeterSystem Tag.G2).length
        ((coxeterSystem Tag.G2).simple g2s * simple Tag.G2 g2l) = 0 := by
      omega
    have h3 : simple Tag.G2 g2s * simple Tag.G2 g2l = 1 :=
      (coxeterSystem Tag.G2).length_eq_zero_iff.1 h0
    have h4 := g2_w_smul_e0
    rw [h3, one_smul] at h4
    have h5 := congrFun h4 g2l
    revert h5
    decide

theorem bridge_g2WeylRep_eq (K : Type) [Field K] :
    g2WeylRep K = g2RootSL2 g2s K WSL * g2RootSL2 g2l K WSL := by
  apply Subtype.ext
  show canonicalRep (coxeterSystem Tag.G2) K (simple Tag.G2 g2s * simple Tag.G2 g2l) =
    simpleRootSL2 Tag.G2 K g2s WSL * simpleRootSL2 Tag.G2 K g2l WSL
  rw [simpleRootSL2_WSL, simpleRootSL2_WSL]
  rw [← weylElt_mul_canonicalRep_of_length_eq (cs := coxeterSystem Tag.G2) (R := K)
    (i := g2s) (w := simple Tag.G2 g2l) bridge_length_w, canonicalRep_simple]

theorem bridge_WSL_mul_self {F : Type} [Field F] (h2 : (2 : F) = 0) :
    (WSL : Matrix.SpecialLinearGroup (Fin 2) F) * WSL = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination -h2 | linear_combination h2

theorem bridge_WSL_eq {F : Type} [Field F] :
    (WSL : Matrix.SpecialLinearGroup (Fin 2) F) =
      CFSG.LieType.Steinberg.sl2Upper (1 : F) * CFSG.LieType.Steinberg.sl2Lower (-1 : F) *
        CFSG.LieType.Steinberg.sl2Upper (1 : F) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_WSL, CFSG.LieType.Steinberg.coe_sl2Upper, CFSG.LieType.Steinberg.coe_sl2Lower,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem bridge_g2WeylRep_inv (K : Type) [Field K] (h2 : (2 : K) = 0) :
    (g2WeylRep K)⁻¹ = g2RootSL2 g2l K WSL * g2RootSL2 g2s K WSL := by
  have hW : (WSL : Matrix.SpecialLinearGroup (Fin 2) K)⁻¹ = WSL :=
    inv_eq_of_mul_eq_one_right (bridge_WSL_mul_self h2)
  rw [bridge_g2WeylRep_eq, mul_inv_rev, ← map_inv, ← map_inv, hW]

theorem bridge_slLong_WSL (σ' : X →+* X) (hσ : ∀ c, σ' (σ' (σ' c)) = c) :
    CFSG.LieType.Steinberg.TwistedD4.slLong σ' hσ
        (WSL : Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.TwistedD4.fixedField σ')) =
      CFSG.LieType.Steinberg.TwistedD4.nHat σ' (CFSG.LieType.Steinberg.TwistedD4.ng 0) := by
  apply Subtype.ext
  rw [bridge_WSL_eq]
  simp only [map_mul, Subgroup.coe_mul]
  rw [CFSG.LieType.Steinberg.TwistedD4.slLong_val, CFSG.LieType.Steinberg.TwistedD4.slLong_val,
    CFSG.LieType.Steinberg.TwistedD4.slLongE_upper,
    CFSG.LieType.Steinberg.TwistedD4.slLongE_lower, CFSG.LieType.Steinberg.TwistedD4.nHat_val,
    CFSG.LieType.Steinberg.TwistedD4.nHatE_zero_eq]
  simp

theorem bridge_slShort_WSL (σ' : X →+* X) (hσ : ∀ c, σ' (σ' (σ' c)) = c) :
    CFSG.LieType.Steinberg.TwistedD4.slShort σ' hσ (WSL : Matrix.SpecialLinearGroup (Fin 2) X) =
      CFSG.LieType.Steinberg.TwistedD4.nHat σ' (CFSG.LieType.Steinberg.TwistedD4.ng 1) := by
  have h1 : σ' (1 : X) = 1 := map_one σ'
  have h2 : σ' (-1 : X) = -1 := by rw [map_neg, map_one]
  apply Subtype.ext
  rw [bridge_WSL_eq]
  simp only [map_mul, Subgroup.coe_mul]
  rw [CFSG.LieType.Steinberg.TwistedD4.slShort_upper, CFSG.LieType.Steinberg.TwistedD4.slShort_lower,
    CFSG.LieType.Steinberg.TwistedD4.nHat_val, CFSG.LieType.Steinberg.TwistedD4.nHatE_one_eq]
  simp only [h1, h2]

theorem bridge_map_WSL {k F : Type} [Field k] [Field F] (f : k →+* F) :
    Matrix.SpecialLinearGroup.map f (WSL : Matrix.SpecialLinearGroup (Fin 2) k) = WSL := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_WSL, Matrix.SpecialLinearGroup.map_apply_coe]

theorem bridge_incl_weylInv (P : D4Par n X σ) (hK : ringChar X = 2) :
    KFacts.trialityG2Incl σ hK (g2WeylRep (fixSubfield σ))⁻¹ =
      (eC P).symm (CFSG.RankThree.PartOne.SEITZ7.Wg σ.toRingHom) := by
  have h2 : (2 : fixSubfield σ) = 0 := two_eq_zero_fixSubfield σ hK
  rw [bridge_g2WeylRep_inv _ h2, map_mul]
  have hl := DFunLike.congr_fun (bridge_long_hom σ P hK) WSL
  have hs := DFunLike.congr_fun (g2RootSL2_short_hom_eq σ P hK) WSL
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hl hs
  rw [hl, hs, bridge_map_WSL]
  have e1 := bridge_slLong_WSL σ.toRingHom P.sigma_cube_hom
  have e2 := bridge_slShort_WSL σ.toRingHom P.sigma_cube_hom
  show (eC P).symm (CFSG.LieType.Steinberg.TwistedD4.slLong σ.toRingHom P.sigma_cube_hom WSL) *
      (eC P).symm (CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom P.sigma_cube_hom WSL) = _
  rw [e1, e2, ← map_mul]
  rfl

theorem g2RootSL2_long_conj_hom_eq_bridge (P : D4Par n X σ) (hK : ringChar X = 2) :
    (KFacts.trialityG2Incl σ hK).comp
      ((MulAut.conj (g2WeylRep (fixSubfield σ))⁻¹).toMonoidHom.comp
        (g2RootSL2 g2l (fixSubfield σ))) = etaB P := by
  refine MonoidHom.ext fun M => ?_
  have hl := DFunLike.congr_fun (bridge_long_hom σ P hK) M
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hl
  set A := KFacts.trialityG2Incl σ hK with hA
  set nn := g2WeylRep (fixSubfield σ) with hnn
  have hconj : A (MulAut.conj nn⁻¹ (g2RootSL2 g2l (fixSubfield σ) M)) =
      A nn⁻¹ * A (g2RootSL2 g2l (fixSubfield σ) M) * (A nn⁻¹)⁻¹ := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv A nn⁻¹]
  show A (MulAut.conj nn⁻¹ (g2RootSL2 g2l (fixSubfield σ) M)) = etaB P M
  rw [hconj, hA, bridge_incl_weylInv σ P hK, ← hA, hl]
  show _ = (eC P).symm (CFSG.RankThree.PartOne.SEITZ7.psiB σ.toRingHom P.sigma_cube_hom M)
  have hpsi : CFSG.RankThree.PartOne.SEITZ7.psiB σ.toRingHom P.sigma_cube_hom M =
      CFSG.RankThree.PartOne.SEITZ7.Wg σ.toRingHom *
        CFSG.LieType.Steinberg.TwistedD4.slLong σ.toRingHom P.sigma_cube_hom M *
          (CFSG.RankThree.PartOne.SEITZ7.Wg σ.toRingHom)⁻¹ := rfl
  rw [hpsi, map_mul, map_mul, map_inv]

theorem g2RootSL2_long_conj_upper_incl (P : D4Par n X σ) (hK : ringChar X = 2)
    (c : fixSubfield σ) :
    KFacts.trialityG2Incl σ hK (MulAut.conj (g2WeylRep (fixSubfield σ))⁻¹
      (g2RootSL2 g2l (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Upper c))) =
      etaB P (CFSG.LieType.Steinberg.sl2Upper c) :=
  DFunLike.congr_fun (g2RootSL2_long_conj_hom_eq_bridge σ P hK)
    (CFSG.LieType.Steinberg.sl2Upper c)

theorem g2RootSL2_long_conj_lower_incl (P : D4Par n X σ) (hK : ringChar X = 2)
    (c : fixSubfield σ) :
    KFacts.trialityG2Incl σ hK (MulAut.conj (g2WeylRep (fixSubfield σ))⁻¹
      (g2RootSL2 g2l (fixSubfield σ) (CFSG.LieType.Steinberg.sl2Lower c))) =
      etaB P (CFSG.LieType.Steinberg.sl2Lower c) :=
  DFunLike.congr_fun (g2RootSL2_long_conj_hom_eq_bridge σ P hK)
    (CFSG.LieType.Steinberg.sl2Lower c)

theorem g2RootSL2_long_conj_hom_eq (P : D4Par n X σ) (hK : ringChar X = 2) :
    (KFacts.trialityG2Incl σ hK).comp
      ((MulAut.conj (g2WeylRep (fixSubfield σ))⁻¹).toMonoidHom.comp
        (g2RootSL2 g2l (fixSubfield σ))) = etaB P := by
  refine MonoidHom.eq_of_eqOn_dense
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixSubfield σ)) ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact g2RootSL2_long_conj_upper_incl σ P hK c
  · exact g2RootSL2_long_conj_lower_incl σ P hK c

theorem g2RootSL2_long_conj_le_B (P : D4Par n X σ) (hK : ringChar X = 2)
    (x : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) :
    KFacts.trialityG2Incl σ hK
      (MulAut.conj (g2WeylRep (fixSubfield σ))⁻¹ (g2RootSL2 g2l (fixSubfield σ) x)) ∈ Bsub σ := by
  rw [Bsub_eq_range_etaB P]
  exact MonoidHom.mem_range.2 ⟨x, (DFunLike.congr_fun (g2RootSL2_long_conj_hom_eq σ P hK) x).symm⟩

end Aux

end CFSG.RankThree.PartTwo.Sec19
