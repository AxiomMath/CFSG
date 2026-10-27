module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeIso
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264D4EightCaseB
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.ClassicalGroups.Orthogonal.RootGroupPair
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAbstract
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadEigen
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslSplit
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz9

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.SeitzReduction
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.GGFinModel CFSG.StandardType.S2MathFi1035Pos
open CFSG.LieType.Steinberg.TwistedD4 (nd ng d4 proj rho rhoPerm)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz

theorem rckTriD4_map_subtype_rootGroup {τ : Tag} {K : Type} [Field K]
    (F : RootOperatorFamily τ) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    (rootGroup F K δ).map (adjointGroup τ K).subtype = rootSubgroup τ K δ := by
  rw [rootGroup_of_isRoot hδ, ← F.subgroupOf_rootSubgroup_eq K ⟨δ, hδ⟩,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (rootSubgroup_le_adjointGroup δ)]

@[expose] noncomputable def rckTriD4_iotaD4 {F : Type} [Field F] [Algebra F GGL]
    (σ : F →+* F) : ↥(twistedGroup σ) →* ModGL d4 GGL :=
  (baseChangeGL (algebraMap F GGL)).comp
    ((adjointGroup d4 F).subtype.comp (twistedGroup σ).subtype)

@[expose] noncomputable def rckTriD4_psi (h r : ℕ) : ModGL d4 GGL →* ModGL d4 GGL :=
  (MulAut.conj ((diagramMap TwistTag.D4 GGL) ^ r)).toMonoidHom.comp
    (Units.map (entrywiseHom (iterateFrobenius GGL 2 h)))

theorem rckTriD4_psi_apply (h r : ℕ) (g : ModGL d4 GGL) :
    rckTriD4_psi h r g = (diagramMap TwistTag.D4 GGL) ^ r *
      (Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) g) *
      ((diagramMap TwistTag.D4 GGL) ^ r)⁻¹ := by
  change MulAut.conj ((diagramMap TwistTag.D4 GGL) ^ r)
      ((Units.map (entrywiseHom (iterateFrobenius GGL 2 h))) g) = _
  rw [MulAut.conj_apply]

theorem rckTriD4_psi_fixed_xPar_pos (h : ℕ) (c : GGL) :
    rckTriD4_psi h 1
      (((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c :
        adjointGroup d4 GGL)) : ModGL d4 GGL) =
      (((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1)
        (iterateFrobenius GGL 2 h c) : adjointGroup d4 GGL)) : ModGL d4 GGL) := by
  rw [rckTriD4_psi_apply, pow_one]
  change twistHom TwistTag.D4 GGL (iterateFrobenius GGL 2 h)
      (((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c :
        adjointGroup d4 GGL)) : ModGL d4 GGL) = _
  rw [← coe_twistC]
  rw [twistC_xPar_single (σ := iterateFrobenius GGL 2 h) (i := nd 2) (c := c), rhoPerm_two]

theorem rckTriD4_psi_fixed_xPar_neg (h : ℕ) (c : GGL) :
    rckTriD4_psi h 1
      (((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) c :
        adjointGroup d4 GGL)) : ModGL d4 GGL) =
      (((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1)
        (iterateFrobenius GGL 2 h c) : adjointGroup d4 GGL)) : ModGL d4 GGL) := by
  rw [rckTriD4_psi_apply, pow_one]
  change twistHom TwistTag.D4 GGL (iterateFrobenius GGL 2 h)
      (((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) c :
        adjointGroup d4 GGL)) : ModGL d4 GGL) = _
  rw [← coe_twistC]
  rw [twistC_xPar_neg_single (σ := iterateFrobenius GGL 2 h) (i := nd 2) (c := c),
    rhoPerm_two]

theorem rckTriD4_baseChange_xPar {K L : Type} [Field K] [Field L] (f : K →+* L)
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (c : K) :
    baseChangeGL f (((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K)) : ModGL d4 K) =
      (((xPar (rootOperatorFamily d4) γ (f c) : adjointGroup d4 L)) : ModGL d4 L) := by
  let sK : K := ((rootOperatorFamily d4).pinnedFamilySign γ : K)
  let sL : L := ((rootOperatorFamily d4).pinnedFamilySign γ : L)
  have hsK : sK * sK = 1 := by
    simpa [sK] using (rootOperatorFamily d4).pinnedFamilySign_mul_self K γ
  have hsL : sL * sL = 1 := by
    simpa [sL] using (rootOperatorFamily d4).pinnedFamilySign_mul_self L γ
  have hf : f sK = sL := by simp [sK, sL]
  have hK : ((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K) : ModGL d4 K) =
      pinnedX d4 K γ (sK * c) := by
    rw [xPar_of_isRoot hγ]
    change (rootOperatorFamily d4).eltUnit K ⟨γ, hγ⟩ c = pinnedX d4 K γ (sK * c)
    have harg : sK * (sK * c) = c := by rw [← mul_assoc, hsK, one_mul]
    calc (rootOperatorFamily d4).eltUnit K ⟨γ, hγ⟩ c
        = (rootOperatorFamily d4).eltUnit K ⟨γ, hγ⟩ (sK * (sK * c)) := by rw [harg]
      _ = pinnedX d4 K γ (sK * c) :=
          ((rootOperatorFamily d4).pinnedX_eq_eltUnit K hγ (sK * c)).symm
  have hL : ((xPar (rootOperatorFamily d4) γ (f c) : adjointGroup d4 L) : ModGL d4 L) =
      pinnedX d4 L γ (sL * f c) := by
    rw [xPar_of_isRoot hγ]
    change (rootOperatorFamily d4).eltUnit L ⟨γ, hγ⟩ (f c) = pinnedX d4 L γ (sL * f c)
    have harg : sL * (sL * f c) = f c := by rw [← mul_assoc, hsL, one_mul]
    calc (rootOperatorFamily d4).eltUnit L ⟨γ, hγ⟩ (f c)
        = (rootOperatorFamily d4).eltUnit L ⟨γ, hγ⟩ (sL * (sL * f c)) := by rw [harg]
      _ = pinnedX d4 L γ (sL * f c) :=
          ((rootOperatorFamily d4).pinnedX_eq_eltUnit L hγ (sL * f c)).symm
  rw [hK, hL, baseChangeGL_pinnedX, map_mul, hf]

theorem rckTriD4_conj_pow_fixed (r : ℕ) {x : ModGL d4 GGL}
    (hx : (diagramMap TwistTag.D4 GGL) * x * (diagramMap TwistTag.D4 GGL)⁻¹ = x) :
    (diagramMap TwistTag.D4 GGL) ^ r * x * ((diagramMap TwistTag.D4 GGL) ^ r)⁻¹ = x := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ]
      calc (diagramMap TwistTag.D4 GGL) ^ r * diagramMap TwistTag.D4 GGL * x *
            ((diagramMap TwistTag.D4 GGL) ^ r * diagramMap TwistTag.D4 GGL)⁻¹
          = (diagramMap TwistTag.D4 GGL) ^ r *
            ((diagramMap TwistTag.D4 GGL) * x * (diagramMap TwistTag.D4 GGL)⁻¹) *
            ((diagramMap TwistTag.D4 GGL) ^ r)⁻¹ := by group
        _ = (diagramMap TwistTag.D4 GGL) ^ r * x *
            ((diagramMap TwistTag.D4 GGL) ^ r)⁻¹ := by rw [hx]
        _ = x := ih

theorem rckTriD4_xPar_single_modGL (c : GGL) :
    ((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c : adjointGroup d4 GGL) :
      ModGL d4 GGL) = xUnit d4 GGL (nd 2) c := by
  apply Units.ext
  rw [xPar_of_isRoot (isRoot_single d4 (nd 2)), RootOperatorFamily.coe_eltElement]
  exact congrArg Units.val ((rootOperatorFamily d4).eltUnit_simple (nd 2) c)

theorem rckTriD4_xPar_neg_modGL (c : GGL) :
    ((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) c : adjointGroup d4 GGL) :
      ModGL d4 GGL) = yUnit d4 GGL (nd 2) c := by
  apply Units.ext
  rw [xPar_of_isRoot (isRoot_neg_single d4 (nd 2)), RootOperatorFamily.coe_eltElement]
  exact congrArg Units.val ((rootOperatorFamily d4).eltUnit_neg_simple (nd 2) c)

theorem rckTriD4_range_one {F : Type} [Field F] [Finite F] [Algebra F GGL]
    (σ : F →+* F) {h : ℕ} (hh : 1 ≤ h) (hTri : TriField F σ h) :
    (rckTriD4_iotaD4 (F := F) σ).range =
      adjointGroup d4 GGL ⊓ (rckTriD4_psi h 1).eqLocus (MonoidHom.id _) := by
  classical
  have hcard : Nat.card F = (2 ^ h) ^ 3 := hTri.2.1
  have hσ : ∀ c : F, σ c = c ^ (2 ^ h) := hTri.2.2
  let Fr : GGL →+* GGL := iterateFrobenius GGL 2 h
  have hFr : ∀ c : GGL, Fr c = c ^ (2 ^ h) := fun c => iterateFrobenius_def 2 h c
  let S : Set (ModGL TwistTag.D4.tag GGL) :=
    {g | g ∈ adjointGroup TwistTag.D4.tag GGL ∧
      diagramMap TwistTag.D4 GGL ^ 1 * Units.map (entrywiseHom Fr) g *
        (diagramMap TwistTag.D4 GGL ^ 1)⁻¹ = g}
  have hfix : S = ((graphFixedRootGroup TwistTag.D4 F σ).map
      (baseChangeGL (algebraMap F GGL)) : Set (ModGL TwistTag.D4.tag GGL)) :=
    fixedSet_D4_eq_map_baseChangeGL (ℓ := 2) (d := h) (by norm_num) hh
      (K := F) hcard (Ω := GGL) 1 (Or.inl rfl) σ (fun c => by simpa using hσ c) Fr hFr
  let br := CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4BridgeEquiv σ hh hcard hσ
  have hrange : ∀ x : ModGL d4 GGL,
      x ∈ (rckTriD4_iotaD4 (F := F) σ).range ↔
      x ∈ (graphFixedRootGroup TwistTag.D4 F σ).map
        (baseChangeGL (algebraMap F GGL)) := by
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨br g, (br g).2, ?_⟩
      show (baseChangeGL (algebraMap F GGL)) ((br g : graphFixedRootGroup TwistTag.D4 F σ) :
          ModGL TwistTag.D4.tag F) = (rckTriD4_iotaD4 (F := F) σ) g
      rw [CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4BridgeEquiv_coe]
      rfl
    · rintro ⟨c, hc, rfl⟩
      let g : ↥(twistedGroup σ) := br.symm ⟨c, hc⟩
      refine ⟨g, ?_⟩
      show (rckTriD4_iotaD4 (F := F) σ) g = (baseChangeGL (algebraMap F GGL)) c
      have hg : (br g : ModGL TwistTag.D4.tag F) = c := by
        have hg' : br g = ⟨c, hc⟩ := br.apply_symm_apply ⟨c, hc⟩
        rw [hg']
      show (baseChangeGL (algebraMap F GGL)) ((g : adjointGroup d4 F) : ModGL TwistTag.D4.tag F) =
        (baseChangeGL (algebraMap F GGL)) c
      rw [show ((g : adjointGroup d4 F) : ModGL TwistTag.D4.tag F) =
        ((br g : graphFixedRootGroup TwistTag.D4 F σ) : ModGL TwistTag.D4.tag F) from
        (CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4BridgeEquiv_coe σ hh hcard hσ g).symm]
      rw [hg]
  have hfixmem : ∀ x : ModGL d4 GGL,
      x ∈ (graphFixedRootGroup TwistTag.D4 F σ).map
        (baseChangeGL (algebraMap F GGL)) ↔
      x ∈ adjointGroup d4 GGL ∧ rckTriD4_psi h 1 x = x := by
    intro x
    constructor
    · intro hx
      have hmem : x ∈ S := by rw [hfix]; exact hx
      refine ⟨hmem.1, ?_⟩
      rw [rckTriD4_psi_apply, pow_one]
      exact hmem.2
    · rintro ⟨hxadj, hxfix⟩
      have hxfix' : (diagramMap TwistTag.D4 GGL) ^ 1 *
          (Units.map (entrywiseHom Fr) x) * ((diagramMap TwistTag.D4 GGL) ^ 1)⁻¹ = x := by
        rw [rckTriD4_psi_apply, pow_one] at hxfix
        exact hxfix
      have hmem : x ∈ S := ⟨hxadj, hxfix'⟩
      rwa [hfix] at hmem
  ext x
  rw [hrange x, hfixmem x]
  rfl

theorem rckTriD4_pow_three (h : ℕ) (d : GGL)
    (hd : iterateFrobenius GGL 2 h d = d) : d ^ 2 ^ (3 * h) = d := by
  have hdh : d ^ 2 ^ h = d := by
    rw [← iterateFrobenius_def (R := GGL) (p := 2) (n := h) d, hd]
  calc d ^ 2 ^ (3 * h) = (d ^ 2 ^ h) ^ 2 ^ (2 * h) := by
        rw [← pow_mul]
        congr 1
        rw [← pow_add]
        congr 1
        ring
    _ = d ^ 2 ^ (2 * h) := by rw [hdh]
    _ = (d ^ 2 ^ h) ^ 2 ^ h := by
        rw [← pow_mul]
        congr 1
        rw [show 2 * h = h + h by ring, pow_add]
    _ = d := by rw [hdh, hdh]

theorem rckTriD4_mem_map_twistedRootSubgroupD4_of (F : Subfield GGL) [Finite ↥F] {h : ℕ}
    (hFcard : Nat.card ↥F = (2 ^ h) ^ 3)
    (hFmem : ∀ c : GGL, c ∈ F ↔ c ^ 2 ^ (3 * h) = c)
    {α : Fin d4.rank → ℤ} {β : Fin (Tag.rank .G2) → ℤ}
    (hα : IsRoot d4 α) (hp : proj α = β) (hfix : rho α = α)
    (hpsi : ∀ c : GGL, rckTriD4_psi h 1
      (((xPar (rootOperatorFamily d4) α c : adjointGroup d4 GGL)) : ModGL d4 GGL) =
      (((xPar (rootOperatorFamily d4) α (iterateFrobenius GGL 2 h c) :
        adjointGroup d4 GGL)) : ModGL d4 GGL)) :
    ∀ x : ModGL d4 GGL,
      x ∈ (twistedRootSubgroupD4 (iterateFrobenius ↥F 2 h) β).map
        ((baseChangeGL (algebraMap ↥F GGL)).comp (adjointGroup d4 ↥F).subtype) ↔
      x ∈ rootSubgroup d4 GGL α ⊓ (rckTriD4_psi h 1).eqLocus (MonoidHom.id _) := by
  intro x
  let σ : ↥F →+* ↥F := iterateFrobenius ↥F 2 h
  have hσ3 : ∀ c, σ (σ (σ c)) = c :=
    sigma_three_of_card (σ := σ) hFcard (fun c => iterateFrobenius_def 2 h c)
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨c, hc, rfl⟩ :=
      (mem_twistedRootSubgroupD4_iff_of_fixed hσ3 hα hp hfix u).1 hu
    rw [MonoidHom.comp_apply]
    change baseChangeGL (algebraMap ↥F GGL)
      (((xPar (rootOperatorFamily d4) α c : adjointGroup d4 ↥F)) : ModGL d4 ↥F) ∈
      rootSubgroup d4 GGL α ⊓ (rckTriD4_psi h 1).eqLocus (MonoidHom.id _)
    rw [rckTriD4_baseChange_xPar (f := algebraMap ↥F GGL) hα c]
    refine ⟨?_, ?_⟩
    · rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hα]
      exact Subgroup.mem_map_of_mem _ (xPar_mem hα ((algebraMap ↥F GGL) c))
    · change rckTriD4_psi h 1
        (((xPar (rootOperatorFamily d4) α ((algebraMap ↥F GGL) c) :
          adjointGroup d4 GGL)) : ModGL d4 GGL) = _
      rw [hpsi]
      have hc' : iterateFrobenius GGL 2 h ((algebraMap ↥F GGL) c) = (algebraMap ↥F GGL) c := by
        have hpow : c ^ 2 ^ h = c := by
          rw [← iterateFrobenius_def (R := ↥F) (p := 2) (n := h) c]
          exact hc
        rw [iterateFrobenius_def, ← map_pow, hpow]
      rw [hc']
      rfl
  · rintro ⟨hxroot, hxfix⟩
    rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hα] at hxroot
    obtain ⟨u, hu, rfl⟩ := hxroot
    obtain ⟨d, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily d4) hα u).1 hu
    have hFrd : iterateFrobenius GGL 2 h d = d := by
      have h1 : rckTriD4_psi h 1
          (((xPar (rootOperatorFamily d4) α d : adjointGroup d4 GGL)) :
            ModGL d4 GGL) =
          (((xPar (rootOperatorFamily d4) α d : adjointGroup d4 GGL)) :
            ModGL d4 GGL) := hxfix
      rw [hpsi] at h1
      exact xPar_injective hα (Subtype.ext h1)
    have hdF : d ∈ F := by
      rw [hFmem]
      exact rckTriD4_pow_three h d hFrd
    let c : ↥F := ⟨d, hdF⟩
    have hcd : (c : GGL) = d := rfl
    have hσc : σ c = c := by
      apply Subtype.ext
      change (algebraMap ↥F GGL) (σ c) = (algebraMap ↥F GGL) c
      have hmap : (algebraMap ↥F GGL) (σ c) =
          iterateFrobenius GGL 2 h ((algebraMap ↥F GGL) c) := by
        rw [iterateFrobenius_def, iterateFrobenius_def, map_pow]
      rw [hmap]
      simpa only [show (algebraMap ↥F GGL) c = d from hcd] using hFrd
    refine ⟨((xPar (rootOperatorFamily d4) α c : adjointGroup d4 ↥F)), ?_, ?_⟩
    · exact (mem_twistedRootSubgroupD4_iff_of_fixed hσ3 hα hp hfix _).2 ⟨c, hσc, rfl⟩
    · rw [MonoidHom.comp_apply]
      change baseChangeGL (algebraMap ↥F GGL)
        (((xPar (rootOperatorFamily d4) α c : adjointGroup d4 ↥F)) : ModGL d4 ↥F) =
        (((xPar (rootOperatorFamily d4) α d : adjointGroup d4 GGL)) : ModGL d4 GGL)
      rw [rckTriD4_baseChange_xPar (f := algebraMap ↥F GGL) hα c]
      exact congrArg (fun e => (((xPar (rootOperatorFamily d4) α e :
        adjointGroup d4 GGL)) : ModGL d4 GGL)) hcd

theorem rckTriD4_rootGroup_one_of (F : Subfield GGL) [Finite ↥F] {h : ℕ}
    (hFcard : Nat.card ↥F = (2 ^ h) ^ 3)
    (hFmem : ∀ c : GGL, c ∈ F ↔ c ^ 2 ^ (3 * h) = c)
    {α : Fin d4.rank → ℤ} {β : Fin (Tag.rank .G2) → ℤ}
    (hα : IsRoot d4 α) (hβ : IsRoot .G2 β) (hp : proj α = β) (hfix : rho α = α)
    (hpsi : ∀ c : GGL, rckTriD4_psi h 1
      (((xPar (rootOperatorFamily d4) α c : adjointGroup d4 GGL)) : ModGL d4 GGL) =
      (((xPar (rootOperatorFamily d4) α (iterateFrobenius GGL 2 h c) :
        adjointGroup d4 GGL)) : ModGL d4 GGL)) :
    ((twistedDatum (iterateFrobenius ↥F 2 h)).rootGroup β).map
        (rckTriD4_iotaD4 (F := ↥F) (iterateFrobenius ↥F 2 h)) =
      rootSubgroup d4 GGL α ⊓ (rckTriD4_psi h 1).eqLocus (MonoidHom.id _) := by
  classical
  let σ : ↥F →+* ↥F := iterateFrobenius ↥F 2 h
  have hL : (twistedRootGroup σ β).map (rckTriD4_iotaD4 (F := ↥F) σ) =
      (twistedRootSubgroupD4 σ β).map
        ((baseChangeGL (algebraMap ↥F GGL)).comp (adjointGroup d4 ↥F).subtype) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨((y : twistedGroup σ) : adjointGroup d4 ↥F),
        Subgroup.mem_subgroupOf.mp hy, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      let y : ↥(twistedGroup σ) := ⟨u, twistedRootSubgroupD4_le_twistedGroup σ hβ hu⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  change (twistedRootGroup σ β).map (rckTriD4_iotaD4 (F := ↥F) σ) = _
  rw [hL]
  ext x
  exact rckTriD4_mem_map_twistedRootSubgroupD4_of F hFcard hFmem hα hp hfix hpsi x

theorem rckTriD4_rootGroup_one_pos (F : Subfield GGL) [Finite ↥F] {h : ℕ}
    (hFcard : Nat.card ↥F = (2 ^ h) ^ 3)
    (hFmem : ∀ c : GGL, c ∈ F ↔ c ^ 2 ^ (3 * h) = c) :
    ((twistedDatum (iterateFrobenius ↥F 2 h)).rootGroup (Pi.single (ng 0) 1)).map
        (rckTriD4_iotaD4 (F := ↥F) (iterateFrobenius ↥F 2 h)) =
      rootSubgroup d4 GGL (Pi.single (nd 2) 1) ⊓
        (rckTriD4_psi h 1).eqLocus (MonoidHom.id _) :=
  rckTriD4_rootGroup_one_of F hFcard hFmem (isRoot_single d4 (nd 2))
    (isRoot_single .G2 (ng 0)) proj_single_two rho_single_two
    fun c => rckTriD4_psi_fixed_xPar_pos h c

theorem rckTriD4_rootGroup_one_neg (F : Subfield GGL) [Finite ↥F] {h : ℕ}
    (hFcard : Nat.card ↥F = (2 ^ h) ^ 3)
    (hFmem : ∀ c : GGL, c ∈ F ↔ c ^ 2 ^ (3 * h) = c) :
    ((twistedDatum (iterateFrobenius ↥F 2 h)).rootGroup (-Pi.single (ng 0) 1)).map
        (rckTriD4_iotaD4 (F := ↥F) (iterateFrobenius ↥F 2 h)) =
      rootSubgroup d4 GGL (-Pi.single (nd 2) 1) ⊓
        (rckTriD4_psi h 1).eqLocus (MonoidHom.id _) :=
  rckTriD4_rootGroup_one_of F hFcard hFmem (isRoot_neg_single d4 (nd 2))
    (isRoot_neg_single .G2 (ng 0)) proj_neg_single_two rho_neg_single_two
    (fun c => rckTriD4_psi_fixed_xPar_neg h c)

theorem rckTriD4_stable_of_P_fix (h r : ℕ) {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ)
    (hP : ∀ c : GGL, (diagramMap TwistTag.D4 GGL) *
      (((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 GGL)) : ModGL d4 GGL) *
      (diagramMap TwistTag.D4 GGL)⁻¹ =
      (((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 GGL)) : ModGL d4 GGL)) :
    (rootSubgroup d4 GGL γ).map (rckTriD4_psi h r) = rootSubgroup d4 GGL γ := by
  classical
  have hpsi : ∀ c : GGL, rckTriD4_psi h r
      (((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 GGL)) : ModGL d4 GGL) =
      (((xPar (rootOperatorFamily d4) γ (iterateFrobenius GGL 2 h c) :
        adjointGroup d4 GGL)) : ModGL d4 GGL) := by
    intro c
    rw [rckTriD4_psi_apply, units_map_entrywiseHom_eq_baseChangeGL,
      rckTriD4_baseChange_xPar (f := iterateFrobenius GGL 2 h) hγ c]
    exact rckTriD4_conj_pow_fixed r (hP _)
  have hFrsurj : Function.Surjective (iterateFrobenius GGL 2 h) := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (by norm_num : 0 < 2) h)
    exact ⟨x, by rw [iterateFrobenius_def, hx]⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily d4) hγ u).1 hu
    change rckTriD4_psi h r
      (((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 GGL)) : ModGL d4 GGL) ∈
      rootSubgroup d4 GGL γ
    rw [hpsi c]
    rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ]
    exact Subgroup.mem_map_of_mem _ (xPar_mem hγ _)
  · intro hx
    rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily d4) hγ u).1 hu
    obtain ⟨d, hd⟩ := hFrsurj c
    refine ⟨(((xPar (rootOperatorFamily d4) γ d : adjointGroup d4 GGL)) : ModGL d4 GGL), ?_, ?_⟩
    · rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ]
      exact Subgroup.mem_map_of_mem _ (xPar_mem hγ d)
    · change rckTriD4_psi h r
        (((xPar (rootOperatorFamily d4) γ d : adjointGroup d4 GGL)) : ModGL d4 GGL) =
        (((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 GGL)) : ModGL d4 GGL)
      rw [hpsi d, hd]

theorem rckTriD4_stable_pos (h r : ℕ) :
    (rootSubgroup d4 GGL (Pi.single (nd 2) 1)).map (rckTriD4_psi h r) =
      rootSubgroup d4 GGL (Pi.single (nd 2) 1) := by
  refine rckTriD4_stable_of_P_fix h r (isRoot_single d4 (nd 2)) fun c => ?_
  rw [rckTriD4_xPar_single_modGL c,
    diagramMap_mul_xUnit_mul_inv TwistTag.D4 GGL (nd 2) c, rhoPerm_two]

theorem rckTriD4_stable_neg (h r : ℕ) :
    (rootSubgroup d4 GGL (-Pi.single (nd 2) 1)).map (rckTriD4_psi h r) =
      rootSubgroup d4 GGL (-Pi.single (nd 2) 1) := by
  refine rckTriD4_stable_of_P_fix h r (isRoot_neg_single d4 (nd 2)) fun c => ?_
  rw [rckTriD4_xPar_neg_modGL c,
    diagramMap_mul_yUnit_mul_inv TwistTag.D4 GGL (nd 2) c, rhoPerm_two]

theorem rckTriD4_q_conj_xUnit_two (c : GGL) :
    d4SwapMap GGL * xUnit d4 GGL (nd 2) c * (d4SwapMap GGL)⁻¹ =
      xUnit d4 GGL (nd 2) c := by
  have hQ : d4SwapMap GGL = labelMap GGL d4Swap d4Swap_cartan := rfl
  rw [hQ]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, coe_xUnit]
  rw [labelMap_mul_xOp (K := GGL) (π := d4Swap) (hπ := d4Swap_cartan)]
  rw [show d4Swap (nd 2) = nd 2 from rfl, mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_one]

theorem rckTriD4_q_conj_yUnit_two (c : GGL) :
    d4SwapMap GGL * yUnit d4 GGL (nd 2) c * (d4SwapMap GGL)⁻¹ =
      yUnit d4 GGL (nd 2) c := by
  have hQ : d4SwapMap GGL = labelMap GGL d4Swap d4Swap_cartan := rfl
  rw [hQ]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, coe_yUnit]
  rw [labelMap_mul_yOp (K := GGL) (π := d4Swap) (hπ := d4Swap_cartan)]
  rw [show d4Swap (nd 2) = nd 2 from rfl, mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_one]

theorem rckTriD4_q_conj_xPar_two (c : GGL) :
    d4SwapMap GGL *
      (((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c : adjointGroup d4 GGL)) :
        ModGL d4 GGL) * (d4SwapMap GGL)⁻¹ =
      (((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c : adjointGroup d4 GGL)) :
        ModGL d4 GGL) := by
  rw [rckTriD4_xPar_single_modGL c]
  exact rckTriD4_q_conj_xUnit_two c

theorem rckTriD4_q_conj_neg_xPar_two (c : GGL) :
    d4SwapMap GGL *
      (((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) c : adjointGroup d4 GGL)) :
        ModGL d4 GGL) * (d4SwapMap GGL)⁻¹ =
      (((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) c : adjointGroup d4 GGL)) :
        ModGL d4 GGL) := by
  rw [rckTriD4_xPar_neg_modGL c]
  exact rckTriD4_q_conj_yUnit_two c

theorem rckTriD4_q_map_rootSubgroup_pos :
    (rootSubgroup d4 GGL (Pi.single (nd 2) 1)).map
        (MulAut.conj (d4SwapMap GGL)).toMonoidHom =
      rootSubgroup d4 GGL (Pi.single (nd 2) 1) := by
  let γ : Fin d4.rank → ℤ := Pi.single (nd 2) 1
  have hγ : IsRoot d4 γ := isRoot_single d4 (nd 2)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ] at hy ⊢
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily d4) hγ u).1 hu
    change d4SwapMap GGL *
      (((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c : adjointGroup d4 GGL)) :
        ModGL d4 GGL) * (d4SwapMap GGL)⁻¹ ∈ Subgroup.map (adjointGroup d4 GGL).subtype
        (rootGroup (rootOperatorFamily d4) GGL (Pi.single (nd 2) 1))
    rw [rckTriD4_q_conj_xPar_two c]
    exact Subgroup.mem_map_of_mem _ (xPar_mem hγ c)
  · intro hx
    rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily d4) hγ u).1 hu
    refine ⟨(((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 GGL)) : ModGL d4 GGL),
      ?_, ?_⟩
    · rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ]
      exact Subgroup.mem_map_of_mem _ (xPar_mem hγ c)
    · change d4SwapMap GGL *
        (((xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c : adjointGroup d4 GGL)) :
          ModGL d4 GGL) * (d4SwapMap GGL)⁻¹ = _
      rw [rckTriD4_q_conj_xPar_two c]
      rfl

theorem rckTriD4_q_map_rootSubgroup_neg :
    (rootSubgroup d4 GGL (-Pi.single (nd 2) 1)).map
        (MulAut.conj (d4SwapMap GGL)).toMonoidHom =
      rootSubgroup d4 GGL (-Pi.single (nd 2) 1) := by
  let γ : Fin d4.rank → ℤ := -Pi.single (nd 2) 1
  have hγ : IsRoot d4 γ := isRoot_neg_single d4 (nd 2)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ] at hy ⊢
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily d4) hγ u).1 hu
    change d4SwapMap GGL *
      (((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) c : adjointGroup d4 GGL)) :
        ModGL d4 GGL) * (d4SwapMap GGL)⁻¹ ∈ Subgroup.map (adjointGroup d4 GGL).subtype
        (rootGroup (rootOperatorFamily d4) GGL (-Pi.single (nd 2) 1))
    rw [rckTriD4_q_conj_neg_xPar_two c]
    exact Subgroup.mem_map_of_mem _ (xPar_mem hγ c)
  · intro hx
    rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily d4) hγ u).1 hu
    refine ⟨(((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 GGL)) : ModGL d4 GGL),
      ?_, ?_⟩
    · rw [← rckTriD4_map_subtype_rootGroup (rootOperatorFamily d4) (K := GGL) hγ]
      exact Subgroup.mem_map_of_mem _ (xPar_mem hγ c)
    · change d4SwapMap GGL *
        (((xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) c : adjointGroup d4 GGL)) :
          ModGL d4 GGL) * (d4SwapMap GGL)⁻¹ = _
      rw [rckTriD4_q_conj_neg_xPar_two c]
      rfl

theorem rckTriD4_psi1_fixed_iff_twist {h : ℕ} (u : ModGL d4 GGL) :
    u ∈ (rckTriD4_psi h 1).eqLocus (MonoidHom.id _) ↔
      twistHom TwistTag.D4 GGL (iterateFrobenius GGL 2 h) u = u := by
  change rckTriD4_psi h 1 u = u ↔ _
  rw [rckTriD4_psi_apply, pow_one]
  rfl

theorem rckTriD4_psi2_fixed_iff_twist {h : ℕ} {FrE : GGL ≃+* GGL}
    (hFrE : FrE.toRingHom = iterateFrobenius GGL 2 h) (u : ModGL d4 GGL) :
    u ∈ (rckTriD4_psi h 2).eqLocus (MonoidHom.id _) ↔
      twistHom TwistTag.D4 GGL FrE.symm.toRingHom u = u := by
  change rckTriD4_psi h 2 u = u ↔ _
  rw [rckTriD4_psi_apply, ← hFrE]
  exact diagramMap_sq_conj_eq_iff (L := GGL) FrE u

theorem rckTriD4_q_conj_fix1_iff_fix2 {h : ℕ} {FrE : GGL ≃+* GGL}
    (hFrE : FrE.toRingHom = iterateFrobenius GGL 2 h) (u : ModGL d4 GGL) :
    u ∈ (rckTriD4_psi h 1).eqLocus (MonoidHom.id _) ↔
      d4SwapMap GGL * u * (d4SwapMap GGL)⁻¹ ∈
        (rckTriD4_psi h 2).eqLocus (MonoidHom.id _) := by
  rw [rckTriD4_psi1_fixed_iff_twist, rckTriD4_psi2_fixed_iff_twist hFrE]
  constructor
  · intro hu
    rw [twistHom_apply, ← hFrE] at hu
    exact d4Twist_inv_conj_swap (K := GGL) FrE hu
  · intro hx
    have hx' : twistHom TwistTag.D4 GGL FrE.symm.toRingHom
        (d4SwapMap GGL * u * (d4SwapMap GGL)⁻¹) =
        d4SwapMap GGL * u * (d4SwapMap GGL)⁻¹ := hx
    rw [twistHom_apply] at hx'
    have hfix := d4Twist_inv_conj_swap (K := GGL) FrE.symm hx'
    have hq : d4SwapMap GGL * (d4SwapMap GGL * u * (d4SwapMap GGL)⁻¹) *
        (d4SwapMap GGL)⁻¹ = u := by
      calc d4SwapMap GGL * (d4SwapMap GGL * u * (d4SwapMap GGL)⁻¹) *
            (d4SwapMap GGL)⁻¹
          = (d4SwapMap GGL * d4SwapMap GGL) * u *
            ((d4SwapMap GGL)⁻¹ * (d4SwapMap GGL)⁻¹) := by group
        _ = u := by
            rw [d4SwapMap_mul_self, d4SwapMap_inv, d4SwapMap_mul_self, one_mul, mul_one]
    have hEE : FrE.symm⁻¹ = FrE := RingEquiv.ext (fun x => rfl)
    rw [hq, hEE, hFrE] at hfix
    rw [twistHom_apply]
    exact hfix

theorem rckTriD4_q_adjoint_eq :
    (adjointGroup d4 GGL).map (MulAut.conj (d4SwapMap GGL)).toMonoidHom =
      adjointGroup d4 GGL := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact labelMap_conj_mem (K := GGL) (π := d4Swap) (hπ := d4Swap_cartan) hg
  · intro g hg
    refine ⟨(d4SwapMap GGL)⁻¹ * g * d4SwapMap GGL, ?_, ?_⟩
    · rw [d4SwapMap_inv]
      exact labelMap_conj_mem (K := GGL) (π := d4Swap) (hπ := d4Swap_cartan) hg
    · change d4SwapMap GGL * ((d4SwapMap GGL)⁻¹ * g * d4SwapMap GGL) *
        (d4SwapMap GGL)⁻¹ = g
      group

theorem rckTriD4_q_fix_eq {h : ℕ} {FrE : GGL ≃+* GGL}
    (hFrE : FrE.toRingHom = iterateFrobenius GGL 2 h) :
    ((rckTriD4_psi h 1).eqLocus (MonoidHom.id _)).map
        (MulAut.conj (d4SwapMap GGL)).toMonoidHom =
      (rckTriD4_psi h 2).eqLocus (MonoidHom.id _) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (rckTriD4_q_conj_fix1_iff_fix2 hFrE u).1 hu
  · intro hx
    refine ⟨(d4SwapMap GGL)⁻¹ * x * d4SwapMap GGL, ?_, ?_⟩
    · have hq : d4SwapMap GGL * ((d4SwapMap GGL)⁻¹ * x * d4SwapMap GGL) *
          (d4SwapMap GGL)⁻¹ = x := by
        calc d4SwapMap GGL * ((d4SwapMap GGL)⁻¹ * x * d4SwapMap GGL) *
              (d4SwapMap GGL)⁻¹
            = (d4SwapMap GGL * (d4SwapMap GGL)⁻¹) * x *
              (d4SwapMap GGL * (d4SwapMap GGL)⁻¹) := by group
          _ = x := by rw [mul_inv_cancel, one_mul, mul_one]
      exact (rckTriD4_q_conj_fix1_iff_fix2 hFrE _).2 (by rwa [hq])
    · change d4SwapMap GGL * ((d4SwapMap GGL)⁻¹ * x * d4SwapMap GGL) *
        (d4SwapMap GGL)⁻¹ = x
      calc d4SwapMap GGL * ((d4SwapMap GGL)⁻¹ * x * d4SwapMap GGL) *
            (d4SwapMap GGL)⁻¹
          = (d4SwapMap GGL * (d4SwapMap GGL)⁻¹) * x *
            (d4SwapMap GGL * (d4SwapMap GGL)⁻¹) := by group
        _ = x := by rw [mul_inv_cancel, one_mul, mul_one]

theorem rckTriD4_range_two {F : Type} [Field F] [Finite F] [Algebra F GGL]
    (σ : F →+* F) {h : ℕ} (hh : 1 ≤ h) (hTri : TriField F σ h) :
    ((MulAut.conj (d4SwapMap GGL)).toMonoidHom.comp
        (rckTriD4_iotaD4 (F := F) σ)).range =
      adjointGroup d4 GGL ⊓ (rckTriD4_psi h 2).eqLocus (MonoidHom.id _) := by
  classical
  let Fr : GGL →+* GGL := iterateFrobenius GGL 2 h
  have hFrsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y
      (pow_pos (by norm_num : 0 < 2) h)
    exact ⟨x, by rw [show Fr = iterateFrobenius GGL 2 h from rfl, iterateFrobenius_def, hx]⟩
  let FrE : GGL ≃+* GGL := RingEquiv.ofBijective Fr ⟨Fr.injective, hFrsurj⟩
  have hFrE : FrE.toRingHom = iterateFrobenius GGL 2 h := rfl
  rw [MonoidHom.range_comp, rckTriD4_range_one (F := F) (σ := σ) hh hTri,
    Subgroup.map_inf _ _ _ (MulAut.conj (d4SwapMap GGL)).injective,
    rckTriD4_q_adjoint_eq, rckTriD4_q_fix_eq hFrE]

theorem rckTriD4_rootGroup_two_pos (F : Subfield GGL) [Finite ↥F] {h : ℕ}
    (hFcard : Nat.card ↥F = (2 ^ h) ^ 3)
    (hFmem : ∀ c : GGL, c ∈ F ↔ c ^ 2 ^ (3 * h) = c) :
    ((twistedDatum (iterateFrobenius ↥F 2 h)).rootGroup (Pi.single (ng 0) 1)).map
        ((MulAut.conj (d4SwapMap GGL)).toMonoidHom.comp
          (rckTriD4_iotaD4 (F := ↥F) (iterateFrobenius ↥F 2 h))) =
      rootSubgroup d4 GGL (Pi.single (nd 2) 1) ⊓
        (rckTriD4_psi h 2).eqLocus (MonoidHom.id _) := by
  classical
  let Fr : GGL →+* GGL := iterateFrobenius GGL 2 h
  have hFrsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y
      (pow_pos (by norm_num : 0 < 2) h)
    exact ⟨x, by rw [show Fr = iterateFrobenius GGL 2 h from rfl, iterateFrobenius_def, hx]⟩
  let FrE : GGL ≃+* GGL := RingEquiv.ofBijective Fr ⟨Fr.injective, hFrsurj⟩
  have hFrE : FrE.toRingHom = iterateFrobenius GGL 2 h := rfl
  rw [← Subgroup.map_map]
  rw [rckTriD4_rootGroup_one_pos F hFcard hFmem,
    Subgroup.map_inf _ _ _ (MulAut.conj (d4SwapMap GGL)).injective,
    rckTriD4_q_map_rootSubgroup_pos, rckTriD4_q_fix_eq hFrE]

theorem rckTriD4_rootGroup_two_neg (F : Subfield GGL) [Finite ↥F] {h : ℕ}
    (hFcard : Nat.card ↥F = (2 ^ h) ^ 3)
    (hFmem : ∀ c : GGL, c ∈ F ↔ c ^ 2 ^ (3 * h) = c) :
    ((twistedDatum (iterateFrobenius ↥F 2 h)).rootGroup (-Pi.single (ng 0) 1)).map
        ((MulAut.conj (d4SwapMap GGL)).toMonoidHom.comp
          (rckTriD4_iotaD4 (F := ↥F) (iterateFrobenius ↥F 2 h))) =
      rootSubgroup d4 GGL (-Pi.single (nd 2) 1) ⊓
        (rckTriD4_psi h 2).eqLocus (MonoidHom.id _) := by
  classical
  let Fr : GGL →+* GGL := iterateFrobenius GGL 2 h
  have hFrsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y
      (pow_pos (by norm_num : 0 < 2) h)
    exact ⟨x, by rw [show Fr = iterateFrobenius GGL 2 h from rfl, iterateFrobenius_def, hx]⟩
  let FrE : GGL ≃+* GGL := RingEquiv.ofBijective Fr ⟨Fr.injective, hFrsurj⟩
  have hFrE : FrE.toRingHom = iterateFrobenius GGL 2 h := rfl
  rw [← Subgroup.map_map]
  rw [rckTriD4_rootGroup_one_neg F hFcard hFmem,
    Subgroup.map_inf _ _ _ (MulAut.conj (d4SwapMap GGL)).injective,
    rckTriD4_q_map_rootSubgroup_neg, rckTriD4_q_fix_eq hFrE]

theorem rckTriD4_iotaD4_injective {F : Type} [Field F] [Algebra F GGL]
    (σ : F →+* F) : Function.Injective (rckTriD4_iotaD4 (F := F) σ) := by
  intro x y hxy
  exact (baseChangeGL_injective (τ := d4) (f := algebraMap F GGL)).comp
    ((Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)) hxy

theorem rckTriD4_fieldData (h : ℕ) (hh : 1 ≤ h) :
    ∃ (F : Subfield GGL) (_ : Finite ↥F),
      Nat.card ↥F = (2 ^ h) ^ 3 ∧ (∀ c : GGL, c ∈ F ↔ c ^ 2 ^ (3 * h) = c) := by
  let F := frobeniusFixedField GGL 2 (3 * h)
  let σ : ↥F →+* ↥F := iterateFrobenius ↥F 2 h
  have hFcard : Nat.card ↥F = (2 ^ h) ^ 3 := by
    change Nat.card (frobeniusFixedField GGL 2 (3 * h)) = (2 ^ h) ^ 3
    rw [card_frobeniusFixedField (k := GGL) (p := 2) (n := 3 * h) (by positivity),
      ← pow_mul, mul_comm]
  have hFmem : ∀ c : GGL, c ∈ F ↔ c ^ 2 ^ (3 * h) = c := fun c =>
    mem_frobeniusFixedField (k := GGL) (p := 2) (n := 3 * h)
  haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact pow_ne_zero _ (pow_ne_zero _ (by norm_num : (2:ℕ) ≠ 0)))
  exact ⟨F, inferInstance, hFcard, hFmem⟩

theorem rckTriD4_model_aux {h r : ℕ} (hh : 1 ≤ h) (hr : r = 1 ∨ r = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F)
      (ι : ↥(twistedGroup σ) →* ModGL d4 GGL),
      TriField F σ h ∧ Function.Injective ι ∧
      ι.range = adjointGroup d4 GGL ⊓ (rckTriD4_psi h r).eqLocus (MonoidHom.id _) ∧
      ((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map ι =
        rootSubgroup d4 GGL (Pi.single (nd 2) 1) ⊓
          (rckTriD4_psi h r).eqLocus (MonoidHom.id _) ∧
      ((twistedDatum σ).rootGroup (-Pi.single (ng 0) 1)).map ι =
        rootSubgroup d4 GGL (-Pi.single (nd 2) 1) ⊓
          (rckTriD4_psi h r).eqLocus (MonoidHom.id _) ∧
      (rootSubgroup d4 GGL (Pi.single (nd 2) 1)).map (rckTriD4_psi h r) =
        rootSubgroup d4 GGL (Pi.single (nd 2) 1) ∧
      (rootSubgroup d4 GGL (-Pi.single (nd 2) 1)).map (rckTriD4_psi h r) =
        rootSubgroup d4 GGL (-Pi.single (nd 2) 1) := by
  classical
  obtain ⟨F, hFin, hFcard, hFmem⟩ := rckTriD4_fieldData h hh
  letI hField : Field ↥F := inferInstance
  letI hFinite : Finite ↥F := hFin
  have hTri : TriField ↥F (iterateFrobenius ↥F 2 h) h :=
    ⟨hh, hFcard, fun c => iterateFrobenius_def 2 h c⟩
  rcases hr with rfl | rfl
  · have hι := rckTriD4_iotaD4_injective (F := ↥F) (iterateFrobenius ↥F 2 h)
    have hrange := rckTriD4_range_one (F := ↥F) (σ := iterateFrobenius ↥F 2 h)
      (h := h) (hh := hh) (hTri := hTri)
    have hpos := rckTriD4_rootGroup_one_pos F hFcard hFmem
    have hneg := rckTriD4_rootGroup_one_neg F hFcard hFmem
    have hsp := rckTriD4_stable_pos h 1
    have hsn := rckTriD4_stable_neg h 1
    refine ⟨↥F, hField, hFinite, iterateFrobenius ↥F 2 h,
      rckTriD4_iotaD4 (F := ↥F) (iterateFrobenius ↥F 2 h), hTri,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hι
    · exact hrange
    · exact hpos
    · exact hneg
    · exact hsp
    · exact hsn
  · have hι := (MulAut.conj (d4SwapMap GGL)).injective.comp
        (rckTriD4_iotaD4_injective (F := ↥F) (iterateFrobenius ↥F 2 h))
    have hrange := rckTriD4_range_two (F := ↥F) (σ := iterateFrobenius ↥F 2 h)
      (h := h) (hh := hh) (hTri := hTri)
    have hpos := rckTriD4_rootGroup_two_pos F hFcard hFmem
    have hneg := rckTriD4_rootGroup_two_neg F hFcard hFmem
    have hsp := rckTriD4_stable_pos h 2
    have hsn := rckTriD4_stable_neg h 2
    refine ⟨↥F, hField, hFinite, iterateFrobenius ↥F 2 h,
      (MulAut.conj (d4SwapMap GGL)).toMonoidHom.comp
        (rckTriD4_iotaD4 (F := ↥F) (iterateFrobenius ↥F 2 h)),
      hTri, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hι
    · exact hrange
    · exact hpos
    · exact hneg
    · exact hsp
    · exact hsn

theorem triD4_model_in_adjD4 {h r : ℕ} (hh : 1 ≤ h) (hr : r = 1 ∨ r = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F)
      (ι : ↥(twistedGroup σ) →* ModGL Tag.D4 GGL),
      TriField F σ h ∧ Function.Injective ι ∧
      ι.range = adjointGroup Tag.D4 GGL ⊓ (triPsi h r).eqLocus (MonoidHom.id _) ∧
      ((twistedDatum σ).rootGroup (Pi.single (ng 0) 1)).map ι =
        rootSubgroup Tag.D4 GGL (Pi.single (nd 2) 1) ⊓
          (triPsi h r).eqLocus (MonoidHom.id _) ∧
      ((twistedDatum σ).rootGroup (-Pi.single (ng 0) 1)).map ι =
        rootSubgroup Tag.D4 GGL (-Pi.single (nd 2) 1) ⊓
          (triPsi h r).eqLocus (MonoidHom.id _) ∧
      (rootSubgroup Tag.D4 GGL (Pi.single (nd 2) 1)).map (triPsi h r) =
        rootSubgroup Tag.D4 GGL (Pi.single (nd 2) 1) ∧
      (rootSubgroup Tag.D4 GGL (-Pi.single (nd 2) 1)).map (triPsi h r) =
        rootSubgroup Tag.D4 GGL (-Pi.single (nd 2) 1) :=
  rckTriD4_model_aux hh hr

end CFSG.StandardType.RCKRP

end
