module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTSpec
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTFrame
public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcAdLinear

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three
  CFSG.RankThree.CentralCover


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

private theorem baseChange_rgrpConjAut_apply {L : Type} [Field L] [Algebra K L]
    [IsAlgClosure K L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (r : ↥(TwistedDiag.Rgrp L Fr)) :
    baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L)
        (((rgrpConjAut hn hK σ hσ Fr hFr r) h : _) : ModGL TwistTag.E6.tag K)
      = (show ModGL TwistTag.E6.tag L from (r : ModGL Tag.E6 L)) *
        baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L)
          ((h : _) : ModGL TwistTag.E6.tag K) *
        (show ModGL TwistTag.E6.tag L from (r : ModGL Tag.E6 L))⁻¹ := by
  obtain ⟨w, rfl⟩ := (twInndiagEquivRgrp hn hK σ hσ Fr hFr).surjective r
  rw [rgrpConjAut_apply_baseChange, RecipeExcLang.coe_twConj]
  rw [map_mul, map_mul, map_inv,
    twInndiagEquivRgrp_apply (n := n) hn hK σ hσ (L := L) (Fr := Fr) hFr]

private theorem cube_root_eq_or_inv {L : Type} [Field L] {η ζ : Lˣ}
    (hη3 : η ^ 3 = 1) (hη1 : η ≠ 1) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    η = ζ ∨ η = ζ⁻¹ := by
  have hηc : (η : L) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hη3, Units.val_one]
  have hη : (η : L) ^ 2 + (η : L) + 1 = 0 := by
    have hfac : ((η : L) - 1) * ((η : L) ^ 2 + (η : L) + 1) = 0 := by
      linear_combination hηc
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) hη1
    · exact h
  have hζc : (ζ : L) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hζ : (ζ : L) ^ 2 + (ζ : L) + 1 = 0 := by
    have hfac : ((ζ : L) - 1) * ((ζ : L) ^ 2 + (ζ : L) + 1) = 0 := by
      linear_combination hζc
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) hζ1
    · exact h
  have hfac : ((η : L) - (ζ : L)) * ((η : L) + (ζ : L) + 1) = 0 := by
    linear_combination hη - hζ
  rcases mul_eq_zero.1 hfac with h | h
  · left
    exact Units.ext (sub_eq_zero.1 h)
  · right
    have h1 : (η : L) = -((ζ : L) + 1) := by linear_combination h
    have hmul : η * ζ = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one, h1]
      linear_combination -hζ
    exact eq_inv_of_mul_eq_one_left hmul

private theorem zmodPowHom_neg_one {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    zmodPowHom ζ hζ (Multiplicative.ofAdd (-1 : ZMod 3)) = ζ⁻¹ := by
  rw [zmodPowHom_apply]
  have hv : ((-1 : ZMod 3)).val = 2 := by decide
  rw [hv]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, show 2 + 1 = 3 by norm_num, hζ])

private theorem exists_smul_exponent {L : Type} [Field L] {ζ η : Lˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (hη3 : η ^ 3 = 1) (hη1 : η ≠ 1) :
    ∃ e : ZMod 3, (e = 1 ∨ e = -1) ∧ η = zmodPowHom ζ hζ (.ofAdd e) := by
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact absurd hζo (by decide)
  rcases cube_root_eq_or_inv hη3 hη1 hζ hζ1 with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [h, zmodPowHom_apply, ZMod.val_one, pow_one]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [h]
    exact (zmodPowHom_neg_one hζ).symm

private theorem units_map_entrywiseHom_rootDiagUnit_zetaVec
    {τ : Tag} {p : ℕ} [NeZero p] {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ p = 1)
    (δL : L ≃+* L) (e : ZMod p)
    (hη : Units.map δL.toMonoidHom ζ = zmodPowHom ζ hζ (.ofAdd e))
    (x : Fin τ.rank → ZMod p) :
    Units.map (entrywiseHom δL.toRingHom) (rootDiagUnit τ (zetaVec ζ hζ x)) =
      rootDiagUnit τ (zetaVec ζ hζ (e • x)) := by
  rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
  congr 1
  funext i
  simp only [zetaVec_apply, Pi.smul_apply, smul_eq_mul, map_pow]
  have hpow : (Units.map δL.toMonoidHom ζ) ^ (x i).val
      = zmodPowHom ζ hζ (.ofAdd (e * x i)) := by
    rw [hη, ← zpow_natCast, zmodPowHom_zpow]
    congr 2
    have hcast : ((x i).val : ZMod p) = x i := ZMod.natCast_zmod_val (x i)
    push_cast
    rw [hcast, mul_comm]
  rw [hpow, zmodPowHom_apply]

theorem tFrame_aut (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : D.AutOK := by
  intro α S hS hα
  obtain ⟨-, -, -, -, -, hcoe, hfield, hαnf, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  obtain ⟨g₁, u, δ, hαeq⟩ := hαnf α
  have hb : RecipeExcLang.IsCompatE6 σ.toRingHom
      (compatDiag TwistTag.E6 σ.toRingHom u) :=
    fun i => compatDiag_perm u i
  let x₁ : ModGL TwistTag.E6.tag K :=
    (g₁ : ModGL TwistTag.E6.tag K) *
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)
  have hx₁Γ : x₁ ∈ RecipeExcLang.twInndiagGroup K σ :=
    mul_mem (RecipeExcLang.graphFixedRootGroup_le_twInndiag σ g₁.2)
      (RecipeExcLang.rootDiagUnit_mem_twInndiag hb)
  have hαmod : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ((α c : _) : ModGL TwistTag.E6.tag K) =
        x₁ * Units.map (entrywiseHom δ.toRingHom) (c : ModGL TwistTag.E6.tag K) * x₁⁻¹ := by
    intro c
    rw [hαeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcoe, hfield]
    simp only [x₁]
    group
  let δL : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv _ _ δ
  have hδL : ∀ c : K, δL (algebraMap K Ω c) = algebraMap K Ω (δ c) :=
    fun c => IsAlgClosure.equivOfEquiv_algebraMap _ _ δ c
  let X : ModGL TwistTag.E6.tag Ω := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) x₁
  have hX_mem : X ∈ TwistedDiag.Rgrp Ω Fr :=
    RecipeExcLang.baseChangeGL_mem_twistedFixed_of_mem_twInndiag (σ := σ) hn hK hσ
      (L := Ω) hFr hx₁Γ
  have hX_adj : X ∈ adjointGroup Tag.E6 Ω :=
    twistedFixedGroup_le_adjointGroup TwistTag.E6 Ω Fr hX_mem
  have hαι : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) ((α c : _) : ModGL TwistTag.E6.tag K) =
        X * Units.map (entrywiseHom δL.toRingHom)
          (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)
            ((c : _) : ModGL TwistTag.E6.tag K)) * X⁻¹ := by
    intro c
    rw [hαmod c]
    rw [map_mul, map_mul, map_inv,
      CFSG.RankThree.Chevalley.SteinbergBN.baseChangeGL_entrywise_comm δ δL hδL]
    rfl
  let η : Ωˣ := Units.map δL.toMonoidHom ζ
  have hη3 : η ^ 3 = 1 := by
    show (Units.map δL.toMonoidHom ζ) ^ 3 = 1
    rw [← map_pow, hζ, map_one]
  have hζne : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact absurd hζo (by decide)
  have hη1 : η ≠ 1 := by
    intro h
    have h' : (η : Ω) = 1 := by
      simpa using congrArg (fun v : Ωˣ => (v : Ω)) h
    have h'' : δL (ζ : Ω) = 1 := by simpa [η] using h'
    have hc : (ζ : Ω) = 1 := δL.injective (by rw [h'', map_one])
    exact hζne (Units.ext hc)
  obtain ⟨e, he, hηe⟩ := exists_smul_exponent hζ hζo hη3 hη1
  have he2 : e * e = 1 := by rcases he with rfl | rfl <;> decide
  have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> decide
  have heS : ∀ x ∈ S, e • x ∈ S := by
    intro x hx
    rcases hS with rfl | rfl
    · trivial
    · rcases he with rfl | rfl
      · simpa using hx
      · have hneg : (-1 : ZMod 3) • x = -x := by
          funext i
          rw [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
          exact neg_one_mul (x i)
        rw [hneg]
        exact NoOffRest.hypE6.neg_mem hx
  let gT : ModGL TwistTag.E6.tag Ω := g
  let y : ModGL TwistTag.E6.tag Ω := gT⁻¹ * X * Units.map (entrywiseHom δL.toRingHom) gT
  have hyC : y ∈ adjointGroup Tag.E6 Ω :=
    mul_mem (mul_mem (inv_mem hL.1) hX_adj)
      (CFSG.RankThree.Chevalley.SteinbergBN.units_map_entrywiseHom_mem_adjointGroup
        δL.toRingHom hL.1)
  have hkey : ∀ x ∈ S, ∃ z ∈ S, (α * D.ad x * α⁻¹ = D.ad z) ∧
      rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ z) =
        y * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (e • x)) * y⁻¹ := by
    intro x hx
    let xT : Fin TwistTag.E6.tag.rank → ZMod 3 := x
    obtain ⟨z, hzS, hz⟩ := hα x hx
    let zT : Fin TwistTag.E6.tag.rank → ZMod 3 := z
    obtain ⟨hxr, hxad⟩ := hD.diag_eq x
    obtain ⟨hzr, hzad⟩ := hD.diag_eq z
    let rx : ↥(TwistedDiag.Rgrp Ω Fr) :=
      ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹, hxr⟩
    let rz : ↥(TwistedDiag.Rgrp Ω Fr) :=
      ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ z) * g⁻¹, hzr⟩
    have hxad' : D.ad x = rgrpConjAut hn hK σ hσ Fr hFr rx := hxad
    have hzad' : D.ad z = rgrpConjAut hn hK σ hσ Fr hFr rz := hzad
    have hconj : rgrpConjAut hn hK σ hσ Fr hFr rz =
        α * rgrpConjAut hn hK σ hσ Fr hFr rx * α⁻¹ := by
      rw [← hzad', ← hxad']
      exact hz.symm
    let wrx : ↥(RecipeExcLang.twInndiagGroup K σ) :=
      (twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm rx
    have hwrx : twInndiagEquivRgrp hn hK σ hσ Fr hFr wrx = rx :=
      MulEquiv.apply_symm_apply _ _
    have hmod : x₁ * Units.map (entrywiseHom δ.toRingHom) (wrx : ModGL TwistTag.E6.tag K) *
        x₁⁻¹ ∈ RecipeExcLang.twInndiagGroup K σ :=
      mul_mem (mul_mem hx₁Γ (RecipeExcLang.entrywise_mem_twInndiag δ wrx.2)) (inv_mem hx₁Γ)
    let r' : ↥(TwistedDiag.Rgrp Ω Fr) :=
      twInndiagEquivRgrp hn hK σ hσ Fr hFr ⟨_, hmod⟩
    have hr'coe : (show ModGL TwistTag.E6.tag Ω from (r' : ModGL Tag.E6 Ω)) =
        X * Units.map (entrywiseHom δL.toRingHom)
          (show ModGL TwistTag.E6.tag Ω from (rx : ModGL Tag.E6 Ω)) * X⁻¹ := by
      show baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)
        (x₁ * Units.map (entrywiseHom δ.toRingHom) (wrx : ModGL TwistTag.E6.tag K) * x₁⁻¹) = _
      rw [map_mul, map_mul, map_inv,
        CFSG.RankThree.Chevalley.SteinbergBN.baseChangeGL_entrywise_comm δ δL hδL]
      have h1 : baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)
          (wrx : ModGL TwistTag.E6.tag K) =
          (show ModGL TwistTag.E6.tag Ω from (rx : ModGL Tag.E6 Ω)) := by
        rw [← twInndiagEquivRgrp_apply (n := n) hn hK σ hσ (L := Ω) (Fr := Fr) hFr, hwrx]
      rw [h1]
      rfl
    have hpt : ∀ v : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
        rgrpConjAut hn hK σ hσ Fr hFr r' (α v) =
          rgrpConjAut hn hK σ hσ Fr hFr rz (α v) := by
      intro v
      have hR : rgrpConjAut hn hK σ hσ Fr hFr rz (α v) =
          α (rgrpConjAut hn hK σ hσ Fr hFr rx v) := by
        conv_lhs => rw [hconj]
        simp only [MulAut.mul_apply]
        show α (rgrpConjAut hn hK σ hσ Fr hFr rx (α.symm (α v))) =
          α (rgrpConjAut hn hK σ hσ Fr hFr rx v)
        rw [MulEquiv.symm_apply_apply]
      rw [hR]
      apply Subtype.ext
      apply baseChangeGL_injective (τ := TwistTag.E6.tag) (algebraMap K Ω)
      rw [baseChange_rgrpConjAut_apply (n := n) hn hK σ hσ (Fr := Fr) hFr (α v) r',
        hαι (rgrpConjAut hn hK σ hσ Fr hFr rx v)]
      rw [hr'coe, baseChange_rgrpConjAut_apply (n := n) hn hK σ hσ (Fr := Fr) hFr v rx,
        hαι v]
      rw [map_mul, map_mul, map_inv]
      group
    have heq : rgrpConjAut hn hK σ hσ Fr hFr r' = rgrpConjAut hn hK σ hσ Fr hFr rz := by
      apply MulEquiv.ext
      intro h
      obtain ⟨v, rfl⟩ := α.surjective h
      exact hpt v
    have hrz : r' = rz := rgrpConjAut_injective hn hK σ hσ Fr hFr heq
    have hvalrz : (show ModGL TwistTag.E6.tag Ω from (rz : ModGL Tag.E6 Ω)) =
        X * Units.map (entrywiseHom δL.toRingHom)
          (show ModGL TwistTag.E6.tag Ω from (rx : ModGL Tag.E6 Ω)) * X⁻¹ := by
      rw [← hrz]
      exact hr'coe
    have hrxval : (show ModGL TwistTag.E6.tag Ω from (rx : ModGL Tag.E6 Ω)) =
        gT * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ xT) * gT⁻¹ := rfl
    have hrzval : (show ModGL TwistTag.E6.tag Ω from (rz : ModGL Tag.E6 Ω)) =
        gT * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ zT) * gT⁻¹ := rfl
    have hδdx : Units.map (entrywiseHom δL.toRingHom)
        (rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ xT)) =
        rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (e • xT)) :=
      units_map_entrywiseHom_rootDiagUnit_zetaVec (τ := TwistTag.E6.tag) hζ δL e hηe xT
    refine ⟨z, hzS, hz, ?_⟩
    have hmain : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ zT) =
        y * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (e • xT)) * y⁻¹ := by
      have hstep : gT * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ zT) * gT⁻¹ =
          X * Units.map (entrywiseHom δL.toRingHom)
            (show ModGL TwistTag.E6.tag Ω from (rx : ModGL Tag.E6 Ω)) * X⁻¹ := by
        rw [← hrzval, hvalrz]
      calc rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ zT)
          = gT⁻¹ * (gT * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ zT) * gT⁻¹) * gT := by
            group
        _ = gT⁻¹ * (X * Units.map (entrywiseHom δL.toRingHom)
              (show ModGL TwistTag.E6.tag Ω from (rx : ModGL Tag.E6 Ω)) * X⁻¹) * gT := by
            rw [hstep]
        _ = y * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (e • xT)) * y⁻¹ := by
            rw [hrxval, map_mul, map_mul, map_inv, hδdx]
            simp only [y]
            group
    exact hmain
  let V : Set (ModGL TwistTag.E6.tag Ω) :=
    {d | ∃ v ∈ S, d = rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ v)}
  have hVD : ∀ d ∈ V, ∃ a : Fin TwistTag.E6.tag.rank → Ωˣ, d = rootDiagUnit TwistTag.E6.tag a := by
    rintro d ⟨v, -, rfl⟩
    exact ⟨zetaVec ζ hζ v, rfl⟩
  have hyV : ∀ d ∈ V, y * d * y⁻¹ ∈ V := by
    rintro d ⟨v, hvS, rfl⟩
    let vT : Fin TwistTag.E6.tag.rank → ZMod 3 := v
    obtain ⟨z, hzS, -, hz⟩ := hkey (e • v) (heS v hvS)
    let zT : Fin TwistTag.E6.tag.rank → ZMod 3 := z
    refine ⟨z, hzS, ?_⟩
    have hvv : e • (e • vT) = vT := by rw [smul_smul, he2, one_smul]
    have hz' : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ zT) =
        y * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (e • (e • vT))) * y⁻¹ := hz
    rw [hvv] at hz'
    exact hz'.symm
  obtain ⟨w, hw⟩ :=
    NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
      (τ := TwistTag.E6.tag) (k := Ω) hVD hyC hyV
  refine ⟨e, w, he0, ?_⟩
  intro x hx
  let xT : Fin TwistTag.E6.tag.rank → ZMod 3 := x
  obtain ⟨z, hzS, hzad, hdz⟩ := hkey x hx
  let zT : Fin TwistTag.E6.tag.rank → ZMod 3 := z
  have hVmem : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (e • x)) ∈ V :=
    ⟨e • x, heS x hx, rfl⟩
  have hw' := hw _ hVmem
  have hdz' : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ z) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w *
        rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (e • x)) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w)⁻¹ := hdz.trans hw'
  have hcw : canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w *
      rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (e • x)) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (adAct (TwistTag.E6.tag) 3 w (e • x))) := by
    rw [canonicalRep_conj_rootDiagUnit (τ := TwistTag.E6.tag) w (zetaVec ζ hζ (e • x))]
    congr 1
    exact weylTuple_zetaVec (τ := TwistTag.E6.tag) (p := 3) ζ hζ w (e • x)
  have hdz'' : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ zT) =
      rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (adAct (TwistTag.E6.tag) 3 w (e • xT))) :=
    hdz'.trans hcw
  have hzar : zT = e • adAct (TwistTag.E6.tag) 3 w xT := by
    have h1 : zetaVec ζ hζ zT =
        zetaVec ζ hζ (adAct (TwistTag.E6.tag) 3 w (e • xT)) :=
      rootDiagUnit_injective (τ := TwistTag.E6.tag) hdz''
    have h2 : zT = adAct (TwistTag.E6.tag) 3 w (e • xT) :=
      zetaVec_injective (τ := TwistTag.E6.tag) (p := 3) hζo hζ h1
    have h3 : adAct (TwistTag.E6.tag) 3 w (e • xT) =
        e • adAct (TwistTag.E6.tag) 3 w xT := adAct_smul w e xT
    exact h2.trans h3
  calc α * D.ad x * α⁻¹ = D.ad z := hzad
    _ = D.ad (e • adAct .E6 3 w x) :=
        congrArg D.ad (show z = e • adAct .E6 3 w x from hzar)

end CFSG.StandardType.E6ThreeModel
