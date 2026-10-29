module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Torus
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIUnitaryTwo
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
open CFSG.HardMathSupport.Dickson.Bal207.OrthFix
open Polynomial

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {p : ℕ}
  {a : K[X]} [Fact (Irreducible a)] {m : ℕ}

@[expose] noncomputable def pairedBlockCoordEquiv
    (hx : OddOrderIsometry Q p x) (ha : a ∈ primaryFactors x.toLinearMap)
    (hne : a ≠ reciprocalPolynomial a)
    (b : Module.Basis (Fin m) (AdjoinRoot a) (primaryComponent x.toLinearMap a)) :
    ↥(supportedBlock Q x a) ≃* GL (Fin m) (AdjoinRoot a) :=
  (pairedBlockEquiv hx ha hne).trans (Matrix.GeneralLinearGroup.toLin' b).symm

theorem pairedBlockCoordEquiv_square
    (hx : OddOrderIsometry Q p x) (ha : a ∈ primaryFactors x.toLinearMap)
    (hne : a ≠ reciprocalPolynomial a)
    (b : Module.Basis (Fin m) (AdjoinRoot a) (primaryComponent x.toLinearMap a))
    {σ : K ≃+* K} {S : V ≃+ V}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (x v) = x (S v)) (haσ : a.map (σ : K →+* K) = a)
    {g g' : ↥(supportedBlock Q x a)}
    (hgg' : ∀ v : V, (g' : V ≃ₗ[K] V) v = S ((g : V ≃ₗ[K] V) (S.symm v))) :
    pairedBlockCoordEquiv hx ha hne b g' =
      semMatUnit b (semilinRestrict hS hSx haσ) (semilinRestrict_smul hS hSx haσ) *
        Matrix.GeneralLinearGroup.map ((extAut a σ haσ) : AdjoinRoot a →+* AdjoinRoot a)
          (pairedBlockCoordEquiv hx ha hne b g) *
        (semMatUnit b (semilinRestrict hS hSx haσ) (semilinRestrict_smul hS hSx haσ))⁻¹ := by
  exact toLin'_symm_conj_semilin b (semilinRestrict hS hSx haσ)
    (semilinRestrict_smul hS hSx haσ) (blockGL Q x a g) (blockGL Q x a g')
    (blockGL_semilinRestrict_square hS hSx haσ hgg')

section ActualBlock

open CFSG.Open (StatedOmega)
open CFSG.ClassicalGroups.Orthogonal
open CFSG.StandardType.ClassicalPosition

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]

@[expose] noncomputable def glBlockCentralizerEquivPrimaryGL
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e e' : Matrix ι ι K} {a : K[X]} [Fact (Irreducible a)] {m : ℕ}
    (hx : OddOrderIsometry Φ (orderOf b) (toLinEquiv ι K b))
    (hodd : Odd (orderOf b))
    (ha : a ∈ primaryFactors (toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (toLinEquiv ι K b).toLinearMap a)
    (ha'e : Matrix.toLinAlgEquiv' e' =
      primaryProjection (toLinEquiv ι K b).toLinearMap (reciprocalPolynomial a))
    (hne : a ≠ reciprocalPolynomial a) (hεe : ε = e + e')
    (basis : Module.Basis (Fin m) (AdjoinRoot a)
      (primaryComponent (toLinEquiv ι K b).toLinearMap a)) :
    ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      GL (Fin m) (AdjoinRoot a) :=
  (glBlockCentralizerEquivSupportedBlock_linear Φ hΦ h8 b hx hodd ha hae ha'e hne hεe).trans
    (pairedBlockCoordEquiv hx ha hne basis)

theorem glBlockCentralizerEquivPrimaryGL_square
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e e' : Matrix ι ι K} {a : K[X]} [Fact (Irreducible a)] {m : ℕ}
    (hx : OddOrderIsometry Φ (orderOf b) (toLinEquiv ι K b))
    (hodd : Odd (orderOf b))
    (ha : a ∈ primaryFactors (toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (toLinEquiv ι K b).toLinearMap a)
    (ha'e : Matrix.toLinAlgEquiv' e' =
      primaryProjection (toLinEquiv ι K b).toLinearMap (reciprocalPolynomial a))
    (hne : a ≠ reciprocalPolynomial a) (hεe : ε = e + e')
    (basis : Module.Basis (Fin m) (AdjoinRoot a)
      (primaryComponent (toLinEquiv ι K b).toLinearMap a))
    {σ : K ≃+* K} {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (toLinEquiv ι K b v) = toLinEquiv ι K b (S v))
    (haσ : a.map (σ : K →+* K) = a)
    {g g' : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)}
    (hgg' : ∀ v, toLinEquiv ι K ((g' : StatedOmega ⇑Φ) : GL ι K) v =
      S (toLinEquiv ι K ((g : StatedOmega ⇑Φ) : GL ι K) (S.symm v))) :
    glBlockCentralizerEquivPrimaryGL Φ hΦ h8 b hx hodd ha hae ha'e hne hεe basis g' =
      semMatUnit basis (semilinRestrict hS hSx haσ) (semilinRestrict_smul hS hSx haσ) *
        Matrix.GeneralLinearGroup.map ((extAut a σ haσ) : AdjoinRoot a →+* AdjoinRoot a)
          (glBlockCentralizerEquivPrimaryGL Φ hΦ h8 b hx hodd ha hae ha'e hne hεe basis g) *
        (semMatUnit basis (semilinRestrict hS hSx haσ) (semilinRestrict_smul hS hSx haσ))⁻¹ := by
  exact pairedBlockCoordEquiv_square hx ha hne basis hS hSx haσ
    (g := glBlockCentralizerEquivSupportedBlock_linear Φ hΦ h8 b hx hodd ha hae ha'e hne hεe g)
    (g' := glBlockCentralizerEquivSupportedBlock_linear Φ hΦ h8 b hx hodd ha hae ha'e hne hεe g')
    (fun v => by simpa only [glBlockCentralizerEquivSupportedBlock_linear_apply] using hgg' v)

end ActualBlock

section NegativeMarking

theorem kgFieldRestriction_linearBlock_of_semilinear_congr
    {X H : Type} [Group X] [Group H] {F : Subgroup H} {C : Subgroup H}
    {m : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (e : ↥F ≃* GL (Fin m) E) (hC : CFSG.Assembly.IsComponentOf C F)
    (θ : X ≃* ↥C) (fX : MulAut X) (fC : MulAut ↥C)
    (hθ : ∀ x : X, θ (fX x) = fC (θ x))
    (B : GL (Fin m) E) (τ : E ≃+* E) (hτ : τ ≠ 1)
    (hsq : ∀ c : ↥C,
      (e ⟨fC c, hC.1 (fC c).2⟩ : GL (Fin m) E) =
        B * Matrix.GeneralLinearGroup.map τ.toRingHom (e ⟨c, hC.1 c.2⟩) * B⁻¹) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ' => kgInducedAut θ' fX ∉ I := by
  apply kgFieldRestriction_of_oneMarking_congr θ fX fC hθ
  refine largeEvenMarking_mono ?_
    (largeEvenMarking_linearBlock_of_semilinear e hC fC B τ hτ hsq)
  intro lab R _ I F' θ' hneg
  rintro ⟨φ, hφ, hind⟩
  apply hneg
  refine ⟨φ, hφ, ?_⟩
  intro c c' hcc'
  exact hind c c' hcc'.symm

section ActualPairedBlockRestriction

open CFSG.Open (StatedOmega)
open CFSG.ClassicalGroups.Orthogonal
open CFSG.StandardType.ClassicalPosition

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]

theorem kgFieldRestriction_orthogonalPairedBlock_of_semilinear
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e e' : Matrix ι ι K} {a : K[X]} [Fact (Irreducible a)] {m : ℕ}
    (hx : OddOrderIsometry Φ (orderOf b) (toLinEquiv ι K b))
    (hodd : Odd (orderOf b))
    (ha : a ∈ primaryFactors (toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (toLinEquiv ι K b).toLinearMap a)
    (ha'e : Matrix.toLinAlgEquiv' e' =
      primaryProjection (toLinEquiv ι K b).toLinearMap (reciprocalPolynomial a))
    (hne : a ≠ reciprocalPolynomial a) (hεe : ε = e + e')
    (basis : Module.Basis (Fin m) (AdjoinRoot a)
      (primaryComponent (toLinEquiv ι K b).toLinearMap a))
    {σ : K ≃+* K} {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (toLinEquiv ι K b v) = toLinEquiv ι K b (S v))
    (haσ : a.map (σ : K →+* K) = a) (hσ : σ ≠ 1)
    (C : Subgroup (StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C
      (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (fC : MulAut ↥C)
    (hfC : ∀ c : ↥C, ∀ v : ι → K,
      toLinEquiv ι K (((fC c : ↥C) : StatedOmega ⇑Φ) : GL ι K) v =
        S (toLinEquiv ι K (((c : ↥C) : StatedOmega ⇑Φ) : GL ι K) (S.symm v))) :
    GGMarkingAll (K := ↥C) fun _ _ _ I _ θ' => kgInducedAut θ' fC ∉ I := by
  haveI : Finite (AdjoinRoot a) := finite_adjoinRoot_of_fact a
  haveI : CharP (AdjoinRoot a) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot a)).injective 2
  let τ : AdjoinRoot a ≃+* AdjoinRoot a := extAut a σ haσ
  have hτext : ∀ c : K, τ (AdjoinRoot.of a c) = AdjoinRoot.of a (σ c) :=
    fun c => extAut_of haσ c
  have hτ : τ ≠ 1 := by
    intro h
    exact hσ ((extAut_eq_one_iff (g := a) haσ).mp h)
  let B : GL (Fin m) (AdjoinRoot a) :=
    semMatUnit basis (semilinRestrict hS hSx haσ) (semilinRestrict_smul hS hSx haσ)
  have hsq : ∀ c : ↥C,
      ((glBlockCentralizerEquivPrimaryGL Φ hΦ h8 b hx hodd ha hae ha'e hne hεe basis)
        ⟨fC c, hC.1 (fC c).2⟩ : GL (Fin m) (AdjoinRoot a)) =
      B * Matrix.GeneralLinearGroup.map τ.toRingHom
        ((glBlockCentralizerEquivPrimaryGL Φ hΦ h8 b hx hodd ha hae ha'e hne hεe basis)
          ⟨c, hC.1 c.2⟩) * B⁻¹ := by
    intro c
    exact glBlockCentralizerEquivPrimaryGL_square Φ hΦ h8 b hx hodd ha hae ha'e hne hεe basis
      hS hSx haσ
      (g := ⟨c, hC.1 c.2⟩) (g' := ⟨fC c, hC.1 (fC c).2⟩)
      (fun v => hfC c v)
  exact kgFieldRestriction_linearBlock_of_semilinear_congr
    (X := ↥C) (H := StatedOmega ⇑Φ)
    (F := glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)
    (C := C)
    (glBlockCentralizerEquivPrimaryGL Φ hΦ h8 b hx hodd ha hae ha'e hne hεe basis)
    hC (MulEquiv.refl ↥C) fC fC (fun x => rfl) B τ hτ hsq

end ActualPairedBlockRestriction

section ActualSelfDualUnitaryBlockRestriction

open CFSG.Assembly

private theorem unitaryTwo_statedAction_allMarkings_congr
    {E : Type} [Field E] [Finite E] [CharP E 2] {t Q : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 t E) (hQ : Q = 2 ^ t)
    {X : Type} [Group X] (e : X ≃* ↥(CFSG.Open.StatedSU 2 Q E))
    (fX : MulAut X) (g : MulAut ↥(CFSG.Open.StatedSU 2 Q E))
    (he : ∀ x : X, e (fX x) = g (e x))
    {B : GL (Fin 2) E} (hB : B ∈ GUFull 2 Q E) {τ : E ≃+* E}
    (hpoint : ∀ y : ↥(CFSG.Open.StatedSU 2 Q E), (g y : GL (Fin 2) E) =
      B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
        (y : GL (Fin 2) E) * B⁻¹)
    (z : hU.fixedField) (hz : τ (z : E) ≠ (z : E)) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ => kgInducedAut θ fX ∉ I := by
  have hSU : CFSG.Open.StatedSU 2 Q E = LargeEvenSUGroup (Fin 2) E (2 ^ t) := by
    rw [hQ]
    exact (largeEvenSUGroup_eq_statedSU 2 (2 ^ t)).symm
  let η := MulEquiv.subgroupCongr hSU
  let gRaw : MulAut ↥(LargeEvenSUGroup (Fin 2) E (2 ^ t)) := MulAut.congr η g
  have hη : ∀ y, η (g y) = gRaw (η y) := by
    intro y
    simp only [gRaw, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have heRaw : ∀ x : X, (e.trans η) (fX x) = gRaw ((e.trans η) x) := by
    intro x
    exact (congrArg η (he x)).trans (hη (e x))
  have hpointRaw : ∀ y : ↥(LargeEvenSUGroup (Fin 2) E (2 ^ t)),
      (gRaw y : GL (Fin 2) E) =
        B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ (y : GL (Fin 2) E) * B⁻¹ := by
    intro y
    change (g (η.symm y) : GL (Fin 2) E) = _
    exact hpoint (η.symm y)
  have hBraw : B ∈ LargeEvenGUSet (Fin 2) E (2 ^ t) := by
    rw [← hQ]
    exact CFSG.StandardType.guFull_subset_guSet hU hQ hB
  exact CFSG.StandardType.unitaryTwo_fieldAction_allMarkings_congr
    hU (e.trans η) fX gRaw heRaw hBraw hpointRaw z hz

open CFSG.Open (StatedOmega StatedSU)
open CFSG.ClassicalGroups.Orthogonal
open CFSG.StandardType.ClassicalPosition

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]

theorem kgFieldRestriction_orthogonalSelfDualBlock_of_semilinear
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e : Matrix ι ι K} {a : K[X]} [Fact (Irreducible a)]
    (hx : OddOrderIsometry Φ (orderOf b) (toLinEquiv ι K b))
    (hodd : Odd (orderOf b))
    (ha : a ∈ primaryFactors (toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (toLinEquiv ι K b).toLinearMap a)
    (hself : a = reciprocalPolynomial a) (hne1 : a ≠ X - 1) (hεe : ε = e)
    {σ : K ≃+* K} {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (toLinEquiv ι K b v) = toLinEquiv ι K b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v))
    (haσ : a.map (σ : K →+* K) = a) (hσ : σ ≠ 1)
    (C : Subgroup (StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C
      (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (fC : MulAut ↥C)
    (hfC : ∀ c : ↥C, ∀ v : ι → K,
      toLinEquiv ι K (((fC c : ↥C) : StatedOmega ⇑Φ) : GL ι K) v =
        S (toLinEquiv ι K (((c : ↥C) : StatedOmega ⇑Φ) : GL ι K) (S.symm v))) :
    GGMarkingAll (K := ↥C) fun _ _ _ I _ θ' => kgInducedAut θ' fC ∉ I := by
  classical
  let x : (ι → K) ≃ₗ[K] (ι → K) := toLinEquiv ι K b
  have hx' : OddOrderIsometry Φ (orderOf b) x := hx
  haveI : Finite (AdjoinRoot a) := finite_adjoinRoot_of_fact a
  haveI : CharP (AdjoinRoot a) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot a)).injective 2
  obtain ⟨d, m, ℓ, f, hU, basis, eSB, B, τ, hd1, hq, hcardE, hd, hdim, hdeg,
    hbarK, hbar, hτeq, hsquare, hτne, hfixed⟩ :=
    exists_selfDual_supportedBlock_unitary_action (Q := Φ) (x := x) hx hodd ha hne1 hself
      hS hSx hSQ hσ haσ
  let F : Subgroup (StatedOmega ⇑Φ) :=
    glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε
  let eMap : ↥F ≃* ↥(supportedBlock Φ x a) :=
    glBlockCentralizerEquivSupportedBlock_selfDual Φ hΦ h8 b hx hodd ha hae hself hne1 hεe
  let eFull : ↥F ≃* ↥(GUFull m (Nat.card K ^ d) (AdjoinRoot a)) := eMap.trans eSB
  let fMap : ↥F →* GL (Fin m) (AdjoinRoot a) :=
    (GUFull m (Nat.card K ^ d) (AdjoinRoot a)).subtype.comp eFull.toMonoidHom
  have hfMap_inj : Function.Injective fMap := by
    intro u v huv
    exact eFull.injective (Subtype.ext huv)
  have hfMap_range : fMap.range = GUFull m (Nat.card K ^ d) (AdjoinRoot a) := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact (eFull u).2
    · intro hg
      refine ⟨eFull.symm ⟨g, hg⟩, ?_⟩
      simp [fMap]
  let C_F : Subgroup ↥F := C.subgroupOf F
  have hC_F : CFSG.Assembly.IsComponentOf C_F ⊤ := by
    have hmapC : C_F.map F.subtype = C := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hC.1]
    have hmapTop : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hcomp : CFSG.Assembly.IsComponentOf (C_F.map F.subtype)
        ((⊤ : Subgroup ↥F).map F.subtype) := by
      simpa [hmapC, hmapTop] using hC
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := F.subtype) F.subtype_injective).1 hcomp
  let C' : Subgroup (GL (Fin m) (AdjoinRoot a)) := C_F.map fMap
  have hC' : CFSG.Assembly.IsComponentOf C' (GUFull m (Nat.card K ^ d) (AdjoinRoot a)) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
      hC_F fMap hfMap_inj
    simpa [C', Subgroup.map_top, hfMap_range] using h
  have hC'eq : C' = StatedSU m (Nat.card K ^ d) (AdjoinRoot a) :=
    CFSG.StandardType.eq_statedSU_of_isComponentOf_unitaryFull hcardE hC'
  let eCF : ↥C ≃* ↥C_F := (Subgroup.subgroupOfEquivOfLe hC.1).symm
  let eCmap : ↥C_F ≃* ↥C' := Subgroup.equivMapOfInjective C_F fMap hfMap_inj
  let eC : ↥C ≃* ↥(StatedSU m (Nat.card K ^ d) (AdjoinRoot a)) :=
    eCF.trans (eCmap.trans (MulEquiv.subgroupCongr hC'eq))
  have heC_coe : ∀ c : ↥C,
      (eC c : GL (Fin m) (AdjoinRoot a)) =
        (eSB (eMap ⟨c, hC.1 c.2⟩) : GL (Fin m) (AdjoinRoot a)) := by
    intro c
    rfl
  have hsquareC : ∀ c : ↥C,
      (eSB (eMap ⟨fC c, hC.1 (fC c).2⟩) : GL (Fin m) (AdjoinRoot a)) =
        (B : GL (Fin m) (AdjoinRoot a)) *
          Matrix.GeneralLinearGroup.map (τ : AdjoinRoot a →+* AdjoinRoot a)
            (eSB (eMap ⟨c, hC.1 c.2⟩)) *
          (B : GL (Fin m) (AdjoinRoot a))⁻¹ := by
    intro c
    refine hsquare (eMap ⟨c, hC.1 c.2⟩) (eMap ⟨fC c, hC.1 (fC c).2⟩) ?_
    intro v
    rw [glBlockCentralizerEquivSupportedBlock_selfDual_apply,
      glBlockCentralizerEquivSupportedBlock_selfDual_apply]
    exact hfC c v
  let fSU : MulAut ↥(StatedSU m (Nat.card K ^ d) (AdjoinRoot a)) := MulAut.congr eC fC
  have hpoint : ∀ y : ↥(StatedSU m (Nat.card K ^ d) (AdjoinRoot a)),
      (fSU y : GL (Fin m) (AdjoinRoot a)) =
        (B : GL (Fin m) (AdjoinRoot a)) *
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
            (y : GL (Fin m) (AdjoinRoot a)) *
          (B : GL (Fin m) (AdjoinRoot a))⁻¹ := by
    intro y
    let c : ↥C := eC.symm y
    have hy : eC c = y := eC.apply_symm_apply y
    have h := hsquareC c
    have hgl : Matrix.GeneralLinearGroup.map (τ : AdjoinRoot a →+* AdjoinRoot a)
        (eSB (eMap ⟨c, hC.1 c.2⟩)) =
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
          (eSB (eMap ⟨c, hC.1 c.2⟩) : GL (Fin m) (AdjoinRoot a)) := by
      apply Units.ext
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
      rfl
    rw [hgl] at h
    have hc : eC.symm y = c := by rw [← hy, eC.symm_apply_apply]
    have hfSU : fSU y = eC (fC c) := by
      simp [fSU, hc]
    have hcGL : (eSB (eMap ⟨c, hC.1 c.2⟩) : GL (Fin m) (AdjoinRoot a)) =
        (y : GL (Fin m) (AdjoinRoot a)) := by
      rw [← heC_coe c]
      exact congrArg Subtype.val hy
    rw [hfSU]
    rw [hcGL] at h
    simpa [heC_coe] using h
  have hm2 : 2 ≤ m := by
    have hq : CFSG.Assembly.IsQuasisimple
        (StatedSU m (Nat.card K ^ d) (AdjoinRoot a)) := by
      rw [← hC'eq]
      exact hC'.2.2
    exact CFSG.LieType.SemisimpleCentralizers.OrderThree.two_le_of_isQuasisimple_statedSU hq
  by_cases hm : m = 2
  · subst m
    have hℓ : ℓ = 2 := CharP.eq (AdjoinRoot a) hU.charP ‹CharP (AdjoinRoot a) 2›
    let hU2 : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (f * d)
        (AdjoinRoot a) := by
      simpa [hℓ] using hU
    have hQeq : Nat.card K ^ d = 2 ^ (f * d) := by
      rw [hq, hℓ, pow_mul]
    have hzexists : ∃ z : ↥(CFSG.RankThree.PartOne.KCOrthogonal.fixedSubfield K
        (AdjoinRoot a) d), τ (z : AdjoinRoot a) ≠ (z : AdjoinRoot a) := by
      by_contra h
      push Not at h
      apply hfixed
      ext z
      exact h z
    obtain ⟨z0, hz0⟩ := hzexists
    have hzmem : (z0 : AdjoinRoot a) ∈ hU2.fixedField := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_fixedField, hU2.bar_apply,
        ← hQeq]
      exact (CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSubfield K (AdjoinRoot a) d
        (z0 : AdjoinRoot a)).1 z0.2
    let z : hU2.fixedField := ⟨z0, hzmem⟩
    have hz : τ (z : AdjoinRoot a) ≠ (z : AdjoinRoot a) := hz0
    exact unitaryTwo_statedAction_allMarkings_congr hU2 hQeq eC fC fSU
      (fun x => by simp only [fSU, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]) B.2 hpoint z hz
  · have hm3 : 3 ≤ m := by omega
    have h32 : (m, Nat.card K ^ d) ≠ (3, 2) := by
      intro h32pair
      have hm3eq : m = 3 := congrArg Prod.fst h32pair
      have hQ2 : Nat.card K ^ d = 2 := congrArg Prod.snd h32pair
      subst m
      have hE4 : Nat.card (AdjoinRoot a) = 2 ^ 2 := by
        rw [hcardE, hQ2]
      have hQ2' : Fintype.card K ^ d = 2 := by
        simpa only [Nat.card_eq_fintype_card] using hQ2
      have hSU : C' = StatedSU 3 2 (AdjoinRoot a) := by
        simpa only [Nat.card_eq_fintype_card, hQ2'] using hC'eq
      exact CFSG.StandardType.ResU3Three.not_isSolvable_of_isQuasisimple
        (hSU ▸ hC'.2.2) (CFSG.StandardType.isSolvable_statedSU_three_two hE4)

    exact CFSG.StandardType.kgFieldRestriction_of_oneMarking_congr eC fC fSU
      (fun x => by simp [fSU])
      (CFSG.StandardType.largeEvenMarking_oneMarking_statedSU_of_fieldAction
        hcardE hm3 h32 fSU B.2 hpoint hτne)

end ActualSelfDualUnitaryBlockRestriction

end NegativeMarking

end CFSG.StandardType.ClassicalBlocks
