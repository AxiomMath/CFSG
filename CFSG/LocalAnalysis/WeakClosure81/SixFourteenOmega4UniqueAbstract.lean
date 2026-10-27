module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenOmega4TransvectionUnique
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN3MovedContradiction
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Omega4Plus
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Defs
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Surv14
public import CFSG.Quasithin.Vol2.Ch9H11Holds
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion
public import CFSG.Quasithin.Background.SmithD37Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Inputs
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.ASVolI.ChH
open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCRootAxis
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open CFSG.Quasithin.G11 CFSG.Quasithin.H13.H11P
open scoped Matrix

local notation "F₄" => GaloisField 2 2
local notation "M₄" => Matrix (Fin 2) (Fin 2) F₄

attribute [local instance] Fintype.ofFinite

abbrev moduleAdditiveSubgroup {W : Type} [CommGroup W] (U : Subgroup W)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) : Module (ZMod 2) (Additive ↥U) :=
  AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    show ((Additive.toMul x : ↥U) : W) * ((Additive.toMul x : ↥U) : W) = 1
    simpa [pow_two] using hU2 ((Additive.toMul x : ↥U) : W) (Additive.toMul x).2)

def restrictMulAut {W : Type} [CommGroup W] {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) (y : ↥Y) : MulAut ↥U where
  toFun u := ⟨(y : MulAut W) (u : W), hYU (y : MulAut W) y.2 u u.2⟩
  invFun u := ⟨(y : MulAut W)⁻¹ (u : W), hYU (y : MulAut W)⁻¹ (Y.inv_mem y.2) u u.2⟩
  left_inv u := Subtype.ext (by
    simp)
  right_inv u := Subtype.ext (by
    simp)
  map_mul' u v := Subtype.ext (map_mul (y : MulAut W) (u : W) (v : W))

def restrictActionHom {W : Type} [CommGroup W] {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U)
    [Module (ZMod 2) (Additive ↥U)] : ↥Y →* GLV (Additive ↥U) where
  toFun y :=
    (MulEquiv.toAdditive (restrictMulAut hYU y)).toLinearEquiv
      (fun c x => ZMod.map_smul (MulEquiv.toAdditive (restrictMulAut hYU y)) c x)
  map_one' := by
    ext x
    simp [restrictMulAut]
  map_mul' y z := by
    ext x
    simp [restrictMulAut, MulAut.mul_apply]

theorem restrictActionHom_injective {W : Type} [CommGroup W] [Finite W]
    {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hNat : NatTensor Y U ⊥ 2 2) (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U)
    [Module (ZMod 2) (Additive ↥U)] :
    Function.Injective (restrictActionHom hYU) := by
  intro y z h
  have hyz : (y : MulAut W) * (z : MulAut W)⁻¹ = 1 := by
    apply eq_one_of_fix_of_natTensor hNat (Y.mul_mem y.2 (Y.inv_mem z.2))
    intro u hu
    have hz : (z : MulAut W)⁻¹ u ∈ U := hYU (z : MulAut W)⁻¹ (Y.inv_mem z.2) u hu
    have h' := congrArg
      (fun φ : GLV (Additive ↥U) => φ (Additive.ofMul (⟨(z : MulAut W)⁻¹ u, hz⟩ : ↥U))) h
    have hres : restrictMulAut hYU y ⟨(z : MulAut W)⁻¹ u, hz⟩ =
        restrictMulAut hYU z ⟨(z : MulAut W)⁻¹ u, hz⟩ := by
      apply Additive.ofMul.injective
      simpa [restrictActionHom] using h'
    have hcoe := congrArg (fun a : ↥U => (a : W)) hres
    simp [restrictMulAut] at hcoe
    show (y : MulAut W) ((z : MulAut W)⁻¹ u) = u
    simpa using hcoe
  exact Subtype.ext (mul_inv_eq_one.mp hyz)

theorem inv_mem_of_forall_mem {W : Type} [CommGroup W] [Finite W] {U : Subgroup W}
    (e : MulAut W) (he : ∀ u ∈ U, e u ∈ U) : ∀ u ∈ U, e⁻¹ u ∈ U := by
  have hfin : Finite ↥U := Subtype.finite
  have hinj : Function.Injective (fun u : ↥U => (⟨e (u : W), he (u : W) u.2⟩ : ↥U)) := by
    intro u v huv
    exact Subtype.ext (e.injective (congrArg Subtype.val huv))
  have hsurj : Function.Surjective (fun u : ↥U => (⟨e (u : W), he (u : W) u.2⟩ : ↥U)) :=
    Finite.surjective_of_injective hinj
  intro u hu
  obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
  have hvu : e (v : W) = u := congrArg Subtype.val hv
  rw [← hvu]
  simp

def restrictMulAutOf {W : Type} [CommGroup W] [Finite W] {U : Subgroup W}
    (e : MulAut W) (he : ∀ u ∈ U, e u ∈ U) : MulAut ↥U where
  toFun u := ⟨e (u : W), he (u : W) u.2⟩
  invFun u := ⟨e⁻¹ (u : W), inv_mem_of_forall_mem e he (u : W) u.2⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (map_mul e (u : W) (v : W))

def restrictLinearOf {W : Type} [CommGroup W] [Finite W] {U : Subgroup W}
    (e : MulAut W) (he : ∀ u ∈ U, e u ∈ U)
    [Module (ZMod 2) (Additive ↥U)] : GLV (Additive ↥U) :=
  (MulEquiv.toAdditive (restrictMulAutOf e he)).toLinearEquiv
    (fun c x => ZMod.map_smul (MulEquiv.toAdditive (restrictMulAutOf e he)) c x)

lemma restrictLinearOf_ofMul {W : Type} [CommGroup W] [Finite W] {U : Subgroup W}
    [Module (ZMod 2) (Additive ↥U)] {e : MulAut W} (he : ∀ u ∈ U, e u ∈ U) (u : ↥U) :
    restrictLinearOf e he (Additive.ofMul u) =
      Additive.ofMul ⟨e (u : W), he (u : W) u.2⟩ := by
  simp [restrictLinearOf, restrictMulAutOf]

lemma mem_conj_of_map_conj_eq {W : Type} [CommGroup W] {Y : Subgroup (MulAut W)}
    {e : MulAut W} (heN : Y.map (MulAut.conj e).toMonoidHom = Y) {y : MulAut W}
    (hy : y ∈ Y) : e * y * e⁻¹ ∈ Y := by
  have h : (MulAut.conj e) y ∈ Y.map (MulAut.conj e).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  rw [heN] at h
  simpa [MulAut.conj_apply] using h

lemma restrictMulAut_conj
    {W : Type} [CommGroup W] [Finite W] {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) {e : MulAut W}
    (heN : Y.map (MulAut.conj e).toMonoidHom = Y) (heU : ∀ u ∈ U, e u ∈ U) (y : ↥Y) :
    restrictMulAutOf e heU * restrictMulAut hYU y * (restrictMulAutOf e heU)⁻¹ =
      restrictMulAut hYU ⟨e * (y : MulAut W) * e⁻¹,
        mem_conj_of_map_conj_eq heN y.2⟩ := by
  ext u
  simp [restrictMulAutOf, restrictMulAut, MulAut.mul_apply]

lemma restrictLinearOf_conj
    {W : Type} [CommGroup W] [Finite W] {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) {e : MulAut W}
    (heN : Y.map (MulAut.conj e).toMonoidHom = Y) (heU : ∀ u ∈ U, e u ∈ U) (y : ↥Y)
    [Module (ZMod 2) (Additive ↥U)] :
    restrictLinearOf e heU * restrictActionHom hYU y * (restrictLinearOf e heU)⁻¹ =
      restrictActionHom hYU ⟨e * (y : MulAut W) * e⁻¹,
        mem_conj_of_map_conj_eq heN y.2⟩ := by
  ext v
  have h := congrArg (fun φ : MulAut ↥U => φ (Additive.toMul v))
    (restrictMulAut_conj hYU heN heU y)
  simpa [restrictLinearOf, restrictActionHom, MulAut.mul_apply] using h

theorem restrictLinearOf_mem_normalizer
    {W : Type} [CommGroup W] [Finite W] {Y : Subgroup (MulAut W)} {U : Subgroup W}
    [Module (ZMod 2) (Additive ↥U)]
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U)
    (H : Subgroup (GLV (Additive ↥U))) (hHY : H = (restrictActionHom hYU).range)
    {e : MulAut W} (heN : Y.map (MulAut.conj e).toMonoidHom = Y)
    (heU : ∀ u ∈ U, e u ∈ U) :
    restrictLinearOf e heU ∈ Subgroup.normalizer (H : Set (GLV (Additive ↥U))) := by
  have heNorm : e ∈ Subgroup.normalizer (Y : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heN
  have heNinv : Y.map (MulAut.conj e⁻¹).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ heNorm)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hHY]
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨y, rfl⟩ := hh
    change restrictLinearOf e heU * restrictActionHom hYU y *
      (restrictLinearOf e heU)⁻¹ ∈ (restrictActionHom hYU).range
    rw [restrictLinearOf_conj hYU heN heU y]
    exact ⟨⟨e * (y : MulAut W) * e⁻¹, mem_conj_of_map_conj_eq heN y.2⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hmem : e⁻¹ * (y : MulAut W) * e ∈ Y :=
      mem_conj_of_map_conj_eq heNinv y.2
    refine (Subgroup.mem_map (f := (MulAut.conj (restrictLinearOf e heU)).toMonoidHom)
      (K := (restrictActionHom hYU).range)).mpr ?_
    have hconj : (MulEquiv.toMonoidHom (MulAut.conj (restrictLinearOf e heU)))
        (restrictActionHom hYU ⟨e⁻¹ * (y : MulAut W) * e, hmem⟩) =
        restrictActionHom hYU y := by
      simpa [MulAut.conj_apply, mul_assoc] using restrictLinearOf_conj hYU heN heU
        (⟨e⁻¹ * (y : MulAut W) * e, hmem⟩ : ↥Y)
    exact ⟨restrictActionHom hYU ⟨e⁻¹ * (y : MulAut W) * e, hmem⟩,
      ⟨⟨e⁻¹ * (y : MulAut W) * e, hmem⟩, rfl⟩, hconj⟩

theorem exists_tensorCoord_of_natTensor
    {W : Type} [CommGroup W] {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hNat : NatTensor Y U ⊥ 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_hK : Nat.card K = 4)
      (β : ↥U →* Multiplicative (Matrix (Fin 2) (Fin 2) K)),
      Function.Bijective β ∧
      ∃ (π : (FFModel.tensorNat 2 K).Gam →* ↥Y),
        Function.Bijective π ∧
        ∀ (γ : (FFModel.tensorNat 2 K).Gam) (u : ↥U)
          (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ U),
          β ⟨((π γ : ↥Y) : MulAut W) (u : W), hu⟩ = tensorAct 2 K γ (β u) := by
  obtain ⟨K, hKfield, hKfinite, hKcard, π, hVia⟩ := hNat
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord (D := FFModel.tensorNat 2 K) rfl rfl hVia
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hKcard])
  have hπinj : Function.Injective π :=
    hVia.injective_of_faithful_on (tensorNat_two_faithful K)
  refine ⟨K, hKfield, hKfinite, ?_, β, ⟨hβinj, hβs⟩, π, ⟨hπinj, hVia.1⟩, ?_⟩
  · rw [hKcard]
    norm_num
  · intro γ u hu
    exact hβe γ u hu

theorem isTensorModel_of_tensorCoord
    {W : Type} [CommGroup W] [Finite W] (hw2 : ∀ w, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hNat : NatTensor Y U ⊥ 2 2) (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U)
    {K : Type} [Field K] [Algebra (ZMod 2) K] [Finite K]
    {β : ↥U →* Multiplicative (Matrix (Fin 2) (Fin 2) K)}
    (hβ : Function.Bijective β)
    {π : (FFModel.tensorNat 2 K).Gam →* ↥Y} (hπ : Function.Bijective π)
    (hβe : ∀ (γ : (FFModel.tensorNat 2 K).Gam) (u : ↥U)
      (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ U),
      β ⟨((π γ : ↥Y) : MulAut W) (u : W), hu⟩ = tensorAct 2 K γ (β u)) :
    letI := moduleAdditiveSubgroup U (fun u _ => hw2 u)
    ∃ H : Subgroup (GLV (Additive ↥U)),
      H = (restrictActionHom hYU).range ∧ IsTensorModel 2 K H := by
  letI := moduleAdditiveSubgroup U (fun u _ => hw2 u)
  let ρ : ↥Y →* GLV (Additive ↥U) := restrictActionHom hYU
  let H : Subgroup (GLV (Additive ↥U)) := ρ.range
  have hρinj : Function.Injective ρ := restrictActionHom_injective hNat hYU
  let ρH : ↥Y ≃* ↥H := MulEquiv.ofBijective ρ.rangeRestrict
    ⟨fun a b h => hρinj (congrArg Subtype.val h), ρ.rangeRestrict_surjective⟩
  let eY : ↥Y ≃* (FFModel.tensorNat 2 K).Gam :=
    (MulEquiv.ofBijective π hπ).symm
  let βe : ↥U ≃* Multiplicative (Matrix (Fin 2) (Fin 2) K) :=
    MulEquiv.ofBijective β hβ
  let ψ : Additive ↥U ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K :=
    (MulEquiv.toAdditiveLeft βe).toLinearEquiv (fun c x => ZMod.map_smul _ c x)
  refine ⟨H, rfl, ⟨ρH.symm.trans eY, ψ, ?_⟩⟩
  intro h v
  let y : ↥Y := ρH.symm h
  have hyρ : ρ y = h := by
    change ((ρH (ρH.symm h) : ↥H) : GLV (Additive ↥U)) = (h : GLV (Additive ↥U))
    rw [ρH.apply_symm_apply]
  have hπγ : π (eY y) = y := by
    change π ((MulEquiv.ofBijective π hπ).symm y) = y
    exact (MulEquiv.ofBijective π hπ).apply_symm_apply y
  have hβe' : β ⟨(y : MulAut W) ((Additive.toMul (α := ↥U) v : ↥U) : W),
      hYU (y : MulAut W) y.2 (Additive.toMul (α := ↥U) v) (Additive.toMul (α := ↥U) v).2⟩ =
      tensorAct 2 K (eY y) (β (Additive.toMul (α := ↥U) v)) := by
    have h := hβe (eY y) (Additive.toMul (α := ↥U) v) (by
      rw [hπγ]
      exact hYU (y : MulAut W) y.2 (Additive.toMul (α := ↥U) v) (Additive.toMul (α := ↥U) v).2)
    simpa [hπγ] using h
  have hact : ((h : GLV (Additive ↥U)) v) =
      Additive.ofMul (restrictMulAut hYU y (Additive.toMul (α := ↥U) v)) := by
    have h1 := congrArg (fun φ : GLV (Additive ↥U) => φ v) hyρ
    exact h1.symm.trans rfl
  calc
    ψ ((h : GLV (Additive ↥U)) v)
        = Multiplicative.toAdd (β ⟨(y : MulAut W) ((Additive.toMul (α := ↥U) v : ↥U) : W),
            hYU (y : MulAut W) y.2 (Additive.toMul (α := ↥U) v)
              (Additive.toMul (α := ↥U) v).2⟩) := by
          rw [hact]
          rfl
    _ = Multiplicative.toAdd (tensorAct 2 K (eY y) (β (Additive.toMul (α := ↥U) v))) := by rw [hβe']
    _ = ((((ρH.symm.trans eY) h).1 : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) * ψ v *
          (((((ρH.symm.trans eY) h).2 : Matrix.GeneralLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K))ᵀ := by
          simp [tensorAct, ψ, βe, MulEquiv.toAdditiveLeft, y]

theorem exists_isTensorModel_two_four_of_natTensor
    {W : Type} [CommGroup W] [Finite W] (hw2 : ∀ w, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hNat : NatTensor Y U ⊥ 2 2) (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) :
    letI := moduleAdditiveSubgroup U (fun u _ => hw2 u)
    ∃ H : Subgroup (GLV (Additive ↥U)),
      H = (restrictActionHom hYU).range ∧ IsTensorModel 2 (GaloisField 2 2) H := by
  letI : Module (ZMod 2) (Additive ↥U) := moduleAdditiveSubgroup U (fun u _ => hw2 u)
  obtain ⟨K, hKfield, hKfinite, hKcard, β, hβ, π, hπ, hβe⟩ :=
    exists_tensorCoord_of_natTensor (W := W) (Y := Y) (U := U) hNat
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hKcard]
    rfl)
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨H, hHrange, hH⟩ := isTensorModel_of_tensorCoord hw2 hNat hYU hβ hπ hβe
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rw [hKcard, GaloisField.card 2 2 (by norm_num)]
    norm_num
  let σ : K ≃+* GaloisField 2 2 := FiniteField.ringEquivOfCardEq hcard
  exact ⟨H, hHrange, isTensorModel_of_ringEquiv σ hH⟩

def transportedAutHom {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ψ : V ≃ₗ[ZMod 2] M₄) : GLV V →* MulAut (VM F₄) :=
  (MulAut.congr (AddEquiv.toMultiplicative ψ.toAddEquiv)).toMonoidHom.comp
    (linToMulAut (ZMod 2) V)

lemma transportedAutHom_apply {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ψ : V ≃ₗ[ZMod 2] M₄) (g : GLV V) (x : M₄) :
    transportedAutHom ψ g (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (ψ (g (ψ.symm x))) := by
  rfl

theorem isTensorModel_map_transportedAutHom_eq_Lm
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Subgroup (GLV V)} {φ : ↥H ≃* ↥(StatedSL 2 F₄) × ↥(StatedSL 2 F₄)}
    {ψ : V ≃ₗ[ZMod 2] M₄}
    (hψ : ∀ (h : ↥H) (v : V),
      ψ ((h : GLV V) v) =
        (((φ h).1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * ψ v *
          ((((φ h).2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ) :
    H.map (transportedAutHom ψ) = Lm F₄ := by
  ext t
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨(slE F₄ (φ ⟨h, hh⟩).1, slE F₄ (φ ⟨h, hh⟩).2), ?_⟩
    apply MulEquiv.ext
    intro X
    rw [← ofAdd_toAdd X]
    rw [transportedAutHom_apply]
    have hX := hψ ⟨h, hh⟩ (ψ.symm (Multiplicative.toAdd X))
    rw [hX]
    simp [rho, tAct, slE, coe_slE, Matrix.mul_assoc]
  · rintro ⟨p, rfl⟩
    let h : ↥H := φ.symm ((slE F₄).symm p.1, (slE F₄).symm p.2)
    refine ⟨h, h.2, ?_⟩
    apply MulEquiv.ext
    intro X
    rw [← ofAdd_toAdd X]
    rw [transportedAutHom_apply]
    have hX := hψ h (ψ.symm (Multiplicative.toAdd X))
    have hφh : φ h = ((slE F₄).symm p.1, (slE F₄).symm p.2) := φ.apply_symm_apply _
    have h1 : (((φ h).1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) =
        ((p.1 : SL₂ F₄) : M₄) := by
      rw [hφh]
      simpa using (coe_slE ((slE F₄).symm p.1)).symm
    have h2 : (((φ h).2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) =
        ((p.2 : SL₂ F₄) : M₄) := by
      rw [hφh]
      simpa using (coe_slE ((slE F₄).symm p.2)).symm
    rw [hX, h1, h2]
    simp [rho, tAct, Matrix.mul_assoc, ψ.apply_symm_apply]

theorem transportedAutHom_mem_normalizer
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Subgroup (GLV V)} {ψ : V ≃ₗ[ZMod 2] M₄}
    (hHmap : H.map (transportedAutHom ψ) = Lm F₄)
    {g : GLV V} (hg : g ∈ Subgroup.normalizer (H : Set (GLV V))) :
    transportedAutHom ψ g ∈
      Subgroup.normalizer ((Lm F₄ : Subgroup (MulAut (VM F₄))) : Set (MulAut (VM F₄))) := by
  have hgmap : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hHmap]
  change (H.map (transportedAutHom ψ)).map
      (MulAut.conj (transportedAutHom ψ g)).toMonoidHom = H.map (transportedAutHom ψ)
  have hcomp : (MulAut.conj (transportedAutHom ψ g)).toMonoidHom.comp
        (transportedAutHom ψ) =
      (transportedAutHom ψ).comp (MulAut.conj g).toMonoidHom := by
    ext h
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hgmap, hHmap]

lemma linToMulAut_injective {V : Type} [AddCommGroup V] [Module (ZMod 2) V] :
    Function.Injective (linToMulAut (ZMod 2) V) := by
  intro g h gh
  ext v
  have h' : Multiplicative.ofAdd (g v) = Multiplicative.ofAdd (h v) := by
    have := congrArg (fun φ : MulAut (Multiplicative V) => φ (Multiplicative.ofAdd v)) gh
    simpa [linToMulAut, AddEquiv.toMultiplicative] using this
  exact Multiplicative.ofAdd.injective h' 

lemma transportedAutHom_injective {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ψ : V ≃ₗ[ZMod 2] M₄) : Function.Injective (transportedAutHom ψ) := by
  intro g h gh
  apply linToMulAut_injective
  exact (MulAut.congr (AddEquiv.toMultiplicative ψ.toAddEquiv)).injective (by
    simpa [transportedAutHom] using gh)

lemma restrictLinearOf_eq_on {W : Type} [CommGroup W] [Finite W] {U : Subgroup W}
    [Module (ZMod 2) (Additive ↥U)] {e f : MulAut W}
    (he : ∀ u ∈ U, e u ∈ U) (hf : ∀ u ∈ U, f u ∈ U)
    (h : restrictLinearOf e he = restrictLinearOf f hf) :
    ∀ u ∈ U, e u = f u := by
  intro u hu
  let uU : ↥U := ⟨u, hu⟩
  have h' := congrArg (fun g : GLV (Additive ↥U) => g (Additive.ofMul uU)) h
  have h'' : Additive.ofMul (e u) = Additive.ofMul (f u) := by
    simpa [restrictLinearOf, restrictMulAutOf] using h'
  exact Additive.ofMul.injective h''

theorem exists_tensorCoord_four_of_natTensor
    {W : Type} [CommGroup W] [Finite W] (hw2 : ∀ w, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hNat : NatTensor Y U ⊥ 2 2) (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) :
    letI := moduleAdditiveSubgroup U (fun u _ => hw2 u)
    ∃ (H : Subgroup (GLV (Additive ↥U)))
      (φ : ↥H ≃* ↥(StatedSL 2 F₄) × ↥(StatedSL 2 F₄))
      (ψ : Additive ↥U ≃ₗ[ZMod 2] M₄),
      H = (restrictActionHom hYU).range ∧
        ∀ (h : ↥H) (v : Additive ↥U),
          ψ ((h : GLV (Additive ↥U)) v) =
            (((φ h).1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * ψ v *
              ((((φ h).2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ := by
  letI : Module (ZMod 2) (Additive ↥U) := moduleAdditiveSubgroup U (fun u _ => hw2 u)
  obtain ⟨H, hHrange, hH⟩ := exists_isTensorModel_two_four_of_natTensor hw2 hNat hYU
  obtain ⟨φ, ψ, hψ⟩ := hH
  exact ⟨H, φ, ψ, hHrange, hψ⟩

end CFSG.LocalAnalysis.WeakClosure81

end

end
