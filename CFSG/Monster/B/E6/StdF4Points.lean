module

public import CFSG.Monster.B.E6.StdF4Orbits
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.Assembly.Subnormal
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6FieldExtensionResidueActions
public import CFSG.LieType.Chevalley.C2E6FirstResidueUnitarySix
public import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryPoints
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Monster.B.Geometry.ProductModel
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical
open scoped Pointwise

theorem conjOrbit_eq_of_mem {M : Type*} [Group M] {H : Subgroup M} {x y : M}
    (hy : y ∈ conjOrbit H x) : conjOrbit H y = conjOrbit H x := by
  obtain ⟨c, hc, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, mul_mem hd hc, by group⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c⁻¹, mul_mem hd (inv_mem hc), by group⟩

theorem mem_centralizer_conj_iff {M : Type*} [Group M] (g x c : M) :
    c ∈ Subgroup.centralizer {g * x * g⁻¹} ↔ g⁻¹ * c * g ∈ Subgroup.centralizer {x} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * c * g * x = g⁻¹ * (c * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * c) * g := by rw [h]
      _ = x * (g⁻¹ * c * g) := by group
  · intro h
    calc c * (g * x * g⁻¹) = g * ((g⁻¹ * c * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * c := by group

theorem conjOrbit_centralizer_conj {M : Type*} [Group M] (g x y : M) :
    conjOrbit (Subgroup.centralizer {g * x * g⁻¹}) (g * y * g⁻¹) =
      (fun z => g * z * g⁻¹) '' conjOrbit (Subgroup.centralizer {x}) y := by
  ext z
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨(g⁻¹ * c * g) * y * (g⁻¹ * c * g)⁻¹, ⟨_, (mem_centralizer_conj_iff g x c).1 hc, rfl⟩,
      by group⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨g * c * g⁻¹, (mem_centralizer_conj_iff g x _).2 (by group; exact hc), by group⟩

@[expose] def FiveOrbits {M : Type*} [Group M] (Ω : Set M) (p : M) : Prop :=
  ∃ q : Fin 5 → M, (∀ i, q i ∈ Ω) ∧
    (∀ y ∈ Ω, ∃ i, y ∈ conjOrbit (Subgroup.centralizer {p}) (q i)) ∧
    (∀ i, (conjOrbit (Subgroup.centralizer {p}) (q i)).ncard = repSize i) ∧
    ∀ i, ∀ y ∈ conjOrbit (Subgroup.centralizer {p}) (q i), orderOf (p * y) = repOrder i

theorem FiveOrbits.conj {M : Type*} [Group M] {Ω : Set M}
    (hΩ : ∀ g y, y ∈ Ω → g * y * g⁻¹ ∈ Ω) {p : M} (h : FiveOrbits Ω p) (g : M) :
    FiveOrbits Ω (g * p * g⁻¹) := by
  obtain ⟨q, hq, hcov, hsize, hord⟩ := h
  have hinj : Function.Injective (fun z : M => g * z * g⁻¹) := fun a b e => by
    simpa using e
  refine ⟨fun i => g * q i * g⁻¹, fun i => hΩ g _ (hq i), fun y hy => ?_, fun i => ?_,
    fun i y hy => ?_⟩
  · obtain ⟨i, hi⟩ := hcov (g⁻¹ * y * g⁻¹⁻¹) (hΩ g⁻¹ y hy)
    refine ⟨i, ?_⟩
    rw [conjOrbit_centralizer_conj]
    exact ⟨_, hi, by group⟩
  · rw [conjOrbit_centralizer_conj, Set.ncard_image_of_injective _ hinj, hsize]
  · rw [conjOrbit_centralizer_conj] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have e : g * p * g⁻¹ * (g * z * g⁻¹) = MulAut.conj g (p * z) := by
      rw [MulAut.conj_apply]
      group
    rw [e, MulEquiv.orderOf_eq, hord i z hz]

theorem repSize_injective : Function.Injective repSize := by decide

theorem FiveOrbits.ncard_orbits {M : Type*} [Group M] {Ω : Set M} {p : M}
    (h : FiveOrbits Ω p) :
    {O : Set M | ∃ y ∈ Ω, O = conjOrbit (Subgroup.centralizer {p}) y}.ncard = 5 := by
  obtain ⟨q, hq, hcov, hsize, -⟩ := h
  have hset : {O : Set M | ∃ y ∈ Ω, O = conjOrbit (Subgroup.centralizer {p}) y} =
      Set.range fun i => conjOrbit (Subgroup.centralizer {p}) (q i) := by
    ext O
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨i, hi⟩ := hcov y hy
      exact ⟨i, (conjOrbit_eq_of_mem hi).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨q i, hq i, rfl⟩
  have hinj : Function.Injective fun i => conjOrbit (Subgroup.centralizer {p}) (q i) :=
    fun i j e => repSize_injective (by rw [← hsize i, ← hsize j]; exact congrArg Set.ncard e)
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

abbrev rootClass :
    Set stdGroup := {x | IsConj rootInv x}

abbrev rootClassStar :
    Set GStar := {y | IsConj rootStar y}

theorem mem_rootClass_iff
    (x : stdGroup) : x ∈ rootClass ↔ ∃ g, rootMap g = x := isConj_iff

theorem fiveOrbits_rootInv :
    FiveOrbits rootClass rootInv := by
  refine ⟨repPoint, fun i => (mem_rootClass_iff _).2 ⟨_, rfl⟩, fun y hy => ?_, fun i => ?_,
    fun i y hy => ?_⟩
  · obtain ⟨g, rfl⟩ := (mem_rootClass_iff y).1 hy
    obtain ⟨i, hi⟩ := exists_repLevel g
    refine ⟨i, ?_⟩
    rw [centralizer_rootInv, repPoint, conjOrbit_PJ_rootMap, lev_repPoint, ← hi]
    exact rootMap_mem_levPoints g
  · rw [centralizer_rootInv, repPoint, conjOrbit_PJ_rootMap, lev_repPoint, ncard_levPoints]
  · rw [centralizer_rootInv, repPoint, conjOrbit_PJ_rootMap, lev_repPoint] at hy
    exact orderOf_rootInv_mul_of_mem_levPoints hy

theorem inl_injective :
    Function.Injective (SemidirectProduct.inl : stdGroup → GStar) :=
  SemidirectProduct.inl_injective

theorem mem_rootClassStar_iff
    (y : GStar) :
    y ∈ rootClassStar ↔ y ∈ SemidirectProduct.inl '' rootClass := by
  rw [rootClassStar, setOf_isConj_rootStar]

theorem fiveOrbits_rootStar :
    FiveOrbits rootClassStar rootStar := by
  refine ⟨fun i => SemidirectProduct.inl (repPoint i), fun i => ?_, fun y hy => ?_, fun i => ?_,
    fun i y hy => ?_⟩
  · rw [mem_rootClassStar_iff]
    exact ⟨_, (mem_rootClass_iff _).2 ⟨_, rfl⟩, rfl⟩
  · rw [mem_rootClassStar_iff] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨g, rfl⟩ := (mem_rootClass_iff x).1 hx
    obtain ⟨i, hi⟩ := exists_repLevel g
    refine ⟨i, ?_⟩
    dsimp only
    rw [centralizer_rootStar, repPoint, conjOrbit_parStar_rootMap, lev_repPoint, ← hi]
    exact ⟨_, rootMap_mem_levPoints g, rfl⟩
  · dsimp only
    rw [centralizer_rootStar, repPoint, conjOrbit_parStar_rootMap, lev_repPoint,
      Set.ncard_image_of_injective _ inl_injective, ncard_levPoints]
  · dsimp only at hy
    rw [centralizer_rootStar, repPoint, conjOrbit_parStar_rootMap, lev_repPoint] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [rootStar, ← map_mul, orderOf_injective _ inl_injective,
      orderOf_rootInv_mul_of_mem_levPoints hx]

theorem fiveOrbits_of_mem_rootClass
    {p : stdGroup} (hp : p ∈ rootClass) :
    FiveOrbits rootClass p := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hp
  refine fiveOrbits_rootInv.conj (fun g y hy => ?_) g
  exact hy.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem fiveOrbits_of_mem_rootClassStar
    {p : GStar} (hp : p ∈ rootClassStar) :
    FiveOrbits rootClassStar p := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hp
  refine fiveOrbits_rootStar.conj (fun g y hy => ?_) g
  exact hy.trans (isConj_iff.2 ⟨g, rfl⟩)

abbrev typeOneVertex :
    Type := Set.range (residue ncs stdDistance firstJ)

abbrev typeFourVertex :
    Set (Set stdChamber) :=
  Set.range (residue ncs stdDistance FourthResidue.fourthJ)

@[expose] def chamberRoot :
    stdChamber → stdGroup :=
  Quotient.lift rootMap fun a b hab => by
    have h : a⁻¹ * b ∈ stdBorelG := QuotientGroup.leftRel_apply.mp hab
    exact (rootMap_eq_rootMap_iff a b).2 (stdBorel_le_nativeParabolic firstJ h)

theorem chamberRoot_mk
    (g : stdGroup) : chamberRoot (g : stdChamber) = rootMap g := rfl

theorem chamberRoot_eq_iff
    (x y : stdChamber) :
    chamberRoot x = chamberRoot y ↔
      residue ncs stdDistance firstJ x = residue ncs stdDistance firstJ y := by
  induction x using QuotientGroup.induction_on with | H g => ?_
  induction y using QuotientGroup.induction_on with | H h => ?_
  rw [chamberRoot_mk, chamberRoot_mk, rootMap_eq_rootMap_iff, residue_mk_eq_iff]

@[expose] def vertexRoot
    (R : typeOneVertex) : stdGroup := chamberRoot R.2.choose

theorem vertexRoot_eq
    (R : typeOneVertex) {x : stdChamber}
    (hx : residue ncs stdDistance firstJ x = R.1) : vertexRoot R = chamberRoot x :=
  (chamberRoot_eq_iff _ _).2 (R.2.choose_spec.trans hx.symm)

theorem vertexRoot_mk
    (g : stdGroup) :
    vertexRoot ⟨residue ncs stdDistance firstJ (g : stdChamber), ⟨_, rfl⟩⟩ = g * rootInv * g⁻¹ :=
  (vertexRoot_eq (x := (g : stdChamber)) _ rfl).trans (chamberRoot_mk g)

theorem vertexRoot_injective :
    Function.Injective vertexRoot := by
  rintro ⟨R, x, rfl⟩ ⟨R', y, rfl⟩ h
  rw [vertexRoot_eq _ rfl, vertexRoot_eq _ rfl, chamberRoot_eq_iff] at h
  exact Subtype.ext h

theorem range_vertexRoot :
    Set.range vertexRoot = rootClass := by
  ext z
  rw [Set.mem_range, mem_rootClass_iff]
  constructor
  · rintro ⟨⟨R, x, rfl⟩, rfl⟩
    induction x using QuotientGroup.induction_on with | H g => ?_
    exact ⟨g, ((vertexRoot_eq (x := (g : stdChamber)) _ rfl).trans (chamberRoot_mk g)).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, vertexRoot_mk g⟩

@[expose] def vertexSmul
    (γ : GStar) (R : typeOneVertex) : typeOneVertex :=
  ⟨(γ • ·) '' R.1, by
    obtain ⟨x, hx⟩ := R.2
    rw [← hx, image_smul_residue]
    exact ⟨_, rfl⟩⟩

theorem vertexRoot_vertexSmul
    (γ : GStar) (R : typeOneVertex) :
    SemidirectProduct.inl (vertexRoot (vertexSmul γ R)) =
      γ * SemidirectProduct.inl (vertexRoot R) * γ⁻¹ := by
  obtain ⟨_, x, rfl⟩ := R
  have hx : (vertexSmul γ ⟨_, x, rfl⟩).1 = residue ncs stdDistance firstJ (γ • x) :=
    image_smul_residue γ firstJ x
  rw [vertexRoot_eq _ hx.symm, vertexRoot_eq _ rfl]
  induction x using QuotientGroup.induction_on with | H g => ?_
  rw [smul_mk, chamberRoot_mk, chamberRoot_mk, conj_inl, apply_rootMap_of_mem_betaGroup,
    rootMap_mul]

theorem vertexSmul_eq_iff
    (γ : GStar) (R : typeOneVertex) :
    vertexSmul γ R = R ↔ γ ∈ Subgroup.centralizer {SemidirectProduct.inl (vertexRoot R)} := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul, ← vertexRoot_vertexSmul,
    inl_injective.eq_iff, vertexRoot_injective.eq_iff]

theorem commute_iff_sq_eq_one {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1) :
    Commute a b ↔ (a * b) ^ 2 = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [pow_two]
  constructor
  · intro h
    rw [mul_assoc, ← mul_assoc b, ← h.eq, mul_assoc, hb, mul_one, ha]
  · intro h
    have e := eq_inv_of_mul_eq_one_left h
    rw [mul_inv_rev, ha', hb'] at e
    exact e

theorem rootMap_mul_self
    (g : stdGroup) : rootMap g * rootMap g = 1 := by
  rw [rootMap]
  calc g * rootInv * g⁻¹ * (g * rootInv * g⁻¹) = g * (rootInv * rootInv) * g⁻¹ := by group
    _ = 1 := by rw [rootInv_mul_self, mul_one, mul_inv_cancel]

theorem commute_rootInv_rootMap_iff
    (g : stdGroup) :
    Commute rootInv (rootMap g) ↔ lev g = 2 ∨ lev g = 1 ∨ lev g = 0 := by
  rw [commute_iff_sq_eq_one rootInv_mul_self (rootMap_mul_self g), ← orderOf_dvd_iff_pow_eq_one]
  obtain ⟨i, hi⟩ := exists_repLevel g
  have hmem : rootMap g ∈ levPoints (repLevel i) := hi ▸ rootMap_mem_levPoints g
  rw [orderOf_rootInv_mul_of_mem_levPoints hmem, hi]
  fin_cases i <;> decide

theorem commute_rootMap_iff
    (g h : stdGroup) :
    Commute (rootMap g) (rootMap h) ↔ Commute rootInv (rootMap (g⁻¹ * h)) := by
  have e1 : rootMap g = MulAut.conj g rootInv := by rw [rootMap, MulAut.conj_apply]
  have e2 : rootMap h = MulAut.conj g (rootMap (g⁻¹ * h)) := by
    rw [MulAut.conj_apply, rootMap_mul, rootMap]
    group
  rw [e1, e2, Commute, SemiconjBy, Commute, SemiconjBy, ← map_mul, ← map_mul]
  exact (MulAut.conj g).injective.eq_iff

theorem exists_typeFour_iff
    (g h : stdGroup) :
    (∃ S ∈ typeFourVertex, (residue ncs stdDistance firstJ (g : stdChamber) ∩ S).Nonempty ∧
      (residue ncs stdDistance firstJ (h : stdChamber) ∩ S).Nonempty) ↔
      ∃ p ∈ PJ, ∃ k ∈ PK, ∃ p' ∈ PJ, g⁻¹ * h = p * k * p' := by
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, ⟨y, hyR, hyS⟩, ⟨y', hyR', hyS'⟩⟩
    induction y using QuotientGroup.induction_on with | H a => ?_
    induction y' using QuotientGroup.induction_on with | H b => ?_
    rw [mem_residue_mk_iff] at hyR hyR'
    have hab : (b : stdChamber) ∈
        residue ncs stdDistance FourthResidue.fourthJ (a : stdChamber) := by
      rw [residue_eq_of_mem hδ hyS]
      exact hyS'
    rw [mem_residue_mk_iff] at hab
    refine ⟨g⁻¹ * a, hyR, a⁻¹ * b, hab, (h⁻¹ * b)⁻¹, inv_mem hyR', by group⟩
  · rintro ⟨p, hp, k, hk, p', hp', e⟩
    refine ⟨residue ncs stdDistance FourthResidue.fourthJ ((g * p : stdGroup) : stdChamber),
      ⟨_, rfl⟩, ⟨_, ?_, self_mem_residue _ _⟩, ⟨((g * p * k : stdGroup) : stdChamber), ?_, ?_⟩⟩
    · rw [mem_residue_mk_iff, inv_mul_cancel_left]
      exact hp
    · rw [mem_residue_mk_iff]
      have e' : h⁻¹ * (g * p * k) = p'⁻¹ := by
        have : h = g * (p * k * p') := by rw [← e, mul_inv_cancel_left]
        rw [this]
        group
      rw [e']
      exact inv_mem hp'
    · rw [mem_residue_mk_iff]
      have e' : (g * p)⁻¹ * (g * p * k) = k := by group
      rw [e']
      exact hk

theorem exists_typeFour_iff_commute
    (R R' : typeOneVertex) :
    (∃ S ∈ typeFourVertex, (R.1 ∩ S).Nonempty ∧ (R'.1 ∩ S).Nonempty) ↔
      Commute (vertexRoot R) (vertexRoot R') := by
  obtain ⟨_, x, rfl⟩ := R
  obtain ⟨_, y, rfl⟩ := R'
  induction x using QuotientGroup.induction_on with | H g => ?_
  induction y using QuotientGroup.induction_on with | H h => ?_
  rw [vertexRoot_eq _ rfl, vertexRoot_eq _ rfl, chamberRoot_mk, chamberRoot_mk,
    commute_rootMap_iff, commute_rootInv_rootMap_iff, ← mem_PJ_PK_PJ_iff]
  exact exists_typeFour_iff g h

theorem standard_F4_root_involution_point_geometry :
    (IsRoot Tag.E6 theta ∧ 0 < height theta ∧
      ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ∀ i, α i ≤ theta i) ∧
    ((rootInv : ModGL Tag.E6 K) = pinnedX Tag.E6 K theta 1 ∧ rootInv ≠ 1 ∧
      rootInv * rootInv = 1 ∧ betaG rootInv = rootInv) ∧
    Subgroup.centralizer {rootStar} = parStar firstJ ∧
    {y : GStar | IsConj rootStar y} =
      SemidirectProduct.inl '' {x : stdGroup | IsConj rootInv x} ∧
    (∀ g : stdGroup, residue ncs stdDistance firstJ (g : stdChamber) =
      (fun x : stdGroup => (x : stdChamber)) '' (g • (PJ : Set stdGroup))) ∧
    (∀ g : stdGroup, vertexRoot ⟨residue ncs stdDistance firstJ (g : stdChamber), ⟨_, rfl⟩⟩ =
      g * rootInv * g⁻¹) ∧
    Function.Injective vertexRoot ∧ Set.range vertexRoot = {x : stdGroup | IsConj rootInv x} ∧
    (∀ (γ : GStar) (R : typeOneVertex), SemidirectProduct.inl (vertexRoot (vertexSmul γ R)) =
      γ * SemidirectProduct.inl (vertexRoot R) * γ⁻¹) ∧
    (∀ (γ : GStar) (R : typeOneVertex), vertexSmul γ R = R ↔
      γ ∈ Subgroup.centralizer {SemidirectProduct.inl (vertexRoot R)}) ∧
    (∀ p : GStar, IsConj rootStar p →
      (∃ q : Fin 5 → GStar, (∀ i, IsConj rootStar (q i)) ∧
        (∀ y, IsConj rootStar y → ∃ i, y ∈ conjOrbit (Subgroup.centralizer {p}) (q i)) ∧
        (∀ i, (conjOrbit (Subgroup.centralizer {p}) (q i)).ncard =
          (![1, 1782, 44352, 1824768, 2097152] : Fin 5 → ℕ) i) ∧
        ∀ i, ∀ y ∈ conjOrbit (Subgroup.centralizer {p}) (q i),
          orderOf (p * y) = (![1, 2, 2, 4, 3] : Fin 5 → ℕ) i) ∧
      {O : Set GStar | ∃ y, IsConj rootStar y ∧
        O = conjOrbit (Subgroup.centralizer {p}) y}.ncard = 5) ∧
    (∀ p : stdGroup, IsConj rootInv p →
      (∃ q : Fin 5 → stdGroup, (∀ i, IsConj rootInv (q i)) ∧
        (∀ y, IsConj rootInv y → ∃ i, y ∈ conjOrbit (Subgroup.centralizer {p}) (q i)) ∧
        (∀ i, (conjOrbit (Subgroup.centralizer {p}) (q i)).ncard =
          (![1, 1782, 44352, 1824768, 2097152] : Fin 5 → ℕ) i) ∧
        ∀ i, ∀ y ∈ conjOrbit (Subgroup.centralizer {p}) (q i),
          orderOf (p * y) = (![1, 2, 2, 4, 3] : Fin 5 → ℕ) i) ∧
      {O : Set stdGroup | ∃ y, IsConj rootInv y ∧
        O = conjOrbit (Subgroup.centralizer {p}) y}.ncard = 5) ∧
    ∀ R R' : typeOneVertex,
      (∃ S ∈ typeFourVertex, (R.1 ∩ S).Nonempty ∧ (R'.1 ∩ S).Nonempty) ↔
        Commute (vertexRoot R) (vertexRoot R') := by
  refine ⟨⟨isRoot_theta, by rw [height_theta]; norm_num, fun α hα i => le_e6HighestRoot hα i⟩,
    ⟨rfl, rootInv_ne_one, rootInv_mul_self, betaG_rootInv⟩, centralizer_rootStar,
    setOf_isConj_rootStar, fun g => residue_stdDistance firstJ g, vertexRoot_mk,
    vertexRoot_injective, range_vertexRoot, vertexRoot_vertexSmul, vertexSmul_eq_iff,
    fun p hp => ?_, fun p hp => ?_, exists_typeFour_iff_commute⟩
  · have h := fiveOrbits_of_mem_rootClassStar hp
    exact ⟨h, h.ncard_orbits⟩
  · have h := fiveOrbits_of_mem_rootClass hp
    exact ⟨h, h.ncard_orbits⟩

end CFSG.Monster.B.E6.StdF4
