module

public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompFrame
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockPair
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestSUWit
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompParts
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDet

public section

namespace CFSG.StandardType

namespace NsFrameComp

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open scoped commutatorElement

section Hom

variable {f n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def toUnitHom :
    ↥(unitarySU 2 f K n) →* LinearMap.GeneralLinearGroup K (Fin n → K) where
  toFun := toUnit
  map_one' := Units.ext lin_one
  map_mul' g g' := Units.ext (lin_mul g g')

theorem coe_toUnitHom (g : ↥(unitarySU 2 f K n)) :
    ((toUnitHom g : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) =
      lin g := rfl

theorem toUnitHom_injective :
    Function.Injective (toUnitHom : ↥(unitarySU 2 f K n) →* _) := fun _ _ hgg' =>
  lin_injective (congrArg Units.val hgg')

theorem toUnitHom_commute_iff {g g' : ↥(unitarySU 2 f K n)} :
    Commute (toUnitHom g) (toUnitHom g') ↔ Commute g g' := by
  constructor
  · intro hc
    exact toUnitHom_injective (by rw [map_mul, map_mul, hc.eq])
  · intro hc
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hc.eq]

theorem toUnitHom_mem_sesqUnitaryGroup (h : UnitaryFieldData 2 f K) (g : ↥(unitarySU 2 f K n)) :
    toUnitHom g ∈ sesqUnitaryGroup (stdHermForm h n) :=
  mem_sesqUnitaryGroup.mpr fun v w => isometry_lin h g v w

theorem exists_toUnitHom_eq (h : UnitaryFieldData 2 f K)
    {g : LinearMap.GeneralLinearGroup K (Fin n → K)} (hg : g ∈ sesqUnitaryGroup (stdHermForm h n))
    (hdet : LinearMap.det (g : Module.End K (Fin n → K)) = 1) :
    ∃ s : ↥(unitarySU 2 f K n), toUnitHom s = g := by
  set M : GL (Fin n) K := Matrix.GeneralLinearGroup.toLin.symm g with hM
  have hMg : Matrix.GeneralLinearGroup.toLin M = g := MulEquiv.apply_symm_apply _ g
  have hlin : ((Matrix.GeneralLinearGroup.toLin M : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (M : Matrix (Fin n) (Fin n) K) :=
    LinearMap.ext fun v => by
      rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, Matrix.toLin'_apply]
  have hMv : ∀ v, (M : Matrix (Fin n) (Fin n) K) *ᵥ v = (g : Module.End K (Fin n → K)) v := by
    intro v
    rw [← hMg, hlin, Matrix.toLin'_apply]
  have hmem : M ∈ unitarySU 2 f K n := by
    refine (mem_unitarySU_iff_isometry h).mpr ⟨?_, fun v w => ?_⟩
    · have h1 : LinearMap.det (Matrix.toLin' (M : Matrix (Fin n) (Fin n) K)) = 1 := by
        rw [← hlin, hMg]
        exact hdet
      rwa [LinearMap.det_toLin'] at h1
    · rw [hMv, hMv]
      exact mem_sesqUnitaryGroup.mp hg v w
  refine ⟨⟨M, hmem⟩, Units.ext (LinearMap.ext fun v => ?_)⟩
  rw [coe_toUnitHom, lin_apply]
  exact hMv v

end Hom

section Data

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem primaryData {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : ↥(unitarySU 2 f K n)}
    (hx : x ^ p = 1) : UnitaryPrimaryData h.bar (stdHermForm h n) (toUnitHom x) where
  invol := h.bar_bar
  symm := stdHermForm_isSymm h n
  sep := stdHermForm_separatingLeft h n
  isom := isometry_lin h x
  squarefree := by
    have : CharP K 2 := h.charP
    have hpK : (p : K) ≠ 0 := by
      rw [CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
      exact one_ne_zero
    refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - 1) ?_ ?_
    · have := (separable_X_pow_sub_C (1 : K) hpK one_ne_zero).squarefree
      rwa [map_one] at this
    · rw [coe_toUnitHom, map_sub, map_pow, aeval_X, map_one, ← SUTB.lin_pow, hx, SUTB.lin_one,
        sub_self]

include h in
theorem two_le_two_pow : 2 ≤ 2 ^ f := by
  have := h.one_le
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this

@[expose] noncomputable def sb (x : ↥(unitarySU 2 f K n)) (a : K[X]) :
    Subgroup ↥(unitarySU 2 f K n) :=
  (specialBlock (stdHermForm h n) (toUnitHom x) a).comap toUnitHom

variable {h}

theorem mem_sb {x g : ↥(unitarySU 2 f K n)} {a : K[X]} :
    g ∈ sb h x a ↔ toUnitHom g ∈ specialBlock (stdHermForm h n) (toUnitHom x) a :=
  Iff.rfl

theorem toUnitHom_mem_unitaryCentralizer {x c : ↥(unitarySU 2 f K n)}
    (hc : c ∈ Subgroup.centralizer {x}) :
    toUnitHom c ∈ unitaryCentralizer (stdHermForm h n) (toUnitHom x) := by
  refine mem_unitaryCentralizer.mpr ⟨toUnitHom_mem_sesqUnitaryGroup h c, ?_⟩
  have h1 : Commute c x := Subgroup.mem_centralizer_singleton_iff.mp hc
  exact congrArg Units.val (toUnitHom_commute_iff.mpr h1).eq

theorem mem_centralizer_of_toUnitHom {x c : ↥(unitarySU 2 f K n)}
    (hc : toUnitHom c ∈ unitaryCentralizer (stdHermForm h n) (toUnitHom x)) :
    c ∈ Subgroup.centralizer {x} := by
  have h1 : Commute (toUnitHom c) (toUnitHom x) :=
    Units.ext (mem_unitaryCentralizer.mp hc).2.eq
  exact Subgroup.mem_centralizer_singleton_iff.mpr (toUnitHom_commute_iff.mp h1).eq

theorem sb_le_centralizer {x : ↥(unitarySU 2 f K n)} {a : K[X]} :
    sb h x a ≤ Subgroup.centralizer {x} := fun _ hg =>
  mem_centralizer_of_toUnitHom (specialBlock_le_unitaryCentralizer hg)

theorem conj_mem_sb {x c g : ↥(unitarySU 2 f K n)} {a : K[X]}
    (hc : c ∈ Subgroup.centralizer {x}) (hg : g ∈ sb h x a) : c * g * c⁻¹ ∈ sb h x a := by
  rw [mem_sb, map_mul, map_mul, map_inv]
  exact conj_mem_specialBlock (toUnitHom_mem_unitaryCentralizer hc) hg

end Data

section Good

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {x : ↥(unitarySU 2 f K n)}

theorem map_sb (hp : p.Prime) (hp2 : p ≠ 2) (hx : x ^ p = 1)
    (a : primaryFactors ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : IsGoodBlock h (toUnitHom x) a) :
    (sb h x a).map toUnitHom = specialBlock (stdHermForm h n) (toUnitHom x) a := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr le_rfl) fun g hg => ?_
  have hF := specialBlockFacts_of_good (primaryData h hp hp2 hx) (two_le_two_pow h) a ha
  have hgU : g ∈ sesqUnitaryGroup (stdHermForm h n) :=
    (mem_unitaryCentralizer.mp (specialBlock_le_unitaryCentralizer hg)).1
  obtain ⟨s, hs⟩ := exists_toUnitHom_eq h hgU (hF.detK g hg)
  refine ⟨s, ?_, hs⟩
  change toUnitHom s ∈ specialBlock (stdHermForm h n) (toUnitHom x) (a : K[X])
  rw [hs]
  exact hg

theorem isQuasisimple_sb (hp : p.Prime) (hp2 : p ≠ 2) (hx : x ^ p = 1)
    (a : primaryFactors ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : IsGoodBlock h (toUnitHom x) a) : CFSG.IsQuasisimple (sb h x a) := by
  have hF := specialBlockFacts_of_good (primaryData h hp hp2 hx) (two_le_two_pow h) a ha
  let e := (sb h x a).equivMapOfInjective toUnitHom toUnitHom_injective
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (e.trans (MulEquiv.subgroupCongr (map_sb hp hp2 hx a ha))).symm (hF.quasisimple ha.1)

variable {G : Type} [Group G] {φ : ↥(unitarySU 2 f K n) →* G}

theorem commute_of_mem_ker (hker : SURep.GGFrameKer φ) {z : ↥(unitarySU 2 f K n)} (hz : φ z = 1)
    (g : ↥(unitarySU 2 f K n)) : Commute z g := by
  obtain ⟨c, hc⟩ := hker z hz
  apply Subtype.ext
  apply Units.ext
  change ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [hc]
  exact scalar_commute c (fun _ => mul_comm _ _) _

theorem isComponentOf_map_sb [Finite K] (hker : SURep.GGFrameKer φ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ f + 1) (hx : x ^ p = 1)
    (a : primaryFactors ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : IsGoodBlock h (toUnitHom x) a) :
    CFSG.Assembly.IsComponentOf ((sb h x a).map φ) (φ.range ⊓ Subgroup.centralizer {φ x}) := by
  rw [SUNS.range_inf_centralizer_eq_map h hker hp hpq hx]
  set C := Subgroup.centralizer ({x} : Set ↥(unitarySU 2 f K n)) with hC
  set J₀ := sb h x a with hJ₀
  have hq : CFSG.IsQuasisimple J₀ := isQuasisimple_sb hp hp2 hx a ha
  have hkerc : (φ.comp J₀.subtype).ker ≤ Subgroup.center J₀ := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    exact Subtype.ext (commute_of_mem_ker hker hg (g' : ↥(unitarySU 2 f K n))).symm.eq
  have hJq : CFSG.IsQuasisimple (J₀.map φ) := by
    have := isQuasisimple_range hq (φ.comp J₀.subtype) hkerc
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
  have hJF : J₀.map φ ≤ C.map φ := Subgroup.map_mono sb_le_centralizer
  have hJn' : ((J₀.map φ).subgroupOf (C.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJF]
    rintro _ _ ⟨j, hj, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨c * j * c⁻¹, conj_mem_sb hc hj, by rw [map_mul, map_mul, map_inv]⟩
  exact ⟨hJF, CFSG.Assembly.IsSubnormal.step hJF hJn' (CFSG.Assembly.IsSubnormal.refl _),
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hJq⟩

theorem commute_of_map_commute (hker : SURep.GGFrameKer φ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hx : x ^ p = 1)
    (a : primaryFactors ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : IsGoodBlock h (toUnitHom x) a) {y : ↥(unitarySU 2 f K n)}
    (hy : ∀ g ∈ sb h x a, φ y * φ g = φ g * φ y) : ∀ g ∈ sb h x a, Commute y g := by
  have hq : CFSG.IsQuasisimple (sb h x a) := isQuasisimple_sb hp hp2 hx a ha
  have h1 := commutator_eq_one_of_central (F := sb h x a) (Z := φ.ker) y hq.1
    (fun z hz g => commute_of_mem_ker hker hz g) (fun g hg => by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hy g hg)
  exact fun g hg => commutatorElement_eq_one_iff_commute.mp (h1 g hg)

theorem exists_smul_of_commute_sb (hp : p.Prime) (hp2 : p ≠ 2) (hx : x ^ p = 1)
    (a : primaryFactors ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : IsGoodBlock h (toUnitHom x) a) {y : ↥(unitarySU 2 f K n)}
    (hyC : y ∈ Subgroup.centralizer {x}) (hy : ∀ g ∈ sb h x a, Commute y g) :
    ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent ((toUnitHom x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X]),
      lin y (v : Fin n → K) = ((c • v : primaryComponent ((toUnitHom x :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X])) :
          Fin n → K) := by
  refine (commute_specialBlock_iff_scalar (primaryData h hp hp2 hx) (two_le_two_pow h) a ha
    (toUnitHom_mem_unitaryCentralizer hyC)).mp fun g hg => ?_
  rw [← map_sb hp hp2 hx a ha] at hg
  obtain ⟨s, hs, rfl⟩ := hg
  exact toUnitHom_commute_iff.mpr (hy s hs)

end Good

end NsFrameComp

end CFSG.StandardType
