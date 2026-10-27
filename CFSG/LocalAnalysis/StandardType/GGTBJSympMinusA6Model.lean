module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticFixed
import all CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly CFSG.StandardType.SpJoin CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial (mem_sesqUnitaryGroup)
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul)

private theorem sympMinusA6_fixSpaceOf_zpowers {K : Type} [Field K] [CharP K 2] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {G : Type} [Group G] (ρ : G →* (Module.End K V)ˣ) (a : G) :
    SmallRule.fixSpaceOf ρ (Subgroup.zpowers a) =
      LinearMap.ker ((ρ a : Module.End K V) - 1) := by
  ext v
  rw [SmallRule.mem_fixSpaceOf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero]
  constructor
  · intro h
    exact h a (Subgroup.mem_zpowers a)
  · intro h
    let H : Subgroup G :=
      { carrier := {u | (ρ u : Module.End K V) v = v}
        one_mem' := by simp
        mul_mem' := by
          intro x y hx hy
          change (ρ (x * y) : Module.End K V) v = v
          rw [map_mul, Units.val_mul, Module.End.mul_apply, hy, hx]
        inv_mem' := by
          intro x hx
          change (ρ x⁻¹ : Module.End K V) v = v
          rw [map_inv]
          have h1 : (((ρ x)⁻¹ : (Module.End K V)ˣ) : Module.End K V)
              (((ρ x : (Module.End K V)ˣ) : Module.End K V) v) =
              (((ρ x)⁻¹ : (Module.End K V)ˣ) : Module.End K V) v :=
            congrArg (fun w => (((ρ x)⁻¹ : (Module.End K V)ˣ) : Module.End K V) w) hx
          rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Module.End.one_apply] at h1
          exact h1.symm }
    have hle : Subgroup.zpowers a ≤ H := Subgroup.zpowers_le.mpr h
    intro u hu
    exact hle hu

private theorem sympMinusA6_map_ker_conj {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (T : (Module.End K V)ˣ) (A : Module.End K V) :
    LinearMap.ker ((T : Module.End K V) * A *
        ((T⁻¹ : (Module.End K V)ˣ) : Module.End K V) - 1) =
      (LinearMap.ker (A - 1)).map (T : Module.End K V) := by
  ext v
  constructor
  · intro hv
    have hv1 : ((T : Module.End K V) * A *
        ((T⁻¹ : (Module.End K V)ˣ) : Module.End K V) - 1) v = 0 := LinearMap.mem_ker.mp hv
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv1
    rw [Module.End.mul_apply, Module.End.mul_apply] at hv1
    refine Submodule.mem_map.mpr ⟨((T⁻¹ : (Module.End K V)ˣ) : Module.End K V) v, ?_, ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      have h := congrArg (fun x => ((T⁻¹ : (Module.End K V)ˣ) : Module.End K V) x) hv1
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply] at h
      exact h
    · rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
  · rintro ⟨w, hw, rfl⟩
    have hw1 : (A - 1) w = 0 := LinearMap.mem_ker.mp hw
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw1
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [Module.End.mul_apply, Module.End.mul_apply]
    have hTT : ((T⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((T : Module.End K V) w) = w := by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    rw [hTT, hw1]

private theorem sympMinusA6_orthogonal_map {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (B : LinearMap.BilinForm K V) (T : (Module.End K V)ˣ)
    (hT : ∀ u v, B ((T : Module.End K V) u) ((T : Module.End K V) v) = B u v)
    (W : Submodule K V) :
    B.orthogonal (W.map (T : Module.End K V)) = (B.orthogonal W).map (T : Module.End K V) := by
  ext v
  constructor
  · intro hv
    refine Submodule.mem_map.mpr ⟨((T⁻¹ : (Module.End K V)ˣ) : Module.End K V) v, ?_, ?_⟩
    · intro u hu
      have h := hv ((T : Module.End K V) u) (Submodule.mem_map.mpr ⟨u, hu, rfl⟩)
      have h2 := hT u (((T⁻¹ : (Module.End K V)ˣ) : Module.End K V) v)
      rw [show (T : Module.End K V) (((T⁻¹ : (Module.End K V)ˣ) : Module.End K V) v) = v by
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Module.End.one_apply]] at h2
      rw [h2] at h
      exact h
    · rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
  · rintro ⟨w, hw, rfl⟩
    intro u hu
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
    rw [hT u' w]
    exact hw u' hu'

private theorem sympMinusA6_spRep_symm {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    [NeZero m] (y : StatedSp m K) (v : Fin m ⊕ Fin m → K) :
    (SmallRule.spRep ((TableBSymp.spProjEquivSp (K := K) (m := m)).symm y) :
        Module.End K (Fin m ⊕ Fin m → K)) v = spEnd y v := by
  have h := SmallRule.spRep_apply (K := K) (m := m)
    ((TableBSymp.spProjEquivSp (K := K) (m := m)).symm y) v
  rw [MulEquiv.apply_symm_apply] at h
  exact h

private theorem sympMinusA6_mem_fixPerp {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    [NeZero m] (W : Submodule K (Fin m ⊕ Fin m → K))
    (s : LargeEvenProj (LargeEvenSpGroup K m)) :
    s ∈ ggSpFixPerp W ↔ ∀ v : Fin m ⊕ Fin m → K, (∀ w ∈ W, spForm m K w v = 0) →
      (SmallRule.spRep s : Module.End K (Fin m ⊕ Fin m → K)) v = v :=
  Iff.rfl

theorem sympMinusA6_fixedFactor_bridge {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    [NeZero m] {f p : ℕ} (hpK : (p : K) ≠ 0) {x : StatedSp m K} (hx : x ^ p = 1)
    (blocks : SpPrimaryBlocks 2 f p x (proj m K x)) :
    (spFixedFactor x).map (TableBSymp.spProjEquivSp (K := K) (m := m)).symm.toMonoidHom =
        ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep
          (Subgroup.zpowers ((TableBSymp.spProjEquivSp (K := K) (m := m)).symm x))) ∧
      Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep
          (Subgroup.zpowers ((TableBSymp.spProjEquivSp (K := K) (m := m)).symm x))) =
        spFixedDim x := by
  classical
  have H := altPrimaryData_spLin hpK hx
  have hker := blocks.fixed_eq
  have hnd : ((spForm m K).restrict (LinearMap.ker (spEnd x - 1))).Nondegenerate := by
    have h := blocks.fixed_nondegenerate
    rwa [hker] at h
  have hdim : spFixedDim x = Module.finrank K (LinearMap.ker (spEnd x - 1)) := by
    unfold spFixedDim
    rw [hker]
  have hspEnd : (SmallRule.spRep ((TableBSymp.spProjEquivSp (K := K) (m := m)).symm x) :
      Module.End K (Fin m ⊕ Fin m → K)) = spEnd x :=
    LinearMap.ext fun v => sympMinusA6_spRep_symm x v
  have hfix : SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers
      ((TableBSymp.spProjEquivSp (K := K) (m := m)).symm x)) = LinearMap.ker (spEnd x - 1) := by
    rw [sympMinusA6_fixSpaceOf_zpowers, hspEnd]
  have hx1 : ∀ w ∈ LinearMap.ker (spEnd x - 1), spEnd x w = w := fun w hw => by
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
  rw [hfix]
  refine ⟨?_, hdim.symm⟩
  ext s
  constructor
  · intro hs
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hs
    refine (sympMinusA6_mem_fixPerp _ _).mpr fun v hv => ?_
    exact (sympMinusA6_spRep_symm g v).trans
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.apply_eq_of_orthogonal H hnd hg hv)
  · intro hs
    obtain ⟨g, rfl⟩ := (TableBSymp.spProjEquivSp (K := K) (m := m)).symm.surjective s
    have hgW : ∀ v : Fin m ⊕ Fin m → K,
        (∀ w ∈ LinearMap.ker (spEnd x - 1), spForm m K w v = 0) → spEnd g v = v := fun v hv =>
      (sympMinusA6_spRep_symm g v).symm.trans ((sympMinusA6_mem_fixPerp _ _).mp hs v hv)
    refine Subgroup.mem_map.mpr ⟨g, mem_spSupported.mpr ⟨?_, fun k hk hk1 v hv => ?_⟩, rfl⟩
    · refine spLin_injective (Units.ext (LinearMap.ext fun v => ?_))
      change spEnd (g * x) v = spEnd (x * g) v
      have hrefl := (spForm_isAlt (r := m) (K := K)).isRefl
      have hdd : (spForm m K).orthogonal ((spForm m K).orthogonal (LinearMap.ker (spEnd x - 1))) =
          LinearMap.ker (spEnd x - 1) :=
        LinearMap.BilinForm.orthogonal_orthogonal spForm_nondegenerate hrefl _
      have hgker : ∀ w ∈ LinearMap.ker (spEnd x - 1),
          spEnd g w ∈ LinearMap.ker (spEnd x - 1) := by
        intro w hw
        have hmem : spEnd g w ∈ (spForm m K).orthogonal
            ((spForm m K).orthogonal (LinearMap.ker (spEnd x - 1))) := by
          intro z hz
          have h1 : spForm m K (spEnd g z) (spEnd g w) = spForm m K z w :=
            mem_sesqUnitaryGroup.mp (spLin_mem g) z w
          rw [hgW z hz] at h1
          rw [h1]
          exact hrefl w z (hz w hw)
        rwa [hdd] at hmem
      obtain ⟨u, v₁, rfl, hv₁, -, hu⟩ :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_decomp H v
      have hgu : spEnd g u = u := hgW u hu
      have hxu : spEnd g (spEnd x u) = spEnd x u := by
        refine hgW _ fun w hw => ?_
        have h2 : spForm m K (spEnd x w) (spEnd x u) = spForm m K w u :=
          mem_sesqUnitaryGroup.mp (spLin_mem x) w u
        rw [hx1 w hw] at h2
        rw [h2]
        exact hu w hw
      simp only [spEnd_mul, Module.End.mul_apply, map_add]
      rw [hx1 v₁ hv₁, hxu, hgu, hx1 _ (hgker v₁ hv₁)]
    · exact hgW v fun w hw => CFSG.HardMathSupport.Timmesfeld.CrossChar.spForm_eq_zero_of_ne H hk
        (fun h => hk1 (Set.mem_singleton_iff.mpr h)) hw hv

private theorem sympMinusA6_spRep_conj_apply {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    [NeZero m] (g s : LargeEvenProj (LargeEvenSpGroup K m)) (w : Fin m ⊕ Fin m → K) :
    (SmallRule.spRep (g * s * g⁻¹) : Module.End K (Fin m ⊕ Fin m → K))
        ((SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) w) =
      (SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K))
        ((SmallRule.spRep s : Module.End K (Fin m ⊕ Fin m → K)) w) := by
  have hcoe : (SmallRule.spRep (g * s * g⁻¹) : Module.End K (Fin m ⊕ Fin m → K)) =
      (SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) *
        (SmallRule.spRep s : Module.End K (Fin m ⊕ Fin m → K)) *
          (((SmallRule.spRep g)⁻¹ : (Module.End K (Fin m ⊕ Fin m → K))ˣ) :
            Module.End K (Fin m ⊕ Fin m → K)) := by
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  rw [hcoe, Module.End.mul_apply, Module.End.mul_apply]
  have hTT : (((SmallRule.spRep g)⁻¹ : (Module.End K (Fin m ⊕ Fin m → K))ˣ) :
      Module.End K (Fin m ⊕ Fin m → K))
      ((SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) w) = w := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  rw [hTT]

private theorem sympMinusA6_spRep_inv_conj_apply {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    [NeZero m] (g s : LargeEvenProj (LargeEvenSpGroup K m)) (w : Fin m ⊕ Fin m → K) :
    (SmallRule.spRep (g⁻¹ * s * g) : Module.End K (Fin m ⊕ Fin m → K)) w =
      (((SmallRule.spRep g)⁻¹ : (Module.End K (Fin m ⊕ Fin m → K))ˣ) :
          Module.End K (Fin m ⊕ Fin m → K))
        ((SmallRule.spRep s : Module.End K (Fin m ⊕ Fin m → K))
          ((SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) w)) := by
  have hcoe : (SmallRule.spRep (g⁻¹ * s * g) : Module.End K (Fin m ⊕ Fin m → K)) =
      (((SmallRule.spRep g)⁻¹ : (Module.End K (Fin m ⊕ Fin m → K))ˣ) :
          Module.End K (Fin m ⊕ Fin m → K)) *
        (SmallRule.spRep s : Module.End K (Fin m ⊕ Fin m → K)) *
          (SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) := by
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  rw [hcoe, Module.End.mul_apply, Module.End.mul_apply]

theorem sympMinusA6_conj {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} [NeZero m]
    (g h : LargeEvenProj (LargeEvenSpGroup K m)) (W : Submodule K (Fin m ⊕ Fin m → K)) :
    SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (g * h * g⁻¹)) =
        (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers h)).map
          (SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) ∧
      (ggSpFixPerp W).map (MulAut.conj g).toMonoidHom =
        ggSpFixPerp (W.map (SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K))) := by
  constructor
  · rw [sympMinusA6_fixSpaceOf_zpowers, sympMinusA6_fixSpaceOf_zpowers]
    have hcoe : (SmallRule.spRep (g * h * g⁻¹) : Module.End K (Fin m ⊕ Fin m → K)) =
        (SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) *
          (SmallRule.spRep h : Module.End K (Fin m ⊕ Fin m → K)) *
            (((SmallRule.spRep g)⁻¹ : (Module.End K (Fin m ⊕ Fin m → K))ˣ) :
              Module.End K (Fin m ⊕ Fin m → K)) := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
    rw [hcoe]
    exact sympMinusA6_map_ker_conj (SmallRule.spRep g) (SmallRule.spRep h)
  · have hT : ∀ u v, SmallRule.spBilin K m
        ((SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) u)
        ((SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) v) =
        SmallRule.spBilin K m u v :=
      fun u v => SmallRule.spRep_isometry g u v
    have horth := sympMinusA6_orthogonal_map (SmallRule.spBilin K m) (SmallRule.spRep g) hT W
    ext s
    constructor
    · intro hs
      rw [Subgroup.mem_map] at hs
      obtain ⟨s', hs', hss'⟩ := hs
      rw [ggSpFixPerp]
      intro v hv
      rw [horth] at hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      have hs'w : (SmallRule.spRep s' : Module.End K (Fin m ⊕ Fin m → K)) w = w := hs' w hw
      have hconj : (MulAut.conj g) s' = s := hss'
      rw [← hconj, MulAut.conj_apply, sympMinusA6_spRep_conj_apply g s' w, hs'w]
    · intro hs
      rw [Subgroup.mem_map]
      refine ⟨g⁻¹ * s * g, ?_, ?_⟩
      · rw [ggSpFixPerp]
        intro w hw
        have hTw : (SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K)) w ∈
            (SmallRule.spBilin K m).orthogonal
              (W.map (SmallRule.spRep g : Module.End K (Fin m ⊕ Fin m → K))) := by
          rw [horth]
          exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
        have hsT := hs _ hTw
        rw [sympMinusA6_spRep_inv_conj_apply g s w, hsT,
          ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply]
      · change (MulAut.conj g) (g⁻¹ * s * g) = s
        rw [MulAut.conj_apply]
        group

private theorem sympMinusA6_mk_eq_symm (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ)
    [NeZero m] :
    LargeEvenProjMk (LargeEvenSpGroup K m) =
      (TableBSymp.spProjEquivSp (K := K) (m := m)).symm.toMonoidHom := by
  ext τ
  change LargeEvenProjMk (LargeEvenSpGroup K m) τ =
    (CFSG.SeitzReduction.F4Pilot.spProjEquiv m K) τ
  rw [CFSG.SeitzReduction.F4Pilot.spProjEquiv_apply]
  rfl

private theorem sympMinusA6_pow_eq_one {p : ℕ} (a : Multiplicative (ZMod p)) : a ^ p = 1 := by
  rw [← ofAdd_toAdd a, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem sympMinusA6_modelData {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} [NeZero m]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L']
    (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m))
    (σ : (Fin m → Multiplicative (ZMod p)) →* L')
    (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (x : LargeEvenProj (LargeEvenSpGroup K m))
    (hψσ : ∀ g, ψ₀ (σ g) =
      x * LargeEvenProjMk (LargeEvenSpGroup K m) (spPlaneTorus m ζ g) * x⁻¹)
    (f₀ : Fin m → Multiplicative (ZMod p)) (J : Subgroup L') (J₀ : Subgroup (StatedSp m K))
    (hJ₀ : (J₀.map (LargeEvenProjMk (LargeEvenSpGroup K m))).map (MulAut.conj x).toMonoidHom =
      J.map ψ₀)
    (hblocks : SpPrimaryBlocks 2 f p (spPlaneTorus m ζ f₀)
      (proj m K (spPlaneTorus m ζ f₀)))
    (hd : spFixedDim (spPlaneTorus m ζ f₀) = 4)
    (hJ₀' : J₀ = ⁅spFixedFactor (spPlaneTorus m ζ f₀), spFixedFactor (spPlaneTorus m ζ f₀)⁆) :
    Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep
        (Subgroup.zpowers (ψ₀ (σ f₀)))) = 4 ∧
      J.map ψ₀ =
        ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (ψ₀ (σ f₀)))),
          ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (ψ₀ (σ f₀))))⁆ := by
  let e := TableBSymp.spProjEquivSp (K := K) (m := m)
  let τ := spPlaneTorus m ζ f₀
  have hMk : LargeEvenProjMk (LargeEvenSpGroup K m) = e.symm.toMonoidHom :=
    sympMinusA6_mk_eq_symm K m
  have hpsi : ψ₀ (σ f₀) = x * e.symm τ * x⁻¹ := by
    rw [hψσ f₀, hMk]
    rfl
  have hconj1 := (sympMinusA6_conj (K := K) (m := m) x (e.symm τ) ⊥).1
  have hconj2 := (sympMinusA6_conj (K := K) (m := m) x (e.symm τ)
    (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (e.symm τ)))).2
  have hpK : (p : K) ≠ 0 := fun h => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp ((CharP.cast_eq_zero_iff K 2 p).mp h)).symm
  have hxp : spPlaneTorus m ζ f₀ ^ p = 1 := by
    rw [← map_pow, show f₀ ^ p = 1 from funext fun i => sympMinusA6_pow_eq_one (f₀ i), map_one]
  have hbridge := sympMinusA6_fixedFactor_bridge (K := K) (m := m) hpK hxp hblocks
  have hW₀ : (SmallRule.fixSpaceOf SmallRule.spRep
      (Subgroup.zpowers (e.symm τ))).map
        (SmallRule.spRep x : Module.End K (Fin m ⊕ Fin m → K)) =
      SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (ψ₀ (σ f₀))) := by
    rw [hconj1.symm, hpsi]
  constructor
  · rw [hpsi, hconj1]
    have hinj : Function.Injective
        (SmallRule.spRep x : Module.End K (Fin m ⊕ Fin m → K)) :=
      ((Module.End.isUnit_iff _).mp (SmallRule.spRep x).isUnit).1
    have hfin : Module.finrank K ((SmallRule.fixSpaceOf SmallRule.spRep
        (Subgroup.zpowers (e.symm τ))).map
          (SmallRule.spRep x : Module.End K (Fin m ⊕ Fin m → K))) =
        Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep
          (Subgroup.zpowers (e.symm τ))) :=
      (Submodule.equivMapOfInjective
        (SmallRule.spRep x : Module.End K (Fin m ⊕ Fin m → K)) hinj _).finrank_eq.symm
    rw [hfin, hbridge.2]
    exact hd
  · rw [hJ₀.symm, hJ₀']
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
    rw [hMk, hbridge.1, hconj2, hW₀]

end CFSG.StandardType.SympMinus

end
