module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om8
import CFSG.LieType.SeitzGeneration.OrthRelRoot
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.ClassicalInvolution.RouteD.TWYPlane
public import CFSG.LieType.SeitzGeneration.OrthNonsplitTools
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniVanish
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.HyperLinear
public import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.RankThree.PartOne.FOC.CompCommutator

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial Module QuadraticMap
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_add_smul_self
  eichler_zero_right eichler_apply_of_polar_eq_zero eichler_conj eichler_of_not
  eichler_mem_orthogonalGroup eichler_mem_elementaryGroup elementaryGroup
  elementaryGroup_le_of_eichler_mem elementaryGroup_le_commutator_of_perp_le_span HypPair
  polar_smul_right_eq polar_smul_left_eq polar_self_eq_zero PolarNondegOn polarNondegOn_top)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem aeval_mul_conj (k x : V ≃ₗ[F] V) (q : F[X]) :
    aeval ((k * x * k⁻¹).toLinearMap) q = (k.conjAlgEquiv F) (aeval x.toLinearMap q) := by
  have hconj : ((k * x * k⁻¹).toLinearMap) = (k.conjAlgEquiv F) x.toLinearMap := by
    ext v
    simp [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.mul_apply]
  rw [hconj]
  exact Polynomial.aeval_algHom_apply (k.conjAlgEquiv F) x.toLinearMap q

theorem primaryComponent_mul_conj (x k : V ≃ₗ[F] V) (h : F[X]) :
    primaryComponent ((k * x * k⁻¹).toLinearMap) h =
      (primaryComponent x.toLinearMap h).map (k : V →ₗ[F] V) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨k⁻¹ v, ?_, by simp⟩
    rw [mem_primaryComponent] at hv ⊢
    have h1 : ((k.conjAlgEquiv F) (aeval x.toLinearMap h)) v = 0 := by
      have := LinearMap.congr_fun (aeval_mul_conj k x h) v
      rw [hv] at this
      exact this.symm
    have h2 : (k : V ≃ₗ[F] V) (aeval x.toLinearMap h (k⁻¹ v)) = 0 := by
      rwa [LinearEquiv.conjAlgEquiv_apply] at h1
    have h3 := congrArg (fun z => (k⁻¹ : V ≃ₗ[F] V) z) h2
    simpa using h3
  · rintro ⟨w, hw, rfl⟩
    rw [mem_primaryComponent] at hw ⊢
    have h2 : aeval ((k * x * k⁻¹).toLinearMap) h (k w) =
        (k : V ≃ₗ[F] V) (aeval x.toLinearMap h w) := by
      rw [LinearMap.congr_fun (aeval_mul_conj k x h) (k w),
        LinearEquiv.conjAlgEquiv_apply]
      simp [LinearMap.comp_apply]
    change ((aeval ((k * x * k⁻¹).toLinearMap)) h) ((k : V ≃ₗ[F] V) w) = 0
    rw [h2, hw, map_zero]

theorem primaryFactors_mul_conj (x k : V ≃ₗ[F] V) :
    primaryFactors ((k * x * k⁻¹).toLinearMap) = primaryFactors x.toLinearMap := by
  have hconj : ((k * x * k⁻¹).toLinearMap) = (k.conjAlgEquiv F) x.toLinearMap := by
    ext v
    simp [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.mul_apply]
  unfold primaryFactors
  rw [hconj, minpoly.algEquiv_eq]

theorem othersSpace_mul_conj (x k : V ≃ₗ[F] V) (h : F[X]) :
    othersSpace ((k * x * k⁻¹).toLinearMap) h =
      (othersSpace x.toLinearMap h).map (k : V →ₗ[F] V) := by
  unfold othersSpace
  rw [primaryFactors_mul_conj, Submodule.map_iSup]
  refine iSup_congr fun a => ?_
  rw [Submodule.map_iSup]
  exact iSup_congr fun _ => primaryComponent_mul_conj x k a

theorem supportedBlock_mul_conj (x k : V ≃ₗ[F] V)
    (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : F[X]) :
    supportedBlock Q (k * x * k⁻¹) h =
      (supportedBlock Q x h).map (MulAut.conj k).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_map]
    refine ⟨k⁻¹ * g * k, ?_, ?_⟩
    · obtain ⟨hgM, hgfix⟩ := mem_supportedBlock.mp hg
      obtain ⟨hgO, hgcomm⟩ := mem_isometryCentralizer.mp hgM
      refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨?_, ?_⟩, ?_⟩
      · have hkI : k⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.inv_mem _ hk
        intro v
        calc Q ((k⁻¹ * g * k) v) = Q (k⁻¹ (g (k v))) := rfl
          _ = Q (g (k v)) :=
            TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hkI _
          _ = Q (k v) := hgO _
          _ = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hk v
      · have hcomm : g * (k * x * k⁻¹) = (k * x * k⁻¹) * g :=
          LinearEquiv.ext fun v => hgcomm v
        have hs : (k⁻¹ * g * k) * x = x * (k⁻¹ * g * k) := by
          calc (k⁻¹ * g * k) * x = k⁻¹ * (g * (k * x * k⁻¹)) * k := by group
            _ = k⁻¹ * ((k * x * k⁻¹) * g) * k := by rw [hcomm]
            _ = x * (k⁻¹ * g * k) := by group
        intro v
        have := congrArg (fun f : V ≃ₗ[F] V => f v) hs
        simpa [LinearEquiv.mul_apply] using this
      · intro r hr
        have hkr : k r ∈ othersSpace ((k * x * k⁻¹).toLinearMap) h := by
          rw [othersSpace_mul_conj x k h]
          exact Submodule.mem_map_of_mem hr
        have h1 := hgfix (k r) hkr
        calc (k⁻¹ * g * k) r = k⁻¹ (g (k r)) := rfl
          _ = k⁻¹ (k r) := by rw [h1]
          _ = r := by simp
    · change (MulAut.conj k) (k⁻¹ * g * k) = g
      rw [MulAut.conj_apply]
      group
  · rintro g ⟨s, hs, rfl⟩
    obtain ⟨hsM, hsfix⟩ := mem_supportedBlock.mp hs
    obtain ⟨hsO, hscomm⟩ := mem_isometryCentralizer.mp hsM
    refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨?_, ?_⟩, ?_⟩
    · have hkI : k⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.inv_mem _ hk
      intro v
      calc Q ((k * s * k⁻¹) v) = Q (k (s (k⁻¹ v))) := rfl
        _ = Q (s (k⁻¹ v)) := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hk _
        _ = Q (k⁻¹ v) := hsO _
        _ = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hkI v
    · have hs' : s * x = x * s := LinearEquiv.ext fun v => hscomm v
      have h1 : (k * s * k⁻¹) * (k * x * k⁻¹) =
          (k * x * k⁻¹) * (k * s * k⁻¹) := by
        calc (k * s * k⁻¹) * (k * x * k⁻¹) = k * (s * x) * k⁻¹ := by group
          _ = k * (x * s) * k⁻¹ := by rw [hs']
          _ = (k * x * k⁻¹) * (k * s * k⁻¹) := by group
      intro v
      have := congrArg (fun f : V ≃ₗ[F] V => f v) h1
      simpa [LinearEquiv.mul_apply] using this
    · intro r hr
      rw [othersSpace_mul_conj x k h] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Submodule.mem_map.mp hr
      calc (k * s * k⁻¹) (k r₀) = k (s r₀) := by simp [LinearEquiv.mul_apply]
        _ = k r₀ := by rw [hsfix r₀ hr₀]

theorem oddOrderIsometry_mul_conj {y k : V ≃ₗ[F] V} (hy : OddOrderIsometry Q p y)
    (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    OddOrderIsometry Q p (k * y * k⁻¹) where
  mem := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    have hkI : k⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.inv_mem _ hk
    intro v
    calc Q ((k * y * k⁻¹) v) = Q (k (y (k⁻¹ v))) := rfl
      _ = Q (y (k⁻¹ v)) := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hk _
      _ = Q (k⁻¹ v) := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hy.mem _
      _ = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hkI v
  pow_eq_one := by
    calc (k * y * k⁻¹) ^ p = (MulAut.conj k) (y ^ p) := by
          rw [map_pow]
          rfl
      _ = 1 := by rw [hy.pow_eq_one, map_one]
  cast_ne_zero := hy.cast_ne_zero
  regular := hy.regular

theorem supportedFixedDerived_conj {y g : V ≃ₗ[F] V} (hy : OddOrderIsometry Q p y)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    supportedFixedDerived Q (g * y * g⁻¹) =
      (supportedFixedDerived Q y).map (MulAut.conj g).toMonoidHom := by
  have hy' := oddOrderIsometry_mul_conj hy hg
  rw [hy'.supportedFixedDerived_eq, hy.supportedFixedDerived_eq,
    supportedBlock_mul_conj y g hg (X - 1), Subgroup.map_commutator]

theorem oddOrderIsometry_of_orthDerived_pow_eq_one (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) {y : ↥(orthDerived Q)} (hy : y ^ p = 1) :
    OddOrderIsometry Q p (y : V ≃ₗ[F] V) where
  mem := CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q y.2
  pow_eq_one := by
    simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hy
  cast_ne_zero := by
    intro h0
    have h1 : ringChar F ∣ p := (ringChar.spec F p).mp h0
    rw [ringChar.eq F 2] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h1).symm
  regular := fun v hv => hQ.1 v fun w => by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hv w

theorem eq_zero_of_quad_eq_zero_of_not_isPlusType {W : Submodule F V}
    (hW : Module.finrank F W = 2) (h : ¬ IsPlusType (Q.comp W.subtype))
    {v : V} (hv : v ∈ W) (hQv : Q v = 0) : v = 0 := by
  by_contra hv0
  apply h
  have hiff := CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_restrict_iff_of_finrank_two
    (Q := Q) hW
  have h' : IsPlusType (Q.restrict W) := by
    rw [hiff]
    exact ⟨v, hv, hv0, hQv⟩
  have heq : Q.restrict W = Q.comp W.subtype := by
    ext u
    rw [QuadraticMap.restrict_apply]
    rfl
  rwa [heq] at h'

theorem span_pair_eq_of_finrank_eq_two {W : Submodule F V} {f f' : V}
    (hf : f ∈ W) (hf' : f' ∈ W) (hfQ : Q f = 0) (hf'Q : Q f' = 0)
    (hff' : polar Q f f' = 1) (hW : Module.finrank F W = 2) :
    Submodule.span F {f, f'} = W := by
  have hli : LinearIndependent F ![f, f'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun z => polar Q z f') hst
    have h2 := congrArg (fun z => polar Q z f) hst
    have h1' : s * polar Q f f' + t * polar Q f' f' = 0 := by
      simpa [polar_add_left, polar_smul_left_eq] using h1
    have h2' : s * polar Q f f + t * polar Q f' f = 0 := by
      simpa [polar_add_left, polar_smul_left_eq] using h2
    rw [polar_self_eq_zero hf'Q, hff', mul_one, mul_zero, add_zero] at h1'
    rw [polar_self_eq_zero hfQ, polar_comm Q f' f, hff', mul_one, mul_zero, zero_add] at h2'
    exact ⟨h1', h2'⟩
  have hle : Submodule.span F ({f, f'} : Set V) ≤ W := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl) <;> assumption
  refine le_antisymm hle ?_
  have hcard : Module.finrank F (Submodule.span F ({f, f'} : Set V)) = 2 := by
    have hr : ({f, f'} : Set V) = Set.range ![f, f'] := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    rw [hr, finrank_span_eq_card hli]
    simp
  have heq : Submodule.span F ({f, f'} : Set V) = W :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hcard, hW])
  rw [heq]

theorem extU_mem_orthogonalGroup {U : Submodule F V} (hU : PolarNondegOn Q U)
    {φ : U ≃ₗ[F] U}
    (hφ : φ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict U)) :
    CFSG.LieType.SeitzGeneration.OrthNS.extU hU φ ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have hc := CFSG.LieType.SeitzGeneration.OrthBlk.isCompl_perp hU
  obtain ⟨u, hu, r, hr, huv⟩ :=
    Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
  subst huv
  rw [map_add, CFSG.LieType.SeitzGeneration.OrthNS.extU_apply_mem hU φ hu,
    CFSG.LieType.SeitzGeneration.OrthNS.extU_apply_perp hU φ hr]
  have hφu : Q (φ ⟨u, hu⟩ : V) = Q (u : V) := by
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hφ ⟨u, hu⟩
    simpa [QuadraticMap.restrict_apply] using this
  have horth1 : polar Q (φ ⟨u, hu⟩ : V) (r : V) = 0 :=
    CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp.mp hr
      (φ ⟨u, hu⟩) (φ ⟨u, hu⟩).2
  have horth2 : polar Q (u : V) (r : V) = 0 :=
    CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp.mp hr u hu
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, hφu, horth1, horth2]

theorem extU_commute_of_fixes {U : Submodule F V} (hU : PolarNondegOn Q U)
    {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgU : ∀ u ∈ U, g u = u) (φ : U ≃ₗ[F] U) :
    CFSG.LieType.SeitzGeneration.OrthNS.extU hU φ * g =
      g * CFSG.LieType.SeitzGeneration.OrthNS.extU hU φ := by
  refine LinearEquiv.ext fun v => ?_
  have hc := CFSG.LieType.SeitzGeneration.OrthBlk.isCompl_perp hU
  obtain ⟨u, hu, r, hr, huv⟩ :=
    Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
  subst huv
  have hgu : g u = u := hgU u hu
  have hgr : g r ∈ CFSG.LieType.SeitzGeneration.OrthBlk.perp Q U := by
    rw [CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp]
    intro y hy
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg (g⁻¹ y) r
    rw [show g (g⁻¹ y) = y by simp] at h1
    rw [h1]
    have h2 : g⁻¹ y = y := by
      calc g⁻¹ y = g⁻¹ (g y) := by rw [hgU y hy]
        _ = y := by simp
    rw [h2]
    exact CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp.mp hr y hy
  have hEU : CFSG.LieType.SeitzGeneration.OrthNS.extU hU φ (u + r) =
      φ ⟨u, hu⟩ + r := by
    rw [map_add, CFSG.LieType.SeitzGeneration.OrthNS.extU_apply_mem hU φ hu,
      CFSG.LieType.SeitzGeneration.OrthNS.extU_apply_perp hU φ hr]
  calc (CFSG.LieType.SeitzGeneration.OrthNS.extU hU φ * g) (u + r)
      = CFSG.LieType.SeitzGeneration.OrthNS.extU hU φ (g (u + r)) := rfl
    _ = CFSG.LieType.SeitzGeneration.OrthNS.extU hU φ (u + g r) := by rw [map_add, hgu]
    _ = φ ⟨u, hu⟩ + g r := by
        rw [map_add, CFSG.LieType.SeitzGeneration.OrthNS.extU_apply_mem hU φ hu,
          CFSG.LieType.SeitzGeneration.OrthNS.extU_apply_perp hU φ hgr]
    _ = g (φ ⟨u, hu⟩) + g r := by rw [hgU (φ ⟨u, hu⟩) (φ ⟨u, hu⟩).2]
    _ = g (φ ⟨u, hu⟩ + r) := by rw [map_add]
    _ = g (CFSG.LieType.SeitzGeneration.OrthNS.extU hU φ (u + r)) := by rw [hEU]
    _ = (g * CFSG.LieType.SeitzGeneration.OrthNS.extU hU φ) (u + r) := rfl

theorem eichler_mem_supportedFixedDerived_signElt {k : ℕ}
    {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)} {x : Fin k → ↥(orthDerived Q)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : IsPlaneFrame Q p U e E)
    (hW : Module.finrank F (polarPerp Q (⨆ j, U j)) = 2)
    {f f' : V} (hfW : f ∈ polarPerp Q (⨆ j, U j))
    (hf'W : f' ∈ polarPerp Q (⨆ j, U j)) (hfQ : Q f = 0) (hf'Q : Q f' = 0)
    (hff' : polar Q f f' = 1)
    (hx : ∀ a, (∀ v ∈ U a, (x a : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x a : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v)
    (hxE : ∀ a, x a ∈ E)
    {a : Fin k} {z w : V}
    (hz : z ∈ U a ⊔ polarPerp Q (⨆ j, U j))
    (hw : w ∈ U a ⊔ polarPerp Q (⨆ j, U j)) :
    eichler Q z w ∈ supportedFixedDerived Q (x a : V ≃ₗ[F] V) := by
  classical
  set W : Submodule F V := polarPerp Q (⨆ j, U j) with hWdef
  set R : Submodule F V := ⨆ j : {j : Fin k // j ≠ a}, U j with hRdef
  set U4 : Submodule F V := U a ⊔ W with hU4def
  have hRfinset : R = ⨆ j ∈ Finset.univ.erase a, U j := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun j => ?_
      exact le_iSup₂ (f := fun i (_ : i ∈ Finset.univ.erase a) => U i) j.val
        (Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩)
    · refine iSup₂_le fun j hj => ?_
      exact le_iSup (fun j : {j : Fin k // j ≠ a} => U j)
        ⟨j, (Finset.mem_erase.mp hj).1⟩
  have hind : iSupIndep U := by
    rw [iSupIndep_def]
    intro j
    rw [Submodule.disjoint_def]
    intro v hv hv'
    have hvperp : v ∈ polarPerp Q (U j) := by
      refine mem_polarPerp_iff.mpr fun y hy => ?_
      refine Submodule.iSup_induction (fun i : Fin k => ⨆ (_ : i ≠ j), U i)
        (motive := fun v => polar Q y v = 0) hv' ?_ ?_ ?_
      · intro i v' hv''
        exact Submodule.iSup_induction (fun _ : i ≠ j => U i) (motive := fun v => polar Q y v = 0)
          hv'' (fun hij v'' hv''' =>
            hF.perp j i (fun h => hij h.symm) y hy v'' hv''') (by simp)
          (fun x y hx hy => by rw [polar_add_right, hx, hy, add_zero])
      · simp
      · intro x y hx hy
        rw [polar_add_right, hx, hy, add_zero]
    have hvperp' : ∀ y ∈ U j, polar Q v y = 0 := by
      intro y hy
      rw [polar_comm]
      exact mem_polarPerp_iff.1 hvperp y hy
    exact (polarNondegOn_of_nondegenerate (hF.nondeg j)) v hv hvperp'
  have hindR : iSupIndep (fun j : {j : Fin k // j ≠ a} => U j) := by
    rw [iSupIndep_def]
    intro j
    rw [Submodule.disjoint_def]
    intro v hv hv'
    have hvperp : v ∈ polarPerp Q (U j.val) := by
      refine mem_polarPerp_iff.mpr fun y hy => ?_
      refine Submodule.iSup_induction
        (fun i : {j : Fin k // j ≠ a} => ⨆ (_ : i ≠ j), U i)
        (motive := fun v => polar Q y v = 0) hv' ?_ ?_ ?_
      · intro i v' hv''
        exact Submodule.iSup_induction (fun _ : i ≠ j => U i)
          (motive := fun v => polar Q y v = 0) hv''
          (fun hij v'' hv''' =>
            hF.perp j.val i.val (fun h => hij (Subtype.ext h.symm)) y hy v'' hv''')
          (by simp) (fun x y hx hy => by simp [polar_add_right, hx, hy])
      · simp
      · intro x y hx hy
        simp [polar_add_right, hx, hy]
    have hvperp' : ∀ y ∈ U j.val, polar Q v y = 0 := by
      intro y hy
      rw [polar_comm]
      exact mem_polarPerp_iff.1 hvperp y hy
    exact (polarNondegOn_of_nondegenerate (hF.nondeg j.val)) v hv hvperp'
  have hsupU : (⨆ j, U j) = U a ⊔ R := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun j => ?_
      by_cases hja : j = a
      · subst hja
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup (fun j : {j : Fin k // j ≠ a} => U j) ⟨j, hja⟩)
    · refine sup_le (le_iSup U a) ?_
      refine iSup_le fun j => le_iSup U j.val
  have hVeq : U4 ⊔ R = ⊤ := by
    calc U4 ⊔ R = (U a ⊔ R) ⊔ W := by rw [hU4def]; ac_rfl
      _ = (⨆ j, U j) ⊔ W := by rw [hsupU]
      _ = ⊤ := by simpa [hWdef] using hF.isCompl_iSup.sup_eq_top
  have hxOdd : OddOrderIsometry Q p (x a : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived_pow_eq_one hQ hp hp2 (hF.isElemAbelian.2 (x a) (hxE a))
  have hxaUa : ∀ v ∈ U a, (x a : V ≃ₗ[F] V) v = v := (hx a).1
  have hxaW : ∀ v ∈ W, (x a : V ≃ₗ[F] V) v = v := fun v hv =>
    hF.apply_eq_of_mem_polarPerp_iSup (hxE a) (hWdef ▸ hv)
  have hxaU4 : ∀ v ∈ U4, (x a : V ≃ₗ[F] V) v = v := by
    intro v hv
    obtain ⟨u, hu, w, hw', rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hxaUa u hu, hxaW w hw']
  have hxaU : ∀ j, ∀ v ∈ U j, (x a : V ≃ₗ[F] V) v ∈ U j := by
    intro j v hv
    by_cases hja : j = a
    · subst hja
      rw [hxaUa v hv]
      exact hv
    · rw [(hx a).2 j hja v hv]
      exact hF.maps_to j v hv
  have hxaR : ∀ v ∈ R, (x a : V ≃ₗ[F] V) v ∈ R := by
    intro v hv
    refine Submodule.iSup_induction (fun j : {j : Fin k // j ≠ a} => U j)
      (motive := fun v => (x a : V ≃ₗ[F] V) v ∈ R) hv ?_ ?_ ?_
    · intro j v' hv'
      exact Submodule.mem_iSup_of_mem j (hxaU j.val v' hv')
    · simp
    · intro x y hx' hy'
      rw [map_add]
      exact R.add_mem hx' hy'
  have hrange_le_R : LinearMap.range (((x a : V ≃ₗ[F] V)).toLinearMap - 1) ≤ R := by
    rintro v ⟨u, rfl⟩
    have hu : u ∈ U4 ⊔ R := hVeq ▸ Submodule.mem_top
    obtain ⟨c, hc, r, hr, rfl⟩ := Submodule.mem_sup.mp hu
    change (x a : V ≃ₗ[F] V) (c + r) - (c + r) ∈ R
    rw [map_add, hxaU4 c hc]
    have hsub : c + (x a : V ≃ₗ[F] V) r - (c + r) = (x a : V ≃ₗ[F] V) r - r := by abel
    rw [hsub]
    exact R.sub_mem (hxaR r hr) hr
  have hfixedR : ∀ r ∈ R, (x a : V ≃ₗ[F] V) r = r → r = 0 := by
    intro r hr hrfix
    obtain ⟨s, hs⟩ := Submodule.exists_finset_of_mem_iSup
      (fun j : {j : Fin k // j ≠ a} => U j) hr
    obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
      (fun j : {j : Fin k // j ≠ a} => U j) r).mp hs
    have hsum : ∑ j ∈ s, ((x a : V ≃ₗ[F] V) (μ j : V) - (μ j : V)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have hmap : ∑ j ∈ s, (x a : V ≃ₗ[F] V) (μ j : V) =
          (x a : V ≃ₗ[F] V) r := by
        rw [← map_sum, hμ]
      rw [hmap, hμ, sub_eq_zero]
      exact hrfix
    have hzero : ∀ j ∈ s, (x a : V ≃ₗ[F] V) (μ j : V) - (μ j : V) = 0 :=
      (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
        (fun j : {j : Fin k // j ≠ a} => U j)).mp hindR s
        (fun j => (x a : V ≃ₗ[F] V) (μ j : V) - (μ j : V))
        (fun j hj => (U j).sub_mem (hxaU j.val (μ j : V) (μ j).2) (μ j).2) hsum
    have hμ0 : ∀ j ∈ s, (μ j : V) = 0 := by
      intro j hj
      have h1 : (x a : V ≃ₗ[F] V) (μ j : V) = (μ j : V) := sub_eq_zero.mp (hzero j hj)
      have h2 : (e j.val : V ≃ₗ[F] V) (μ j : V) = (μ j : V) := by
        rw [← (hx a).2 j.val j.2 (μ j : V) (μ j).2]
        exact h1
      exact hF.eq_zero_of_apply_eq j.val (μ j : V) (μ j).2 h2
    rw [← hμ]
    exact Finset.sum_eq_zero fun j hj => by simp [hμ0 j hj]
  have hRperpU4 : ∀ r ∈ R, ∀ v ∈ U4, polar Q r v = 0 := by
    intro r hr v hv
    obtain ⟨u, hu, w, hw', rfl⟩ := Submodule.mem_sup.mp hv
    rw [polar_add_right]
    have h1 : polar Q r u = 0 := by
      refine Submodule.iSup_induction (fun j : {j : Fin k // j ≠ a} => U j)
        (motive := fun r => polar Q r u = 0) hr ?_ ?_ ?_
      · intro j r' hr'
        exact hF.perp j.val a j.2 r' hr' u hu
      · simp
      · intro x y hx' hy'
        simp [polar_add_left, hx', hy']
    have h2 : polar Q r w = 0 := by
      refine Submodule.iSup_induction (fun j : {j : Fin k // j ≠ a} => U j)
        (motive := fun r => polar Q r w = 0) hr ?_ ?_ ?_
      · intro j r' hr'
        rw [polar_comm]
        rw [polar_comm]
        exact mem_polarPerp_iff.1 hw' r' (le_iSup U j.val hr')
      · simp
      · intro x y hx' hy'
        simp [polar_add_left, hx', hy']
    rw [h1, h2, add_zero]
  have hRreg : PolarNondegOn Q R := by
    rw [hRfinset]
    exact polarNondegOn_of_nondegenerate (hF.nondeg_biSup (Finset.univ.erase a))
  have hU4perp : U4 = polarPerp Q R := by
    refine le_antisymm ?_ ?_
    · intro v hv
      rw [mem_polarPerp_iff]
      intro r hr
      exact hRperpU4 r hr v hv
    · intro v hv
      have hv' : v ∈ U4 ⊔ R := hVeq ▸ Submodule.mem_top
      obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.mp hv'
      have hr0 : r = 0 := by
        have hperp : ∀ y ∈ R, polar Q r y = 0 := by
          intro y hy
          have h1 : polar Q (u + r) y = 0 := by
            rw [polar_comm]
            exact mem_polarPerp_iff.1 hv y hy
          have h2 : polar Q u y = 0 := by
            rw [polar_comm]
            exact hRperpU4 y hy u hu
          rwa [polar_add_left, h2, zero_add] at h1
        exact hRreg r hr hperp
      rw [hr0, add_zero]
      exact hu
  have hU4reg : PolarNondegOn Q U4 := by
    rw [hU4perp]
    exact CFSG.LocalAnalysis.GLTheoremA.T173U.polarNondegOn_polarPerp hQ hRreg
  have hQ4comp : (QuadraticMap.polarBilin (Q.comp U4.subtype)).Nondegenerate :=
    CFSG.LieType.SeitzGeneration.nondegenerate_comp_subtype hU4reg
  have hheq : Q.restrict U4 = Q.comp U4.subtype := by
    ext u
    rw [QuadraticMap.restrict_apply]
    rfl
  have hQ4 : (QuadraticMap.polarBilin (Q.restrict U4)).Nondegenerate := by
    rwa [hheq]
  have hperpU4 : CFSG.LieType.SeitzGeneration.OrthBlk.perp Q U4 = R := by
    rw [hU4perp]
    refine le_antisymm (CFSG.LocalAnalysis.GLTheoremA.T173U.perp_polarPerp_le hQ hRreg) ?_
    intro r hr
    rw [CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp]
    intro x hx
    rw [polar_comm]
    exact mem_polarPerp_iff.1 hx r hr
  have hcyc : ∀ r ∈ R, eichler Q z w r = r := by
    intro r hr
    have hz4 : z ∈ U4 := by rw [hU4def]; exact hz
    have hw4 : w ∈ U4 := by rw [hU4def]; exact hw
    exact eichler_apply_of_polar_eq_zero (hRperpU4 r hr z hz4) (hRperpU4 r hr w hw4)
  have hxaz : (x a : V ≃ₗ[F] V) z = z := by
    obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add, hxaUa u hu, hxaW w' hw']
  have hxaw : (x a : V ≃ₗ[F] V) w = w := by
    obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, hxaUa u hu, hxaW w' hw']
  have hcomm : eichler Q z w * (x a : V ≃ₗ[F] V) =
      (x a : V ≃ₗ[F] V) * eichler Q z w := by
    have h := eichler_conj (Q := Q) hxOdd.mem z w
    rw [hxaz, hxaw] at h
    calc eichler Q z w * (x a : V ≃ₗ[F] V)
        = ((x a : V ≃ₗ[F] V) * eichler Q z w * (x a : V ≃ₗ[F] V)⁻¹) *
            (x a : V ≃ₗ[F] V) := by rw [h]
      _ = (x a : V ≃ₗ[F] V) * eichler Q z w := by group
  let B : Subgroup (V ≃ₗ[F] V) := supportedBlock Q (x a : V ≃ₗ[F] V) (X - 1)
  let Hom : (U4 ≃ₗ[F] U4) →* (V ≃ₗ[F] V) :=
    CFSG.LieType.SeitzGeneration.OrthNS.extU hU4reg
  have hEXTB : (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict U4)).map Hom ≤ B := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine mem_supportedBlock.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact extU_mem_orthogonalGroup hU4reg hφ
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (extU_commute_of_fixes hU4reg hxOdd.mem hxaU4 φ)
    · intro v hv
      exact CFSG.LieType.SeitzGeneration.OrthNS.extU_apply_perp hU4reg φ
        (by
          rw [hperpU4]
          exact hrange_le_R
            (CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine.othersSpace_le_range hxOdd hv))

  let P : HypPair (Q.restrict U4) :=
    { e := ⟨f, by rw [hU4def]; exact Submodule.mem_sup_right hfW⟩
      f := ⟨f', by rw [hU4def]; exact Submodule.mem_sup_right hf'W⟩
      Q_e := by simpa [QuadraticMap.restrict_apply] using hfQ
      Q_f := by simpa [QuadraticMap.restrict_apply] using hf'Q
      polar_ef := by
        rw [hheq, CFSG.RankThree.PartOne.KCOrthogonal.polar_comp_subtype]
        exact hff' }
  have hWspan : Submodule.span F {f, f'} = W :=
    span_pair_eq_of_finrank_eq_two hfW hf'W hfQ hf'Q hff' hW
  have hWreg : PolarNondegOn Q W := by
    rw [hWdef]
    exact CFSG.LocalAnalysis.GLTheoremA.T173U.polarNondegOn_polarPerp hQ
      (polarNondegOn_of_nondegenerate (by
        have h := hF.nondeg_biSup (Finset.univ : Finset (Fin k))
        rw [show (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⨆ j, U j by simp] at h
        exact h))
  have hPperp_aniso : ∀ x : U4, x ∈ P.perp → x ≠ 0 → (Q.restrict U4) x ≠ 0 := by
    intro x hx hx0 hQx
    apply hx0
    have hfx : polar Q f (x : V) = 0 := by
      have hc := (HypPair.mem_perp.mp hx).1
      have hconv : polar (Q.restrict U4) P.e x = polar Q f (x : V) := by
        dsimp only [P]
        simp [QuadraticMap.restrict_apply, QuadraticMap.polar]
      rwa [hconv] at hc
    have hf'x : polar Q f' (x : V) = 0 := by
      have hc := (HypPair.mem_perp.mp hx).2
      have hconv : polar (Q.restrict U4) P.f x = polar Q f' (x : V) := by
        dsimp only [P]
        simp [QuadraticMap.restrict_apply, QuadraticMap.polar]
      rwa [hconv] at hc
    obtain ⟨u, hu, w, hw', hxuw⟩ := Submodule.mem_sup.mp x.2
    have hfw : polar Q f w = 0 := by
      have h1 : polar Q f (u + w) = 0 := by rw [hxuw]; exact hfx
      rw [polar_add_right] at h1
      have hfu : polar Q f u = 0 := by
        rw [polar_comm]; exact mem_polarPerp_iff.1 hfW u (le_iSup U a hu)
      rw [hfu, zero_add] at h1
      exact h1
    have hf'w : polar Q f' w = 0 := by
      have h1 : polar Q f' (u + w) = 0 := by rw [hxuw]; exact hf'x
      rw [polar_add_right] at h1
      have hf'u : polar Q f' u = 0 := by
        rw [polar_comm]; exact mem_polarPerp_iff.1 hf'W u (le_iSup U a hu)
      rw [hf'u, zero_add] at h1
      exact h1
    have hwperp : ∀ y ∈ W, polar Q w y = 0 := by
      intro y hy
      rw [← hWspan] at hy
      rw [Submodule.mem_span_pair] at hy
      obtain ⟨α, β, rfl⟩ := hy
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq]
      have h1 : polar Q w f = 0 := by rw [polar_comm]; exact hfw
      have h2 : polar Q w f' = 0 := by rw [polar_comm]; exact hf'w
      rw [h1, h2, mul_zero, mul_zero, add_zero]
    have hw0 : w = 0 := hWreg w hw' hwperp
    have hxUa : (x : V) ∈ U a := by
      rw [← hxuw, hw0, add_zero]
      exact hu
    have hxval0 : (x : V) = 0 :=
      eq_zero_of_quad_eq_zero_of_not_isPlusType (hF.finrank_eq a) (hF.not_isPlusType a)
        hxUa (by simpa using hQx)
    exact Subtype.ext hxval0
  have hspanP : P.perp ≤
      Submodule.span F {x | x ∈ P.perp ∧ (Q.restrict U4) x ≠ 0} := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨hx, hPperp_aniso x hx hx0⟩
  have hle : elementaryGroup (Q.restrict U4) ≤ orthDerived (Q.restrict U4) :=
    elementaryGroup_le_commutator_of_perp_le_span hQ4 P hspanP
  have hmap : (orthDerived (Q.restrict U4)).map Hom ≤ ⁅B, B⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hEXTB hEXTB
  have hz4 : z ∈ U4 := by rw [hU4def]; exact hz
  have hw4 : w ∈ U4 := by rw [hU4def]; exact hw
  have hφΩ : eichler (Q.restrict U4) ⟨z, hz4⟩ ⟨w, hw4⟩ ∈ orthDerived (Q.restrict U4) :=
    hle (eichler_mem_elementaryGroup (Q.restrict U4) _ _)
  have hHomE : Hom (eichler (Q.restrict U4) ⟨z, hz4⟩ ⟨w, hw4⟩) = eichler Q z w := by
    have h1 : eichler (Q.restrict U4) ⟨z, hz4⟩ ⟨w, hw4⟩ =
        eichler (Q.comp U4.subtype) ⟨z, hz4⟩ ⟨w, hw4⟩ := by rw [hheq]
    dsimp only [Hom]
    rw [h1, CFSG.LieType.SeitzGeneration.OrthNS.extU_eichler]
  have hmem : eichler Q z w ∈ ⁅B, B⁆ := by
    rw [← hHomE]
    exact hmap (Subgroup.mem_map_of_mem Hom hφΩ)
  rw [OddOrderIsometry.supportedFixedDerived_eq hxOdd]
  exact hmem

theorem orthDerived_le_iSup_supportedFixedDerived {k : ℕ}
    {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)} {x : Fin k → ↥(orthDerived Q)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : Module.finrank F V = 2 * l) (hl : 3 ≤ l)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : IsPlaneFrame Q p U e E)
    {f f' : V} (hfW : f ∈ polarPerp Q (⨆ j, U j))
    (hf'W : f' ∈ polarPerp Q (⨆ j, U j)) (hfQ : Q f = 0) (hf'Q : Q f' = 0)
    (hff' : polar Q f f' = 1)
    (hW : Module.finrank F (polarPerp Q (⨆ j, U j)) = 2)
    (hx : ∀ a, (∀ v ∈ U a, (x a : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x a : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v)
    (hxE : ∀ a, x a ∈ E) :
    orthDerived Q ≤ ⨆ a, supportedFixedDerived Q (x a : V ≃ₗ[F] V) := by
  classical
  set W : Submodule F V := polarPerp Q (⨆ j, U j) with hWdef
  set H : Subgroup (V ≃ₗ[F] V) := ⨆ a, supportedFixedDerived Q (x a : V ≃ₗ[F] V)
  have hxaOdd : ∀ a, OddOrderIsometry Q p (x a : V ≃ₗ[F] V) := fun a =>
    oddOrderIsometry_of_orthDerived_pow_eq_one hQ hp hp2 (hF.isElemAbelian.2 (x a) (hxE a))
  have hHleO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine iSup_le fun a => ?_
    exact (OddOrderIsometry.supportedFixedDerived_le_orthDerived (hxaOdd a)).trans
      (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q)
  have hWspan : Submodule.span F {f, f'} = W :=
    span_pair_eq_of_finrank_eq_two hfW hf'W hfQ hf'Q hff' hW
  have hforall_f : ∀ r ∈ (⨆ j, U j), eichler Q f r ∈ H := by
    intro r hr
    have hmain : ∀ r ∈ (⨆ j, U j), polar Q f r = 0 ∧ eichler Q f r ∈ H := by
      intro r hr
      refine Submodule.iSup_induction U (motive := fun r => polar Q f r = 0 ∧
        eichler Q f r ∈ H) hr ?_ ?_ ?_
      · intro j v hv
        refine ⟨?_, ?_⟩
        · rw [polar_comm]
          exact mem_polarPerp_iff.1 hfW v (le_iSup U j hv)
        · exact le_iSup (fun a => supportedFixedDerived Q (x a : V ≃ₗ[F] V)) j
            (eichler_mem_supportedFixedDerived_signElt hQ hp hp2 hF hW (f := f) (f' := f')
              hfW hf'W hfQ hf'Q hff' hx hxE
              (Submodule.mem_sup_right hfW) (Submodule.mem_sup_left hv))
      · exact ⟨by simp, by rw [eichler_zero_right]; exact Subgroup.one_mem _⟩
      · intro x y hx' hy'
        refine ⟨?_, ?_⟩
        · rw [polar_add_right, hx'.1, hy'.1, add_zero]
        · rw [← eichler_mul hx'.1 hy'.1]
          exact H.mul_mem hx'.2 hy'.2
    exact (hmain r hr).2
  have hforall_f' : ∀ r ∈ (⨆ j, U j), eichler Q f' r ∈ H := by
    intro r hr
    have hmain : ∀ r ∈ (⨆ j, U j), polar Q f' r = 0 ∧ eichler Q f' r ∈ H := by
      intro r hr
      refine Submodule.iSup_induction U (motive := fun r => polar Q f' r = 0 ∧
        eichler Q f' r ∈ H) hr ?_ ?_ ?_
      · intro j v hv
        refine ⟨?_, ?_⟩
        · rw [polar_comm]
          exact mem_polarPerp_iff.1 hf'W v (le_iSup U j hv)
        · exact le_iSup (fun a => supportedFixedDerived Q (x a : V ≃ₗ[F] V)) j
            (eichler_mem_supportedFixedDerived_signElt hQ hp hp2 hF hW (f := f) (f' := f')
              hfW hf'W hfQ hf'Q hff' hx hxE
              (Submodule.mem_sup_right hf'W) (Submodule.mem_sup_left hv))
      · exact ⟨by simp, by rw [eichler_zero_right]; exact Subgroup.one_mem _⟩
      · intro x y hx' hy'
        refine ⟨?_, ?_⟩
        · rw [polar_add_right, hx'.1, hy'.1, add_zero]
        · rw [← eichler_mul hx'.1 hy'.1]
          exact H.mul_mem hx'.2 hy'.2
    exact (hmain r hr).2
  have hroot_f : ∀ w : V, polar Q f w = 0 → eichler Q f w ∈ H := by
    intro w hfw
    obtain ⟨r, hr, y, hy, hwr⟩ := Submodule.mem_sup.mp
      (hF.isCompl_iSup.sup_eq_top ▸ Submodule.mem_top (x := w))
    have hfr : polar Q f r = 0 := by
      rw [polar_comm]
      exact mem_polarPerp_iff.1 hfW r hr
    have hfy : polar Q f y = 0 := by
      have h1 : polar Q f (r + y) = 0 := by rw [hwr]; exact hfw
      rwa [polar_add_right, hfr, zero_add] at h1
    have hySpan : y ∈ Submodule.span F {f, f'} := by
      rw [hWspan]; exact hy
    rw [Submodule.mem_span_pair] at hySpan
    obtain ⟨α, β, hαβ⟩ := hySpan
    have hβ : β = 0 := by
      have h1 : polar Q f y = 0 := hfy
      rw [← hαβ, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_self_eq_zero hfQ, hff', mul_zero, mul_one, zero_add] at h1
      exact h1
    have hyα : y = α • f := by rw [← hαβ, hβ, zero_smul, add_zero]
    have hαf : eichler Q f (α • f) = 1 := by
      rw [show α • f = 0 + α • f by rw [zero_add], eichler_add_smul_self hfQ 0 α,
        eichler_zero_right]
    have hmul : eichler Q f r * eichler Q f (α • f) = eichler Q f (r + α • f) :=
      eichler_mul hfr (by rw [polar_smul_right_eq, polar_self_eq_zero hfQ, mul_zero])
    rw [show w = r + α • f by rw [← hwr, hyα], ← hmul, hαf, mul_one]
    exact hforall_f r hr
  have hroot_f' : ∀ w : V, polar Q f' w = 0 → eichler Q f' w ∈ H := by
    intro w hfw
    obtain ⟨r, hr, y, hy, hwr⟩ := Submodule.mem_sup.mp
      (hF.isCompl_iSup.sup_eq_top ▸ Submodule.mem_top (x := w))
    have hfr : polar Q f' r = 0 := by
      rw [polar_comm]
      exact mem_polarPerp_iff.1 hf'W r hr
    have hfy : polar Q f' y = 0 := by
      have h1 : polar Q f' (r + y) = 0 := by rw [hwr]; exact hfw
      rwa [polar_add_right, hfr, zero_add] at h1
    have hySpan : y ∈ Submodule.span F {f, f'} := by
      rw [hWspan]; exact hy
    rw [Submodule.mem_span_pair] at hySpan
    obtain ⟨α, β, hαβ⟩ := hySpan
    have hα : α = 0 := by
      have h1 : polar Q f' y = 0 := hfy
      rw [← hαβ, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_self_eq_zero hf'Q, polar_comm Q f' f, hff', mul_one, mul_zero, add_zero] at h1
      exact h1
    have hyβ : y = β • f' := by rw [← hαβ, hα, zero_smul, zero_add]
    have hβf : eichler Q f' (β • f') = 1 := by
      rw [show β • f' = 0 + β • f' by rw [zero_add], eichler_add_smul_self hf'Q 0 β,
        eichler_zero_right]
    have hmul : eichler Q f' r * eichler Q f' (β • f') = eichler Q f' (r + β • f') :=
      eichler_mul hfr (by rw [polar_smul_right_eq, polar_self_eq_zero hf'Q, mul_zero])
    rw [show w = r + β • f' by rw [← hwr, hyβ], ← hmul, hβf, mul_one]
    exact hforall_f' r hr
  rw [CFSG.LocalAnalysis.GLTheoremA.T173U.orthDerived_eq_elementaryGroup_of_three_le hQ hl hdim]
  refine elementaryGroup_le_of_eichler_mem fun z w hz hzw => ?_
  by_cases h : Q z = 0 ∧ polar Q z w = 0
  · exact eichler_mem_of_relRoot (H := H) hHleO (polarNondegOn_top hQ)
      (Submodule.mem_top) (Submodule.mem_top) hfQ hf'Q (by rw [hff']; exact one_ne_zero)
      (fun w _ => hroot_f w) (fun w _ => hroot_f' w) z (Submodule.mem_top) w (Submodule.mem_top)
  · rw [eichler_of_not h]
    exact Subgroup.one_mem _

end CFSG.StandardType.OmNsRootGen

end
