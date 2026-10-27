module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.TorusM8POmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaModel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTori
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourS2Plane
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourS1Plane
import CFSG.LocalAnalysis.StandardType.GGF4PairRootLeviTransport
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagSpin
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusSingleton
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusCentralizer
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEight
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
import CFSG.LieType.BorelTits.LeviOrder
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

namespace S2FramePlane

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  QuadraticMap

variable {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

private theorem polar_frame_scalars {t : spinGroup (quadMinus 4 K b c)} {l : Fin (4 - 1)}
    {μ ν : K} (ht : spinAction (quadMinus 4 K b c) t (minusVec 4 l true) = μ • minusVec 4 l true)
    (hf : spinAction (quadMinus 4 K b c) t (minusVec 4 l false) = ν • minusVec 4 l false) :
    μ * ν = 1 := by
  have h := polar_spinAction (quadMinus 4 K b c) t (minusVec 4 l true) (minusVec 4 l false)
  rw [ht, hf, polar_smul_left, polar_smul_right, polar_minusVec_minusVec] at h
  simpa [smul_eq_mul] using h

theorem spinAction_eq_of_mem_ggTorus_of_commute [CharP K 2]
    {t : spinGroup (quadMinus 4 K b c)} (ht : t ∈ ggTorus (minusDatum 4 hirr))
    (h1 : ∀ z ∈ minusRootGroup 4 hirr (Pi.single (1 : Fin (4 - 1)) 1), t * z * t⁻¹ = z)
    (h2 : ∀ z ∈ minusRootGroup 4 hirr (Pi.single (2 : Fin (4 - 1)) 1), t * z * t⁻¹ = z) :
    (∀ (l : Fin (4 - 1)), l ≠ 0 → ∀ r : Bool,
      spinAction (quadMinus 4 K b c) t (minusVec 4 l r) = minusVec 4 l r) ∧
    (∀ p : Fin 2 → K, spinAction (quadMinus 4 K b c) t (planeVec 4 p) = planeVec 4 p) ∧
    ∃ μ : Kˣ, spinAction (quadMinus 4 K b c) t (minusVec 4 0 true) = (μ : K) • minusVec 4 0 true ∧
      spinAction (quadMinus 4 K b c) t (minusVec 4 0 false) =
        ((μ⁻¹ : Kˣ) : K) • minusVec 4 0 false := by
  have hn : (4 : ℕ) ≤ 4 := le_rfl
  have hvec := fun l r =>
    ClassicalPosition.exists_spinAction_minusVec_eq_smul_POmegaMinus 4 hirr ht hn l r
  have hpl := fun p => ClassicalPosition.exists_spinAction_planeVec_eq_POmegaMinus 4 hirr ht hn p
  have hcomm : ∀ z, t * z * t⁻¹ = z → ∀ v,
      spinAction (quadMinus 4 K b c) t (spinAction (quadMinus 4 K b c) z v) =
        spinAction (quadMinus 4 K b c) z (spinAction (quadMinus 4 K b c) t v) := by
    intro z hz v
    have hzt : t * z = z * t := by
      calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [hz]
    have h := congrArg (fun y => spinAction (quadMinus 4 K b c) y v) hzt
    simpa only [map_mul, LinearEquiv.mul_apply] using h
  obtain ⟨μ2e, hμ2e⟩ := hvec 2 true
  obtain ⟨μ2f, hμ2f⟩ := hvec 2 false
  obtain ⟨μ1e, hμ1e⟩ := hvec 1 true
  obtain ⟨μ1f, hμ1f⟩ := hvec 1 false
  obtain ⟨μ0e, hμ0e⟩ := hvec 0 true
  obtain ⟨μ0f, hμ0f⟩ := hvec 0 false
  have hp2 := polar_frame_scalars hμ2e hμ2f
  have hp1 := polar_frame_scalars hμ1e hμ1f
  have hp0 := polar_frame_scalars hμ0e hμ0f
  have hk2 : ¬ (2 : Fin (4 - 1)).val + 1 < 4 - 1 := by decide
  have hshort : ∀ p : Fin 2 → K,
      spinAction (quadMinus 4 K b c) t (planeVec 4 p) + (planeNorm b c p * μ2f) • minusVec 4 2 true =
        μ2f • planeVec 4 p + (planeNorm b c p * μ2e) • minusVec 4 2 true := by
    intro p
    have hz : twShortRoot 4 hirr 2 true (.ofAdd p) ∈
        minusRootGroup 4 hirr (Pi.single (2 : Fin (4 - 1)) 1) := by
      rw [minusRootGroup_eq_short 4 hirr 2 true (toStdB_single_of_not_lt' 4 hk2)]
      exact ⟨_, rfl⟩
    have h := hcomm _ (h2 _ hz) (minusVec 4 2 false)
    rw [hμ2f, LinearEquiv.map_smul, spinAction_twShortRoot] at h
    simp only [polar_minusVec_minusVec, polar_minusVec_planeVec, Bool.not_true,
      and_self, ite_true, one_smul, zero_smul, sub_zero, mul_one, map_add,
      map_sub, LinearEquiv.map_smul, hμ2e, hμ2f] at h
    linear_combination (norm := module) h
  have he2 : μ2e = μ2f := by
    have h := congrFun (hshort planeOne) (.inl 2)
    obtain ⟨q, hq⟩ := hpl planeOne
    rw [hq] at h
    simpa [planeNorm_planeOne, planeVec, minusVec, eVec] using h.symm
  have hf2 : μ2f = 1 := by
    rw [he2] at hp2
    exact CFSG.SeitzReduction.OmegaPilot.eq_one_of_mul_self_eq_one hp2
  have he2' : μ2e = 1 := he2.trans hf2
  have hplane : ∀ p : Fin 2 → K,
      spinAction (quadMinus 4 K b c) t (planeVec 4 p) = planeVec 4 p := by
    intro p
    have h := hshort p
    rw [he2', hf2, one_smul] at h
    exact add_right_cancel h
  have hk1 : (1 : Fin (4 - 1)).val + 1 < 4 - 1 := by decide
  have he1 : μ1e = 1 := by
    have hz : (minusFrame 4 b c).longRoot (succ_ne_of_lt 4 hk1) true false (.ofAdd 1) ∈
        minusRootGroup 4 hirr (Pi.single (1 : Fin (4 - 1)) 1) := by
      rw [minusRootGroup_single_of_lt 4 hirr hk1]
      exact ⟨_, rfl⟩
    have h := hcomm _ (h1 _ hz) (minusVec 4 2 true)
    have hj : (⟨(1 : Fin (4 - 1)).val + 1, hk1⟩ : Fin (4 - 1)) = 2 := rfl
    rw [hμ2e, he2', one_smul, HypFrame.spinAction_longRoot, minusFrame_vec, hj] at h
    simp only [polar_minusVec_minusVec, Bool.not_false, and_self, ite_true,
      one_mul, one_smul, map_add, map_sub, LinearEquiv.map_smul, hμ1e, hμ2e, he2'] at h
    have h' := congrFun h (.inl 1)
    simpa [minusVec, eVec, fVec] using h'
  have hf1 : μ1f = 1 := by rw [he1, one_mul] at hp1; exact hp1
  have hμ0 : μ0e ≠ 0 := left_ne_zero_of_mul_eq_one hp0
  refine ⟨?_, hplane, Units.mk0 μ0e hμ0, hμ0e, ?_⟩
  · intro l hl r
    fin_cases l
    · exact absurd rfl hl
    · cases r
      · rw [hf1, one_smul] at hμ1f; exact hμ1f
      · rw [he1, one_smul] at hμ1e; exact hμ1e
    · cases r
      · rw [hf2, one_smul] at hμ2f; exact hμ2f
      · rw [he2', one_smul] at hμ2e; exact hμ2e
  · rw [hμ0f, Units.val_inv_eq_inv_val, Units.val_mk0, eq_inv_of_mul_eq_one_right hp0]

open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveProjection matrixDerived matrixLinearIso)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus minusIndexEquiv reindexVectorEquiv)

theorem reindexVectorEquiv_single {ι : Type} [DecidableEq ι] {d : ℕ} (e : ι ≃ Fin d) (y : ι) :
    reindexVectorEquiv (K := K) e (Pi.single y 1) = Pi.single (e y) 1 := by
  funext i
  rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointData.reindexVectorEquiv_apply]
  by_cases h : i = e y
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    exact h (by rw [← h', Equiv.apply_symm_apply])

@[expose] noncomputable def spinPilotMinus [Finite K] :
    spinGroup (quadMinus 4 K b c) →* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c) :=
  (matrixProjectiveProjection _).comp (AutOm.spinModelMinus le_rfl hirr)

theorem matrixLinearIso_spinModelMinus [Finite K] (x : spinGroup (quadMinus 4 K b c))
    (w : Vm 4 K) :
    matrixLinearIso ((AutOm.spinModelMinus le_rfl hirr x : matrixDerived _) : GL (Fin (2 * 4)) K)
        (reindexVectorEquiv (minusIndexEquiv 4 (by omega)) w) =
      reindexVectorEquiv (minusIndexEquiv 4 (by omega)) (spinAction (quadMinus 4 K b c) x w) :=
  AutOm.spinModelMinus_mulVec le_rfl hirr x w

theorem projHom_derivedEquiv_spinModelMinus [Finite K] (x : spinGroup (quadMinus 4 K b c)) :
    projHom _ (derivedEquiv _ (AutOm.spinModelMinus le_rfl hirr x)) = spinPilotMinus hirr x := by
  simp [projHom, spinPilotMinus]

theorem spinPilotMinus_mem_minusPairPerp [Finite K] {z : spinGroup (quadMinus 4 K b c)}
    (he : spinAction (quadMinus 4 K b c) z (minusVec 4 0 true) = minusVec 4 0 true)
    (hf : spinAction (quadMinus 4 K b c) z (minusVec 4 0 false) = minusVec 4 0 false) :
    spinPilotMinus hirr z ∈ minusPairPerp (by omega) b c 0 := by
  refine ⟨derivedEquiv _ (AutOm.spinModelMinus le_rfl hirr z), ?_,
    projHom_derivedEquiv_spinModelMinus hirr z⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_stabSub, coe_derivedEquiv]
  constructor
  · rw [← reindexVectorEquiv_single, matrixLinearIso_spinModelMinus]
    exact congrArg _ he
  · rw [← reindexVectorEquiv_single, matrixLinearIso_spinModelMinus]
    exact congrArg _ hf

theorem torusLin_single_of_ne {ι : Type} [DecidableEq ι] {a b y : ι} (hya : y ≠ a) (hyb : y ≠ b)
    (μ : Kˣ) : torusLin a b μ (Pi.single y 1) = (Pi.single y 1 : ι → K) := by
  funext i
  rw [torusLin_apply]
  by_cases hi : i = y
  · subst hi
    simp [torusEntry, hya, hyb]
  · simp [Pi.single_eq_of_ne hi]

theorem single_plane_eq_planeVec (j : Fin 2) :
    (Pi.single (.inr (.inr j)) 1 : Vm 4 K) = planeVec 4 (Pi.single j 1) := by
  funext y
  rcases y with l | l | j'
  · simp [planeVec]
  · simp [planeVec]
  · by_cases h : j' = j
    · subst h
      simp [planeVec]
    · simp [planeVec, h]

theorem spinPilotMinus_mem_minusPairTorus [Finite K] {t : spinGroup (quadMinus 4 K b c)}
    (hfr : ∀ (l : Fin (4 - 1)), l ≠ 0 → ∀ r : Bool,
      spinAction (quadMinus 4 K b c) t (minusVec 4 l r) = minusVec 4 l r)
    (hpl : ∀ p : Fin 2 → K, spinAction (quadMinus 4 K b c) t (planeVec 4 p) = planeVec 4 p)
    {μ : Kˣ}
    (he : spinAction (quadMinus 4 K b c) t (minusVec 4 0 true) = (μ : K) • minusVec 4 0 true)
    (hf : spinAction (quadMinus 4 K b c) t (minusVec 4 0 false) =
      ((μ⁻¹ : Kˣ) : K) • minusVec 4 0 false) :
    spinPilotMinus hirr t ∈ minusPairTorus (by omega) b c 0 := by
  have hspin : spinAction (quadMinus 4 K b c) t =
      torusLin (K := K) (.inl 0 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (.inr (.inl 0)) μ := by
    apply (Pi.basisFun K _).ext'
    intro y
    rw [Pi.basisFun_apply]
    rcases y with l | l | j
    · by_cases hl : l = 0
      · subst hl
        exact he.trans (torusLin_single_left (by simp) μ).symm
      · rw [torusLin_single_of_ne (by simpa using hl) (by simp)]
        exact hfr l hl true
    · by_cases hl : l = 0
      · subst hl
        exact hf.trans (torusLin_single_right (by simp) μ).symm
      · rw [torusLin_single_of_ne (by simp) (by simpa using hl)]
        exact hfr l hl false
    · rw [torusLin_single_of_ne (by simp) (by simp), single_plane_eq_planeVec]
      exact hpl _
  refine ⟨derivedEquiv _ (AutOm.spinModelMinus le_rfl hirr t), ?_,
    projHom_derivedEquiv_spinModelMinus hirr t⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  refine ⟨μ, ?_⟩
  rw [coe_derivedEquiv]
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := (reindexVectorEquiv (K := K) (minusIndexEquiv 4 (by omega))).surjective v
  rw [matrixLinearIso_spinModelMinus, hspin]
  funext i
  rw [torusLin_apply, CFSG.ComponentClassification.CatalogueBOrthogonalPointData.reindexVectorEquiv_apply,
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.reindexVectorEquiv_apply,
    torusLin_apply]
  congr 2
  simp only [torusEntry, Equiv.symm_apply_eq]

theorem spinPilotMinus_bijective [Finite K] [CharP K 2] :
    Function.Bijective (spinPilotMinus hirr) := by
  have hQ : ∃ v, coordinateQuadMinus 4 K (by omega) b c v ≠ 0 :=
    (isHypCoord_coordinateQuadMinus (by omega) b c 0).exists_ne_zero
  have hinj : Function.Injective
      (matrixProjectiveProjection (coordinateQuadMinus 4 K (by omega) b c)) := by
    intro A B h
    have h' : projHom _ (derivedEquiv _ A) = projHom _ (derivedEquiv _ B) := by
      simpa [projHom] using h
    exact (derivedEquiv _).injective (projHom_injective hQ h')
  exact ⟨hinj.comp (AutOm.spinModelMinus_injective le_rfl hirr),
    (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveProjection_surjective
      _).comp (AutOm.spinModelMinus_surjective le_rfl hirr)⟩

theorem spinAction_minusVec_zero_of_mem {k : Fin (4 - 1)} (hk : k ≠ 0)
    {z : spinGroup (quadMinus 4 K b c)}
    (hz : z ∈ minusRootGroup 4 hirr (Pi.single k 1) ⊔ minusRootGroup 4 hirr (-Pi.single k 1))
    (r : Bool) : spinAction (quadMinus 4 K b c) z (minusVec 4 0 r) = minusVec 4 0 r := by
  let S : Subgroup (spinGroup (quadMinus 4 K b c)) :=
    (stabSub (K := K) (.inl 0 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (.inr (.inl 0))).comap
      (spinAction (quadMinus 4 K b c))
  have hlong : ∀ {i j : Fin (4 - 1)} (hij : i ≠ j), i ≠ 0 → j ≠ 0 → ∀ s t : Bool,
      ((minusFrame 4 b c).longRoot hij s t).range ≤ S := by
    rintro i j hij hi hj s t _ ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · exact HypFrame.spinAction_longRoot_vec_of_ne _ hij s t (Multiplicative.toAdd a)
        (Ne.symm hi) (Ne.symm hj) true
    · exact HypFrame.spinAction_longRoot_vec_of_ne _ hij s t (Multiplicative.toAdd a)
        (Ne.symm hi) (Ne.symm hj) false
  have hshort : ∀ s : Bool, (twShortRoot 4 hirr 2 s).range ≤ S := by
    rintro s _ ⟨a, rfl⟩
    have h0 : ∀ u : Bool, polar (quadMinus 4 K b c) (minusVec 4 0 u) (minusVec 4 2 s) = 0 := by
      intro u
      rw [polar_minusVec_minusVec, if_neg (fun h => absurd h.1 (by decide))]
    refine ⟨?_, ?_⟩
    · exact spinAction_twShortRoot_of_polar 4 hirr 2 s (Multiplicative.toAdd a) (h0 true)
        (polar_minusVec_planeVec 4 b c 0 true _)
    · exact spinAction_twShortRoot_of_polar 4 hirr 2 s (Multiplicative.toAdd a) (h0 false)
        (polar_minusVec_planeVec 4 b c 0 false _)
  have hle : minusRootGroup 4 hirr (Pi.single k 1) ⊔ minusRootGroup 4 hirr (-Pi.single k 1) ≤ S := by
    fin_cases k
    · exact absurd rfl hk
    · have hk1 : (1 : Fin (4 - 1)).val + 1 < 4 - 1 := by decide
      refine sup_le ?_ ?_
      · rw [show ((⟨1, by decide⟩ : Fin (4 - 1)) : Fin (4 - 1)) = 1 from rfl,
          minusRootGroup_single_of_lt 4 hirr hk1]
        exact hlong (succ_ne_of_lt 4 hk1) (by decide) (by simp [Fin.ext_iff]) true false
      · rw [show ((⟨1, by decide⟩ : Fin (4 - 1)) : Fin (4 - 1)) = 1 from rfl,
          minusRootGroup_eq_long 4 hirr (succ_ne_of_lt 4 hk1).symm true false
            (toStdB_neg_single_of_lt' 4 hk1)]
        exact hlong (succ_ne_of_lt 4 hk1).symm (by simp [Fin.ext_iff]) (by decide) true false
    · have hk2 : ¬ (2 : Fin (4 - 1)).val + 1 < 4 - 1 := by decide
      refine sup_le ?_ ?_
      · rw [show ((⟨2, by decide⟩ : Fin (4 - 1)) : Fin (4 - 1)) = 2 from rfl,
          minusRootGroup_eq_short 4 hirr 2 true (toStdB_single_of_not_lt' 4 hk2)]
        exact hshort true
      · rw [show ((⟨2, by decide⟩ : Fin (4 - 1)) : Fin (4 - 1)) = 2 from rfl,
          minusRootGroup_eq_short 4 hirr 2 false (toStdB_neg_single_of_not_lt' 4 hk2)]
        exact hshort false
  have hzS := hle hz
  cases r
  · exact hzS.2
  · exact hzS.1

end S2FramePlane

section Plane

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.SeitzReduction.OmegaPilot S2FramePlane
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus minusIndexEquiv)

theorem exists_simplePair_of_tableBPos_POmegaMinus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 1 ≤ f)
    {ψ : (ggU .POmegaMinus 4 f).K →* G} (hpos : GGTableBPos p Bs X .POmegaMinus 4 f ψ)
    (w : CoxeterMatrix.F₄.Group) {i j : Fin 4} (hij : i ≠ j)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    ∃ (ν : GGWeyl (ggU .POmegaMinus 4 f).D →* (ggU .POmegaMinus 4 f).K)
      (u : GGWeyl (ggU .POmegaMinus 4 f).D) (c d : Fin 3),
      GGWeylLift (ggU .POmegaMinus 4 f).D ν ∧
      (CoxeterMatrix.F₄ i j = 2 → c = 0 ∧ d = 2 ∨ c = 2 ∧ d = 0) ∧
      (CoxeterMatrix.F₄ i j = 3 → c = 0 ∧ d = 1) ∧
      (CoxeterMatrix.F₄ i j = 4 → c = 2 ∧ d = 1 ∨ c = 1 ∧ d = 2) ∧
      ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) =
        (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single c 1)).map
          ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) ∧
      ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) =
        (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single d 1)).map
          ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) := by
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 f := ⟨Nat.prime_two, hf, le_rfl⟩
  obtain ⟨ν, hν⟩ := (ggTagFacts_POmegaMinus hadm (by decide)).2.1
  obtain ⟨u, c, d, hSi, hSj, h2, h3, h4⟩ :=
    exists_f4_pair_rootLevi_transport (ggU .POmegaMinus 4 f).D hpp hp2 hEl hNT hAind hpres hXA
      ψ ε hεrefl hεlevi (Equiv.refl _) hM ν hν w i j hij hi hj
  exact ⟨ν, u, c, d, hν, h2, h3, h4, hSi, hSj⟩

theorem exists_su4Plane_of_tableBPos_POmegaMinus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    {ψ : (ggU .POmegaMinus 4 f).K →* G}
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K)
    (hrange : ψ.range = X) (hpos : GGTableBPos p Bs X .POmegaMinus 4 f ψ)
    (htor : ∀ b ∈ Bs, ∃ t ∈ ggTorus (ggU .POmegaMinus 4 f).D,
      ∀ z, b * ψ z * b⁻¹ = ψ (t * z * t⁻¹))
    (w : CoxeterMatrix.F₄.Group) {r u : MulAut ↥Bs}
    (hr : r = ((e (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hrX : r ∈ ggAutomizer X Bs) (huX : u ∈ ggAutomizer X Bs)
    (hDX : ¬ ggHyperplane Bs r ⊓ ggHyperplane Bs u ≤ Subgroup.centralizer (X : Set G)) :
    ∃ J' : Subgroup G,
      LargeEvenLayer (X ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r ⊓ ggHyperplane Bs u : Subgroup G) : Set G)) = J' ∧
      CFSG.Assembly.IsComponentOf J' (X ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r ⊓ ggHyperplane Bs u : Subgroup G) : Set G)) ∧
      Bs ⊓ Subgroup.centralizer (J' : Set G) = ggHyperplane Bs r ⊓ ggHyperplane Bs u ∧
      ggRankOneIn X Bs r ≤ J' ∧ ggRankOneIn X Bs u ≤ J' ∧
      CFSG.Blueprint.LieModel J' .PSU 4 2 f ∧ p ∣ Nat.card J' ∧ ¬ LargeEvenSmall J' := by
  set D' : Subgroup G := ggHyperplane Bs r ⊓ ggHyperplane Bs u with hD'
  have hf1 : 1 ≤ f := by omega
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have hr2 : r ^ 2 = 1 := (ggCoxRefl_isReflection hpres.2 ⟨w, 2, hr⟩).1
  have hu2 : u ^ 2 = 1 := (ggCoxRefl_isReflection hpres.2 ⟨w, 1, hu⟩).1
  obtain ⟨ν, v, c, d, hν, -, -, h4, hSi, hSj⟩ :=
    exists_simplePair_of_tableBPos_POmegaMinus hpp hp2 hEl hNT hAind hpres hXA hf1 hpos w h21
      (hr ▸ hrX) (hu ▸ huX)
  rw [← hr] at hSi
  rw [← hu] at hSj
  have hcd : c = 2 ∧ d = 1 ∨ c = 1 ∧ d = 2 := h4 (by decide)
  set ψ' : (ggU .POmegaMinus 4 f).K →* G := (MulAut.conj (ψ (ν v))).toMonoidHom.comp ψ with hψ'
  have hψ'apply : ∀ z, ψ' z = ψ (ν v * z * (ν v)⁻¹) := fun z => by
    rw [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_mul, map_inv]
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (PsiDiag.SpinM.center_eq_bot (minusCoeffs_irr 2 f) le_rfl).le
  have hinj' : Function.Injective ψ' := (MulAut.conj (ψ (ν v))).injective.comp hinj
  have hrange' : ψ'.range = X := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, (hψ'apply z).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨(ν v)⁻¹ * z * ν v, ?_⟩
      rw [hψ'apply]
      exact congrArg ψ (by group)
  have htor' : ∀ b ∈ Bs, ∃ t ∈ ggTorus (ggU .POmegaMinus 4 f).D,
      ∀ z, b * ψ' z * b⁻¹ = ψ' (t * z * t⁻¹) := by
    intro b hb
    obtain ⟨t, ht, htz⟩ := htor b hb
    refine ⟨(ν v)⁻¹ * t * ν v, ggWeylLift_inv_conj_mem_ggTorus _ hν v ht, fun z => ?_⟩
    rw [hψ'apply, hψ'apply, htz]
    exact congrArg ψ (by group)
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hirr := minusCoeffs_irr 2 f
  have hH := isHypCoord_coordinateQuadMinus (K := GaloisField 2 f) (by omega : 1 ≤ 4)
    (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 0
  let Φe : (ggU .POmegaMinus 4 f).K ≃* matrixProjectiveDerived (coordinateQuadMinus 4
      (GaloisField 2 f) (by omega) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) :=
    MulEquiv.ofBijective (spinPilotMinus hirr) (spinPilotMinus_bijective hirr)
  let φ : matrixProjectiveDerived (coordinateQuadMinus 4 (GaloisField 2 f) (by omega)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) →* G := ψ'.comp Φe.symm.toMonoidHom
  have hφΦ : ∀ z, φ (spinPilotMinus hirr z) = ψ' z := fun z => by
    change ψ' (Φe.symm (Φe z)) = ψ' z
    exact congrArg ψ' (Φe.symm_apply_apply z)
  have hφinj : Function.Injective φ := hinj'.comp Φe.symm.injective
  have hφrange : φ.range = X := by
    rw [← hrange']
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨spinPilotMinus hirr z, hφΦ z⟩
  set J' : Subgroup G := (minusPairPerp (by omega) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
    (0 : Fin (4 - 1))).map φ with hJ'
  have hLevJ : ∀ k : Fin 3, k ≠ 0 →
      (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single k 1)).map ψ' ≤ J' := by
    rintro k hk _ ⟨y, hy, rfl⟩
    refine ⟨spinPilotMinus hirr y, ?_, hφΦ y⟩
    exact spinPilotMinus_mem_minusPairPerp hirr
      (spinAction_minusVec_zero_of_mem hirr (k := k) hk hy true)
      (spinAction_minusVec_zero_of_mem hirr (k := k) hk hy false)
  have hc0 : c ≠ 0 := by rcases hcd with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hd0 : d ≠ 0 := by rcases hcd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hrJ : ggRankOneIn X Bs r ≤ J' := hSi ▸ hLevJ c hc0
  have huJ : ggRankOneIn X Bs u ≤ J' := hSj ▸ hLevJ d hd0
  have hJX : J' ≤ X := hφrange ▸ Subgroup.map_le_range _ _
  have hDBs : D' ≤ Bs := by
    rintro b ⟨⟨c', -, rfl⟩, -⟩
    exact c'.2
  have hSrX : ggRankOneIn X Bs r ≤ X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    ggOTwoPrime_le _
  have hSuX : ggRankOneIn X Bs u ≤ X ⊓ Subgroup.centralizer (ggHyperplane Bs u : Set G) :=
    ggOTwoPrime_le _
  have hX0 : ∀ b ∈ D', ∃ t : (ggU .POmegaMinus 4 f).K,
      (∀ z, b * ψ' z * b⁻¹ = ψ' (t * z * t⁻¹)) ∧
        spinPilotMinus hirr t ∈ minusPairTorus _ (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
          (0 : Fin (4 - 1)) := by
    intro b hb
    obtain ⟨t, ht, htz⟩ := htor' b (hDBs hb)
    have hfix : ∀ k : Fin 3, (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single k 1)).map ψ' ≤
        Subgroup.centralizer ({b} : Set G) →
        ∀ y ∈ ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single k 1), t * y * t⁻¹ = y := by
      intro k hk y hy
      have hby : ψ' y * b = b * ψ' y :=
        Subgroup.mem_centralizer_singleton_iff.mp (hk ⟨y, hy, rfl⟩)
      apply hinj'
      rw [← htz, ← hby]
      group
    have hbr : (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single c 1)).map ψ' ≤
        Subgroup.centralizer ({b} : Set G) := by
      rw [← hSi]
      intro y hy
      have hy' := (hSrX hy).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hy' b hb.1).symm
    have hbu : (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single d 1)).map ψ' ≤
        Subgroup.centralizer ({b} : Set G) := by
      rw [← hSj]
      intro y hy
      have hy' := (hSuX hy).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hy' b hb.2).symm
    have h12 : (∀ y ∈ ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single (1 : Fin 3) 1),
        t * y * t⁻¹ = y) ∧ ∀ y ∈ ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single (2 : Fin 3) 1),
        t * y * t⁻¹ = y := by
      rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hfix 1 hbu, hfix 2 hbr⟩
      · exact ⟨hfix 1 hbr, hfix 2 hbu⟩
    obtain ⟨hfr, hpl, μ, he, hf'⟩ := spinAction_eq_of_mem_ggTorus_of_commute hirr ht
      (fun z hz => h12.1 z (Subgroup.mem_sup_left hz))
      (fun z hz => h12.2 z (Subgroup.mem_sup_left hz))
    exact ⟨t, htz, spinPilotMinus_mem_minusPairTorus hirr hfr hpl he hf'⟩
  have hφapply : ∀ y, φ y = ψ' (Φe.symm y) := fun y => rfl
  have hDJ : D' ≤ Subgroup.centralizer (J' : Set G) := by
    intro b hb
    obtain ⟨t, htz, htX⟩ := hX0 b hb
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hyt : Φe t * y = y * Φe t :=
      Subgroup.mem_centralizer_iff.mp (hH.pairPerpOf_le_centralizer hK4 hy) (Φe t) htX
    have e2 : t * Φe.symm y * t⁻¹ = Φe.symm y := by
      apply Φe.injective
      rw [map_mul, map_mul, map_inv, Φe.apply_symm_apply, hyt, mul_inv_cancel_right]
    have e1 := htz (Φe.symm y)
    rw [e2] at e1
    rw [hφapply]
    calc ψ' (Φe.symm y) * b = b * ψ' (Φe.symm y) * b⁻¹ * b := by rw [e1]
      _ = b * ψ' (Φe.symm y) := by group
  have hcent : Bs ⊓ Subgroup.centralizer (J' : Set G) = D' := by
    refine le_antisymm ?_ (le_inf hDBs hDJ)
    rintro b ⟨hb, hbc⟩
    exact ⟨mem_ggHyperplane_of_mem_centralizer_ggRankOneIn hrX hr2 hb
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hrJ) hbc),
      mem_ggHyperplane_of_mem_centralizer_ggRankOneIn huX hu2 hb
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr huJ) hbc)⟩
  obtain ⟨b0, hb0D, hb0X⟩ := Set.not_subset.mp hDX
  obtain ⟨t0, ht0z, ht0X⟩ := hX0 b0 hb0D
  have ht01 : spinPilotMinus hirr t0 ≠ 1 := by
    intro h1
    have ht1 : t0 = 1 := (spinPilotMinus_bijective hirr).1 (h1.trans (map_one _).symm)
    apply hb0X
    show b0 ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [← hrange'] at hg
    obtain ⟨z, rfl⟩ := hg
    have h1' := ht0z z
    rw [ht1, one_mul, inv_one, mul_one] at h1'
    calc ψ' z * b0 = b0 * ψ' z * b0⁻¹ * b0 := by rw [h1']
      _ = b0 * ψ' z := by group
  have hfixC : ∀ g ∈ X ⊓ Subgroup.centralizer (D' : Set G), ∃ y, φ y = g ∧
      y ∈ Subgroup.centralizer (pairTorusOf (coordinateQuadMinus 4 (GaloisField 2 f) _
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) (minusIndexEquiv 4 (by norm_num) (.inl 0))
        (minusIndexEquiv 4 (by norm_num) (.inr (.inl 0))) : Set (matrixProjectiveDerived (coordinateQuadMinus 4
          (GaloisField 2 f) _ (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) := by
    rintro g ⟨hgX, hgD⟩
    rw [← hφrange] at hgX
    obtain ⟨y, rfl⟩ := hgX
    refine ⟨y, rfl, ?_⟩
    have hc0' : b0 * ψ' (Φe.symm y) = ψ' (Φe.symm y) * b0 := by
      rw [← hφapply]
      exact Subgroup.mem_centralizer_iff.mp hgD b0 hb0D
    have e1 := ht0z (Φe.symm y)
    rw [hc0', mul_inv_cancel_right] at e1
    have e2 : t0 * Φe.symm y * t0⁻¹ = Φe.symm y := (hinj' e1).symm
    have e3 := congrArg Φe e2
    rw [map_mul, map_mul, map_inv, Φe.apply_symm_apply] at e3
    have hz1 : y ∈ Subgroup.centralizer ({spinPilotMinus hirr t0} : Set _) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      change y * Φe t0 = Φe t0 * y
      calc y * Φe t0 = Φe t0 * y * (Φe t0)⁻¹ * Φe t0 := by rw [e3]
        _ = Φe t0 * y := by group
    rwa [hH.centralizer_singleton_eq_centralizer_pairTorusOf hK4 ht0X ht01] at hz1
  have hcomm : ∀ g ∈ X ⊓ Subgroup.centralizer (D' : Set G),
      ∀ h ∈ X ⊓ Subgroup.centralizer (D' : Set G), g * h * g⁻¹ * h⁻¹ ∈ J' := by
    intro g hg h hh
    obtain ⟨y1, rfl, hy1⟩ := hfixC g hg
    obtain ⟨y2, rfl, hy2⟩ := hfixC h hh
    refine ⟨y1 * y2 * y1⁻¹ * y2⁻¹, hH.commutator_mem_pairPerpOf hK4 hy1 hy2, ?_⟩
    simp only [map_mul, map_inv]
  have hJq : CFSG.IsQuasisimple J' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((minusPairPerp _ (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (0 : Fin (4 - 1))).equivMapOfInjective
        φ hφinj)
      (isQuasisimple_minusPairPerp_of_four_le le_rfl hirr 0)
  obtain ⟨hlay, hcompJ⟩ :=
    TableBSymp.largeEvenLayer_eq_of_commutator_mem (le_inf hJX (Subgroup.le_centralizer_iff.mp hDJ))
      hcomm hJq
  obtain ⟨ε, -, hεlevi, -⟩ := id hpos
  have hk2 : 2 < (ggU .POmegaMinus 4 f).D.rank := by change 2 < 4 - 1; norm_num
  obtain ⟨F, _, _, θ, -, hθinj, hθ, hFcard⟩ :=
    exists_sl2_ggRankOneIn_node_POmegaMinus hf1 hker hεlevi 1 ⟨2, hk2⟩
  rw [if_neg (by norm_num)] at hFcard
  have hL2 : (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single (2 : Fin 3) 1)).map ψ =
      ggRankOneIn X Bs ((ε (1 * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple
        ⟨2, hk2⟩ * 1⁻¹) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
    rw [hεlevi, map_one]
    rfl
  have hcardL2 : Nat.card ((ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single (2 : Fin 3) 1)).map ψ') =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.card_map_of_injective hinj', ← Subgroup.card_map_of_injective hinj, hL2, ← hθ,
      ← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv]
  have hdvd : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ∣ Nat.card J' := by
    rw [← hcardL2]
    exact Subgroup.card_dvd_of_le (hLevJ 2 (by decide))
  rw [CFSG.LieType.BorelTits.card_specialLinearGroup_fin_two hFcard] at hdvd
  have hpJ : p ∣ Nat.card J' := by
    refine dvd_trans ?_ hdvd
    refine Dvd.dvd.mul_left (hpf.trans ?_) _
    have h4 : (2 ^ (2 * f)) ^ 2 = (2 ^ f) ^ 4 := by ring
    rw [h4]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ f) 4
  have hsmall : ¬ LargeEvenSmall J' := by
    have hJ0 : 0 < Nat.card J' := Nat.card_pos
    have hbig : ∀ N, N = 25920 ∨ N = 360 → ¬ (2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) ∣ N := by
      rintro N hN hdN
      have hN0 : 0 < N := by rcases hN with rfl | rfl <;> norm_num
      have hle := Nat.le_of_dvd hN0 hdN
      rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | h3
      · rcases hN with rfl | rfl <;> norm_num at hdN
      · have h64 : 64 ≤ 2 ^ (2 * f) :=
          calc 64 = 2 ^ 6 := by norm_num
            _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hsq : 4096 ≤ (2 ^ (2 * f)) ^ 2 :=
          calc 4096 = 64 ^ 2 := by norm_num
            _ ≤ (2 ^ (2 * f)) ^ 2 := Nat.pow_le_pow_left h64 2
        have hN' : N ≤ 25920 := by rcases hN with rfl | rfl <;> norm_num
        have : 64 * 4095 ≤ 2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1) :=
          Nat.mul_le_mul h64 (by omega)
        omega
    rintro (hU | hA)
    · exact hbig _ (Or.inl rfl) (IOneOrthEnd.card_of_isU42 hU ▸ hdvd)
    · obtain ⟨e6⟩ := hA
      exact hbig _ (Or.inr rfl)
        ((Nat.card_congr e6.toEquiv).trans IOneOrthEnd.card_alternatingGroup_six ▸ hdvd)
  exact ⟨J', hlay, hcompJ, hcent, hrJ, huJ,
    lieModel_map_minusPairPerp_four (GaloisField.card 2 f (by omega)) hirr hφinj 0, hpJ, hsmall⟩

end Plane

end CFSG.StandardType

end
