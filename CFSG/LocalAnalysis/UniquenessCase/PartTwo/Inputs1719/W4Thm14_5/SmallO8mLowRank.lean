module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mLowRankGeometry
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mPerp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mPerpPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mRankOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mWeightArithmetic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mShortSection
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bGamma
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyDisplacement
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSpinMinus
import CFSG.SignalizerFunctorTheorem.NonLocal.AbelianLift
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.NontrivialFactor
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.DigitConds
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Digits
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums
import CFSG.LieType.TitsSimplicity.Descent
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.H16TwoM22
public import CFSG.Quasithin.Background.RonanH143Main
public import CFSG.Quasithin.Background.RonanH154Vocab
public import CFSG.Quasithin.Background.RonanH155Vocab
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mLowRank

open Module Representation
open CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.Theory.Representation
open scoped TensorProduct MonoidAlgebra

section Conjugation

variable {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G W)

open CFSG.QuasithinUnique.Setup.X7b

@[expose] noncomputable def conjugateActor (u : G) (a : W ≃ₗ[ZMod 2] W) :
    W ≃ₗ[ZMod 2] W := repLinEquiv ρ u * a * (repLinEquiv ρ u)⁻¹

theorem conjugateActor_mul_self (u : G) (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) :
    conjugateActor ρ u a * conjugateActor ρ u a = 1 := by
  unfold conjugateActor
  calc
    (repLinEquiv ρ u * a * (repLinEquiv ρ u)⁻¹) *
        (repLinEquiv ρ u * a * (repLinEquiv ρ u)⁻¹) =
      repLinEquiv ρ u * (a * a) * (repLinEquiv ρ u)⁻¹ := by group
    _ = 1 := by rw [ha, mul_one, mul_inv_cancel]

theorem conjugateActor_ne_one (u : G) (a : W ≃ₗ[ZMod 2] W) (ha : a ≠ 1) :
    conjugateActor ρ u a ≠ 1 := by
  intro h
  apply ha
  have heq := congrArg (fun b : W ≃ₗ[ZMod 2] W =>
    (repLinEquiv ρ u)⁻¹ * b * repLinEquiv ρ u) h
  simpa [conjugateActor, mul_assoc] using heq

theorem finrank_conjugateActor_sub_one (u : G) (a : W ≃ₗ[ZMod 2] W) :
    finrank (ZMod 2) (LinearMap.range ((conjugateActor ρ u a).toLinearMap - 1)) =
      finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  have hlin : (conjugateActor ρ u a).toLinearMap - 1 =
      (repLinEquiv ρ u).toLinearMap ∘ₗ (a.toLinearMap - 1) ∘ₗ
        (repLinEquiv ρ u).symm.toLinearMap := by
    apply LinearMap.ext
    intro w
    simp [conjugateActor, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [hlin]
  exact CFSG.QuasithinUnique.Setup.Family.finrank_range_conj _ _

theorem conjugateActor_intertwines (u : G) (a : W ≃ₗ[ZMod 2] W) (α : MulAut G)
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w)) :
    ∀ g w, conjugateActor ρ u a (ρ g w) =
      ρ ((MulAut.conj u * α * MulAut.conj u⁻¹) g) (conjugateActor ρ u a w) := by
  intro g w
  have hm : ∀ x y v, ρ (x * y) v = ρ x (ρ y v) := by
    intro x y v
    rw [map_mul, Module.End.mul_apply]
  have hac : ∀ v, conjugateActor ρ u a v = ρ u (a (ρ u⁻¹ v)) := by
    intro v
    simp only [conjugateActor, LinearEquiv.mul_apply, ← repLinEquiv_inv, repLinEquiv_apply]
  rw [hac, hac]
  simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
  change ρ u (a (ρ u⁻¹ (ρ g w))) =
    ρ (u * α (u⁻¹ * g * u) * u⁻¹) (ρ u (a (ρ u⁻¹ w)))
  have hg : ρ u⁻¹ (ρ g w) = ρ (u⁻¹ * g * u) (ρ u⁻¹ w) := by
    rw [← hm, ← hm]
    congr 2
    group
  rw [hg, heq, ← hm, ← hm]
  congr 2
  group

end Conjugation

section PerpendicularWeights

variable {k V G : Type} [Field k] [AddCommGroup V] [Module k V] [Group G]

theorem fixed_of_perp_of_eigenvalue (σ : Representation k G V) {R S : Subgroup G}
    (hp : ∀ r ∈ R, ∀ s ∈ S, (σ s - 1) * (σ r - 1) = 0)
    {v : V} (_hv : v ≠ 0) {r : G} (hr : r ∈ R) {c : k} (hc : c ≠ 1)
    (heig : σ r v = c • v) : ∀ s ∈ S, σ s v = v := by
  intro s hs
  have h := LinearMap.congr_fun (hp r hr s hs) v
  have hrv : (σ r - 1) v = (c - 1) • v := by
    rw [LinearMap.sub_apply, heig, Module.End.one_apply, sub_smul, one_smul]
  change (σ s - 1) ((σ r - 1) v) = 0 at h
  rw [hrv, map_smul] at h
  have hz : (σ s - 1) v = 0 := (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc)
  exact sub_eq_zero.mp hz


end PerpendicularWeights

section TorusCoordinates

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)

omit [Finite K] [CharP K 2] in
theorem shortTorus_scalar_planeVec (i : Fin 3) (a : Kˣ) (p : Fin 2 → K) :
    spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).shortTorus i true a)
      (planeVec 4 p) = planeVec 4 p := by
  rw [(minusFrame 4 b c).spinAction_shortTorus]
  simp only [Bool.not_true]
  rw [show QuadraticMap.polar (quadMinus 4 K b c) (planeVec 4 p)
      ((minusFrame 4 b c).vec i false) = 0 from polar_planeVec_fVec 4 b c p i,
    show QuadraticMap.polar (quadMinus 4 K b c) (planeVec 4 p)
      ((minusFrame 4 b c).vec i true) = 0 from polar_planeVec_eVec 4 b c p i]
  simp

include hirrQ in
theorem shortTorus_scalar_mul {i j : Fin 3} (hij : i ≠ j) (a : Kˣ) :
    (minusFrame 4 b c).shortTorus i true a * (minusFrame 4 b c).shortTorus j true a =
      ((minusFrame 4 b c).longTorus hij true true a) ^ 2 := by
  apply CFSG.AGLEmbeddingD2.SquareSpinMinus.spinAction_injective hirrQ
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.pi_ext
  intro x d
  have hd : (Pi.single x d : Vm 4 K) = d • Pi.single x 1 := by
    ext y
    by_cases h : y = x <;> simp [h]
  rw [hd, map_smul, map_smul]
  congr 1
  rcases x with l | l | t
  · change spinAction (quadMinus 4 K b c)
      ((minusFrame 4 b c).shortTorus i true a * (minusFrame 4 b c).shortTorus j true a)
        ((minusFrame 4 b c).vec l true) =
      spinAction (quadMinus 4 K b c) (((minusFrame 4 b c).longTorus hij true true a) ^ 2)
        ((minusFrame 4 b c).vec l true)
    simp only [map_mul, pow_two, LinearEquiv.mul_apply]
    rw [(minusFrame 4 b c).spinAction_shortTorus_vec,
      map_smul, (minusFrame 4 b c).spinAction_shortTorus_vec,
      (minusFrame 4 b c).spinAction_longTorus_vec,
      map_smul, (minusFrame 4 b c).spinAction_longTorus_vec, smul_smul, smul_smul]
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [shortCoroot, longCoroot, pow_two]
  · change spinAction (quadMinus 4 K b c)
      ((minusFrame 4 b c).shortTorus i true a * (minusFrame 4 b c).shortTorus j true a)
        ((minusFrame 4 b c).vec l false) =
      spinAction (quadMinus 4 K b c) (((minusFrame 4 b c).longTorus hij true true a) ^ 2)
        ((minusFrame 4 b c).vec l false)
    simp only [map_mul, pow_two, LinearEquiv.mul_apply]
    rw [(minusFrame 4 b c).spinAction_shortTorus_vec,
      map_smul, (minusFrame 4 b c).spinAction_shortTorus_vec,
      (minusFrame 4 b c).spinAction_longTorus_vec,
      map_smul, (minusFrame 4 b c).spinAction_longTorus_vec, smul_smul, smul_smul]
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [shortCoroot, longCoroot, pow_two]
  · have hp : (Pi.single (.inr (.inr t)) 1 : Vm 4 K) = planeVec 4 (Pi.single t 1) := by
      ext (l | l | u) <;> simp [planeVec, Pi.single_apply]
    rw [hp]
    simp only [map_mul, pow_two]
    change spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).shortTorus i true a)
        (spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).shortTorus j true a)
          (planeVec 4 (Pi.single t 1))) =
      spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longTorus hij true true a)
        (spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longTorus hij true true a)
          (planeVec 4 (Pi.single t 1)))
    rw [shortTorus_scalar_planeVec, shortTorus_scalar_planeVec,
      spinAction_longTorus_planeVec, spinAction_longTorus_planeVec]

include hirrQ in
theorem shortTorus_scalar_mul_inv {i j : Fin 3} (hij : i ≠ j) (a : Kˣ) :
    (minusFrame 4 b c).shortTorus i true a *
        ((minusFrame 4 b c).shortTorus j true a)⁻¹ =
      ((minusFrame 4 b c).longTorus hij true false a) ^ 2 := by
  apply CFSG.AGLEmbeddingD2.SquareSpinMinus.spinAction_injective hirrQ
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.pi_ext
  intro x d
  have hd : (Pi.single x d : Vm 4 K) = d • Pi.single x 1 := by
    ext y
    by_cases h : y = x <;> simp [h]
  rw [hd, map_smul, map_smul]
  congr 1
  rcases x with l | l | t
  · change spinAction (quadMinus 4 K b c)
      ((minusFrame 4 b c).shortTorus i true a * ((minusFrame 4 b c).shortTorus j true a)⁻¹)
        ((minusFrame 4 b c).vec l true) =
      spinAction (quadMinus 4 K b c) (((minusFrame 4 b c).longTorus hij true false a) ^ 2)
        ((minusFrame 4 b c).vec l true)
    rw [← map_inv]
    simp only [map_mul, pow_two, LinearEquiv.mul_apply]
    rw [(minusFrame 4 b c).spinAction_shortTorus_vec,
      map_smul, (minusFrame 4 b c).spinAction_shortTorus_vec,
      (minusFrame 4 b c).spinAction_longTorus_vec,
      map_smul, (minusFrame 4 b c).spinAction_longTorus_vec, smul_smul, smul_smul]
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [shortCoroot, longCoroot, pow_two]
  · change spinAction (quadMinus 4 K b c)
      ((minusFrame 4 b c).shortTorus i true a * ((minusFrame 4 b c).shortTorus j true a)⁻¹)
        ((minusFrame 4 b c).vec l false) =
      spinAction (quadMinus 4 K b c) (((minusFrame 4 b c).longTorus hij true false a) ^ 2)
        ((minusFrame 4 b c).vec l false)
    rw [← map_inv]
    simp only [map_mul, pow_two, LinearEquiv.mul_apply]
    rw [(minusFrame 4 b c).spinAction_shortTorus_vec,
      map_smul, (minusFrame 4 b c).spinAction_shortTorus_vec,
      (minusFrame 4 b c).spinAction_longTorus_vec,
      map_smul, (minusFrame 4 b c).spinAction_longTorus_vec, smul_smul, smul_smul]
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [shortCoroot, longCoroot, pow_two]
  · have hp : (Pi.single (.inr (.inr t)) 1 : Vm 4 K) = planeVec 4 (Pi.single t 1) := by
      ext (l | l | u) <;> simp [planeVec, Pi.single_apply]
    rw [hp, ← map_inv]
    simp only [map_mul, pow_two]
    change spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).shortTorus i true a)
        (spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).shortTorus j true a⁻¹)
          (planeVec 4 (Pi.single t 1))) =
      spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longTorus hij true false a)
        (spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longTorus hij true false a)
          (planeVec 4 (Pi.single t 1)))
    rw [shortTorus_scalar_planeVec, shortTorus_scalar_planeVec,
      spinAction_longTorus_planeVec, spinAction_longTorus_planeVec]

theorem simple_longTorus_mem_H (i : Fin 3) (hi : i.val < 2) (a : Kˣ) :
    (minusFrame 4 b c).longTorus (succ_ne_of_lt 4 (k := i) (by omega)) true false a ∈
      (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H := by
  refine Subgroup.mem_iSup_of_mem i ?_
  rw [minusTorus_of_lt 4 hirrQ (k := i) (by omega)]
  exact ⟨a, rfl⟩

theorem shortTorus_scalar_mem_H (i : Fin 3) (a : Kˣ) :
    (minusFrame 4 b c).shortTorus i true a ∈
      (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H := by
  let H := (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H
  have h2 : (minusFrame 4 b c).shortTorus 2 true a ∈ H := by
    refine Subgroup.mem_iSup_of_mem (2 : Fin 3) ?_
    rw [minusTorus_of_not_lt 4 hirrQ (k := (2 : Fin 3)) (by norm_num),
      minusFrame_shortTorus_eq 4 hirrQ]
    exact shortTorusElt_mem 4 hirrQ 2 (smul_ne_zero a.ne_zero planeOne_ne_zero)
  have step {j l : Fin 3} (hjl : j ≠ l)
      (hh : (minusFrame 4 b c).longTorus hjl true false a ∈ H)
      (hl : (minusFrame 4 b c).shortTorus l true a ∈ H) :
      (minusFrame 4 b c).shortTorus j true a ∈ H := by
    have heq : (minusFrame 4 b c).shortTorus j true a =
        ((minusFrame 4 b c).longTorus hjl true false a) ^ 2 *
          (minusFrame 4 b c).shortTorus l true a := by
      rw [← shortTorus_scalar_mul_inv hirrQ hjl a]
      group
    rw [heq]
    exact mul_mem (pow_mem hh 2) hl
  have h1 := step (j := 1) (l := 2) (by decide)
    (simple_longTorus_mem_H hirrQ 1 (by norm_num) a) h2
  have h0 := step (j := 0) (l := 1) (by decide)
    (simple_longTorus_mem_H hirrQ 0 (by norm_num) a) h1
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

omit [Finite K] [CharP K 2] in
theorem shortTorus_scalar_mem_shortSL2 (i : Fin 3) (a : Kˣ) :
    (minusFrame 4 b c).shortTorus i true a ∈
      (shortPosHom 4 hirrQ i).range ⊔ (shortNegHom 4 hirrQ i).range := by
  rw [minusFrame_shortTorus_eq 4 hirrQ]
  exact shortTorus_le 4 hirrQ i
    (shortTorusElt_mem 4 hirrQ i (smul_ne_zero a.ne_zero planeOne_ne_zero))

theorem longTorus_true_mem_H {i j : Fin 3} (hij : i ≠ j) (t : Bool) (a : Kˣ) :
    (minusFrame 4 b c).longTorus hij true t a ∈
      (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H := by
  have hsquare : Function.Surjective (fun u : Kˣ => u ^ 2) :=
    Finite.surjective_of_injective fun u v h => Units.ext (CharTwo.sq_inj.mp
      (by simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val h))
  obtain ⟨u, rfl⟩ := hsquare a
  rw [map_pow]
  cases t
  · rw [← shortTorus_scalar_mul_inv hirrQ hij u]
    exact mul_mem (shortTorus_scalar_mem_H hirrQ i u)
      (inv_mem (shortTorus_scalar_mem_H hirrQ j u))
  · rw [← shortTorus_scalar_mul hirrQ hij u]
    exact mul_mem (shortTorus_scalar_mem_H hirrQ i u) (shortTorus_scalar_mem_H hirrQ j u)

omit [Finite K] [CharP K 2] in
theorem mat_shortTorus_scalar_eVec (i l : Fin 3) (a : Kˣ) :
    mat 4 ((minusFrame 4 b c).shortTorus i true a) (.inl l) (.inl l) =
      if l = i then (a : K) ^ 2 else 1 := by
  have h := (minusFrame 4 b c).spinAction_shortTorus_vec i true a l true
  change spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).shortTorus i true a)
      (minusVec 4 l true) =
    ((a ^ shortCoroot i true l true : Kˣ) : K) • minusVec 4 l true at h
  have hentry := mat_minusPos_of_smul 4 h
  change mat 4 _ (.inl l) (.inl l) = _ at hentry
  rw [hentry]
  by_cases hl : l = i <;> simp [shortCoroot, hl]

omit [Finite K] [CharP K 2] in
theorem mat_longTorus_eVec {i j : Fin 3} (hij : i ≠ j) (s t : Bool) (a : Kˣ) (l : Fin 3) :
    mat 4 ((minusFrame 4 b c).longTorus hij s t a) (.inl l) (.inl l) =
      ((a ^ longCoroot i j s t l true : Kˣ) : K) := by
  have h := (minusFrame 4 b c).spinAction_longTorus_vec hij s t a l true
  change spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longTorus hij s t a)
      (minusVec 4 l true) =
    ((a ^ longCoroot i j s t l true : Kˣ) : K) • minusVec 4 l true at h
  exact mat_minusPos_of_smul 4 h

end TorusCoordinates

section FieldExponents

variable {F k : Type} [Field F] [Finite F] [Field k]

theorem modEq_of_forall_map_pow_eq (φ : F →+* k) {a b : ℕ}
    (h : ∀ u : Fˣ, φ (u : F) ^ a = φ (u : F) ^ b) :
    Nat.ModEq (Nat.card F - 1) a b := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have heq : u ^ a = u ^ b := by
    apply Units.ext
    apply φ.injective
    simpa only [map_pow, Units.val_pow_eq_pow_val] using h u
  have hc : Nat.ModEq (orderOf u) a b := (pow_eq_pow_iff_modEq).mp heq
  rwa [hu, Nat.card_units] at hc

theorem card_le_one_of_long_lowered_exponents {e : ℕ} {J : Finset ℕ}
    (hJ : J ⊆ Finset.range e)
    (h : ∀ j ∈ J, Nat.ModEq (2 ^ e - 1) ((∑ i ∈ J, 2 ^ i) - 2 ^ j) 0) :
    J.card ≤ 1 := by
  by_contra hcard
  have h2 : 2 ≤ J.card := by omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < J.card)
  have hstrict := CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.pair_le_sum h2 hj
  have hbound := CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.sum_two_pow_le J
    (fun i hi => Finset.mem_range.mp (hJ hi))
  have hbit : 0 < 2 ^ j := by positivity
  have hlt : (∑ i ∈ J, 2 ^ i) - 2 ^ j < 2 ^ e - 1 := by omega
  have hz : (∑ i ∈ J, 2 ^ i) - 2 ^ j = 0 :=
    (h j hj).eq_of_lt_of_lt hlt (by omega)
  omega

theorem eq_of_short_lowered_weights {e i j : ℕ} (he : 2 ≤ e)
    (hF : Nat.card F = 2 ^ (2 * e)) (φ : F →+* k)
    (hi : i < 2 * e) (hj : j < 2 * e)
    (h : ∀ u : Fˣ, φ (u : F) ^ ((2 ^ e - 1) * 2 ^ i) =
      φ (u : F) ^ ((2 ^ e - 1) * 2 ^ j)) : i = j := by
  have hc := modEq_of_forall_map_pow_eq φ h
  have hq : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hfactor : 2 ^ (2 * e) - 1 = (2 ^ e - 1) * (2 ^ e + 1) := by
    rw [show 2 * e = e + e by omega, pow_add]
    rw [Nat.sub_mul, Nat.mul_add, one_mul, mul_one]
    omega
  rw [hF, hfactor] at hc
  exact pow_two_modEq_add_one_injective he hi hj
    (Nat.ModEq.mul_left_cancel' (by omega : 2 ^ e - 1 ≠ 0) hc)

theorem short_label_eq_empty_of_lowered_weights {e : ℕ} (he : 2 ≤ e)
    (hF : Nat.card F = 2 ^ (2 * e)) (φ : F →+* k) {J : Finset ℕ}
    (hJ : J ⊆ Finset.range (2 * e))
    (hdiv : 2 ^ e - 1 ∣ ∑ i ∈ J, 2 ^ i)
    (hw : ∀ i ∈ J, ∀ j ∈ J, ∀ u : Fˣ,
      φ (u : F) ^ ((2 ^ e - 1) * 2 ^ i) = φ (u : F) ^ ((2 ^ e - 1) * 2 ^ j)) :
    J = ∅ := by
  classical
  have hcard : J.card ≤ 1 := Finset.card_le_one.mpr fun i hi j hj =>
    eq_of_short_lowered_weights he hF φ (Finset.mem_range.mp (hJ hi))
      (Finset.mem_range.mp (hJ hj)) (hw i hi j hj)
  by_contra hne
  have hpos : 0 < J.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (by omega : J.card = 1)
  simp only [Finset.sum_singleton] at hdiv
  have hq : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have heven : Even (2 ^ e) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hodd : Odd (2 ^ e - 1) := Nat.Even.sub_odd (by omega) heven odd_one
  have hcop : Nat.Coprime (2 ^ e - 1) (2 ^ j) :=
    (Nat.coprime_two_right.mpr hodd).pow_right j
  have hone := hcop.eq_one_of_dvd hdiv
  omega

end FieldExponents

section NontrivialFrobenius

variable {F k : Type} [Field F] [Finite F] [CharP F 2] [Field k] [CharP k 2]

omit [Finite F] [CharP F 2] in
theorem map_pow_two_pow_ne_one (φ : F →+* k) {a : Fˣ} (ha : a ≠ 1) (j : ℕ) :
    φ (a : F) ^ (2 ^ j) ≠ 1 := by
  intro h
  have hf : φ (a : F) = 1 := iterateFrobenius_inj k 2 j
    (by simpa only [iterateFrobenius_def, one_pow] using h)
  have hv : (a : F) = 1 := φ.injective (hf.trans (map_one φ).symm)
  exact ha (Units.ext hv)

omit [CharP F 2] in
theorem exists_unit_ne_one_of_four_le (hF : 4 ≤ Nat.card F) : ∃ a : Fˣ, a ≠ 1 := by
  have : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp (by
    rw [Nat.card_units]
    omega)
  exact exists_ne (1 : Fˣ)

end NontrivialFrobenius

section LoweringPowers

variable {F k : Type} [Field F] [Field k]

theorem map_neg_two_pow_succ_of_sq_eq (φ : F →+* k) {z u : F}
    (hz : z ^ 2 = u) (j : ℕ) :
    φ z ^ (-(2 ^ (j + 1) : ℤ)) = (φ u ^ (2 ^ j))⁻¹ := by
  rw [show (2 ^ (j + 1) : ℤ) = ((2 ^ (j + 1) : ℕ) : ℤ) by norm_cast,
    zpow_neg, zpow_natCast]
  congr 1
  rw [pow_succ, Nat.mul_comm, pow_mul, ← map_pow, hz]

end LoweringPowers

section QuadraticLoweringPowers

open CFSG.LieType.Universal.Spin.Twisted

variable {K k : Type} [Field K] [Finite K] [CharP K 2] [Field k] {b c : K}
  [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] {e : ℕ}

theorem map_neg_two_pow_succ_of_rotation (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    (φ : ShortField b c →+* k) (t z : (ShortField b c)ˣ)
    (hz : (z : ShortField b c) ^ 2 = (t : ShortField b c) / star (t : ShortField b c))
    (j : ℕ) : φ (z : ShortField b c) ^ (-(2 ^ (j + 1) : ℤ)) =
      φ (t : ShortField b c) ^ ((2 ^ e - 1) * 2 ^ j) := by
  rw [map_neg_two_pow_succ_of_sq_eq φ hz j]
  have hq : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hnonzero : φ (t : ShortField b c) ≠ 0 := (map_ne_zero φ).mpr t.ne_zero
  have hrot : φ ((t : ShortField b c) / star (t : ShortField b c)) =
      (φ (t : ShortField b c) ^ (2 ^ e - 1))⁻¹ := by
    rw [SmallO8mTorus.star_shortField_eq_pow he hK, map_div₀, map_pow,
      pow_sub₀ _ hnonzero hq]
    simp only [pow_one, div_eq_mul_inv, mul_inv_rev, inv_inv]
  rw [hrot, inv_pow, inv_inv, ← pow_mul]

end QuadraticLoweringPowers

section HighestLine

open CFSG.Quasithin.SmithCurtis

variable {G k V : Type} [Group G] [Finite G] [Field k] [AddCommGroup V] [Module k V]

theorem line_invariant_of_highest_of_sup_eq_top
    {B : Type} {M : CoxeterMatrix B} {Weyl : Type} [Group Weyl]
    {cs : CoxeterSystem M Weyl} {D : CurtisDatum G cs 2}
    (σ : Representation k G V) {y : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType σ y χ μ) (S : Subgroup G)
    (hgen : (D.U ⊔ D.H) ⊔ S = ⊤) (hfix : ∀ s ∈ S, σ s y = y) :
    ∀ g, σ g y ∈ Submodule.span k {y} := by
  let L : Subgroup G :=
    { carrier := {g | σ g y ∈ Submodule.span k {y}}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh
        change σ (g * h) y ∈ Submodule.span k {y}
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hh
        rw [map_mul, Module.End.mul_apply, ← hc, map_smul]
        exact Submodule.smul_mem _ _ hg
      inv_mem' := by
        intro g hg
        change σ g⁻¹ y ∈ Submodule.span k {y}
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hg
        have hc0 : c ≠ 0 := by
          intro hc0
          rw [hc0, zero_smul] at hc
          have h := congrArg (σ g⁻¹) hc
          rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply] at h
          exact ht.2.1 h.symm
        have h := congrArg (σ g⁻¹) hc
        rw [map_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply] at h
        have hi : σ g⁻¹ y = c⁻¹ • y := by
          have ht := congrArg (fun w : V => c⁻¹ • w) h
          simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using ht
        rw [hi]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y) }
  have hU : D.U ≤ L := fun u hu => by
    change σ u y ∈ Submodule.span k {y}
    rw [(D.mem_fixU σ).mp ht.1 u hu]
    exact Submodule.mem_span_singleton_self y
  have hH : D.H ≤ L := fun h hh => by
    change σ h y ∈ Submodule.span k {y}
    rw [ht.2.2.1 h hh]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
  have hS : S ≤ L := fun s hs => by
    change σ s y ∈ Submodule.span k {y}
    rw [hfix s hs]
    exact Submodule.mem_span_singleton_self y
  have hall : L = ⊤ := eq_top_iff.mpr (hgen ▸ sup_le (sup_le hU hH) hS)
  intro g
  have hg : g ∈ L := hall ▸ Subgroup.mem_top g
  exact hg

theorem finrank_eq_one_of_highest_of_sup_eq_top
    {B : Type} {M : CoxeterMatrix B} {Weyl : Type} [Group Weyl]
    {cs : CoxeterSystem M Weyl} {D : CurtisDatum G cs 2}
    (σ : Representation k G V) (hσ : IsSimpleRep σ)
    {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType σ y χ μ)
    (S : Subgroup G) (hgen : (D.U ⊔ D.H) ⊔ S = ⊤) (hfix : ∀ s ∈ S, σ s y = y) :
    finrank k V = 1 := by
  have hy := line_invariant_of_highest_of_sup_eq_top σ ht S hgen hfix
  have hline : ∀ g, ∀ v ∈ Submodule.span k {y}, σ g v ∈ Submodule.span k {y} := by
    intro g v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hy g)
  have htop : Submodule.span k {y} = ⊤ := by
    rcases hσ.2 _ hline with h | h
    · have hm := Submodule.mem_span_singleton_self y (R := k)
      rw [h] at hm
      exact (ht.2.1 hm).elim
    · exact h
  have hd : finrank k (Submodule.span k {y}) = 1 := finrank_span_singleton ht.2.1
  rw [htop, finrank_top] at hd
  exact hd

theorem eq_one_of_highest_of_sup_eq_top
    {B : Type} {M : CoxeterMatrix B} {Weyl : Type} [Group Weyl]
    {cs : CoxeterSystem M Weyl} {D : CurtisDatum G cs 2}
    (σ : Representation k G V) (hσ : IsSimpleRep σ)
    {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType σ y χ μ)
    (S : Subgroup G) (hgen : (D.U ⊔ D.H) ⊔ S = ⊤)
    (hfix : ∀ s ∈ S, σ s y = y) (hperf : commutator G = ⊤) :
    ∀ g, σ g = 1 := by
  have hd := finrank_eq_one_of_highest_of_sup_eq_top σ hσ ht S hgen hfix
  have hscalar : ∀ g, ∃ c : k, σ g = c • LinearMap.id := by
    intro g
    obtain ⟨c, hc⟩ := (LinearEquiv.smul_id_of_finrank_eq_one hd).surjective (σ g)
    exact ⟨c, hc.symm.trans (LinearEquiv.smul_id_of_finrank_eq_one_apply hd c)⟩
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.rep_trivial_of_commute hperf σ
  intro g h
  obtain ⟨c, hc⟩ := hscalar g
  obtain ⟨d, hd⟩ := hscalar h
  apply LinearMap.ext
  intro v
  simp only [hc, hd, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_smul]
  rw [mul_comm]

theorem chi_eq_one_of_perp_of_sup_eq_top
    {B : Type} {M : CoxeterMatrix B} {Weyl : Type} [Group Weyl]
    {cs : CoxeterSystem M Weyl} {D : CurtisDatum G cs 2}
    (σ : Representation k G V) (hσ : IsSimpleRep σ)
    {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType σ y χ μ)
    (R S : Subgroup G) (hgen : (D.U ⊔ D.H) ⊔ S = ⊤)
    (hp : ∀ r ∈ R, ∀ s ∈ S, (σ s - 1) * (σ r - 1) = 0)
    (hperf : commutator G = ⊤) (hnt : ∃ g, σ g ≠ 1) :
    ∀ r ∈ R, r ∈ D.H → χ r = 1 := by
  intro r hr hrH
  by_contra hc
  have hfix := fixed_of_perp_of_eigenvalue σ hp ht.2.1 hr hc (ht.2.2.1 r hrH)
  have hall := eq_one_of_highest_of_sup_eq_top σ hσ ht S hgen hfix hperf
  obtain ⟨g, hg⟩ := hnt
  exact hg (hall g)

end HighestLine

section FixedBlockTransport

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K W : Type} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)

@[expose] noncomputable def naturalActor
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) :
    Vm 4 K ≃ₗ[K] Vm 4 K :=
  let E := coordinateMinusIsometry 4 K (by norm_num : 1 ≤ 4) b c
  (E.toLinearEquiv.trans (matrixLinearIso s.val)).trans E.symm.toLinearEquiv

omit [Finite K] [CharP K 2] in
theorem naturalActor_mem_orthogonalGroup
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) :
    naturalActor s ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  let E := coordinateMinusIsometry 4 K (by norm_num : 1 ≤ 4) b c
  change quadMinus 4 K b c (E.symm (matrixLinearIso s.val (E v))) = quadMinus 4 K b c v
  rw [E.symm.map_app]
  have hs := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp s.2 (E v)
  change coordinateQuadMinus 4 K (by norm_num) b c (matrixLinearIso s.val (E v)) =
    coordinateQuadMinus 4 K (by norm_num) b c (E v) at hs
  exact hs.trans (E.map_app v)

omit [Finite K] [CharP K 2] in
theorem naturalActor_mul_self
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) (hs : s * s = 1) :
    naturalActor s * naturalActor s = 1 := by
  have hS : matrixLinearIso s.val * matrixLinearIso s.val = 1 := by
    rw [← map_mul, show s.val * s.val = 1 from congrArg Subtype.val hs, map_one]
  apply LinearEquiv.ext
  intro v
  let E := coordinateMinusIsometry 4 K (by norm_num : 1 ≤ 4) b c
  change E.symm (matrixLinearIso s.val (E (E.symm (matrixLinearIso s.val (E v))))) = v
  rw [E.apply_symm_apply, ← LinearEquiv.mul_apply, hS]
  exact E.symm_apply_apply v

omit [Finite K] [CharP K 2] in
theorem naturalActor_finrank_sub_one
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) :
    finrank K (LinearMap.range ((naturalActor s).toLinearMap - 1)) =
      finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) := by
  let E := coordinateMinusIsometry 4 K (by norm_num : 1 ≤ 4) b c
  let f := (matrixLinearIso s.val).toLinearMap - 1
  have hr : LinearMap.range ((naturalActor s).toLinearMap - 1) =
      (LinearMap.range f).map E.symm.toLinearEquiv.toLinearMap := by
    ext v
    rw [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨f (E w), ⟨E w, rfl⟩, ?_⟩
      simp [naturalActor, f, E, map_sub]
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨E.symm w, ?_⟩
      simp [naturalActor, f, E, map_sub]
  rw [hr, LinearEquiv.finrank_map_eq]

omit [Finite W] in
theorem exists_fixed_block_binary_conjugate
    (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W)
    (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
    (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) (hs : s * s = 1)
    (hα : ∀ g, SmallO8mCurtis.coordinateEquiv hirrQ (α g) =
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s)
        (SmallO8mCurtis.coordinateEquiv hirrQ g))
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w))
    (hrank : finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) ≤ 2) :
    ∃ (r : Vm 4 K ≃ₗ[K] Vm 4 K) (β : MulAut (spinGroup (quadMinus 4 K b c)))
      (a' : W ≃ₗ[ZMod 2] W),
      r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) ∧ r * r = 1 ∧
      r (eVec 4 2) = eVec 4 2 ∧ r (fVec 4 2) = fVec 4 2 ∧
      (∀ p : Fin 2 → K, r (planeVec 4 p) = planeVec 4 p) ∧
      a' * a' = 1 ∧ a' ≠ 1 ∧
      finrank (ZMod 2) (LinearMap.range (a'.toLinearMap - 1)) =
        finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ∧
      (∀ g, spinAction (quadMinus 4 K b c) (β g) =
        r * spinAction (quadMinus 4 K b c) g * r⁻¹) ∧
      (∀ g w, a' (ρ g w) = ρ (β g) (a' w)) := by
  let T := naturalActor s
  have hTO := naturalActor_mem_orthogonalGroup s
  have hT2 := naturalActor_mul_self s hs
  have hTr : finrank K (LinearMap.range (T.toLinearMap - 1)) ≤ 2 :=
    (naturalActor_finrank_sub_one s).trans_le hrank
  obtain ⟨u, hfix⟩ := exists_spin_conj_fix_short_block_of_rank_le_two hirrQ hTO hT2 hTr
  let g := spinAction (quadMinus 4 K b c) u
  let r := g * T * g⁻¹
  let β := MulAut.conj u * α * MulAut.conj u⁻¹
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ u)
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
    mul_mem (mul_mem hgO hTO) (inv_mem hgO)
  have hr2 : r * r = 1 := by
    dsimp only [r]
    calc (g * T * g⁻¹) * (g * T * g⁻¹) = g * (T * T) * g⁻¹ := by group
      _ = 1 := by rw [hT2, mul_one, mul_inv_cancel]
  have hβ : ∀ x, spinAction (quadMinus 4 K b c) (β x) =
      r * spinAction (quadMinus 4 K b c) x * r⁻¹ := by
    intro x
    have hconj := SmallO8mCurtis.spinAction_conj_of_coordinate hirrQ α s hα
    simp only [β, MulAut.mul_apply, MulAut.conj_apply, inv_inv]
    change spinAction (quadMinus 4 K b c) (u * α (u⁻¹ * x * u) * u⁻¹) = _
    rw [map_mul, map_mul, hconj, map_mul, map_mul, map_inv]
    change g * (T * (g⁻¹ * spinAction (quadMinus 4 K b c) x * g) * T⁻¹) * g⁻¹ = _
    dsimp only [r]
    group
  refine ⟨r, β, conjugateActor ρ u a, hrO, hr2, hfix.1, hfix.2.1, hfix.2.2,
    conjugateActor_mul_self ρ u a ha, conjugateActor_ne_one ρ u a ha1,
    finrank_conjugateActor_sub_one ρ u a, hβ, ?_⟩
  exact conjugateActor_intertwines ρ u a α heq

end FixedBlockTransport

section ExtendedPerpendicularity

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

variable {K W : Type} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {e : ℕ} (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e) {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
  [Finite (spinGroup (quadMinus 4 K b c))]
  (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W) [ρ.IsIrreducible]
  (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
  (α : MulAut (spinGroup (quadMinus 4 K b c)))
  (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) (hs : s * s = 1)
  (hα : ∀ g, SmallO8mCurtis.coordinateEquiv hirrQ (α g) =
    matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s)
      (SmallO8mCurtis.coordinateEquiv hirrQ g))
  (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w))
  (hrank : finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
  (hrankNatural : finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) ≤ 2)
  {k : Type} [Field k]
  [Algebra (Module.End (MonoidAlgebra (ZMod 2)
    (spinGroup (quadMinus 4 K b c))) ρ.asModule) k]

include he hK hirrQ a ha ha1 α s hs hα heq hrank hrankNatural in
omit [Finite (spinGroup (quadMinus 4 K b c))] in
theorem shortSL2_perp_longSL2_of_ne :
    ∀ l : Fin 3, ∀ g ∈ (shortPosHom 4 hirrQ l).range ⊔ (shortNegHom 4 hirrQ l).range,
      ∀ {i j : Fin 3} (hij : i ≠ j), i ≠ l → j ≠ l → ∀ t u : Bool,
        ∀ n ∈ ((minusFrame 4 b c).longSL2 hij t u).range,
          (ρ g - 1) * (ρ n - 1) = 0 ∧ (ρ n - 1) * (ρ g - 1) = 0 := by
  obtain ⟨r, β, a', hr, hr2, hre, hrf, hrp, ha', ha'1, hdim, hβ, heq'⟩ :=
    exists_fixed_block_binary_conjugate hirrQ ρ a ha ha1 α s hs hα heq hrankNatural
  have hrank' : finrank (ZMod 2) (LinearMap.range (a'.toLinearMap - 1)) ≤ 2 * e + 1 :=
    hdim.trans_le hrank
  exact SmallO8mPerpPair.shortSL2_perp_longSL2_of_ne he hK hirrQ ρ a' ha' ha'1
    hrank' r hr hr2 hre hrf hrp β hβ heq'

include he hK hirrQ a ha ha1 α s hs hα heq hrank hrankNatural in
omit [Finite (spinGroup (quadMinus 4 K b c))] in
theorem extendScalars_shortSL2_perp_longSL2_of_ne :
    ∀ l : Fin 3, ∀ g ∈ (shortPosHom 4 hirrQ l).range ⊔ (shortNegHom 4 hirrQ l).range,
      ∀ {i j : Fin 3} (hij : i ≠ j), i ≠ l → j ≠ l → ∀ t u : Bool,
        ∀ n ∈ ((minusFrame 4 b c).longSL2 hij t u).range,
          (extendScalars k (CFSG.endFieldRep ρ) g - 1) *
              (extendScalars k (CFSG.endFieldRep ρ) n - 1) = 0 ∧
            (extendScalars k (CFSG.endFieldRep ρ) n - 1) *
              (extendScalars k (CFSG.endFieldRep ρ) g - 1) = 0 := by
  intro l g hg i j hij hi hj t u n hn
  have hp := shortSL2_perp_longSL2_of_ne he hK hirrQ ρ a ha ha1 α s hs hα heq
    hrank hrankNatural l g hg hij hi hj t u n hn
  exact ⟨extendScalars_endFieldRep_sub_one_mul_sub_one ρ k hp.1,
    extendScalars_endFieldRep_sub_one_mul_sub_one ρ k hp.2⟩

end ExtendedPerpendicularity

section Nontriviality

variable {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible]
  (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
  (k : Type) [Field k]
  [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k]

include a ha ha1 in
theorem exists_ne_one_extendScalars_endFieldRep :
    ∃ g, extendScalars k (CFSG.endFieldRep ρ) g ≠ 1 := by
  by_contra h
  have hall : ∀ g, extendScalars k (CFSG.endFieldRep ρ) g = 1 := by
    simpa only [not_exists, not_not] using h
  have hρ : ∀ g, ρ g = 1 := fun g =>
    (CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.extendScalars_endFieldRep_eq_one_iff
      ρ k g).mp (hall g)
  exact ha1 (SmallO8mPerpPair.eq_one_of_commute_rep ρ a ha fun g w => by
    rw [hρ, Module.End.one_apply, Module.End.one_apply])

end Nontriviality

section ScalarCharacter

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Quasithin.SmithCurtis

variable {K k V : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
  [Finite (spinGroup (quadMinus 4 K b c))]
  {σ : Representation k (spinGroup (quadMinus 4 K b c)) V}
  {y : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
  (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y χ μ)

include hirrQ ht in
theorem chi_shortTorus_scalar_eq_one_of_long_signs {i j : Fin 3} (hij : i ≠ j)
    (a : Kˣ)
    (hplus : χ ((minusFrame 4 b c).longTorus hij true true a) = 1)
    (hminus : χ ((minusFrame 4 b c).longTorus hij true false a) = 1) :
    χ ((minusFrame 4 b c).shortTorus i true a) = 1 ∧
      χ ((minusFrame 4 b c).shortTorus j true a) = 1 := by
  have hp : χ ((minusFrame 4 b c).shortTorus i true a) *
      χ ((minusFrame 4 b c).shortTorus j true a) = 1 := by
    rw [← ht.chi_mul (shortTorus_scalar_mem_H hirrQ i a)
      (shortTorus_scalar_mem_H hirrQ j a), shortTorus_scalar_mul hirrQ hij a, pow_two,
      ht.chi_mul (longTorus_true_mem_H hirrQ hij true a)
        (longTorus_true_mem_H hirrQ hij true a), hplus, one_mul]
  have hm : χ ((minusFrame 4 b c).shortTorus i true a) *
      (χ ((minusFrame 4 b c).shortTorus j true a))⁻¹ = 1 := by
    have hinv : χ (((minusFrame 4 b c).shortTorus j true a)⁻¹) =
        (χ ((minusFrame 4 b c).shortTorus j true a))⁻¹ := by
      have hmul := ht.chi_mul (shortTorus_scalar_mem_H hirrQ j a)
        (inv_mem (shortTorus_scalar_mem_H hirrQ j a))
      rw [mul_inv_cancel, ht.chi_one] at hmul
      exact eq_inv_of_mul_eq_one_right hmul.symm
    rw [← hinv, ← ht.chi_mul (shortTorus_scalar_mem_H hirrQ i a)
      (inv_mem (shortTorus_scalar_mem_H hirrQ j a)), shortTorus_scalar_mul_inv hirrQ hij a,
      pow_two, ht.chi_mul (longTorus_true_mem_H hirrQ hij false a)
        (longTorus_true_mem_H hirrQ hij false a), hminus, one_mul]
  have hnonzero : χ ((minusFrame 4 b c).shortTorus j true a) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hp
    exact zero_ne_one hp
  have heq : χ ((minusFrame 4 b c).shortTorus i true a) =
      χ ((minusFrame 4 b c).shortTorus j true a) := by
    apply (div_eq_one_iff_eq hnonzero).mp
    simpa only [div_eq_mul_inv] using hm
  have hsq : χ ((minusFrame 4 b c).shortTorus j true a) ^ 2 = 1 := by
    simpa only [heq, pow_two] using hp
  have hj1 := CharTwo.sq_inj.mp (hsq.trans (one_pow 2).symm)
  exact ⟨heq.trans hj1, hj1⟩

include hirrQ ht in
omit [CharP k 2] in
theorem chi_shortTorus_scalar_eq_long_square {i j : Fin 3} (hij : i ≠ j) (a : Kˣ)
    (hj : χ ((minusFrame 4 b c).shortTorus j true a) = 1) :
    χ ((minusFrame 4 b c).shortTorus i true a) =
      χ ((minusFrame 4 b c).longTorus hij true false a) ^ 2 := by
  have hi : χ (((minusFrame 4 b c).shortTorus j true a)⁻¹) = 1 := by
    have h := ht.chi_mul (shortTorus_scalar_mem_H hirrQ j a)
      (inv_mem (shortTorus_scalar_mem_H hirrQ j a))
    rw [mul_inv_cancel, ht.chi_one, hj, one_mul] at h
    exact h.symm
  have h := ht.chi_mul (shortTorus_scalar_mem_H hirrQ i a)
    (inv_mem (shortTorus_scalar_mem_H hirrQ j a))
  rw [hi, mul_one, shortTorus_scalar_mul_inv hirrQ hij a, pow_two,
    ht.chi_mul (longTorus_true_mem_H hirrQ hij false a)
      (longTorus_true_mem_H hirrQ hij false a)] at h
  simpa only [pow_two] using h.symm

end ScalarCharacter

section LoweredScalarCharacter

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.SignalizerFunctorTheorem.NonLocal

variable {K k V : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
  {σ : Representation k (spinGroup (quadMinus 4 K b c)) V}
  {v : V} (hv : v ≠ 0) {weight : spinGroup (quadMinus 4 K b c) → k}
  (hweight : ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H, σ h v = weight h • v)

include hv hweight in
theorem lowered_shortTorus_scalar_eq_one_of_long_signs {i j : Fin 3} (hij : i ≠ j)
    (a : Kˣ)
    (hplus : σ ((minusFrame 4 b c).longTorus hij true true a) v = v)
    (hminus : σ ((minusFrame 4 b c).longTorus hij true false a) v = v) :
    weight ((minusFrame 4 b c).shortTorus i true a) = 1 ∧
      weight ((minusFrame 4 b c).shortTorus j true a) = 1 := by
  let H := (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H
  let f : H → k := fun h => weight h
  have hf : IsWeight σ H f := ⟨v, hv, fun h => hweight h h.2⟩
  let x : H := ⟨(minusFrame 4 b c).shortTorus i true a, shortTorus_scalar_mem_H hirrQ i a⟩
  let z : H := ⟨(minusFrame 4 b c).shortTorus j true a, shortTorus_scalar_mem_H hirrQ j a⟩
  let p : H := ⟨(minusFrame 4 b c).longTorus hij true true a,
    longTorus_true_mem_H hirrQ hij true a⟩
  let m : H := ⟨(minusFrame 4 b c).longTorus hij true false a,
    longTorus_true_mem_H hirrQ hij false a⟩
  have hp : f p = 1 := smul_left_injective k hv
    ((hweight p p.2).symm.trans (hplus.trans (one_smul k v).symm))
  have hm : f m = 1 := smul_left_injective k hv
    ((hweight m m.2).symm.trans (hminus.trans (one_smul k v).symm))
  have hxz : x * z = p ^ 2 := Subtype.ext (shortTorus_scalar_mul hirrQ hij a)
  have hxzi : x * z⁻¹ = m ^ 2 := Subtype.ext (shortTorus_scalar_mul_inv hirrQ hij a)
  have hprod : f x * f z = 1 := by
    rw [← hf.mul x z, hxz, hf.pow p 2, hp, one_pow]
  have hquot : f x / f z = 1 := by
    rw [div_eq_mul_inv, ← hf.inv z, ← hf.mul x z⁻¹, hxzi, hf.pow m 2, hm, one_pow]
  have hx : f x = f z := (div_eq_one_iff_eq (hf.ne_zero z)).mp hquot
  have hz : f z = 1 := CharTwo.sq_inj.mp
    ((show f z ^ 2 = 1 by simpa only [hx, pow_two] using hprod).trans (one_pow 2).symm)
  exact ⟨hx.trans hz, hz⟩

end LoweredScalarCharacter

section HighestPosition

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Quasithin.SmithCurtis

variable {K k V : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
  [Finite (spinGroup (quadMinus 4 K b c))]
  {σ : Representation k (spinGroup (quadMinus 4 K b c)) V}
  (hσ : IsSimpleRep σ) {y : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
  (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y χ μ)
  (hnt : ∃ g, σ g ≠ 1)
  (hgen : ((SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).U ⊔
      (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H) ⊔
      ((shortPosHom 4 hirrQ 0).range ⊔ (shortNegHom 4 hirrQ 0).range) = ⊤)
  (hp : ∀ l : Fin 3,
    ∀ g ∈ (shortPosHom 4 hirrQ l).range ⊔ (shortNegHom 4 hirrQ l).range,
      ∀ {i j : Fin 3} (hij : i ≠ j), i ≠ l → j ≠ l → ∀ t u : Bool,
        ∀ n ∈ ((minusFrame 4 b c).longSL2 hij t u).range,
          (σ g - 1) * (σ n - 1) = 0 ∧ (σ n - 1) * (σ g - 1) = 0)

include hσ ht hnt hgen hp in
omit [CharP k 2] in
theorem chi_longTorus_one_two_eq_one (t : Bool) (a : Kˣ) :
    χ ((minusFrame 4 b c).longTorus (show (1 : Fin 3) ≠ 2 by decide) true t a) = 1 := by
  let R := ((minusFrame 4 b c).longSL2 (show (1 : Fin 3) ≠ 2 by decide) true t).range
  let S := (shortPosHom 4 hirrQ 0).range ⊔ (shortNegHom 4 hirrQ 0).range
  have hperp : ∀ r ∈ R, ∀ s ∈ S, (σ s - 1) * (σ r - 1) = 0 := by
    intro r hr s hs
    exact (hp 0 s hs (show (1 : Fin 3) ≠ 2 by decide) (by decide) (by decide)
      true t r hr).1
  exact chi_eq_one_of_perp_of_sup_eq_top σ hσ ht R S hgen hperp
    (isPerfect_spinGroup_quadMinus (by norm_num) hirrQ).commutator_eq_top hnt
      _ ⟨diagSL2 a, rfl⟩ (longTorus_true_mem_H hirrQ _ t a)

include hσ ht hnt hgen hp in
theorem chi_shortTorus_one_two_eq_one (a : Kˣ) :
    χ ((minusFrame 4 b c).shortTorus 1 true a) = 1 ∧
      χ ((minusFrame 4 b c).shortTorus 2 true a) = 1 :=
  chi_shortTorus_scalar_eq_one_of_long_signs hirrQ ht (by decide) a
    (chi_longTorus_one_two_eq_one hirrQ hσ ht hnt hgen hp true a)
    (chi_longTorus_one_two_eq_one hirrQ hσ ht hnt hgen hp false a)

variable [Algebra K k] {e : ℕ} (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
  (hsplit : SplitOver k (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H)

include hσ ht hnt hgen hp he hK hsplit in
theorem finrank_fixSub_Us_one_eq_one :
    finrank k (fixSub σ ((SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Us 1)) = 1 := by
  classical
  obtain ⟨J, hJ, hchar, hdim, hfix, hweights⟩ :=
    SmallO8mRankOne.exists_longString_weights hirrQ hK hsplit hσ ht 1 (by norm_num)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hJe : J = ∅ := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨v, hvS, hv, hvH⟩ := hweights j hj
    change ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
      σ h v = (χ h * (algebraMap K k
        (mat 4 h (.inl 1) (.inl 1) / mat 4 h (.inl 2) (.inl 2)) ^
          (-(2 ^ j : ℤ)))) • v at hvH
    obtain ⟨a, ha⟩ := exists_unit_ne_one_of_four_le (F := K) hK4
    let T := (minusFrame 4 b c).shortTorus 2 true a
    let P := (minusFrame 4 b c).shortTorus 1 true a
    have heigT : σ T v = (algebraMap K k (a : K) ^ (2 ^ (j + 1))) • v := by
      have h := hvH T (shortTorus_scalar_mem_H hirrQ 2 a)
      rw [(chi_shortTorus_one_two_eq_one hirrQ hσ ht hnt hgen hp a).2] at h
      dsimp only [T] at h ⊢
      rw [mat_shortTorus_scalar_eVec, mat_shortTorus_scalar_eVec] at h
      rw [show (2 ^ j : ℤ) = ((2 ^ j : ℕ) : ℤ) by norm_cast] at h
      simp only [show (1 : Fin 3) ≠ 2 by decide, if_false, if_true, 
        map_pow, one_mul, one_div, zpow_neg, zpow_natCast, map_inv₀] at h
      rw [inv_pow, inv_inv, ← pow_mul] at h
      simpa only [pow_succ, Nat.mul_comm] using h
    have hnv : algebraMap K k (a : K) ^ (2 ^ (j + 1)) ≠ 1 :=
      map_pow_two_pow_ne_one (algebraMap K k) ha (j + 1)
    have hfixLong : ∀ t : Bool,
        σ ((minusFrame 4 b c).longTorus (show (0 : Fin 3) ≠ 1 by decide) true t a) v = v := by
      intro t
      exact fixed_of_perp_of_eigenvalue σ
        (R := (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range)
        (S := ((minusFrame 4 b c).longSL2 (show (0 : Fin 3) ≠ 1 by decide) true t).range)
        (fun r hr s hs => (hp 2 r hr (show (0 : Fin 3) ≠ 1 by decide)
          (by decide) (by decide) true t s hs).2) hv
        (shortTorus_scalar_mem_shortSL2 hirrQ 2 a) hnv heigT _ ⟨diagSL2 a, rfl⟩
    have hp1 := (lowered_shortTorus_scalar_eq_one_of_long_signs hirrQ hv hvH
      (show (0 : Fin 3) ≠ 1 by decide) a (hfixLong true) (hfixLong false)).2
    have heigP : σ P v = (algebraMap K k (a : K) ^ (2 ^ (j + 1)))⁻¹ • v := by
      have h := hvH P (shortTorus_scalar_mem_H hirrQ 1 a)
      rw [(chi_shortTorus_one_two_eq_one hirrQ hσ ht hnt hgen hp a).1] at h
      dsimp only [P] at h ⊢
      rw [mat_shortTorus_scalar_eVec, mat_shortTorus_scalar_eVec] at h
      rw [show (2 ^ j : ℤ) = ((2 ^ j : ℕ) : ℤ) by norm_cast] at h
      simp only [show (2 : Fin 3) ≠ 1 by decide, if_false, if_true, 
        map_pow, one_mul, div_one, zpow_neg, zpow_natCast] at h
      rw [← pow_mul (algebraMap K k (a : K)) 2 (2 ^ j)] at h
      simpa only [pow_succ, Nat.mul_comm] using h
    have hpfix : σ P v = v := by
      have h := hvH P (shortTorus_scalar_mem_H hirrQ 1 a)
      rw [hp1, one_smul] at h
      exact h
    have hcoef : (algebraMap K k (a : K) ^ (2 ^ (j + 1)))⁻¹ = 1 :=
      smul_left_injective k hv (heigP.symm.trans (hpfix.trans (one_smul k v).symm))
    exact hnv (inv_eq_one.mp hcoef)
  rw [hdim, hJe]
  simp

include hσ ht hnt hgen hp he hK hsplit in
theorem finrank_fixSub_Us_zero_le_two :
    finrank k (fixSub σ ((SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Us 0)) ≤ 2 := by
  classical
  obtain ⟨J, hJ, hchar, hdim, hfix, hweights⟩ :=
    SmallO8mRankOne.exists_longString_weights hirrQ hK hsplit hσ ht 0 (by norm_num)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hbits : ∀ j ∈ J,
      Nat.ModEq (2 ^ e - 1) ((∑ i ∈ J, 2 ^ i) - 2 ^ j) 0 := by
    intro j hj
    obtain ⟨v, hvS, hv, hvH⟩ := hweights j hj
    change ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
      σ h v = (χ h * (algebraMap K k
        (mat 4 h (.inl 0) (.inl 0) / mat 4 h (.inl 1) (.inl 1)) ^
          (-(2 ^ j : ℤ)))) • v at hvH
    obtain ⟨u, hu⟩ := exists_unit_ne_one_of_four_le (F := K) hK4
    have hnv : algebraMap K k (u : K) ^ (2 ^ (j + 1)) ≠ 1 :=
      map_pow_two_pow_ne_one (algebraMap K k) hu (j + 1)
    have heig1 : σ ((minusFrame 4 b c).shortTorus 1 true u) v =
        (algebraMap K k (u : K) ^ (2 ^ (j + 1))) • v := by
      have h := hvH _ (shortTorus_scalar_mem_H hirrQ 1 u)
      rw [(chi_shortTorus_one_two_eq_one hirrQ hσ ht hnt hgen hp u).1,
        mat_shortTorus_scalar_eVec, mat_shortTorus_scalar_eVec,
        show (2 ^ j : ℤ) = ((2 ^ j : ℕ) : ℤ) by norm_cast] at h
      simp only [show (0 : Fin 3) ≠ 1 by decide, if_false, if_true, 
        map_pow, one_mul, one_div, zpow_neg, zpow_natCast, map_inv₀] at h
      rw [inv_pow, inv_inv, ← pow_mul] at h
      simpa only [pow_succ, Nat.mul_comm] using h
    have hfix02 : ∀ t : Bool, ∀ a : Kˣ,
        σ ((minusFrame 4 b c).longTorus (show (0 : Fin 3) ≠ 2 by decide) true t a) v = v := by
      intro t a
      exact fixed_of_perp_of_eigenvalue σ
        (R := (shortPosHom 4 hirrQ 1).range ⊔ (shortNegHom 4 hirrQ 1).range)
        (S := ((minusFrame 4 b c).longSL2 (show (0 : Fin 3) ≠ 2 by decide) true t).range)
        (fun r hr s hs => (hp 1 r hr (show (0 : Fin 3) ≠ 2 by decide)
          (by decide) (by decide) true t s hs).2) hv
        (shortTorus_scalar_mem_shortSL2 hirrQ 1 u) hnv heig1 _ ⟨diagSL2 a, rfl⟩
    have hpow : ∀ a : Kˣ,
        algebraMap K k (a : K) ^ (2 * ((∑ i ∈ J, 2 ^ i) - 2 ^ j)) = 1 := by
      intro a
      have hp0 := (lowered_shortTorus_scalar_eq_one_of_long_signs hirrQ hv hvH
        (show (0 : Fin 3) ≠ 2 by decide) a (hfix02 true a) (hfix02 false a)).1
      have hχ0 := chi_shortTorus_scalar_eq_long_square hirrQ ht
        (show (0 : Fin 3) ≠ 1 by decide) a
        (chi_shortTorus_one_two_eq_one hirrQ hσ ht hnt hgen hp a).1
      have hchar' : χ ((minusFrame 4 b c).longTorus (show (0 : Fin 3) ≠ 1 by decide)
          true false a) = algebraMap K k (a : K) ^ ∑ i ∈ J, 2 ^ i := hchar a
      rw [hχ0, hchar', mat_shortTorus_scalar_eVec, mat_shortTorus_scalar_eVec,
        show (2 ^ j : ℤ) = ((2 ^ j : ℕ) : ℤ) by norm_cast] at hp0
      simp only [show (1 : Fin 3) ≠ 0 by decide, if_false, if_true, 
        map_pow, div_one, zpow_neg, zpow_natCast] at hp0
      have hle : 2 ^ j ≤ ∑ i ∈ J, 2 ^ i := Finset.single_le_sum (fun i hi => Nat.zero_le _) hj
      have hnonzero : algebraMap K k (a : K) ≠ 0 :=
        (map_ne_zero (algebraMap K k)).mpr a.ne_zero
      have heq : (algebraMap K k (a : K) ^ ∑ i ∈ J, 2 ^ i) ^ 2 *
          ((algebraMap K k (a : K) ^ 2) ^ (2 ^ j))⁻¹ =
            algebraMap K k (a : K) ^ (2 * ((∑ i ∈ J, 2 ^ i) - 2 ^ j)) := by
        rw [Nat.mul_sub, pow_sub₀ _ hnonzero (Nat.mul_le_mul_left 2 hle),
          pow_mul', pow_mul]
      exact heq ▸ hp0
    have hpow' : ∀ a : Kˣ,
        algebraMap K k (a : K) ^ ((∑ i ∈ J, 2 ^ i) - 2 ^ j) = 1 := by
      intro a
      have h := hpow a
      rw [pow_mul'] at h
      exact CharTwo.sq_inj.mp (h.trans (one_pow 2).symm)
    have hc := modEq_of_forall_map_pow_eq (algebraMap K k)
      (a := (∑ i ∈ J, 2 ^ i) - 2 ^ j) (b := 0) (fun a => (hpow' a).trans (pow_zero _).symm)
    rwa [hK] at hc
  have hcard := card_le_one_of_long_lowered_exponents hJ hbits
  rw [hdim]
  calc 2 ^ J.card ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hcard
    _ = 2 := by norm_num

end HighestPosition

section QuadraticCharacters

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Quasithin.SmithCurtis

variable {K k V : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
  [Finite (spinGroup (quadMinus 4 K b c))]
  {σ : Representation k (spinGroup (quadMinus 4 K b c)) V}
  {y : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
  (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y χ μ)

omit [CharP K 2] [Finite (spinGroup (quadMinus 4 K b c))] in
theorem shortTorusHom_scalar (i : Fin 3) (a : Kˣ) :
    shortTorusHom 4 hirrQ i (Units.map (algebraMap K (ShortField b c)).toMonoidHom a) =
      (minusFrame 4 b c).shortTorus i true a := by
  rw [shortTorusHom_apply, minusFrame_shortTorus_eq 4 hirrQ]
  congr 1
  exact fieldCoord_algebraMap (a : K)

omit [CharP K 2] [CharP k 2] [Finite (spinGroup (quadMinus 4 K b c))] in
theorem dvd_short_exponent_of_scalar_trivial {e C : ℕ} (hK : Nat.card K = 2 ^ e)
    [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] (φ : ShortField b c →+* k)
    (hchar : ∀ t : (ShortField b c)ˣ, χ (shortTorusHom 4 hirrQ 2 t) = φ (t : ShortField b c) ^ C)
    (hscalar : ∀ a : Kˣ, χ ((minusFrame 4 b c).shortTorus 2 true a) = 1) :
    2 ^ e - 1 ∣ C := by
  let ψ := φ.comp (algebraMap K (ShortField b c))
  have hp : ∀ a : Kˣ, ψ (a : K) ^ C = ψ (a : K) ^ 0 := by
    intro a
    have h := hchar (Units.map (algebraMap K (ShortField b c)).toMonoidHom a)
    rw [shortTorusHom_scalar, hscalar] at h
    exact h.symm.trans (pow_zero _).symm
  have hc := modEq_of_forall_map_pow_eq ψ hp
  rw [hK] at hc
  exact Nat.modEq_zero_iff_dvd.mp hc

include ht in
omit [CharP k 2] in
theorem chi_shortTorus_one_eq_two
    (hlong : ∀ a : Kˣ,
      χ ((minusFrame 4 b c).longTorus (show (1 : Fin 3) ≠ 2 by decide) true false a) = 1)
    (t : (ShortField b c)ˣ) :
    χ (shortTorusHom 4 hirrQ 1 t) = χ (shortTorusHom 4 hirrQ 2 t) := by
  have heq := (mul_inv_eq_iff_eq_mul).mp
    (SmallO8mTorus.shortTorusHom_mul_inv hirrQ (show (1 : Fin 3) ≠ 2 by decide) t)
  rw [heq, ht.chi_mul (longTorus_true_mem_H hirrQ _ false _)
    (SmallO8mTorus.shortTorusHom_mem_H hirrQ 2 t), hlong, one_mul]

end QuadraticCharacters

section HeckeEigenvalue

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Quasithin.SmithCurtis

variable {K k V : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
  [Finite (spinGroup (quadMinus 4 K b c))]
  {σ : Representation k (spinGroup (quadMinus 4 K b c)) V}
  {y : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
  (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y χ μ)

include ht in
theorem hecke_eq_zero_of_fixed_rankOne (i : Fin 3)
    (hfix : ∀ g ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).X i ⊔
      (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Y i, σ g y = y) : μ i = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ
  have hn : D.n i ∈ D.X i ⊔ D.Y i := minusDatum_n_mem 4 hirrQ i
  have hz := CFSG.LieType.Steinberg.heckeT_eq_zero_of_fixed σ i
    (fun x hx => hfix x (Subgroup.mem_sup_left hx)) (hfix _ hn)
  rw [ht.2.2.2] at hz
  exact (smul_eq_zero.mp hz).resolve_right ht.2.1

end HeckeEigenvalue

section TorusAndRankOneGeneration

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Quasithin.SmithCurtis

variable {K k V : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
  [Finite (spinGroup (quadMinus 4 K b c))]
  {σ : Representation k (spinGroup (quadMinus 4 K b c)) V}
  {y : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
  (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y χ μ)

include ht in
omit [CharP k 2] in
theorem chi_eq_highestChar_of_simple_tori (φ : K →+* k)
    (hchar : ∀ (i : Fin 3) (hi : i.val < 2) (a : Kˣ),
      χ ((minusFrame 4 b c).longTorus (succ_ne_of_lt 4 (k := i) (by omega)) true false a) =
        SmallO8mCurtis.highestChar φ
          ((minusFrame 4 b c).longTorus (succ_ne_of_lt 4 (k := i) (by omega)) true false a))
    (hshort : ∀ t : (ShortField b c)ˣ,
      χ (shortTorusHom 4 hirrQ 2 t) = SmallO8mCurtis.highestChar φ (shortTorusHom 4 hirrQ 2 t)) :
    ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
      χ h = SmallO8mCurtis.highestChar φ h := by
  have hv0 : SmallO8mCurtis.highestVec (k := k) ≠ 0 := by
    intro h
    have h0 := congrFun h (.inl 0)
    simp [SmallO8mCurtis.highestVec] at h0
  let D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ
  let H := D.H
  let f : H → k := fun h => SmallO8mCurtis.highestChar φ (h : spinGroup (quadMinus 4 K b c))
  have hf : CFSG.SignalizerFunctorTheorem.NonLocal.IsWeight
      (SmallO8mCurtis.naturalRep 4 b c φ) H f :=
    ⟨SmallO8mCurtis.highestVec, hv0,
      fun h => SmallO8mCurtis.naturalRep_highestChar hirrQ φ h.2⟩
  have hone : SmallO8mCurtis.highestChar φ 1 = 1 := hf.one
  have hmul : ∀ g ∈ H, ∀ h ∈ H,
      SmallO8mCurtis.highestChar φ (g * h) =
        SmallO8mCurtis.highestChar φ g * SmallO8mCurtis.highestChar φ h :=
    fun g hg h hh => hf.mul ⟨g, hg⟩ ⟨h, hh⟩
  intro h hh
  have hhH : h ∈ H := hh
  change h ∈ ⨆ i : Fin 3, minusTorus 4 hirrQ i at hh
  have heq : ∀ g ∈ ⨆ i : Fin 3, minusTorus 4 hirrQ i,
      g ∈ H ∧ χ g = SmallO8mCurtis.highestChar φ g := by
    intro g hg
    refine Subgroup.iSup_induction (minusTorus 4 hirrQ)
      (C := fun g => g ∈ H ∧ χ g = SmallO8mCurtis.highestChar φ g) hg (fun i g hgi => ?_) ?_
      (fun g g' hg hg' => ?_)
    · have hgH : g ∈ H := Subgroup.mem_iSup_of_mem i hgi
      refine ⟨hgH, ?_⟩
      by_cases hi : i.val < 2
      · rw [minusTorus_of_lt 4 hirrQ (k := i) (by omega)] at hgi
        obtain ⟨a, rfl⟩ := hgi
        exact hchar i hi a
      · have hi2 : i = 2 := by
          apply Fin.ext
          change i.val = 2
          have := i.isLt
          omega
        subst i
        rw [minusTorus_of_not_lt 4 hirrQ (k := (2 : Fin 3)) (by norm_num),
          ← range_shortTorusHom] at hgi
        obtain ⟨t, rfl⟩ := hgi
        exact hshort t
    · exact ⟨one_mem _, (ht.chi_one).trans hone.symm⟩
    · refine ⟨mul_mem hg.1 hg'.1, ?_⟩
      rw [ht.chi_mul hg.1 hg'.1, hmul g hg.1 g' hg'.1, hg.2, hg'.2]
  exact (heq h hh).2

include ht in
omit [CharP k 2] in
theorem fixed_by_all_of_rankOne_fixed
    (hfix : ∀ i : Fin 3, ∀ g ∈
      (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).X i ⊔
        (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Y i, σ g y = y) :
    ∀ g, σ g y = y := by
  let D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ
  let P := σ.stabilizer y
  have hH : D.H ≤ P := by
    change (⨆ i : Fin 3, minusTorus 4 hirrQ i) ≤ P
    refine iSup_le fun i => ?_
    intro h hh
    exact hfix i h (minusDatum_H_le 4 hirrQ i hh)
  have hU : D.U ≤ P := fun u hu => ht.1 u hu
  have hn : ∀ i : Fin 3, minusWeyl 4 hirrQ i ∈ P := fun i =>
    hfix i _ (minusDatum_n_mem 4 hirrQ i)
  have htop : P = ⊤ := CFSG.LieType.TitsSimplicity.eq_top_of_forall_n_mem
    (minusDatum_isCTGroupDatum 4 hirrQ (by norm_num))
    (show D.H ⊔ D.U ≤ P from sup_le hH hU) hn
  intro g
  have hg : g ∈ P := htop ▸ Subgroup.mem_top g
  exact hg

end TorusAndRankOneGeneration

section ShortSectionBound

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Quasithin.SmithCurtis

variable {K k V : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
  [Finite (spinGroup (quadMinus 4 K b c))]
  {σ : Representation k (spinGroup (quadMinus 4 K b c)) V}
  (hσ : IsSimpleRep σ) {y : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
  (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y χ μ)
  (hnt : ∃ g, σ g ≠ 1)
  (hp : ∀ l : Fin 3,
    ∀ g ∈ (shortPosHom 4 hirrQ l).range ⊔ (shortNegHom 4 hirrQ l).range,
      ∀ {i j : Fin 3} (hij : i ≠ j), i ≠ l → j ≠ l → ∀ t u : Bool,
        ∀ n ∈ ((minusFrame 4 b c).longSL2 hij t u).range,
          (σ g - 1) * (σ n - 1) = 0 ∧ (σ n - 1) * (σ g - 1) = 0)
  {e : ℕ} (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
  (hsplit : SplitOver k (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H)
  [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] (φ : ShortField b c →+* k)

include hσ ht hnt hp he hK hsplit φ in
theorem short_character_and_section :
    (∀ t : (ShortField b c)ˣ, χ (shortTorusHom 4 hirrQ 2 t) = 1) ∧
      finrank k (fixSub σ ((SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Us 2)) = 1 ∧
        ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range, σ g y = y := by
  classical
  have : Finite (ShortField b c) := finite_shortField
  let D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ
  have hgen := SmallO8mCurtis.borel_sup_first_short_eq_top hirrQ
  have hlong := chi_longTorus_one_two_eq_one hirrQ hσ ht hnt hgen hp
  have hscalar := chi_shortTorus_one_two_eq_one hirrQ hσ ht hnt hgen hp
  obtain ⟨J, hJ, hchar, hdim, hfix, hweights⟩ :=
    SmallO8mShortSection.exists_shortString_weights hirrQ hK he φ hsplit hσ ht
  have hdiv : 2 ^ e - 1 ∣ ∑ i ∈ J, 2 ^ i :=
    dvd_short_exponent_of_scalar_trivial hirrQ hK φ hchar (fun a => (hscalar a).2)
  have hF : Nat.card (ShortField b c) = 2 ^ (2 * e) := by
    rw [CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.card_shortField, hK,
      ← pow_mul, Nat.mul_comm]
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hbit : ∀ j ∈ J, ∀ t : (ShortField b c)ˣ,
      χ (shortTorusHom 4 hirrQ 0 t) * φ (t : ShortField b c) ^ ((2 ^ e - 1) * 2 ^ j) = 1 := by
    intro j hj
    obtain ⟨v, hvS, hv, hvH⟩ := hweights j hj
    obtain ⟨a, ha⟩ := exists_unit_ne_one_of_four_le (F := K) hK4
    let ψ := φ.comp (algebraMap K (ShortField b c))
    have heig : σ ((minusFrame 4 b c).longTorus (show (1 : Fin 3) ≠ 2 by decide)
        true true a) v = (ψ (a : K) ^ (2 ^ j))⁻¹ • v := by
      obtain ⟨z, hz, hcentral⟩ := SmallO8mTorus.exists_longTorus_mul_inv_mem_centralizer hirrQ a
      have h := hvH _ (longTorus_true_mem_H hirrQ _ true a)
        (Units.map (algebraMap K (ShortField b c)).toMonoidHom z) hcentral
      rw [hlong true a] at h
      simp only [one_mul] at h
      change σ ((minusFrame 4 b c).longTorus (show (1 : Fin 3) ≠ 2 by decide)
          true true a) v =
        φ (algebraMap K (ShortField b c) (z : K)) ^ (-(2 ^ (j + 1) : ℤ)) • v at h
      have heq : φ (algebraMap K (ShortField b c) (z : K)) ^ (-(2 ^ (j + 1) : ℤ)) =
          (ψ (a : K) ^ (2 ^ j))⁻¹ := map_neg_two_pow_succ_of_sq_eq ψ hz j
      exact heq ▸ h
    have hnv : (ψ (a : K) ^ (2 ^ j))⁻¹ ≠ 1 := by
      exact inv_ne_one.mpr (map_pow_two_pow_ne_one ψ ha j)
    have hfix0 : ∀ g ∈ (shortPosHom 4 hirrQ 0).range ⊔ (shortNegHom 4 hirrQ 0).range,
        σ g v = v := by
      intro g hg
      exact fixed_of_perp_of_eigenvalue σ
        (R := ((minusFrame 4 b c).longSL2 (show (1 : Fin 3) ≠ 2 by decide) true true).range)
        (S := (shortPosHom 4 hirrQ 0).range ⊔ (shortNegHom 4 hirrQ 0).range)
        (fun r hr s hs => (hp 0 s hs (show (1 : Fin 3) ≠ 2 by decide)
          (by decide) (by decide) true true r hr).1) hv ⟨diagSL2 a, rfl⟩ hnv heig g hg
    intro t
    obtain ⟨z, hz, hcentral⟩ := SmallO8mTorus.exists_shortTorusHom_mul_inv_mem_centralizer
      hirrQ (show (0 : Fin 3) ≠ 2 by decide) t
    have h := hvH _ (SmallO8mTorus.shortTorusHom_mem_H hirrQ 0 t) z hcentral
    rw [map_neg_two_pow_succ_of_rotation he hK φ t z hz j] at h
    exact smul_left_injective k hv (h.symm.trans
      ((hfix0 _ (SmallO8mPerpPair.shortTorusHom_mem hirrQ 0 t)).trans (one_smul k v).symm))
  have hsame : ∀ i ∈ J, ∀ j ∈ J, ∀ u : (ShortField b c)ˣ,
      φ (u : ShortField b c) ^ ((2 ^ e - 1) * 2 ^ i) =
        φ (u : ShortField b c) ^ ((2 ^ e - 1) * 2 ^ j) := by
    intro i hi j hj u
    have hχ : χ (shortTorusHom 4 hirrQ 0 u) ≠ 0 := by
      intro hz
      have h := hbit i hi u
      rw [hz, zero_mul] at h
      exact zero_ne_one h
    exact mul_left_cancel₀ hχ ((hbit i hi u).trans (hbit j hj u).symm)
  have hJe := short_label_eq_empty_of_lowered_weights he hF φ hJ hdiv hsame
  refine ⟨?_, ?_, hfix hJe⟩
  · intro t
    simpa only [hJe, Finset.sum_empty, pow_zero] using hchar t
  · simpa only [hJe, Finset.card_empty, pow_zero] using hdim

end ShortSectionBound

section NaturalHighestType

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Quasithin.SmithCurtis

variable {K k V : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
  [Finite (spinGroup (quadMinus 4 K b c))]
  {σ : Representation k (spinGroup (quadMinus 4 K b c)) V}
  (hσ : IsSimpleRep σ) {y : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
  (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y χ μ)
  (hnt : ∃ g, σ g ≠ 1)
  (hp : ∀ l : Fin 3,
    ∀ g ∈ (shortPosHom 4 hirrQ l).range ⊔ (shortNegHom 4 hirrQ l).range,
      ∀ {i j : Fin 3} (hij : i ≠ j), i ≠ l → j ≠ l → ∀ t u : Bool,
        ∀ n ∈ ((minusFrame 4 b c).longSL2 hij t u).range,
          (σ g - 1) * (σ n - 1) = 0 ∧ (σ n - 1) * (σ g - 1) = 0)
  {e : ℕ} (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
  (hsplit : SplitOver k (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H)
  [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] (φ : ShortField b c →+* k)

include hσ ht hnt hp he hK hsplit φ in
theorem natural_type_of_perpendicularity :
    μ = 0 ∧ ∃ ψ : K →+* k,
      ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
        χ h = SmallO8mCurtis.highestChar ψ h := by
  classical
  let : Algebra K k := (φ.comp (algebraMap K (ShortField b c))).toAlgebra
  let D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ
  have hgen := SmallO8mCurtis.borel_sup_first_short_eq_top hirrQ
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hdim0 := finrank_fixSub_Us_zero_le_two hirrQ hσ ht hnt hgen hp he hK hsplit
  have hdim1 := finrank_fixSub_Us_one_eq_one hirrQ hσ ht hnt hgen hp he hK hsplit
  obtain ⟨hμ0, hχ0⟩ := SmallO8mRankOne.longRankOne_of_finrank_le hirrQ hK4 hsplit hσ ht
    0 (by norm_num) hdim0
  obtain ⟨hμ1, hχ1⟩ := SmallO8mRankOne.longRankOne_of_finrank_le hirrQ hK4 hsplit hσ ht
    1 (by norm_num) (hdim1.le.trans (by norm_num))
  obtain ⟨hshort, hdim2, hfix2⟩ := short_character_and_section hirrQ hσ ht hnt hp he hK hsplit φ
  have hfix2' : ∀ g ∈ D.X 2 ⊔ D.Y 2, σ g y = y := by
    rw [show D.X 2 ⊔ D.Y 2 = (shortPosHom 4 hirrQ 2).range ⊔
      (shortNegHom 4 hirrQ 2).range from rankOne_minusRootGroup_of_not_lt 4 hirrQ (by norm_num)]
    exact hfix2
  have hμ2 := hecke_eq_zero_of_fixed_rankOne hirrQ ht 2 hfix2'
  have hχ1' : ∀ a : Kˣ,
      χ ((minusFrame 4 b c).longTorus (show (1 : Fin 3) ≠ 2 by decide) true false a) = 1 :=
    chi_longTorus_one_two_eq_one hirrQ hσ ht hnt hgen hp false
  have hfix1 : ∀ g ∈ D.X 1 ⊔ D.Y 1, σ g y = y := by
    obtain ⟨J, hJ, hchar, hdim, hfix, hweights⟩ :=
      SmallO8mRankOne.exists_longString_weights hirrQ hK hsplit hσ ht 1 (by norm_num)
    have hcard : J.card = 0 := by
      have heq : 2 ^ J.card = 1 := hdim.symm.trans hdim1
      by_contra hne
      have hle : 2 ^ 1 ≤ 2 ^ J.card := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [heq] at hle
      norm_num at hle
    exact hfix (Finset.card_eq_zero.mp hcard)
  have hχ0_nontrivial : ¬ ∀ a : Kˣ,
      χ ((minusFrame 4 b c).longTorus (show (0 : Fin 3) ≠ 1 by decide) true false a) = 1 := by
    intro hzero
    obtain ⟨J, hJ, hchar, hdim, hfix, hweights⟩ :=
      SmallO8mRankOne.exists_longString_weights hirrQ hK hsplit hσ ht 0 (by norm_num)
    have hcard : J.card ≤ 1 := by
      have hd : 2 ^ J.card ≤ 2 := hdim.symm.trans_le hdim0
      by_contra hne
      have hle : 2 ^ 2 ≤ 2 ^ J.card := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hJe : J = ∅ := by
      by_contra hne
      have hpos : 0 < J.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (by omega : J.card = 1)
      obtain ⟨a, ha⟩ := exists_unit_ne_one_of_four_le (F := K) hK4
      have hpow : algebraMap K k (a : K) ^ (2 ^ j) = 1 := by
        simpa only [Finset.sum_singleton] using (hchar a).symm.trans (hzero a)
      exact map_pow_two_pow_ne_one (algebraMap K k) ha j hpow
    have hfix0 := hfix hJe
    have hall := fixed_by_all_of_rankOne_fixed hirrQ ht (fun i => by
      fin_cases i
      · exact hfix0
      · exact hfix1
      · exact hfix2')
    have htriv : ∀ g, σ g = 1 := by
      intro g
      apply LinearMap.ext
      intro v
      have hspan : ∀ w ∈ orbitSpan σ y, σ g w = w := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨t, rfl⟩ := hw
          change σ g (σ t y) = σ t y
          rw [hall, hall]
        | zero => exact map_zero _
        | add x z hx hz ihx ihz => rw [map_add, ihx, ihz]
        | smul c x hx ih => rw [map_smul, ih]
      exact hspan v (by rw [orbitSpan_eq_top hσ ht.2.1]; exact Submodule.mem_top)
    obtain ⟨g, hg⟩ := hnt
    exact hg (htriv g)
  obtain ⟨ψ, hψ⟩ := hχ0.resolve_left hχ0_nontrivial
  refine ⟨funext (fun i => by fin_cases i <;> assumption), ψ, ?_⟩
  apply chi_eq_highestChar_of_simple_tori hirrQ ht ψ
  · intro i hi a
    have heq : i = 0 ∨ i = 1 := by
      fin_cases i <;> simp_all
    rcases heq with rfl | rfl
    · rw [hψ]
      change ψ (a : K) = ψ (mat 4 _ (.inl 0) (.inl 0))
      rw [mat_longTorus_eVec]
      simp [longCoroot]
    · rw [hχ1']
      change 1 = ψ (mat 4 _ (.inl 0) (.inl 0))
      rw [mat_longTorus_eVec]
      simp [longCoroot]
  · intro t
    rw [hshort]
    change 1 = ψ (mat 4 (shortTorusHom 4 hirrQ 2 t) (.inl 0) (.inl 0))
    have hact : spinAction (quadMinus 4 K b c) (shortTorusHom 4 hirrQ 2 t) (minusVec 4 0 true) =
        (1 : K) • minusVec 4 0 true := by
      rw [shortTorusHom_apply]
      simpa only [minusVec_true, one_smul] using
        spinAction_shortTorusElt_eVec_of_ne 4 hirrQ (show (0 : Fin 3) ≠ 2 by decide)
          (fieldCoord (t : ShortField b c))
    have hm : mat 4 (shortTorusHom 4 hirrQ 2 t) (.inl 0) (.inl 0) = 1 :=
      mat_minusPos_of_smul 4 hact
    exact (map_one ψ).symm.trans (congrArg ψ hm).symm

end NaturalHighestType

section OriginalField

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Quasithin.SmithCurtis

theorem natural_isCurtisType_of_small_isometry_of_finrank_le_two
    {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {e : ℕ} (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    [Finite (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))]
    (ρ : Representation (ZMod 2) (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) W)
    [ρ.IsIrreducible] (_hfaith : Function.Injective ρ)
    (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
    (α : MulAut (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)))
    (s : CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixIsometries
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadMinus
        4 K (by norm_num) b c)) (hs : s * s = 1)
    (hα : ∀ g, SmallO8mCurtis.coordinateEquiv hirrQ (α g) =
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveConjugationHom
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadMinus
          4 K (by norm_num) b c)
        (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixIsometryInclusion _ s)
        (SmallO8mCurtis.coordinateEquiv hirrQ g))
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w))
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
    (_hcomm : ∀ d : EndRing ρ, ∀ w, a (d w) = d (a w))
    {k : Type} [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))) ρ.asModule) k]
    {y : k ⊗[Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))) ρ.asModule] ρ.asModule}
    {χ : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (hrankNatural : Module.finrank K
      (LinearMap.range ((CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso
        s.val).toLinearMap - 1)) ≤ 2)
    (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ μ) :
    μ = 0 ∧ ∃ φ : K →+* k,
      ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
        χ h = SmallO8mCurtis.highestChar φ h := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : FiniteDimensional (ZMod 2) W := Module.finite_iff_finite.mpr inferInstance
  let G := spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)
  let E := Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule
  have : CharP E 2 := CFSG.HardMathSupport.GuralnickMalle.endField_charP ρ 2
  have : FiniteDimensional E ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  let L := AlgebraicClosure E
  have : CharP L 2 := inferInstance
  have : Fact (∀ r : K, r ^ 2 ≠ -c + b * r) := fact_shortField hirrQ
  have : Finite (ShortField b c) := finite_shortField
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective 2
  let φ : ShortField b c →+* L :=
    (CFSG.HardMathSupport.GuralnickMalle.nonempty_ringHom_algebraicClosure
      (K := E) (F₀ := ShortField b c) (p := 2)).some
  let D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ
  obtain ⟨yE, χE, μE, htE, hχE, hμE⟩ :=
    CFSG.HardMathSupport.GuralnickMalle.exists_isCurtisType_endField ρ D k ht
  have htL := SmallO8mCurtis.isCurtisType_extendScalars (k' := L) D (CFSG.endFieldRep ρ) htE
  let σ := extendScalars L (CFSG.endFieldRep ρ)
  have hσ : IsSimpleRep σ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ L
  have hnt : ∃ g, σ g ≠ 1 := exists_ne_one_extendScalars_endFieldRep ρ a ha ha1 L
  have hsplit : SplitOver L D.H := SmallO8mCurtis.curtisDatum_splitOver hirrQ
  have hperp := extendScalars_shortSL2_perp_longSL2_of_ne (k := L) he hK hirrQ ρ
    a ha ha1 α s hs hα heq hrank hrankNatural
  obtain ⟨hμL, ψ, hψ⟩ := natural_type_of_perpendicularity hirrQ hσ htL hnt hperp he hK hsplit φ
  obtain ⟨hμ0, θ, hθ⟩ := SmallO8mCurtis.natural_character_descends hirrQ (algebraMap E L)
    (fun i => by have h := congrFun hμL i; exact h) ψ hψ
  let θk : K →+* k := (algebraMap E k).comp θ
  refine ⟨funext (fun i => by
    change μ i = 0
    rw [hμE i]
    have h : μE i = 0 := congrFun hμ0 i
    rw [h, map_zero]), θk, ?_⟩
  intro h hh
  rw [hχE h hh, hθ h hh]
  rfl

end OriginalField

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mLowRank
