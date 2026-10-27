module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviWeyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e7Lift_cartan_eq : Tag.cartan .E7 = CartanMatrix.E 7 := by
  change Tag.cartanE 7 = CartanMatrix.E 7
  exact cartanE_eq 7

private theorem e7Lift_symm (i j : Fin Tag.E7.rank) :
    CartanMatrix.E₇ i j = CartanMatrix.E₇ j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem e7Lift_cartan_diag (i : Fin Tag.E7.rank) : Tag.cartan .E7 i i = 2 := by
  change Tag.cartanE 7 i i = 2
  exact if_pos rfl

private theorem e7Lift_det : (CartanMatrix.E₇).det = 2 := by
  rw [← CFSG.LieType.Chevalley.laplaceDet_eq_det]
  decide +kernel

private theorem e7Lift_two_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp2 h2

private def e7Lift_label (x : Fin Tag.E7.rank → ℤ) (i : Fin Tag.E7.rank) : ℤ :=
  ∑ j, Tag.cartan .E7 i j * x j

private theorem e7Lift_reflect_eq (i : Fin Tag.E7.rank) (x : Fin Tag.E7.rank → ℤ) :
    reflect .E7 i x = x - e7Lift_label x i • Pi.single i 1 := by
  simp [reflect, e7Lift_label]

private theorem e7Lift_label_sub_smul (i j : Fin Tag.E7.rank)
    (x : Fin Tag.E7.rank → ℤ) (c : ℤ) :
    e7Lift_label (x - c • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) i =
      e7Lift_label x i - c * Tag.cartan .E7 i j := by
  have h1 : ∀ k : Fin Tag.E7.rank,
      Tag.cartan .E7 i k * (x - c • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) k =
      Tag.cartan .E7 i k * x k -
        Tag.cartan .E7 i k * (c * (if k = j then (1 : ℤ) else 0)) := by
    intro k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_sub]
  rw [e7Lift_label, Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_sub_distrib]
  have h2 : ∑ k, Tag.cartan .E7 i k * (c * (if k = j then (1 : ℤ) else 0)) =
      c * Tag.cartan .E7 i j := by
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro b _ hb; simp [hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [h2, e7Lift_label]

private theorem e7Lift_label_reflect_self (i : Fin Tag.E7.rank) (x : Fin Tag.E7.rank → ℤ) :
    e7Lift_label (reflect .E7 i x) i = - e7Lift_label x i := by
  rw [e7Lift_reflect_eq, e7Lift_label_sub_smul, e7Lift_cartan_diag]
  ring

private def e7Lift_H (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (x : Fin Tag.E7.rank → ℤ) : V :=
  ∑ k, (x k : ZMod p) • h k

private def e7Lift_A (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V) (x : Fin Tag.E7.rank → ℤ) (v : V) : ZMod p :=
  ∑ k, (x k : ZMod p) * α k v

private theorem e7Lift_H_single {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (i : Fin Tag.E7.rank) :
    e7Lift_H p h (Pi.single i 1) = h i := by
  rw [e7Lift_H, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem e7Lift_H_zsmul {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (c : ℤ) (x : Fin Tag.E7.rank → ℤ) :
    e7Lift_H p h (c • x) = (c : ZMod p) • e7Lift_H p h x := by
  simp only [e7Lift_H, Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_smul, Finset.smul_sum]

private theorem e7Lift_H_sub {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (x y : Fin Tag.E7.rank → ℤ) :
    e7Lift_H p h (x - y) = e7Lift_H p h x - e7Lift_H p h y := by
  simp only [e7Lift_H, Pi.sub_apply, Int.cast_sub, sub_smul, Finset.sum_sub_distrib]

private theorem e7Lift_H_sub_smul {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (c : ℤ) (x y : Fin Tag.E7.rank → ℤ) :
    e7Lift_H p h (x - c • y) = e7Lift_H p h x - (c : ZMod p) • e7Lift_H p h y := by
  rw [e7Lift_H_sub, e7Lift_H_zsmul]

private theorem e7Lift_A_single_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V) (i : Fin Tag.E7.rank) (v : V) :
    e7Lift_A p α (Pi.single i 1) v = α i v := by
  rw [e7Lift_A, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem e7Lift_A_add_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V) (x y : Fin Tag.E7.rank → ℤ) (v : V) :
    e7Lift_A p α (x + y) v = e7Lift_A p α x v + e7Lift_A p α y v := by
  simp only [e7Lift_A, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

private theorem e7Lift_A_zsmul_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V) (c : ℤ) (x : Fin Tag.E7.rank → ℤ) (v : V) :
    e7Lift_A p α (c • x) v = (c : ZMod p) * e7Lift_A p α x v := by
  simp only [e7Lift_A, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem e7Lift_A_sub_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V) (x y : Fin Tag.E7.rank → ℤ) (v : V) :
    e7Lift_A p α (x - y) v = e7Lift_A p α x v - e7Lift_A p α y v := by
  rw [sub_eq_add_neg, ← neg_one_smul ℤ y, e7Lift_A_add_left, e7Lift_A_zsmul_left]
  ring

private theorem e7Lift_A_sub_right {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V) (x : Fin Tag.E7.rank → ℤ) (v w : V) :
    e7Lift_A p α x (v - w) = e7Lift_A p α x v - e7Lift_A p α x w := by
  simp only [e7Lift_A, map_sub, mul_sub, Finset.sum_sub_distrib]

private theorem e7Lift_A_smul_right {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V) (x : Fin Tag.E7.rank → ℤ)
    (c : ZMod p) (v : V) :
    e7Lift_A p α x (c • v) = c * e7Lift_A p α x v := by
  simp only [e7Lift_A, map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem e7Lift_A_h {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    (x : Fin Tag.E7.rank → ℤ) (j : Fin Tag.E7.rank) :
    e7Lift_A p α x (h j) = ((e7Lift_label x j : ℤ) : ZMod p) := by
  rw [e7Lift_A]
  have h1 : ∀ k, (x k : ZMod p) * α k (h j) =
      ((CartanMatrix.E₇ j k * x k : ℤ) : ZMod p) := by
    intro k
    rw [hpair k j, ← Int.cast_mul, e7Lift_symm k j, mul_comm]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Int.cast_sum]
  congr 1
  simp only [e7Lift_label]
  exact Finset.sum_congr rfl fun k _ => by rw [e7Lift_cartan_eq]

private theorem e7Lift_A_reflect_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V) (i : Fin Tag.E7.rank)
    (x : Fin Tag.E7.rank → ℤ) (v : V) :
    e7Lift_A p α (reflect .E7 i x) v =
      e7Lift_A p α x v - ((e7Lift_label x i : ℤ) : ZMod p) * α i v := by
  rw [e7Lift_reflect_eq, e7Lift_A_sub_left, e7Lift_A_zsmul_left, e7Lift_A_single_left]

private theorem e7Lift_alpha_H {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    (x : Fin Tag.E7.rank → ℤ) (i : Fin Tag.E7.rank) :
    α i (e7Lift_H p h x) = ((e7Lift_label x i : ℤ) : ZMod p) := by
  rw [e7Lift_H]
  simp only [map_sum, map_smul, smul_eq_mul]
  have h1 : ∀ k, (x k : ZMod p) * α i (h k) =
      ((CartanMatrix.E₇ i k * x k : ℤ) : ZMod p) := by
    intro k
    rw [hpair i k, ← Int.cast_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Int.cast_sum]
  congr 1
  simp only [e7Lift_label]
  exact Finset.sum_congr rfl fun k _ => by rw [e7Lift_cartan_eq]

private theorem e7Lift_cast_simple {ι : Type*} {M N : CoxeterMatrix ι} (h : M = N) (i : ι) :
    (Eq.ndrec (motive := fun (N' : CoxeterMatrix ι) => M.Group ≃* N'.Group)
      (MulEquiv.refl M.Group) h) (M.simple i) = N.simple i := by
  subst h
  rfl

private noncomputable def e7LiftEquiv : CoxeterMatrix.E₇.Group ≃* WeylGroup .E7 :=
  Eq.ndrec (motive := fun (N : CoxeterMatrix (Fin 7)) => CoxeterMatrix.E₇.Group ≃* N.Group)
    (MulEquiv.refl CoxeterMatrix.E₇.Group) CFSG.StandardType.FrameRoute.coxeterE7_eq

private theorem e7LiftEquiv_simple (i : Fin 7) :
    e7LiftEquiv (CoxeterMatrix.E₇.simple i) = simple .E7 i := by
  unfold e7LiftEquiv
  exact e7Lift_cast_simple CFSG.StandardType.FrameRoute.coxeterE7_eq i

private theorem e7Lift_claim1 {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E7 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E7.rank) (v : V), ρ (simple .E7 i) v = v - α i v • h i) :
    ∀ (w : WeylGroup .E7) (x : Fin Tag.E7.rank → ℤ),
      ρ w (e7Lift_H p h x) = e7Lift_H p h (w • x) := by
  intro w
  induction w using (coxeterSystem .E7).simple_induction_left with
  | one => intro x; simp
  | mul_simple_left w i ih =>
      intro x
      rw [map_mul, LinearEquiv.mul_apply]
      rw [ih x, hρ i, e7Lift_alpha_H (p := p) h α hpair (w • x) i,
        ← e7Lift_H_single (p := p) h i, ← e7Lift_H_sub_smul (p := p) h]
      rw [mul_smul, simple_smul, e7Lift_reflect_eq]

private theorem e7Lift_A_simple {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E7 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E7.rank) (v : V), ρ (simple .E7 i) v = v - α i v • h i)
    (i : Fin Tag.E7.rank) (x : Fin Tag.E7.rank → ℤ) (v : V) :
    e7Lift_A p α (simple .E7 i • x) (ρ (simple .E7 i) v) = e7Lift_A p α x v := by
  rw [hρ i v, simple_smul]
  rw [e7Lift_A_sub_right (p := p), e7Lift_A_smul_right (p := p),
    e7Lift_A_reflect_left (p := p), e7Lift_A_h (p := p) h α hpair,
    e7Lift_label_reflect_self, Int.cast_neg]
  ring

private theorem e7Lift_claim2 {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E7.rank → V) (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E7 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E7.rank) (v : V), ρ (simple .E7 i) v = v - α i v • h i) :
    ∀ (w : WeylGroup .E7) (x : Fin Tag.E7.rank → ℤ) (v : V),
      e7Lift_A p α (w • x) (ρ w v) = e7Lift_A p α x v := by
  intro w
  induction w using (coxeterSystem .E7).simple_induction_right with
  | one => intro x v; simp
  | mul_simple_right w i ih =>
      intro x v
      rw [map_mul, LinearEquiv.mul_apply, mul_smul]
      rw [ih (simple .E7 i • x) (ρ (simple .E7 i) v)]
      exact e7Lift_A_simple (p := p) h α hpair ρ hρ i x v

private theorem e7Lift_weyl_coroot_smul {p : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin Tag.E7.rank → V)
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E7 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E7.rank) (v : V), ρ (simple .E7 i) v = v - α i v • h i)
    (w : WeylGroup .E7) (x : Fin Tag.E7.rank → ℤ) :
    ρ w (∑ k, (x k : ZMod p) • h k) = ∑ k, ((w • x) k : ZMod p) • h k := by
  simpa only [e7Lift_H] using e7Lift_claim1 h α hpair ρ hρ w x

private theorem e7Lift_weyl_dual_smul {p : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin Tag.E7.rank → V)
    (α : Fin Tag.E7.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E7 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E7.rank) (v : V), ρ (simple .E7 i) v = v - α i v • h i)
    (w : WeylGroup .E7) (x : Fin Tag.E7.rank → ℤ) (v : V) :
    ∑ k, ((w • x) k : ZMod p) * α k (ρ w v) = ∑ k, (x k : ZMod p) * α k v := by
  simpa only [e7Lift_A] using e7Lift_claim2 h α hpair ρ hρ w x v

theorem ggTBJE7Levi_weylLift
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 7 → MulAut ↥Bs} {h : Fin 7 → V} {α : Fin 7 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p))
    {f : CoxeterMatrix.E₇.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₇.simple i) : MulAut ↥Bs) = φ i) :
    ∃ e : WeylGroup .E7 ≃* CoxeterMatrix.E₇.Group,
      (∀ i, e (simple .E7 i) = CoxeterMatrix.E₇.simple i) ∧
      ∀ (u : WeylGroup .E7) (c : Fin Tag.E7.rank → ℤ) (w : V),
        ggLin (p := p) ι (f (e u) : MulAut ↥Bs) (∑ j, (c j : ZMod p) • h j) =
            ∑ j, ((u • c) j : ZMod p) • h j ∧
          ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ι (f (e u) : MulAut ↥Bs) w) =
            ∑ j, (c j : ZMod p) * α j w := by
  let e : WeylGroup .E7 ≃* CoxeterMatrix.E₇.Group := e7LiftEquiv.symm
  have he : ∀ i, e (simple .E7 i) = CoxeterMatrix.E₇.simple i := by
    intro i
    apply e7LiftEquiv.injective
    rw [MulEquiv.apply_symm_apply]
    exact (e7LiftEquiv_simple i).symm
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer X Bs
  let Φ : WeylGroup .E7 →* ↥A := f.toMonoidHom.comp e.toMonoidHom
  let ρ : WeylGroup .E7 →* (V ≃ₗ[ZMod p] V) := (ggLin (p := p) ι).comp (A.subtype.comp Φ)
  have hρu : ∀ u, ρ u = ggLin (p := p) ι (f (e u) : MulAut ↥Bs) := fun u => rfl
  have hρ : ∀ (i : Fin Tag.E7.rank) (v : V), ρ (simple .E7 i) v = v - α i v • h i := by
    intro i v
    have hfun : ρ (simple .E7 i) = ggLin (p := p) ι (φ i) := by
      change ggLin (p := p) ι (((Φ (simple .E7 i)) : ↥A) : MulAut ↥Bs) =
        ggLin (p := p) ι (φ i)
      rw [show Φ (simple .E7 i) = f (CoxeterMatrix.E₇.simple i) by
        show f (e (simple .E7 i)) = f (CoxeterMatrix.E₇.simple i)
        rw [he i]]
      rw [show ((f (CoxeterMatrix.E₇.simple i) : ↥A) : MulAut ↥Bs) = φ i from hf i]
    rw [hfun]
    exact hlin i v
  refine ⟨e, he, ?_⟩
  intro u c w
  constructor
  · simpa only [hρu u] using e7Lift_weyl_coroot_smul (p := p) h α hpair ρ hρ u c
  · simpa only [hρu u] using e7Lift_weyl_dual_smul (p := p) h α hpair ρ hρ u c w

theorem ggTBJE7Levi_reflSet_eq
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 7 → MulAut ↥Bs} {h : Fin 7 → V} {α : Fin 7 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {F : WeylGroup .E7 →* ↥(ggAutomizer X Bs)}
    (hF : ∀ i, (F (simple .E7 i) : MulAut ↥Bs) = φ i)
    (hFh : ∀ (u : WeylGroup .E7) (c : Fin Tag.E7.rank → ℤ),
      ggLin (p := p) ι (F u : MulAut ↥Bs) (∑ j, (c j : ZMod p) • h j) =
        ∑ j, ((u • c) j : ZMod p) • h j)
    (hFα : ∀ (u : WeylGroup .E7) (c : Fin Tag.E7.rank → ℤ) (w : V),
      ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ι (F u : MulAut ↥Bs) w) =
        ∑ j, (c j : ZMod p) * α j w)
    {Ψ : Set (Fin Tag.E7.rank → ℤ)} (hΨ : ∀ c ∈ Ψ, IsRoot .E7 c) :
    {t | t ∈ ggAutomizer X Bs ∧ ∃ c ∈ Ψ, ∀ w,
        ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j} =
      (fun c => ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) '' Ψ := by
  have hR : ∀ c ∈ Ψ, ∀ w,
      ggLin (p := p) ι ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) w =
        w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j := by
    intro c hc w
    obtain ⟨u, j, huj⟩ := isRoot_iff_exists_smul_single.1 (hΨ c hc)
    have hroot : rootReflection c = u * simple .E7 j * u⁻¹ := rootReflection_eq_conj huj
    have huc : u⁻¹ • c = (Pi.single j 1 : Fin Tag.E7.rank → ℤ) := by
      rw [← huj, ← mul_smul, inv_mul_cancel, one_smul]
    have hHj : (∑ k, ((Pi.single j 1 : Fin Tag.E7.rank → ℤ) k : ZMod p) • h k) = h j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hFroot : ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (F u : MulAut ↥Bs) * (F (simple .E7 j) : MulAut ↥Bs) *
          (F u⁻¹ : MulAut ↥Bs) := by
      rw [hroot]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have hcancel : ggLin (p := p) ι (F u : MulAut ↥Bs)
        (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) = w := by
      rw [← LinearEquiv.mul_apply, ← map_mul]
      simp
    have hFuh : ggLin (p := p) ι (F u : MulAut ↥Bs) (h j) =
        ∑ k, (c k : ZMod p) • h k := by
      have h1 := hFh u (Pi.single j 1)
      rw [hHj, huj] at h1
      exact h1
    have hAj : α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) =
        ∑ k, (c k : ZMod p) * α k w := by
      have h1 := hFα u⁻¹ c w
      rw [huc] at h1
      have hsingle : (∑ k, ((Pi.single j 1 : Fin Tag.E7.rank → ℤ) k : ZMod p) *
          α k (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w)) =
          α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      rwa [hsingle] at h1
    calc
      ggLin (p := p) ι ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) w
          = ggLin (p := p) ι (F u : MulAut ↥Bs)
              (ggLin (p := p) ι (F (simple .E7 j) : MulAut ↥Bs)
                (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w)) := by
            rw [hFroot, map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply]
      _ = ggLin (p := p) ι (F u : MulAut ↥Bs)
              (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w -
                α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) • h j) := by
            rw [hF j, hlin j]
      _ = ggLin (p := p) ι (F u : MulAut ↥Bs)
              (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) -
            α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) •
              ggLin (p := p) ι (F u : MulAut ↥Bs) (h j) := by
            rw [map_sub, map_smul]
      _ = w - (∑ k, (c k : ZMod p) * α k w) • ∑ k, (c k : ZMod p) • h k := by
            rw [hcancel, hAj, hFuh]
  ext t
  constructor
  · rintro ⟨-, c, hc, hform⟩
    refine ⟨c, hc, ?_⟩
    apply ggLin_injective (p := p) ι
    ext w
    rw [hform w, hR c hc w]
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(F (rootReflection c)).2, c, hc, hR c hc⟩

end CFSG.StandardType

end
