module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.SetAction

variable {G X : Type*} [Group G] [DecidableEq X] (ρ : G →* Equiv.Perm X) {m : ℕ}
  (F : Fin m → Finset X) (H : Subgroup G)

theorem image_eq_of_subset {g : G} {S T : Finset X} (h : ∀ p ∈ S, ρ g p ∈ T)
    (hc : S.card = T.card) : S.image (ρ g) = T := by
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    exact h p hp
  · rw [Finset.card_image_of_injective _ (ρ g).injective, hc]

variable {ρ F H}

@[expose] noncomputable def actFun (himg : ∀ h ∈ H, ∀ i, ∃ j, (F i).image (ρ h) = F j)
    (h : H) (i : Fin m) : Fin m :=
  Classical.choose (himg h.1 h.2 i)

theorem image_actFun (himg : ∀ h ∈ H, ∀ i, ∃ j, (F i).image (ρ h) = F j) (h : H)
    (i : Fin m) : (F i).image (ρ h) = F (actFun himg h i) :=
  Classical.choose_spec (himg h.1 h.2 i)

theorem actFun_injective (hF : Function.Injective F)
    (himg : ∀ h ∈ H, ∀ i, ∃ j, (F i).image (ρ h) = F j) (h : H) :
    Function.Injective (actFun himg h) := by
  intro i j hij
  apply hF
  have h1 := image_actFun himg h i
  have h2 := image_actFun himg h j
  rw [hij, ← h2] at h1
  exact Finset.image_injective (ρ h).injective h1

theorem actFun_unique (hF : Function.Injective F)
    (himg : ∀ h ∈ H, ∀ i, ∃ j, (F i).image (ρ h) = F j) {h : H} {i j : Fin m}
    (hj : (F i).image (ρ h) = F j) : actFun himg h i = j :=
  hF ((image_actFun himg h i).symm.trans hj)

@[expose] noncomputable def setAct (hF : Function.Injective F)
    (himg : ∀ h ∈ H, ∀ i, ∃ j, (F i).image (ρ h) = F j) : H →* Equiv.Perm (Fin m) where
  toFun h := Equiv.ofBijective (actFun himg h)
    ((Finite.injective_iff_bijective).1 (actFun_injective hF himg h))
  map_one' := by
    ext i
    simp only [Equiv.ofBijective_apply, Equiv.Perm.coe_one, id_eq]
    refine congrArg Fin.val (actFun_unique hF himg ?_)
    rw [OneMemClass.coe_one, map_one, Equiv.Perm.coe_one, Finset.image_id]
  map_mul' g h := by
    ext i
    simp only [Equiv.ofBijective_apply, Equiv.Perm.coe_mul, Function.comp_apply]
    refine congrArg Fin.val (actFun_unique hF himg ?_)
    rw [Subgroup.coe_mul, map_mul, Equiv.Perm.coe_mul, ← Finset.image_image,
      image_actFun himg h i, image_actFun himg g]

theorem setAct_apply (hF : Function.Injective F)
    (himg : ∀ h ∈ H, ∀ i, ∃ j, (F i).image (ρ h) = F j) (h : H) (i : Fin m) :
    setAct hF himg h i = actFun himg h i := rfl

theorem image_setAct (hF : Function.Injective F)
    (himg : ∀ h ∈ H, ∀ i, ∃ j, (F i).image (ρ h) = F j) (h : H) (i : Fin m) :
    (F i).image (ρ h) = F (setAct hF himg h i) :=
  image_actFun himg h i

theorem setAct_eq_of_image (hF : Function.Injective F)
    (himg : ∀ h ∈ H, ∀ i, ∃ j, (F i).image (ρ h) = F j) {h : H} {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ i, (F i).image (ρ h) = F (σ i)) : setAct hF himg h = σ := by
  ext i
  exact congrArg Fin.val (actFun_unique hF himg (hσ i))

theorem mem_ker_setAct (hF : Function.Injective F)
    (himg : ∀ h ∈ H, ∀ i, ∃ j, (F i).image (ρ h) = F j) {h : H} :
    h ∈ (setAct hF himg).ker ↔ ∀ i, (F i).image (ρ h) = F i := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h1 i
    have := image_setAct hF himg h i
    rwa [h1, Equiv.Perm.coe_one, id_eq] at this
  · intro h1
    exact setAct_eq_of_image hF himg (σ := 1) fun i => h1 i

end CFSG.RankThree.PartTwo.Sec4.Sporadic.SetAction
