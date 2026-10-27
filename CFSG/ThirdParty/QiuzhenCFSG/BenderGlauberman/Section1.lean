module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunctionHelpers
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Lemma 1.3 and the Λ-orbits of irreducible characters

Lemma 1.3 (the Brauer--Suzuki pairing on `T`), Lemma 1.7 (the orbits of the
dual group `ΛHom H0 U` on the irreducible characters of `H0`), and the
index-2 case of Lemma 1.7(iii).
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

/-- Lemma 1.3: for class functions vanishing outside `T`,
`(δ1*, δ2*)_G = (δ1^H, δ2^H)_H` and they agree on `T`. -/
public theorem lemma_1_3 {G : Type u} [Group G] [Fintype G] (c : Hyp11 G) (h12 : Hyp12 c)
    {δ1 δ2 : ClassFunction (↥c.H0)}
    (_hδ1 : IsClassFunction δ1) (_hδ2 : IsClassFunction δ2)
    (hδ1T : supportedOn δ1 {x : ↥c.H0 | (x : G) ∈ c.T})
    (hδ2T : supportedOn δ2 {x : ↥c.H0 | (x : G) ∈ c.T}) :
    scalarProduct G (inducedClassFunction c.H0 δ1) (inducedClassFunction c.H0 δ2) =
      scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 δ1)
        (inducedFromSub (h12.H0_normal_in_H).1 δ2) ∧
      ∀ g : G, g ∈ c.T → (hgH : g ∈ c.H) →
        inducedClassFunction c.H0 δ1 g =
          (inducedFromSub (h12.H0_normal_in_H).1 δ1) ⟨g, hgH⟩ := by
  classical
  let hH0 : c.H0 ≤ c.H := (h12.H0_normal_in_H).1
  let K : Subgroup (↥c.H) := c.H0.subgroupOf c.H
  let δ1' : ClassFunction (↥K) := fun x => δ1 ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  let δ2' : ClassFunction (↥K) := fun x => δ2 ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  have hcard : (Nat.card (↥K) : ℂ)⁻¹ = (Nat.card (↥c.H0) : ℂ)⁻¹ := by
    congr 1
    exact_mod_cast Nat.card_congr {
      toFun := fun x : ↥K => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.H0 => ⟨⟨(y : G), hH0 y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; ext; rfl }
  have hpart1 : scalarProduct G (inducedClassFunction c.H0 δ1) (inducedClassFunction c.H0 δ2) =
      scalarProduct (↥c.H) (inducedFromSub hH0 δ1) (inducedFromSub hH0 δ2) := by
    calc
      scalarProduct G (inducedClassFunction c.H0 δ1) (inducedClassFunction c.H0 δ2)
          = ((Nat.card (↥c.H0) : ℂ)⁻¹ * (Nat.card (↥c.H0) : ℂ)⁻¹) *
              ∑ z : G, ∑ h : ↥c.H0, pairingSummand c.H0 δ1 δ2 z h := by
              rw [pairing_induced_expand]
      _ = ((Nat.card (↥c.H0) : ℂ)⁻¹ * (Nat.card (↥c.H0) : ℂ)⁻¹) *
              ∑ z : ↥c.H, ∑ h : ↥c.H0, pairingSummand c.H0 δ1 δ2 (z : G) h := by
              rw [pairing_sum_eq_sum_subgroup h12.T_is_TI h12.T_normalizer δ1 δ2 hδ1T hδ2T]
      _ = ((Nat.card (↥K) : ℂ)⁻¹ * (Nat.card (↥K) : ℂ)⁻¹) *
              ∑ z : ↥c.H, ∑ h : ↥K, pairingSummand K δ1' δ2' z h := by
              rw [← hcard]
              congr 1
              refine Finset.sum_congr rfl ?_
              intro z hz
              refine Finset.sum_bij (fun h hh =>
                (⟨⟨(h : G), hH0 h.2⟩, Subgroup.mem_subgroupOf.mpr h.2⟩ : ↥K)) ?_ ?_ ?_ ?_
              · intro h hh
                simp
              · intro h₁ hh₁ h₂ hh₂ hEq
                exact Subtype.ext
                  (congrArg (fun x : ↥K => ((x : ↥c.H) : G)) hEq)
              · intro h hh
                refine ⟨⟨(h : G), Subgroup.mem_subgroupOf.mp h.2⟩, by simp, ?_⟩
                ext; rfl
              · intro h hh
                by_cases hz0 : (z : G)⁻¹ * (h : G) * (z : G) ∈ c.H0
                · have hz1 : z⁻¹ * ((⟨⟨(h : G), hH0 h.2⟩, Subgroup.mem_subgroupOf.mpr h.2⟩ : ↥K) : ↥c.H) * z ∈ K := by
                    change (z : G)⁻¹ * (h : G) * (z : G) ∈ c.H0
                    exact hz0
                  rw [pairingSummand, pairingSummand]
                  simp [hz0, hz1, δ1', δ2']
                · have hz1 : z⁻¹ * ((⟨⟨(h : G), hH0 h.2⟩, Subgroup.mem_subgroupOf.mpr h.2⟩ : ↥K) : ↥c.H) * z ∉ K := by
                    intro hK
                    apply hz0
                    change (z : G)⁻¹ * (h : G) * (z : G) ∈ c.H0 at hK
                    exact hK
                  rw [pairingSummand, pairingSummand]
                  simp [hz0, hz1]
      _ = scalarProduct (↥c.H) (inducedClassFunction K δ1') (inducedClassFunction K δ2') := by
              rw [pairing_induced_expand]
      _ = scalarProduct (↥c.H) (inducedFromSub hH0 δ1) (inducedFromSub hH0 δ2) := by
              rfl
  have hpart2 : ∀ g : G, g ∈ c.T → (hgH : g ∈ c.H) →
      inducedClassFunction c.H0 δ1 g = (inducedFromSub hH0 δ1) ⟨g, hgH⟩ := by
    intro g hgT hgH
    calc
      inducedClassFunction c.H0 δ1 g
          = (Nat.card (↥c.H0) : ℂ)⁻¹ * ∑ x : G, inducedSummand δ1 g x := by
              unfold inducedClassFunction inducedSummand
              rfl
      _ = (Nat.card (↥c.H0) : ℂ)⁻¹ * ∑ x : ↥c.H, inducedSummand δ1 g (x : G) := by
              rw [induced_sum_eq_sum_subgroup h12.T_is_TI h12.T_normalizer δ1 hδ1T hgT]
      _ = (Nat.card (↥K) : ℂ)⁻¹ * ∑ x : ↥c.H, inducedSummand δ1 g (x : G) := by
              rw [hcard]
      _ = (inducedFromSub hH0 δ1) ⟨g, hgH⟩ := by
              unfold inducedFromSub
              unfold inducedClassFunction inducedSummand
              congr 1
  exact ⟨hpart1, hpart2⟩

/-! ## Lemma 1.7: Λ-orbits of irreducible characters of `H0` -/

section Lemma17

variable {G : Type u} [Group G] [Fintype G]

/-- A homomorphism `H →* ℂˣ` viewed as a class function on `H`. -/
@[expose] public def LambdaChar {H : Type u} [Group H] (l : H →* ℂˣ) : ClassFunction H :=
  fun x => (l x : ℂ)

/-- Linear characters of `H0` that are trivial on `U`, i.e. the dual of `H0/U`. -/
@[expose] public def LambdaHom (H0 U : Subgroup G) : Subgroup (↥H0 →* ℂˣ) where
  carrier := {l : ↥H0 →* ℂˣ | ∀ u : ↥H0, (u : G) ∈ U → l u = 1}
  one_mem' := by intro u hu; simp
  mul_mem' := by intro a b ha hb u hu; simp [ha u hu, hb u hu]
  inv_mem' := by intro a ha u hu; simp [ha u hu]

/-- The sum over a finite group of a nontrivial homomorphism into `ℂˣ` is zero. -/
public lemma sum_monoidHom_ne_one {A : Type u} [Group A] [Fintype A] (χ : A →* ℂˣ)
    (hχ : χ ≠ 1) : ∑ a : A, (χ a : ℂ) = 0 := by
  classical
  have hex : ∃ a₀ : A, χ a₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (MonoidHom.ext fun a => Units.ext (by simpa using h a))
  rcases hex with ⟨a₀, ha₀⟩
  have hc : (χ a₀ : ℂ) ≠ 1 := by
    intro hc1
    exact ha₀ (Units.ext hc1)
  have hS : (χ a₀ : ℂ) * ∑ a : A, (χ a : ℂ) = ∑ a : A, (χ a : ℂ) := by
    calc
      (χ a₀ : ℂ) * ∑ a : A, (χ a : ℂ) = ∑ a : A, (χ a₀ : ℂ) * (χ a : ℂ) := by
            rw [Finset.mul_sum]
      _ = ∑ a : A, (χ (a₀ * a) : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [map_mul]
            rfl
      _ = ∑ a : A, (χ a : ℂ) := by
            refine Finset.sum_bij (fun a ha => a₀ * a) ?_ ?_ ?_ ?_
            · intro a ha
              simp
            · intro a ha b hb hEq
              exact mul_left_cancel hEq
            · intro b hb
              refine ⟨a₀⁻¹ * b, by simp, ?_⟩
              simp
            · intro a ha
              rfl
  have h0 : ((χ a₀ : ℂ) - 1) * (∑ a : A, (χ a : ℂ)) = 0 := by
    rw [sub_mul, hS, one_mul]
    ring
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

/-- From `⁅H0,H0⁆ ≤ U` to the quotient-commutativity condition on `H0/U`. -/
public lemma commutator_le_quotient_comm (H0 U : Subgroup G)
    (hcomm : ⁅H0, H0⁆ ≤ U) : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0 := by
  intro x y
  apply Subgroup.mem_subgroupOf.mpr
  have hEqG : ((x : G) * (y : G)) / ((y : G) * (x : G)) = ⁅(x : G), (y : G)⁆ := by
    change ((x : G) * (y : G)) / ((y : G) * (x : G)) =
      (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹
    rw [div_eq_mul_inv]
    group
  have hmem : ((x : G) * (y : G)) / ((y : G) * (x : G)) ∈ U := by
    rw [hEqG]
    exact hcomm (Subgroup.commutator_mem_commutator x.2 y.2)
  simpa using hmem

/-- Any nontrivial element of `H0/U` is separated from `1` by a character of the dual. -/
public lemma LambdaHom_separates (H0 U : Subgroup G)
    (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (x : ↥H0) (hx : (x : G) ∉ U) : ∃ l : LambdaHom H0 U, l.1 x ≠ 1 := by
  classical
  let K := U.subgroupOf H0
  let : CommGroup (↥H0 ⧸ K) :=
    { QuotientGroup.Quotient.group K with
      mul_comm := by
        intro a b
        refine Quotient.inductionOn₂' a b ?_
        intro x y
        change ((x * y : ↥H0) : ↥H0 ⧸ K) = ((y * x : ↥H0) : ↥H0 ⧸ K)
        apply Quotient.sound
        exact (QuotientGroup.leftRel_apply (s := K) (x := x * y) (y := y * x)).mpr (by
          have hEq : (x * y)⁻¹ * (y * x) = (y⁻¹ * x⁻¹) / (x⁻¹ * y⁻¹) := by
            rw [div_eq_mul_inv]
            group
          rw [hEq]
          exact hcomm y⁻¹ x⁻¹) }
  have hxK : x ∉ K := by
    intro hxK
    exact hx (Subgroup.mem_subgroupOf.mp hxK)
  have hQpos : 0 < Monoid.exponent (↥H0 ⧸ K) := by
    exact Monoid.exponent_pos_of_exists (Fintype.card (↥H0 ⧸ K)) (Fintype.card_pos)
      (fun g => pow_card_eq_one (x := g))
  have : NeZero (Monoid.exponent (↥H0 ⧸ K) : ℂ) := ⟨by exact_mod_cast (ne_of_gt hQpos)⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent (↥H0 ⧸ K)) :=
    IsSepClosed.hasEnoughRootsOfUnity ℂ (Monoid.exponent (↥H0 ⧸ K))
  have hxne : (QuotientGroup.mk' K x : ↥H0 ⧸ K) ≠ 1 := by
    intro h1
    exact hxK ((QuotientGroup.eq_one_iff (N := K) x).mp h1)
  have hxbot : (x : ↥H0 ⧸ K) ∉ (⊥ : Subgroup (↥H0 ⧸ K)) := by
    intro hb
    exact hxne (Subgroup.mem_bot.mp hb)
  have hnotall : ¬ (∀ φ : (↥H0 ⧸ K) →* ℂˣ,
      (∀ y : ↥H0 ⧸ K, y ∈ (⊥ : Subgroup (↥H0 ⧸ K)) → φ y = 1) → φ x = 1) := by
    intro hall
    exact hxbot ((CommGroup.forall_monoidHom_apply_eq_one_iff (G := ↥H0 ⧸ K) (M := ℂ)
      (⊥ : Subgroup (↥H0 ⧸ K)) (x : ↥H0 ⧸ K)).mp hall)
  push Not at hnotall
  rcases hnotall with ⟨φ, hφkill, hφx⟩
  refine ⟨⟨φ.comp (QuotientGroup.mk' K), ?_⟩, ?_⟩
  · intro u hu
    have hu1 : QuotientGroup.mk' K u = 1 := (QuotientGroup.eq_one_iff (N := K) u).mpr hu
    simpa using congrArg φ hu1
  · simpa using hφx

/-- The monoid homomorphisms from a finite group to `ℂˣ` form a finite type. -/
public noncomputable instance instFintypeMonoidHomUnits {H : Type u} [Group H] [Fintype H] :
    Fintype (H →* ℂˣ) := by
  have hpos : 0 < Monoid.exponent H := by
    exact Monoid.exponent_pos_of_exists (Fintype.card H) (Fintype.card_pos)
      (fun g => pow_card_eq_one (x := g))
  haveI : NeZero (Monoid.exponent H : ℂ) := ⟨by exact_mod_cast (ne_of_gt hpos)⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent H) :=
    IsSepClosed.hasEnoughRootsOfUnity ℂ (Monoid.exponent H)
  exact Fintype.ofFinite (α := H →* ℂˣ)

/-- The dual group `ΛHom H0 U` is finite. -/
public noncomputable instance instFintypeLambdaHom (H0 U : Subgroup G) :
    Fintype ↥(LambdaHom H0 U) := by
  classical
  infer_instance

/-- `∑_{l ∈ ΛHom} l(x) = 0` for `x ∈ H0 \ U` — the regular character of `H0/U`
vanishes off `U`. -/
public lemma dual_sum_zero (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (x : ↥H0) (hx : (x : G) ∉ U) : ∑ l : LambdaHom H0 U, (l.1 x : ℂ) = 0 := by
  classical
  let ev : LambdaHom H0 U →* ℂˣ :=
    { toFun := fun l => l.1 x
      map_one' := by simp
      map_mul' := by intro a b; rfl }
  have hevne : ev ≠ 1 := by
    rcases LambdaHom_separates H0 U hK hcomm x hx with ⟨l₀, hl₀⟩
    intro h1
    exact hl₀ (congrArg (fun f => f l₀) h1)
  exact sum_monoidHom_ne_one ev hevne

/-- `r(ℒ)ν = Σ_{λ∈Λ} λ·ν` — the multiplicity-weighted orbit sum. -/
@[expose] public def orbitSumAll (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (ν : ClassFunction (↥H0)) : ClassFunction (↥H0) :=
  fun x => ∑ l : LambdaHom H0 U, (l.1 x : ℂ) * ν x

/-- The `Λ`-orbit of `ν` as a finset of distinct class functions. -/
@[expose] public def orbit (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (ν : ClassFunction (↥H0)) : Finset (ClassFunction (↥H0)) := by
  classical
  exact Finset.univ.image (fun l : LambdaHom H0 U => LambdaChar l.1 * ν)

/-- `r(ℒν) = Σ_{μ ∈ ℒν} μ` — the sum over the distinct orbit elements. -/
@[expose] public def orbitSum (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (ν : ClassFunction (↥H0)) : ClassFunction (↥H0) :=
  fun x => ∑ μ ∈ orbit H0 U ν, μ x

/-- The stabilizer of `ν` in `ΛHom H0 U`. -/
@[expose] public def Stab (H0 U : Subgroup G) (ν : ClassFunction (↥H0)) :
    Subgroup (LambdaHom H0 U) where
  carrier := {l : LambdaHom H0 U | LambdaChar l.1 * ν = ν}
  one_mem' := by
    change LambdaChar (1 : ↥(LambdaHom H0 U)).1 * ν = ν
    have h1 : LambdaChar (1 : ↥(LambdaHom H0 U)).1 = (1 : ClassFunction (↥H0)) := by
      ext x
      simp [LambdaChar]
    rw [h1, one_mul]
  mul_mem' := by
    intro a b ha hb
    change LambdaChar (a * b).1 * ν = ν
    change LambdaChar a.1 * ν = ν at ha
    change LambdaChar b.1 * ν = ν at hb
    have h : LambdaChar (a * b).1 = LambdaChar a.1 * LambdaChar b.1 := by
      ext x
      simp [LambdaChar, map_mul]
    rw [h, mul_assoc, hb]
    exact ha
  inv_mem' := by
    intro a ha
    change LambdaChar (a⁻¹).1 * ν = ν
    change LambdaChar a.1 * ν = ν at ha
    have h : LambdaChar (a⁻¹).1 = (LambdaChar a.1)⁻¹ := by
      ext x
      simp [LambdaChar, map_inv, Units.val_inv]
    rw [h]
    calc
      (LambdaChar a.1)⁻¹ * ν = (LambdaChar a.1)⁻¹ * (LambdaChar a.1 * ν) := by
            congr 1
            exact ha.symm
      _ = ((LambdaChar a.1)⁻¹ * LambdaChar a.1) * ν := by rw [mul_assoc]
      _ = ν := by
            have h1 : (LambdaChar a.1)⁻¹ * LambdaChar a.1 = 1 := by
              ext x
              have hx : (a.1 x : ℂ) ≠ 0 := Units.ne_zero (a.1 x)
              simp [LambdaChar, hx]
            rw [h1, one_mul]

/-- Every fiber of the orbit map `l ↦ ΛChar l · ν` has size `|Stab ν|`. -/
public lemma orbit_fiber_card (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (ν : ClassFunction (↥H0))
    (μ : ClassFunction (↥H0)) (hμ : μ ∈ orbit H0 U ν) :
    (Finset.univ.filter (fun l : LambdaHom H0 U => LambdaChar l.1 * ν = μ)).card =
      (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card := by
  classical
  change μ ∈ Finset.univ.image (fun l : LambdaHom H0 U => LambdaChar l.1 * ν) at hμ
  rcases (Finset.mem_image.mp hμ) with ⟨l₀, hl₀, hfl₀⟩
  have hbij : (Finset.univ.filter (fun l : LambdaHom H0 U => LambdaChar l.1 * ν = μ)).card =
      (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card := by
    refine Finset.card_bij (fun l hl => l₀⁻¹ * l) ?_ ?_ ?_
    · intro l hl
      simp at hl
      have hll : LambdaChar (l₀⁻¹ * l).1 * ν = ν := by
        calc
          LambdaChar (l₀⁻¹ * l).1 * ν = (LambdaChar l₀.1)⁻¹ * LambdaChar l.1 * ν := by
                funext x
                simp [LambdaChar, map_mul, map_inv, Units.val_inv]
          _ = (LambdaChar l₀.1)⁻¹ * (LambdaChar l.1 * ν) := by rw [mul_assoc]
          _ = (LambdaChar l₀.1)⁻¹ * μ := by rw [hl]
          _ = (LambdaChar l₀.1)⁻¹ * (LambdaChar l₀.1 * ν) := by rw [← hfl₀]
          _ = ν := by
                rw [← mul_assoc]
                have h1 : (LambdaChar l₀.1)⁻¹ * LambdaChar l₀.1 = 1 := by
                  ext x
                  have hx : (l₀.1 x : ℂ) ≠ 0 := Units.ne_zero (l₀.1 x)
                  simp [LambdaChar, hx]
                rw [h1, one_mul]
      simpa
    · intro a ha b hb hEq
      exact mul_left_cancel hEq
    · intro s hs
      simp at hs
      refine ⟨l₀ * s, ?_, ?_⟩
      · have hsl : LambdaChar (l₀ * s).1 * ν = μ := by
          calc
            LambdaChar (l₀ * s).1 * ν = LambdaChar l₀.1 * LambdaChar s.1 * ν := by
                  funext x
                  simp [LambdaChar, map_mul]
            _ = LambdaChar l₀.1 * (LambdaChar s.1 * ν) := by rw [mul_assoc]
            _ = LambdaChar l₀.1 * ν := by rw [hs]
            _ = μ := hfl₀
        simpa
      · simp
  exact hbij

/-- If the stabilizer of `ν` is trivial, the orbit map `l ↦ ΛChar l · ν` is
injective. -/
public lemma orbit_map_injective_of_stab_one (H0 U : Subgroup G)
    [Fintype ↥(LambdaHom H0 U)] (ν : ClassFunction (↥H0))
    (hstab : (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card = 1) :
    Function.Injective (fun l : LambdaHom H0 U => LambdaChar l.1 * ν) := by
  classical
  intro a b hab
  change LambdaChar a.1 * ν = LambdaChar b.1 * ν at hab
  have h : LambdaChar (b⁻¹ * a).1 * ν = ν := by
    calc
      LambdaChar (b⁻¹ * a).1 * ν = (LambdaChar b.1)⁻¹ * (LambdaChar a.1 * ν) := by
            funext x
            simp [LambdaChar, map_mul, map_inv, Units.val_inv, mul_assoc]
      _ = (LambdaChar b.1)⁻¹ * (LambdaChar b.1 * ν) := by rw [hab]
      _ = ν := by
            rw [← mul_assoc]
            have h1 : (LambdaChar b.1)⁻¹ * LambdaChar b.1 = 1 := by
              ext x
              have hx : (b.1 x : ℂ) ≠ 0 := Units.ne_zero (b.1 x)
              simp [LambdaChar, hx]
            rw [h1, one_mul]
  have hmem : b⁻¹ * a ∈ Finset.univ.filter
      (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using h⟩
  have hone : (1 : LambdaHom H0 U) ∈ Finset.univ.filter
      (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν) :=
    by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : LambdaChar (1 : ↥(LambdaHom H0 U)).1 = (1 : ClassFunction (↥H0)) := by
        ext x
        simp [LambdaChar]
      rw [h1, one_mul]
  rcases (Finset.card_eq_one.mp hstab) with ⟨z, hz⟩
  rw [hz] at hmem hone
  have hmem' : b⁻¹ * a = z := by simpa using hmem
  have hone' : (1 : LambdaHom H0 U) = z := by simpa using hone
  have hEq : b⁻¹ * a = 1 := by
    rw [hmem', hone']
  calc
    a = b * (b⁻¹ * a) := by group
    _ = b * 1 := by rw [hEq]
    _ = b := by simp

/-- `orbitSumAll ν x = |Stab ν| · orbitSum ν x` — the fiber decomposition of the
orbit sum. -/
public lemma orbitSumAll_eq_card_stab (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (ν : ClassFunction (↥H0)) (x : ↥H0) :
    orbitSumAll H0 U ν x =
      ((Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card : ℂ) *
        orbitSum H0 U ν x := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := orbit H0 U ν)
    (g := fun l : LambdaHom H0 U => LambdaChar l.1 * ν)
    (f := fun l : LambdaHom H0 U => ((LambdaChar l.1 * ν) x))
    (by intro l hl; exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)
  calc
    orbitSumAll H0 U ν x = ∑ l : LambdaHom H0 U, ((LambdaChar l.1 * ν) x) := by
          simp [orbitSumAll, LambdaChar]
    _ = ∑ μ ∈ orbit H0 U ν, ∑ l ∈ Finset.univ.filter (fun l : LambdaHom H0 U =>
          LambdaChar l.1 * ν = μ), ((LambdaChar l.1 * ν) x) := by
          rw [← hfib]
    _ = ∑ μ ∈ orbit H0 U ν, ∑ l ∈ Finset.univ.filter (fun l : LambdaHom H0 U =>
          LambdaChar l.1 * ν = μ), μ x := by
          refine Finset.sum_congr rfl ?_
          intro μ hμ
          refine Finset.sum_congr rfl ?_
          intro l hl
          rw [(Finset.mem_filter.mp hl).2]
    _ = ∑ μ ∈ orbit H0 U ν,
          (Finset.univ.filter (fun l : LambdaHom H0 U => LambdaChar l.1 * ν = μ)).card • μ x := by
          refine Finset.sum_congr rfl ?_
          intro μ hμ
          rw [Finset.sum_const]
    _ = ∑ μ ∈ orbit H0 U ν,
          ((Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card : ℂ) *
            μ x := by
          refine Finset.sum_congr rfl ?_
          intro μ hμ
          rw [nsmul_eq_mul]
          congr 1
          exact_mod_cast orbit_fiber_card H0 U ν μ hμ
    _ = ((Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card : ℂ) *
          ∑ μ ∈ orbit H0 U ν, μ x := by
          rw [Finset.mul_sum]
    _ = ((Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card : ℂ) *
          orbitSum H0 U ν x := rfl

/-- Lemma 1.7(i): `r(ℒν)` vanishes on `T = H0 \ U`. -/
public theorem lemma_1_7_i (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (ν : ClassFunction (↥H0)) (x : ↥H0) (hx : (x : G) ∉ U) :
    orbitSum H0 U ν x = 0 := by
  classical
  have hzero : orbitSumAll H0 U ν x = 0 := by
    calc
      orbitSumAll H0 U ν x = ∑ l : LambdaHom H0 U, (l.1 x : ℂ) * ν x := rfl
      _ = ν x * ∑ l : LambdaHom H0 U, (l.1 x : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro l hl
            ring
      _ = 0 := by
            rw [dual_sum_zero H0 U hK hcomm x hx]
            ring
  have hbridge := orbitSumAll_eq_card_stab H0 U ν x
  have hprod : ((Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card : ℂ) *
      orbitSum H0 U ν x = 0 := by
    rwa [← hbridge]
  have hcne : ((Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card : ℂ) ≠ 0 := by
    have hnon : (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).Nonempty := by
      refine ⟨1, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change LambdaChar (1 : ↥(LambdaHom H0 U)).1 * ν = ν
      have h1 : LambdaChar (1 : ↥(LambdaHom H0 U)).1 = (1 : ClassFunction (↥H0)) := by
        ext x
        simp [LambdaChar]
      rw [h1, one_mul]
    exact_mod_cast (Finset.card_pos.mpr hnon).ne'
  exact (mul_eq_zero.mp hprod).resolve_left hcne

/-- Elements of the `Λ`-orbit of an irreducible character are irreducible. -/
public lemma orbit_mem_isIrreducible (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    {ν : ClassFunction (↥H0)} (hν : IsIrreducibleCharacter ν)
    {μ : ClassFunction (↥H0)} (hμ : μ ∈ orbit H0 U ν) : IsIrreducibleCharacter μ := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, hEq⟩
  have hlam : IsLinearCharacter (fun x : ↥H0 => ((l.1 x : ℂˣ) : ℂ)) := isLinearCharacter_of_hom l.1
  rw [← hEq]
  change IsIrreducibleCharacter ((fun x : ↥H0 => ((l.1 x : ℂˣ) : ℂ)) * ν)
  exact isIrreducibleCharacter_mul_linear hlam hν


/-- Lemma 1.7(ii): the Fourier expansion of `χ|_{H₀}` regrouped over the `Λ`-orbits:
`χ|_{H₀} = Σⱼ (χ|_{H₀}, νⱼ)_{H₀}·r(Λνⱼ) + Σ'₍ν₎ (χ, (ν − ν₍rep₎)*)_G·ν`, where
`rep : ι → Irr H₀` is a system of orbit representatives (`hrep`) and the prime
omits the representatives (their coefficient is `(χ, 0*)_G = 0`). -/
public theorem lemma_1_7_ii (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit H0 U (rep i))
    (χ : ClassFunction G) (hχ : IsGeneralizedCharacter χ) (x : ↥H0) :
    χ (x : G) =
      (∑ i : ι, scalarProduct (↥H0) (fun y : ↥H0 => χ (y : G)) (rep i) *
          orbitSum H0 U (rep i) x) +
      (∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
        scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
          ν.1 x) := by
  classical
  let χH0 : ClassFunction (↥H0) := fun y : ↥H0 => χ (y : G)
  have hχcls : IsClassFunction χ := isClassFunction_of_isGeneralizedCharacter hχ
  have hχH0 : IsGeneralizedCharacter χH0 := isGeneralizedCharacter_restrict H0 hχ
  have hfourier : χ (x : G) = ∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
      scalarProduct (↥H0) χH0 ν.1 * ν.1 x := by
    exact classFunction_eq_sum_irr_coeffs (G := ↥H0) (φ := χH0) hχH0 x
  have hfib1 : (∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
        scalarProduct (↥H0) χH0 ν.1 * ν.1 x) =
      ∑ i : ι, ∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
        scalarProduct (↥H0) χH0 ν.1 * ν.1 x := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := fun ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν} =>
        Classical.choose (hrep ν))
      (f := fun ν => scalarProduct (↥H0) χH0 ν.1 * ν.1 x)
      (by intro ν hν; simp)
  have hfib2 : (∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
        scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
          ν.1 x) =
      ∑ i : ι, ∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
        scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
          ν.1 x := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := fun ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν} =>
        Classical.choose (hrep ν))
      (f := fun ν =>
        scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
          ν.1 x)
      (by intro ν hν; simp)
  have horbitSum_i (i : ι) :
      (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i), ν.1 x) =
        orbitSum H0 U (rep i) x := by
    classical
    change (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i), ν.1 x) =
      ∑ μ ∈ orbit H0 U (rep i), μ x
    symm
    refine Finset.sum_bij (fun μ hμ =>
        (⟨μ, orbit_mem_isIrreducible H0 U (hrep_irr i) hμ⟩ :
          {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν})) ?_ ?_ ?_ ?_
    · intro μ hμ
      have hgi : Classical.choose
          (hrep ⟨μ, orbit_mem_isIrreducible H0 U (hrep_irr i) hμ⟩) = i := by
        exact ((Classical.choose_spec
          (hrep ⟨μ, orbit_mem_isIrreducible H0 U (hrep_irr i) hμ⟩)).2 i hμ).symm
      simp [hgi]
    · intro a ha b hb hEq
      exact congrArg Subtype.val hEq
    · intro ν hν
      have hmem : ν.1 ∈ orbit H0 U (rep (Classical.choose (hrep ν))) :=
        (Classical.choose_spec (hrep ν)).1
      have hgi : Classical.choose (hrep ν) = i := (Finset.mem_filter.mp hν).2
      have hνi : ν.1 ∈ orbit H0 U (rep i) := by rwa [hgi] at hmem
      refine ⟨ν.1, hνi, ?_⟩
      exact Subtype.ext rfl
    · intro μ hμ
      rfl
  have hfib_i (i : ι) :
      (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
          scalarProduct (↥H0) χH0 ν.1 * ν.1 x) =
        (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
            scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x) +
          scalarProduct (↥H0) χH0 (rep i) * orbitSum H0 U (rep i) x := by
    classical
    have hcoeff (ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν})
        (hνi : ν.1 ∈ orbit H0 U (rep i)) :
        scalarProduct (↥H0) χH0 ν.1 =
          scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) +
            scalarProduct (↥H0) χH0 (rep i) := by
      calc
        scalarProduct (↥H0) χH0 ν.1 = scalarProduct G χ (inducedClassFunction H0 ν.1) := by
              rw [scalarProduct_restrict_induced H0 hχcls ν.1]
        _ = scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i) +
              inducedClassFunction H0 (rep i)) := by
              have hsub : inducedClassFunction H0 (ν.1 - rep i) +
                  inducedClassFunction H0 (rep i) = inducedClassFunction H0 ν.1 := by
                have h := inducedClassFunction_sub H0 ν.1 (rep i)
                rw [h]
                abel
              rw [hsub]
        _ = scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) +
              scalarProduct G χ (inducedClassFunction H0 (rep i)) := by
              rw [scalarProduct_add_right]
        _ = scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) +
              scalarProduct (↥H0) χH0 (rep i) := by
              rw [scalarProduct_restrict_induced H0 hχcls (rep i)]
    calc
      (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
          scalarProduct (↥H0) χH0 ν.1 * ν.1 x)
          = (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
              (scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) +
                scalarProduct (↥H0) χH0 (rep i)) * ν.1 x) := by
              refine Finset.sum_congr rfl ?_
              intro ν hν
              have hmem : ν.1 ∈ orbit H0 U (rep (Classical.choose (hrep ν))) :=
                (Classical.choose_spec (hrep ν)).1
              have hgi : Classical.choose (hrep ν) = i := (Finset.mem_filter.mp hν).2
              have hνi : ν.1 ∈ orbit H0 U (rep i) := by rwa [hgi] at hmem
              rw [hcoeff ν hνi]
      _ = (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
              scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x) +
          scalarProduct (↥H0) χH0 (rep i) *
            (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
              ν.1 x) := by
              calc
                (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
                    (scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) +
                      scalarProduct (↥H0) χH0 (rep i)) * ν.1 x)
                    = (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
                        (scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x +
                        scalarProduct (↥H0) χH0 (rep i) * ν.1 x)) := by
                        refine Finset.sum_congr rfl ?_
                        intro ν hν
                        rw [add_mul]
                _ = (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
                        scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x) +
                    (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
                        scalarProduct (↥H0) χH0 (rep i) * ν.1 x) := by
                        rw [Finset.sum_add_distrib]
                _ = (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
                        scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x) +
                    scalarProduct (↥H0) χH0 (rep i) *
                      (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
                        ν.1 x) := by
                        rw [← Finset.mul_sum]
      _ = (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
              scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x) +
          scalarProduct (↥H0) χH0 (rep i) * orbitSum H0 U (rep i) x := by
              rw [horbitSum_i i]
  calc
    χ (x : G) = ∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
          scalarProduct (↥H0) χH0 ν.1 * ν.1 x := hfourier
    _ = ∑ i : ι, ∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
          scalarProduct (↥H0) χH0 ν.1 * ν.1 x := hfib1
    _ = ∑ i : ι,
          ((∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
              scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x) +
            scalarProduct (↥H0) χH0 (rep i) * orbitSum H0 U (rep i) x) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hfib_i i
    _ = (∑ i : ι, ∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
            scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x) +
        (∑ i : ι, scalarProduct (↥H0) χH0 (rep i) * orbitSum H0 U (rep i) x) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
            scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
              ν.1 x) +
        (∑ i : ι, scalarProduct (↥H0) χH0 (rep i) * orbitSum H0 U (rep i) x) := by
          rw [hfib2]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro ν hν
          have hgi : Classical.choose (hrep ν) = i := (Finset.mem_filter.mp hν).2
          have href : rep (Classical.choose (hrep ν)) = rep i := by rw [hgi]
          rw [href]
    _ = (∑ i : ι, scalarProduct (↥H0) χH0 (rep i) * orbitSum H0 U (rep i) x) +
        (∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
          scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
            ν.1 x) := by
          rw [add_comm]

/-! ## Lemma 1.7(iii): the index-2 case

In case `|H0 : U| = 2`, the dual group `ΛHom H0 U` has exactly two elements:
`1` and `λ₂` (the nontrivial character of `H0/U`, which takes the value `-1`
on `T = H0 \ U`). Then every `Λ`-orbit has at most two elements,
`{νⱼ, λ₂νⱼ}`, and the orbit-sum terms of Lemma 1.7(ii) vanish on `T` by
Lemma 1.7(i); the `e_ν`-sum regroups to `Σⱼ (χ, (νⱼ − λ₂νⱼ)*)_G νⱼ` on `T`.
-/

/-- From `|H0 : U| = 2` we get an element of `H0` outside `U`. -/
private lemma exists_not_mem_of_index_two (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hindex : (U.subgroupOf H0).index = 2) : ∃ x : ↥H0, x ∉ U.subgroupOf H0 := by
  classical
  let K := U.subgroupOf H0
  have hKtop : K ≠ ⊤ := by
    intro htop
    have : K.index = 1 := by rw [htop]; simp
    rw [this] at hindex
    norm_num at hindex
  by_contra h
  push_neg at h
  exact hKtop ((Subgroup.eq_top_iff' K).mpr h)

/-- A chosen element of `H0 \ U` (witness of `exists_not_mem_of_index_two`). -/
private noncomputable def witnessIndexTwo (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hindex : (U.subgroupOf H0).index = 2) : ↥H0 := by
  classical
  exact Classical.choose (exists_not_mem_of_index_two H0 U hK hindex)

private lemma witnessIndexTwo_spec (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hindex : (U.subgroupOf H0).index = 2) :
    witnessIndexTwo H0 U hK hindex ∉ U.subgroupOf H0 := by
  classical
  exact Classical.choose_spec (exists_not_mem_of_index_two H0 U hK hindex)

/-- The nontrivial element `λ₂` of `ΛHom H0 U`, separating `witnessIndexTwo` from `1`.

Public because it appears in the statement of `lemma_1_7_iii`. -/
public noncomputable def lambda2 (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (hindex : (U.subgroupOf H0).index = 2) : LambdaHom H0 U := by
  classical
  exact Classical.choose (LambdaHom_separates H0 U hK hcomm (witnessIndexTwo H0 U hK hindex)
    (witnessIndexTwo_spec H0 U hK hindex))

private lemma lambda2_separates (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (hindex : (U.subgroupOf H0).index = 2) :
    (lambda2 H0 U hK hcomm hindex).1 (witnessIndexTwo H0 U hK hindex) ≠ 1 := by
  classical
  exact Classical.choose_spec (LambdaHom_separates H0 U hK hcomm (witnessIndexTwo H0 U hK hindex)
    (witnessIndexTwo_spec H0 U hK hindex))

/-- The quotient `H0/U` has exactly `2` elements. -/
private lemma card_quotient_of_index_two (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hindex : (U.subgroupOf H0).index = 2) :
    Fintype.card (↥H0 ⧸ U.subgroupOf H0) = 2 := by
  classical
  let K := U.subgroupOf H0
  have hcard : Nat.card (↥H0 ⧸ K) = K.index := (Subgroup.index_eq_card (H := K)).symm
  calc
    Fintype.card (↥H0 ⧸ K) = Nat.card (↥H0 ⧸ K) := by rw [Nat.card_eq_fintype_card]
    _ = K.index := hcard
    _ = 2 := hindex

/-- In a subgroup of index `2`, every square lies in the subgroup. -/
private lemma sq_mem_of_index_two (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hindex : (U.subgroupOf H0).index = 2) (x : ↥H0) : x ^ 2 ∈ U.subgroupOf H0 := by
  classical
  let K := U.subgroupOf H0
  have hpow : (QuotientGroup.mk' K x : ↥H0 ⧸ K) ^ 2 = 1 := by
    have hc := pow_card_eq_one (x := (QuotientGroup.mk' K x : ↥H0 ⧸ K))
    rw [card_quotient_of_index_two H0 U hK hindex] at hc
    exact hc
  have hq : QuotientGroup.mk' K (x ^ 2) = 1 := by
    rw [map_pow]
    exact hpow
  exact (QuotientGroup.eq_one_iff (N := K) (x ^ 2)).mp hq

/-- Every element of the quotient `H0/U` is `1` or the class of `witnessIndexTwo`. -/
private lemma quotient_dichotomy_of_index_two (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hindex : (U.subgroupOf H0).index = 2) :
    ∀ y : ↥H0 ⧸ U.subgroupOf H0,
      y = 1 ∨ y = QuotientGroup.mk' (U.subgroupOf H0) (witnessIndexTwo H0 U hK hindex) := by
  classical
  let K := U.subgroupOf H0
  let w := witnessIndexTwo H0 U hK hindex
  intro y
  have hcard : Fintype.card (↥H0 ⧸ K) = 2 := card_quotient_of_index_two H0 U hK hindex
  have huniv : (Finset.univ : Finset (↥H0 ⧸ K)).card = 2 := by
    simpa using hcard
  rcases Finset.card_eq_two.mp huniv with ⟨a, b, hab, huniv2⟩
  have h1ab : (1 : ↥H0 ⧸ K) = a ∨ (1 : ↥H0 ⧸ K) = b := by
    have h1 : (1 : ↥H0 ⧸ K) ∈ ({a, b} : Finset (↥H0 ⧸ K)) := by rw [← huniv2]; simp
    simpa using h1
  have hwab : QuotientGroup.mk' K w = a ∨ QuotientGroup.mk' K w = b := by
    have hw : QuotientGroup.mk' K w ∈ ({a, b} : Finset (↥H0 ⧸ K)) := by rw [← huniv2]; simp
    simpa using hw
  have hyab : y = a ∨ y = b := by
    have hy : y ∈ ({a, b} : Finset (↥H0 ⧸ K)) := by rw [← huniv2]; simp
    simpa using hy
  have h1w : (1 : ↥H0 ⧸ K) ≠ QuotientGroup.mk' K w := by
    intro hEq
    exact witnessIndexTwo_spec H0 U hK hindex
      ((QuotientGroup.eq_one_iff (N := K) w).mp hEq.symm)
  rcases h1ab with h1a | h1b
  · rcases hwab with hwa | hwb
    · exfalso
      exact h1w (hwa.trans h1a.symm).symm
    · rcases hyab with hya | hyb
      · exact Or.inl (hya.trans h1a.symm)
      · exact Or.inr (hyb.trans hwb.symm)
  · rcases hwab with hwa | hwb
    · rcases hyab with hya | hyb
      · exact Or.inr (hya.trans hwa.symm)
      · exact Or.inl (hyb.trans h1b.symm)
    · exfalso
      exact h1w (hwb.trans h1b.symm).symm

/-- Elements of `ΛHom H0 U` agree on quotients that are equal modulo `U`. -/
private lemma lambdaHom_eq_of_quotient_eq (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hindex : (U.subgroupOf H0).index = 2) (l : LambdaHom H0 U) (x y : ↥H0)
    (hq : QuotientGroup.mk' (U.subgroupOf H0) x = QuotientGroup.mk' (U.subgroupOf H0) y) :
    l.1 x = l.1 y := by
  classical
  let K := U.subgroupOf H0
  have hyw : x⁻¹ * y ∈ K := by
    apply (QuotientGroup.eq_one_iff (N := K) (x⁻¹ * y)).mp
    calc
      QuotientGroup.mk' K (x⁻¹ * y) = (QuotientGroup.mk' K x)⁻¹ * QuotientGroup.mk' K y := by
            rw [map_mul, map_inv]
      _ = 1 := by rw [hq]; exact inv_mul_cancel _
  have hkill : l.1 (x⁻¹ * y) = 1 := l.2 (x⁻¹ * y) (Subgroup.mem_subgroupOf.mp hyw)
  calc
    l.1 x = l.1 x * 1 := (mul_one (l.1 x)).symm
    _ = l.1 x * l.1 (x⁻¹ * y) := by rw [hkill]
    _ = l.1 x * (l.1 x⁻¹ * l.1 y) := by rw [map_mul]
    _ = l.1 x * ((l.1 x)⁻¹ * l.1 y) := by rw [map_inv]
    _ = l.1 y := by rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- `λ₂(witnessIndexTwo) = -1`. -/
private lemma lambda2_x0 (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (hindex : (U.subgroupOf H0).index = 2) :
    ((lambda2 H0 U hK hcomm hindex).1 (witnessIndexTwo H0 U hK hindex) : ℂ) = -1 := by
  classical
  let lam2 := lambda2 H0 U hK hcomm hindex
  let w := witnessIndexTwo H0 U hK hindex
  have hsqC : ((lam2.1 w : ℂ) ^ 2) = 1 := by
    have hsq : (lam2.1 w) ^ 2 = 1 := by
      calc
        (lam2.1 w) ^ 2 = lam2.1 (w ^ 2) := by rw [map_pow]
        _ = 1 := lam2.2 (w ^ 2) (Subgroup.mem_subgroupOf.mp (sq_mem_of_index_two H0 U hK hindex w))
    simpa using (congrArg (fun u : ℂˣ => (u : ℂ)) hsq)
  have hcases : (lam2.1 w : ℂ) = 1 ∨ (lam2.1 w : ℂ) = -1 := by
    rw [← sq_eq_one_iff]
    exact hsqC
  have hne1 : (lam2.1 w : ℂ) ≠ 1 := by
    intro h1
    exact lambda2_separates H0 U hK hcomm hindex (Units.ext h1)
  rcases hcases with h1 | hm1
  · exact (hne1 h1).elim
  · exact hm1

/-- The dual group `ΛHom H0 U` consists exactly of `1` and `λ₂`. -/
private lemma lambda2_dichotomy (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (hindex : (U.subgroupOf H0).index = 2) :
    ∀ l : LambdaHom H0 U, l.1 = 1 ∨ l.1 = (lambda2 H0 U hK hcomm hindex).1 := by
  classical
  let K := U.subgroupOf H0
  let lam2 := lambda2 H0 U hK hcomm hindex
  let w := witnessIndexTwo H0 U hK hindex
  intro l
  have hpoint (m : LambdaHom H0 U) (y : ↥H0) : m.1 y = 1 ∨ m.1 y = m.1 w := by
    rcases quotient_dichotomy_of_index_two H0 U hK hindex (QuotientGroup.mk' K y) with hq | hq
    · left
      exact m.2 y (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := K) y).mp hq))
    · right
      exact lambdaHom_eq_of_quotient_eq H0 U hK hindex m y w hq
  by_cases hw : l.1 w = 1
  · left
    ext y
    rcases hpoint l y with hy1 | hyw
    · exact (congrArg (fun u : ℂˣ => (u : ℂ)) hy1).trans (by simp [MonoidHom.one_apply])
    · exact (congrArg (fun u : ℂˣ => (u : ℂ)) (hyw.trans hw)).trans (by simp [MonoidHom.one_apply])
  · right
    ext y
    have hlwC : (l.1 w : ℂ) = (lam2.1 w : ℂ) := by
      have hsqC : ((l.1 w : ℂ) ^ 2) = 1 := by
        have hsq : (l.1 w) ^ 2 = 1 := by
          calc
            (l.1 w) ^ 2 = l.1 (w ^ 2) := by rw [map_pow]
            _ = 1 := l.2 (w ^ 2) (Subgroup.mem_subgroupOf.mp (sq_mem_of_index_two H0 U hK hindex w))
        simpa using (congrArg (fun u : ℂˣ => (u : ℂ)) hsq)
      have hcasesC : (l.1 w : ℂ) = 1 ∨ (l.1 w : ℂ) = -1 := by
        rw [← sq_eq_one_iff]
        exact hsqC
      rcases hcasesC with h1 | hm1
      · exact (hw (Units.ext h1)).elim
      · rw [hm1]
        exact (lambda2_x0 H0 U hK hcomm hindex).symm
    have hl : l.1 y = lam2.1 y := by
      rcases quotient_dichotomy_of_index_two H0 U hK hindex (QuotientGroup.mk' K y) with hq | hq
      · calc
          l.1 y = 1 := l.2 y (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := K) y).mp hq))
          _ = lam2.1 y := (lam2.2 y (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := K) y).mp hq))).symm
      · calc
          l.1 y = l.1 w := lambdaHom_eq_of_quotient_eq H0 U hK hindex l y w hq
          _ = lam2.1 w := Units.ext hlwC
          _ = lam2.1 y := (lambdaHom_eq_of_quotient_eq H0 U hK hindex lam2 y w hq).symm
    exact congrArg (fun u : ℂˣ => (u : ℂ)) hl

/-- `λ₂(x) = -1` for `x ∈ T = H0 \ U`. -/
private lemma lambda2_T (H0 U : Subgroup G) (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (hindex : (U.subgroupOf H0).index = 2) (x : ↥H0) (hx : (x : G) ∉ U) :
    ((lambda2 H0 U hK hcomm hindex).1 x : ℂ) = -1 := by
  classical
  let K := U.subgroupOf H0
  let lam2 := lambda2 H0 U hK hcomm hindex
  have hsqC : ((lam2.1 x : ℂ) ^ 2) = 1 := by
    have hsq : (lam2.1 x) ^ 2 = 1 := by
      calc
        (lam2.1 x) ^ 2 = lam2.1 (x ^ 2) := by rw [map_pow]
        _ = 1 := lam2.2 (x ^ 2) (Subgroup.mem_subgroupOf.mp (sq_mem_of_index_two H0 U hK hindex x))
    simpa using (congrArg (fun u : ℂˣ => (u : ℂ)) hsq)
  have hcases : (lam2.1 x : ℂ) = 1 ∨ (lam2.1 x : ℂ) = -1 := by
    rw [← sq_eq_one_iff]
    exact hsqC
  by_contra hne
  rcases hcases with h1 | hm1
  · have hxK : x ∈ K := by
      rcases quotient_dichotomy_of_index_two H0 U hK hindex (QuotientGroup.mk' K x) with hq | hq
      · exact (QuotientGroup.eq_one_iff (N := K) x).mp hq
      · have hlx : lam2.1 x = lam2.1 (witnessIndexTwo H0 U hK hindex) := by
          exact lambdaHom_eq_of_quotient_eq H0 U hK hindex lam2 x (witnessIndexTwo H0 U hK hindex) hq
        have hxC : (lam2.1 x : ℂ) = -1 := by
          rw [hlx]
          exact lambda2_x0 H0 U hK hcomm hindex
        have hneC : (1 : ℂ) ≠ -1 := by norm_num
        exact (hneC (h1.symm.trans hxC)).elim
    exfalso
    exact hx (Subgroup.mem_subgroupOf.mp hxK)
  · exact hne hm1

/-- Membership in the `Λ`-orbit of `ν` when `|H0 : U| = 2`:
the orbit is `{ν, λ₂ν}` (possibly a singleton). -/
private lemma orbit_mem_iff_of_index_two (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (hindex : (U.subgroupOf H0).index = 2) (ν μ : ClassFunction (↥H0)) :
    μ ∈ orbit H0 U ν ↔ μ = ν ∨ μ = LambdaChar (lambda2 H0 U hK hcomm hindex).1 * ν := by
  classical
  let lam2 := lambda2 H0 U hK hcomm hindex
  constructor
  · intro hμ
    rcases Finset.mem_image.mp hμ with ⟨l, hl, hEq⟩
    rcases lambda2_dichotomy H0 U hK hcomm hindex l with h1 | hl2
    · left
      have hL : LambdaChar l.1 = (1 : ClassFunction (↥H0)) := by
        ext y
        simp [LambdaChar, h1]
      rw [← hEq, hL, one_mul]
    · right
      rw [← hEq, hl2]
  · intro hμ
    rcases hμ with hEq | hEq
    · rw [hEq]
      refine Finset.mem_image.mpr ?_
      refine ⟨(1 : LambdaHom H0 U), by simp, ?_⟩
      have h1 : LambdaChar (1 : ↥(LambdaHom H0 U)).1 = (1 : ClassFunction (↥H0)) := by
        ext y
        simp [LambdaChar]
      rw [h1, one_mul]
    · rw [hEq]
      refine Finset.mem_image.mpr ?_
      refine ⟨lam2, by simp, ?_⟩
      rfl

/-- The fiber of `repOf` over `i` is in bijection with the orbit of `rep i`. -/
private lemma fiber_sum_eq_orbit_sum (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit H0 U (rep i))
    (f : ClassFunction (↥H0) → ℂ) (i : ι) :
    (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i), f ν.1) =
      ∑ μ ∈ orbit H0 U (rep i), f μ := by
  classical
  symm
  refine Finset.sum_bij (fun μ hμ =>
      (⟨μ, orbit_mem_isIrreducible H0 U (hrep_irr i) hμ⟩ :
        {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν})) ?_ ?_ ?_ ?_
  · intro μ hμ
    have hgi : Classical.choose
        (hrep ⟨μ, orbit_mem_isIrreducible H0 U (hrep_irr i) hμ⟩) = i := by
      exact ((Classical.choose_spec
        (hrep ⟨μ, orbit_mem_isIrreducible H0 U (hrep_irr i) hμ⟩)).2 i hμ).symm
    simp [hgi]
  · intro a ha b hb hEq
    exact congrArg Subtype.val hEq
  · intro ν hν
    have hmem : ν.1 ∈ orbit H0 U (rep (Classical.choose (hrep ν))) :=
      (Classical.choose_spec (hrep ν)).1
    have hgi : Classical.choose (hrep ν) = i := (Finset.mem_filter.mp hν).2
    have hνi : ν.1 ∈ orbit H0 U (rep i) := by rwa [hgi] at hmem
    refine ⟨ν.1, hνi, ?_⟩
    exact Subtype.ext rfl
  · intro μ hμ
    rfl

/-- Lemma 1.7(iii): in case `|H0 : U| = 2`, with `δⱼ := νⱼ − λ₂νⱼ`, we have
`χ = Σⱼ (χ, δⱼ*)_G νⱼ` on `T = H0 \ U`. -/
public theorem lemma_1_7_iii (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    (hindex : (U.subgroupOf H0).index = 2)
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit H0 U (rep i))
    (χ : ClassFunction G) (hχ : IsGeneralizedCharacter χ) (x : ↥H0) (hx : (x : G) ∉ U) :
    χ (x : G) =
      ∑ i : ι, scalarProduct G χ
        (inducedClassFunction H0 (rep i - LambdaChar (lambda2 H0 U hK hcomm hindex).1 * rep i)) *
        rep i x := by
  classical
  let χH0 : ClassFunction (↥H0) := fun y : ↥H0 => χ (y : G)
  let lam2 := lambda2 H0 U hK hcomm hindex
  let L2 : ClassFunction (↥H0) := LambdaChar lam2.1
  have hii := lemma_1_7_ii H0 U rep hrep_irr hrep χ hχ x
  have hTsum : (∑ i : ι, scalarProduct (↥H0) χH0 (rep i) * orbitSum H0 U (rep i) x) = 0 := by
    rw [Finset.sum_eq_zero]
    intro i hi
    rw [lemma_1_7_i H0 U hK hcomm (rep i) x hx]
    ring
  have hfib : (∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
        scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
          ν.1 x) =
      ∑ i : ι, ∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
        scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x := by
    have hfib2 : (∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
          scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
            ν.1 x) =
        ∑ i : ι, ∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
          scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
            ν.1 x := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
        (g := fun ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν} =>
          Classical.choose (hrep ν))
        (f := fun ν =>
          scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
            ν.1 x)
        (by intro ν hν; simp)
    rw [hfib2]
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro ν hν
    have hgi : Classical.choose (hrep ν) = i := (Finset.mem_filter.mp hν).2
    have href : rep (Classical.choose (hrep ν)) = rep i := by rw [hgi]
    rw [href]
  have hfib_iii (i : ι) :
      (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
          scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x) =
        scalarProduct G χ (inducedClassFunction H0 (rep i - L2 * rep i)) * rep i x := by
    classical
    let h : ClassFunction (↥H0) → ℂ := fun μ =>
      scalarProduct G χ (inducedClassFunction H0 (μ - rep i)) * μ x
    have hfib : (∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i), h ν.1) =
        ∑ μ ∈ orbit H0 U (rep i), h μ :=
      fiber_sum_eq_orbit_sum H0 U rep hrep_irr hrep h i
    rw [hfib]
    by_cases hfix : L2 * rep i = rep i
    · have horb : orbit H0 U (rep i) = {rep i} := by
        ext μ
        rw [orbit_mem_iff_of_index_two H0 U hK hcomm hindex (rep i) μ]
        rw [hfix, or_self]
        simp
      have hz : h (rep i) = 0 := by
        simp [h, inducedClassFunction_zero, scalarProduct_zero_right]
      rw [horb, Finset.sum_singleton, hz]
      simp [hfix, inducedClassFunction_zero, scalarProduct_zero_right]
    · have horb : orbit H0 U (rep i) = {rep i, L2 * rep i} := by
        ext μ
        rw [orbit_mem_iff_of_index_two H0 U hK hcomm hindex (rep i) μ]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rfl
      have hz : h (rep i) = 0 := by
        simp [h, inducedClassFunction_zero, scalarProduct_zero_right]
      have hpair : h (L2 * rep i) =
          scalarProduct G χ (inducedClassFunction H0 (rep i - L2 * rep i)) * rep i x := by
        calc
          h (L2 * rep i) =
              scalarProduct G χ (inducedClassFunction H0 (L2 * rep i - rep i)) * (L2 * rep i) x := rfl
          _ = scalarProduct G χ (inducedClassFunction H0 (-(rep i - L2 * rep i))) *
                (L2 * rep i) x := by
                rw [show L2 * rep i - rep i = -(rep i - L2 * rep i) by rw [neg_sub]]
          _ = - scalarProduct G χ (inducedClassFunction H0 (rep i - L2 * rep i)) *
                (L2 * rep i) x := by
                rw [inducedClassFunction_neg, scalarProduct_neg_right]
          _ = - scalarProduct G χ (inducedClassFunction H0 (rep i - L2 * rep i)) *
                ((lam2.1 x : ℂ) * rep i x) := rfl
          _ = - scalarProduct G χ (inducedClassFunction H0 (rep i - L2 * rep i)) * (-1 : ℂ) *
                rep i x := by
                rw [lambda2_T H0 U hK hcomm hindex x hx]
                ring
          _ = scalarProduct G χ (inducedClassFunction H0 (rep i - L2 * rep i)) * rep i x := by
                ring
      rw [horb, Finset.sum_pair (a := rep i) (b := L2 * rep i) (Ne.symm hfix), hz, hpair]
      ring
  calc
    χ (x : G) = (∑ i : ι, scalarProduct (↥H0) χH0 (rep i) * orbitSum H0 U (rep i) x) +
        (∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
          scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
            ν.1 x) := hii
    _ = ∑ ν : {ν : ClassFunction (↥H0) // IsIrreducibleCharacter ν},
          scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep (Classical.choose (hrep ν)))) *
            ν.1 x := by
          rw [hTsum]
          simp
    _ = ∑ i : ι, ∑ ν ∈ Finset.univ.filter (fun ν => Classical.choose (hrep ν) = i),
          scalarProduct G χ (inducedClassFunction H0 (ν.1 - rep i)) * ν.1 x := hfib
    _ = ∑ i : ι, scalarProduct G χ
          (inducedClassFunction H0 (rep i - LambdaChar (lambda2 H0 U hK hcomm hindex).1 * rep i)) *
          rep i x := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hfib_iii i

end Lemma17

end CFSG.BenderGlauberman
