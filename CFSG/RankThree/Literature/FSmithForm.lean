module

public import CFSG.Foundations.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.Literature.FSmith

open Subgroup QuadraticMap
open scoped commutatorElement

section Extraspecial

variable {Q : Type*} [Group Q] (hQ : IsExtraspecialPGroup 2 Q)
include hQ

theorem commutatorElement_mem_center (x y : Q) : ⁅x, y⁆ ∈ center Q := by
  rw [← hQ.2.1, _root_.commutator_def]
  exact commutator_mem_commutator (mem_top x) (mem_top y)

theorem sq_eq_one_of_mem_center {c : Q} (hc : c ∈ center Q) : c ^ 2 = 1 := by
  have h := pow_card_eq_one' (G := center Q) (x := ⟨c, hc⟩)
  rw [hQ.2.2.2] at h
  simpa using congrArg Subtype.val h

theorem eq_of_mem_center {c d : Q} (hc : c ∈ center Q) (hd : d ∈ center Q) (hc1 : c ≠ 1)
    (hd1 : d ≠ 1) : c = d := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center Q)).1 hQ.2.2.2
  have h1 := hy ⟨c, hc⟩ (fun h => hc1 (congrArg Subtype.val h))
  have h2 := hy ⟨d, hd⟩ (fun h => hd1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem sq_mem_center [Finite Q] (x : Q) : x ^ 2 ∈ center Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 Q) := ⟨hQ.1⟩
  rw [← hQ.2.2.1]
  exact pth_power_mem_frattini_of_isPGroup x

theorem mul_sq_eq [Finite Q] (x y : Q) : (x * y) ^ 2 = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by
  have hc := mem_center_iff.mp (commutatorElement_mem_center hQ y x)
  have hyx : y * x = ⁅y, x⁆ * x * y := by simp only [commutatorElement_def]; group
  calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
    _ = x * ⁅y, x⁆ * x * y * y := by rw [hyx]; group
    _ = ⁅y, x⁆ * x * x * y * y := by rw [← hc x]
    _ = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group

theorem ofMul_of_eq_zero_iff (x : Q) :
    Additive.ofMul (Abelianization.of x) = 0 ↔ x ∈ center Q := by
  rw [← hQ.2.1, ← Abelianization.ker_of, MonoidHom.mem_ker]
  exact Additive.ofMul.injective.eq_iff' rfl

end Extraspecial

section Indicator

variable {Q : Type*} [Group Q]

theorem exists_ofMul_of (v : Additive (Abelianization Q)) :
    ∃ q : Q, Additive.ofMul (Abelianization.of q) = v := by
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  exact ⟨q, hq⟩

theorem ofMul_of_mul (x y : Q) :
    Additive.ofMul (Abelianization.of (x * y)) =
      Additive.ofMul (Abelianization.of x) + Additive.ofMul (Abelianization.of y) := by
  rw [map_mul, ofMul_mul]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

@[expose] noncomputable def ind (c : Q) : ZMod 2 :=
  open _root_.Classical in if c = 1 then 0 else 1

theorem ind_one : ind (1 : Q) = 0 := by simp [ind]

theorem ind_eq_zero_iff {c : Q} : ind c = 0 ↔ c = 1 := by
  unfold ind
  split_ifs with h
  · simp [h]
  · simp only [one_ne_zero, false_iff]
    exact h

theorem ind_mul (hQ : IsExtraspecialPGroup 2 Q) {c d : Q} (hc : c ∈ center Q)
    (hd : d ∈ center Q) : ind (c * d) = ind c + ind d := by
  by_cases hc1 : c = 1
  · subst hc1
    rw [one_mul, ind_one, zero_add]
  by_cases hd1 : d = 1
  · subst hd1
    rw [mul_one, ind_one, add_zero]
  have hcd : c = d := eq_of_mem_center hQ hc hd hc1 hd1
  subst hcd
  have h2 : c * c = 1 := by rw [← pow_two]; exact sq_eq_one_of_mem_center hQ hc
  rw [h2, ind_one]
  exact (CharTwo.add_self_eq_zero (ind c)).symm

theorem ind_inv (hQ : IsExtraspecialPGroup 2 Q) {c : Q} (hc : c ∈ center Q) :
    ind c⁻¹ = ind c := by
  have h2 : c * c = 1 := by rw [← pow_two]; exact sq_eq_one_of_mem_center hQ hc
  rw [inv_eq_of_mul_eq_one_right h2]

end Indicator

section Form

variable {Q : Type*} [Group Q] [Finite Q] (hQ : IsExtraspecialPGroup 2 Q)

@[expose] noncomputable def sqInd : Abelianization Q → ZMod 2 :=
  Quotient.lift (fun x : Q => ind (x ^ 2)) (by
    intro x y hxy
    have hw : x⁻¹ * y ∈ commutator Q := QuotientGroup.leftRel_apply.1 hxy
    rw [hQ.2.1] at hw
    have hy : y = x * (x⁻¹ * y) := by group
    change ind (x ^ 2) = ind (y ^ 2)
    rw [hy, mul_sq_eq hQ, sq_eq_one_of_mem_center hQ hw, mul_one,
      show ⁅x⁻¹ * y, x⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_center_iff.mp hw x).symm, one_mul])

theorem sqInd_of (x : Q) : sqInd hQ (Abelianization.of x) = ind (x ^ 2) := rfl

theorem polar_sqInd (x y : Q) :
    polar (fun v : Additive (Abelianization Q) => sqInd hQ (Additive.toMul v))
        (Additive.ofMul (Abelianization.of x)) (Additive.ofMul (Abelianization.of y)) =
      ind ⁅x, y⁆ := by
  rw [polar, ← ofMul_of_mul]
  change sqInd hQ (Abelianization.of (x * y)) - sqInd hQ (Abelianization.of x) -
    sqInd hQ (Abelianization.of y) = ind ⁅x, y⁆
  rw [sqInd_of, sqInd_of, sqInd_of, mul_sq_eq hQ,
    ind_mul hQ (mul_mem (commutatorElement_mem_center hQ y x) (sq_mem_center hQ x))
      (sq_mem_center hQ y),
    ind_mul hQ (commutatorElement_mem_center hQ y x) (sq_mem_center hQ x)]
  have h : ind ⁅y, x⁆ = ind ⁅x, y⁆ := by
    rw [← commutatorElement_inv, ind_inv hQ (commutatorElement_mem_center hQ x y)]
  rw [h]
  ring

variable [Module (ZMod 2) (Additive (Abelianization Q))]

@[expose] noncomputable def extraspecialQuadForm :
    QuadraticForm (ZMod 2) (Additive (Abelianization Q)) :=
  QuadraticMap.ofPolar (fun v => sqInd hQ (Additive.toMul v))
    (fun a v => by
      rcases zmod2_cases a with rfl | rfl
      · rw [zero_smul, zero_mul, zero_smul]
        change sqInd hQ 1 = 0
        rw [show (1 : Abelianization Q) = Abelianization.of 1 from (map_one _).symm, sqInd_of,
          one_pow, ind_one]
      · rw [one_smul, one_mul, one_smul])
    (fun u u' v => by
      obtain ⟨x, rfl⟩ := exists_ofMul_of u
      obtain ⟨x', rfl⟩ := exists_ofMul_of u'
      obtain ⟨y, rfl⟩ := exists_ofMul_of v
      rw [← ofMul_of_mul, polar_sqInd, polar_sqInd, polar_sqInd,
        commutatorElement_mul_left_eq_conj_mul,
        show x * ⁅x', y⁆ * x⁻¹ = ⁅x', y⁆ by
          rw [mem_center_iff.mp (commutatorElement_mem_center hQ x' y) x]; group,
        ind_mul hQ (commutatorElement_mem_center hQ x' y) (commutatorElement_mem_center hQ x y),
        add_comm])
    (fun a u v => by
      rcases zmod2_cases a with rfl | rfl
      · rw [zero_smul, zero_smul]
        obtain ⟨y, rfl⟩ := exists_ofMul_of v
        rw [show (0 : Additive (Abelianization Q)) = Additive.ofMul (Abelianization.of 1) by
          rw [map_one]; rfl, polar_sqInd, commutatorElement_one_left, ind_one]
      · rw [one_smul, one_smul])

theorem extraspecialQuadForm_apply (x : Q) :
    extraspecialQuadForm hQ (Additive.ofMul (Abelianization.of x)) =
      open _root_.Classical in if x ^ 2 = 1 then 0 else 1 := rfl

theorem polar_extraspecialQuadForm_apply (x y : Q) :
    polar (extraspecialQuadForm hQ) (Additive.ofMul (Abelianization.of x))
        (Additive.ofMul (Abelianization.of y)) =
      open _root_.Classical in if ⁅x, y⁆ = 1 then 0 else 1 :=
  polar_sqInd hQ x y

theorem polar_extraspecialQuadForm_eq_zero_iff (x y : Q) :
    polar (extraspecialQuadForm hQ) (Additive.ofMul (Abelianization.of x))
        (Additive.ofMul (Abelianization.of y)) = 0 ↔ x * y = y * x := by
  rw [polar_extraspecialQuadForm_apply]
  change ind ⁅x, y⁆ = 0 ↔ _
  rw [ind_eq_zero_iff, commutatorElement_eq_one_iff_mul_comm]

theorem extraspecialQuadForm_nondegenerate :
    (extraspecialQuadForm hQ).polarBilin.Nondegenerate := by
  have : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun v hv => ?_
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  rw [ofMul_of_eq_zero_iff hQ, mem_center_iff]
  intro y
  have h := hv (Additive.ofMul (Abelianization.of y))
  rw [polarBilin_apply_apply, polar_extraspecialQuadForm_eq_zero_iff] at h
  exact h.symm

end Form

section ConjAut

variable {H : Type*} [Group H] {Q : Subgroup H} (hQn : Q.Normal)

@[expose] def conjAut (g : H) : MulAut Q := @MulAut.conjNormal H _ Q hQn g

theorem conjAut_apply (g : H) (x : Q) : (conjAut hQn g x : H) = g * x * g⁻¹ :=
  @MulAut.conjNormal_apply H _ Q hQn g x

variable [Module (ZMod 2) (Additive (Abelianization Q))]

@[expose] noncomputable def conjEndo : H →* Module.End (ZMod 2) (Additive (Abelianization Q)) where
  toFun g := (MonoidHom.toAdditive
    (Abelianization.map (conjAut hQn g).toMonoidHom)).toZModLinearMap 2
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    change Additive.ofMul (Abelianization.of (conjAut hQn 1 q)) = _
    rw [show conjAut hQn 1 q = q from Subtype.ext (by rw [conjAut_apply]; group)]
    rfl
  map_mul' g g' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    change Additive.ofMul (Abelianization.of (conjAut hQn (g * g') q)) =
      Additive.ofMul (Abelianization.of (conjAut hQn g (conjAut hQn g' q)))
    rw [show conjAut hQn (g * g') q = conjAut hQn g (conjAut hQn g' q) from
      Subtype.ext (by rw [conjAut_apply, conjAut_apply, conjAut_apply]; group)]

theorem conjEndo_apply (g : H) (x : Q) :
    conjEndo hQn g (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (conjAut hQn g x)) := rfl

@[expose] noncomputable def conjLinEquiv : H →* (Additive (Abelianization Q) ≃ₗ[ZMod 2]
    Additive (Abelianization Q)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    (Additive (Abelianization Q))).toMonoidHom.comp (conjEndo hQn).toHomUnits

theorem conjLinEquiv_apply (g : H) (x : Q) :
    conjLinEquiv hQn g (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (conjAut hQn g x)) := rfl

end ConjAut

section Conj

variable {H : Type*} [Group H] {Q : Subgroup H} [Finite Q] (hQ : IsExtraspecialPGroup 2 Q)
  (hQn : Q.Normal) [Module (ZMod 2) (Additive (Abelianization Q))]

theorem conjLinEquiv_mem (g : H) :
    conjLinEquiv hQn g ∈ TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hQ) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  rw [conjLinEquiv_apply, extraspecialQuadForm_apply, extraspecialQuadForm_apply]
  have h : (conjAut hQn g x) ^ 2 = 1 ↔ x ^ 2 = 1 := by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  by_cases hx : x ^ 2 = 1
  · simp [hx, h.mpr hx]
  · simp [hx, show ¬ (conjAut hQn g x) ^ 2 = 1 from fun h' => hx (h.mp h')]

@[expose] noncomputable def extraspecialConjOrth :
    H →* TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hQ) :=
  (conjLinEquiv hQn).codRestrict _ (conjLinEquiv_mem hQ hQn)

theorem extraspecialConjOrth_apply (g : H) (x : Q) :
    ((extraspecialConjOrth hQ hQn g : TauCeti.QuadraticMap.orthogonalGroup
        (extraspecialQuadForm hQ)) : Additive (Abelianization Q) ≃ₗ[ZMod 2]
        Additive (Abelianization Q)) (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (conjAut hQn g x)) := rfl

omit [Finite Q] [Module (ZMod 2) (Additive (Abelianization Q))] in
include hQ in
theorem ind_conj_mul_inv_mul {g : H}
    (hg : ∀ x : Q, (conjAut hQn g x) * x⁻¹ ∈ center Q) (x y : Q) :
    ind (conjAut hQn g (x * y) * (x * y)⁻¹) =
      ind (conjAut hQn g x * x⁻¹) + ind (conjAut hQn g y * y⁻¹) := by
  rw [← ind_mul hQ (hg x) (hg y), map_mul]
  have hc := mem_center_iff.mp (hg y)
  congr 1
  calc conjAut hQn g x * conjAut hQn g y * (x * y)⁻¹
      = conjAut hQn g x * (conjAut hQn g y * y⁻¹) * x⁻¹ := by group
    _ = conjAut hQn g x * x⁻¹ * (conjAut hQn g y * y⁻¹) := by
      rw [mul_assoc (conjAut hQn g x), ← hc x⁻¹]; group

theorem mem_of_extraspecialConjOrth_eq_one (hCQ : centralizer (Q : Set H) ≤ Q) {g : H}
    (hg : extraspecialConjOrth hQ hQn g = 1) : g ∈ Q := by
  classical
  have hfix : ∀ x : Q, (conjAut hQn g x) * x⁻¹ ∈ center Q := by
    intro x
    have h := congrArg (fun r : TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hQ) =>
      (r : Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q))
        (Additive.ofMul (Abelianization.of x))) hg
    simp only [extraspecialConjOrth_apply, OneMemClass.coe_one, LinearEquiv.coe_one, id] at h
    rw [← ofMul_of_eq_zero_iff hQ, ofMul_of_mul, h, ← ofMul_of_mul, mul_inv_cancel, map_one]
    rfl
  let μ : Q →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (ind (conjAut hQn g x * x⁻¹))
      map_one' := by
        rw [map_one, inv_one, mul_one, ind_one]
        rfl
      map_mul' := fun x y => by
        rw [ind_conj_mul_inv_mul hQ hQn hfix, ofAdd_add] }
  let μ' : Additive (Abelianization Q) →+ ZMod 2 :=
    MonoidHom.toAdditive (Abelianization.lift μ)
  have : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  obtain ⟨u, hu⟩ := (LinearMap.BilinForm.toDual (extraspecialQuadForm hQ).polarBilin
    (extraspecialQuadForm_nondegenerate hQ)).surjective (AddMonoidHom.toZModLinearMap 2 μ')
  obtain ⟨q₀, rfl⟩ := exists_ofMul_of u
  have key : ∀ x : Q, conjAut hQn g x * x⁻¹ = ⁅(q₀ : Q), x⁆ := by
    intro x
    have h := LinearMap.congr_fun hu (Additive.ofMul (Abelianization.of x))
    rw [LinearMap.BilinForm.toDual_def, polarBilin_apply_apply,
      polar_extraspecialQuadForm_apply] at h
    have h' : ind ⁅q₀, x⁆ = ind (conjAut hQn g x * x⁻¹) := h
    by_contra hne
    have hc1 := commutatorElement_mem_center hQ q₀ x
    by_cases ha : conjAut hQn g x * x⁻¹ = 1
    · rw [ha, ind_one, ind_eq_zero_iff] at h'
      exact hne (ha.trans h'.symm)
    · by_cases hb : ⁅(q₀ : Q), x⁆ = 1
      · rw [hb, ind_one, eq_comm, ind_eq_zero_iff] at h'
        exact ha h'
      · exact hne (eq_of_mem_center hQ (hfix x) hc1 ha hb)
  have hcent : (q₀ : H)⁻¹ * g ∈ centralizer (Q : Set H) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun c : Q => (c : H)) (key ⟨y, hy⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjAut_apply, commutatorElement_def] at h1
    have h2 : g * y * g⁻¹ = (q₀ : H) * y * (q₀ : H)⁻¹ := by
      have := congrArg (· * y) h1
      simp only [inv_mul_cancel_right] at this
      exact this
    calc y * ((q₀ : H)⁻¹ * g) = (q₀ : H)⁻¹ * ((q₀ : H) * y * (q₀ : H)⁻¹) * g := by group
      _ = (q₀ : H)⁻¹ * (g * y * g⁻¹) * g := by rw [h2]
      _ = (q₀ : H)⁻¹ * g * y := by group
  have := hCQ hcent
  have hg' : g = (q₀ : H) * ((q₀ : H)⁻¹ * g) := by group
  rw [hg']
  exact Q.mul_mem q₀.2 this

end Conj

end CFSG.RankThree.Literature.FSmith
