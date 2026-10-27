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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.RankThree.Asc83Table

open Subgroup
open scoped Matrix

universe u v

variable {L : Type u} [Group L]

abbrev Automizer (B : Subgroup L) : Type u :=
  normalizer (B : Set L) ⧸ (centralizer (B : Set L)).subgroupOf (normalizer (B : Set L))

@[expose] def ActsNontriviallyOnTwoSubgroup (B : Subgroup L) : Prop :=
  ∃ T : Subgroup L, IsPGroup 2 T ∧ B ≤ normalizer (T : Set L) ∧ ⁅T, B⁆ ≠ ⊥

section Transport

variable {L' : Type v} [Group L']

theorem map_equiv_centralizer_eq (e : L ≃* L') (B : Subgroup L) :
    (centralizer (B : Set L)).map e.toMonoidHom =
      centralizer ((B.map e.toMonoidHom : Subgroup L') : Set L') := by
  ext y
  simp only [mem_map, mem_centralizer_iff, SetLike.mem_coe, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hx b hb]
  · intro hy
    refine ⟨e.symm y, fun b hb => ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy (e b) ⟨b, hb, rfl⟩

@[expose] noncomputable def normalizerCongr (e : L ≃* L') (B : Subgroup L) :
    normalizer (B : Set L) ≃* normalizer ((B.map e.toMonoidHom : Subgroup L') : Set L') :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_equiv_normalizer_eq B e))

theorem normalizerCongr_apply (e : L ≃* L') (B : Subgroup L) (g : normalizer (B : Set L)) :
    ((normalizerCongr e B g : normalizer _) : L') = e g := rfl

noncomputable def automizerCongr (e : L ≃* L') (B : Subgroup L) :
    Automizer B ≃* Automizer (B.map e.toMonoidHom) :=
  QuotientGroup.congr _ _ (normalizerCongr e B) (by
    ext ⟨y, hy⟩
    rw [mem_map, mem_subgroupOf, ← map_equiv_centralizer_eq e B]
    constructor
    · rintro ⟨⟨x, hxN⟩, hx, hxy⟩
      rw [mem_subgroupOf] at hx
      refine ⟨x, hx, ?_⟩
      exact congrArg Subtype.val hxy
    · rintro ⟨x, hx, hxy⟩
      have hxN : x ∈ normalizer (B : Set L) := by
        rw [← map_equiv_normalizer_eq B e] at hy
        obtain ⟨x', hx', hxx'⟩ := mem_map.1 hy
        rwa [e.injective (hxy.trans hxx'.symm)]
      exact ⟨⟨x, hxN⟩, by rwa [mem_subgroupOf], Subtype.ext hxy⟩)

end Transport

theorem mem_normalizer_closure_of_conj_mem {S : Set L} [Finite (closure S)] {g : L}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ closure S) : g ∈ normalizer (closure S : Set L) := by
  have hle : closure S ≤ (closure S).comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    intro s hs
    exact h s hs
  let c : closure S → closure S := fun b => ⟨g * b * g⁻¹, hle b.2⟩
  have hc : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    simpa [c] using congrArg Subtype.val hab
  have hs : Function.Surjective c := Finite.surjective_of_injective hc
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hle hy, fun hy => ?_⟩
  obtain ⟨b, hb⟩ := hs ⟨g * y * g⁻¹, hy⟩
  have : g * (b : L) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hb
  rw [mul_left_inj, mul_right_inj] at this
  exact this ▸ b.2

section Coordinates

variable {n : ℕ} {B : Subgroup L} (f : Multiplicative (Fin n → ZMod 3) ≃* B)

@[expose] noncomputable def conjAdd (g : normalizer (B : Set L)) :
    (Fin n → ZMod 3) →+ (Fin n → ZMod 3) :=
  AddMonoidHom.toMultiplicative.symm
    (f.symm.toMonoidHom.comp ((normalizerMonoidHom B g).toMonoidHom.comp f.toMonoidHom))

theorem conjAdd_apply (g : normalizer (B : Set L)) (v : Fin n → ZMod 3) :
    conjAdd f g v =
      Multiplicative.toAdd (f.symm (normalizerMonoidHom B g (f (Multiplicative.ofAdd v)))) :=
  rfl

theorem conjAdd_mul (g h : normalizer (B : Set L)) :
    conjAdd f (g * h) = (conjAdd f g).comp (conjAdd f h) := by
  ext v
  simp only [conjAdd_apply, map_mul, AddMonoidHom.coe_comp, Function.comp_apply, ofAdd_toAdd,
    MulEquiv.apply_symm_apply]
  rfl

theorem conjAdd_one : conjAdd f (1 : normalizer (B : Set L)) = AddMonoidHom.id _ := by
  ext v
  simp [conjAdd_apply]

omit [Group L] in
@[expose] def toLin (φ : (Fin n → ZMod 3) →+ (Fin n → ZMod 3)) :
    (Fin n → ZMod 3) →ₗ[ZMod 3] (Fin n → ZMod 3) where
  toFun := φ
  map_add' := φ.map_add
  map_smul' c v := by
    rw [RingHom.id_apply]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ZMod 3) = c := ⟨c.val, ZMod.natCast_zmod_val c⟩
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

@[expose] noncomputable def conjMat (g : normalizer (B : Set L)) :
    Matrix (Fin n) (Fin n) (ZMod 3) :=
  LinearMap.toMatrix' (toLin (conjAdd f g))

theorem conjMat_apply (g : normalizer (B : Set L)) (i j : Fin n) :
    conjMat f g i j = conjAdd f g (Pi.single j 1) i := by
  rw [conjMat, LinearMap.toMatrix'_apply]
  rfl

theorem conjMat_mul (g h : normalizer (B : Set L)) :
    conjMat f (g * h) = conjMat f g * conjMat f h := by
  rw [conjMat, conjMat, conjMat, ← LinearMap.toMatrix'_comp, conjAdd_mul]
  rfl

theorem conjMat_one : conjMat f (1 : normalizer (B : Set L)) = 1 := by
  rw [conjMat, conjAdd_one, ← LinearMap.toMatrix'_id]
  rfl

@[expose] noncomputable def rho : normalizer (B : Set L) →* GL (Fin n) (ZMod 3) :=
  MonoidHom.toHomUnits
    { toFun := conjMat f
      map_one' := conjMat_one f
      map_mul' := conjMat_mul f }

theorem coe_rho (g : normalizer (B : Set L)) :
    ((rho f g : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) = conjMat f g := rfl

theorem ker_rho : (rho f).ker = (centralizer (B : Set L)).subgroupOf (normalizer (B : Set L)) := by
  rw [← normalizerMonoidHom_ker]
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, coe_rho]
  constructor
  · intro h
    ext b
    have hv := congrArg (fun M => M *ᵥ Multiplicative.toAdd (f.symm b)) h
    simp only [Matrix.one_mulVec] at hv
    rw [conjMat, LinearMap.toMatrix'_mulVec] at hv
    change conjAdd f g (Multiplicative.toAdd (f.symm b)) = _ at hv
    rw [conjAdd_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply] at hv
    have := congrArg (fun v => (f (Multiplicative.ofAdd v) : L)) hv
    simpa using this
  · intro h
    rw [conjMat, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => funext fun i => ?_
    change conjAdd f g v i = v i
    rw [conjAdd_apply, h]
    simp

noncomputable def automizerEquivRange : Automizer B ≃* (rho f).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_rho f).symm).trans
    (QuotientGroup.quotientKerEquivRange (rho f))

theorem rho_apply_eq (g : normalizer (B : Set L)) (M : Matrix (Fin n) (Fin n) (ZMod 3))
    (hM : ∀ j, (g : L) * (f (Multiplicative.ofAdd (Pi.single j 1)) : L) * (g : L)⁻¹ =
      (f (Multiplicative.ofAdd fun i => M i j) : L)) :
    ((rho f g : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) = M := by
  ext i j
  rw [coe_rho, conjMat_apply, conjAdd_apply]
  have : normalizerMonoidHom B g (f (Multiplicative.ofAdd (Pi.single j 1))) =
      f (Multiplicative.ofAdd fun i => M i j) := Subtype.ext (hM j)
  rw [this, MulEquiv.symm_apply_apply]
  rfl

end Coordinates

section Basis

open scoped IsMulCommutative

@[expose] noncomputable def powHom {C : Type*} [CommGroup C] {n : ℕ} (v : Fin n → C)
    (hv : ∀ i, v i ^ 3 = 1) : Multiplicative (Fin n → ZMod 3) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd a i).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

variable {n : ℕ} (x : Fin n → L)

@[expose] def basisProd (a : Fin n → ZMod 3) : L := (List.ofFn fun i => x i ^ (a i).val).prod

variable {x} (hx : ∀ i, x i ^ 3 = 1) (hc : ∀ i j, Commute (x i) (x j))
include hx hc

@[expose] noncomputable def basisHom : Multiplicative (Fin n → ZMod 3) →* closure (Set.range x) :=
  haveI : IsMulCommutative (closure (Set.range x)) :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  powHom (fun i => ⟨x i, subset_closure ⟨i, rfl⟩⟩) (fun i => Subtype.ext (by simpa using hx i))

theorem coe_basisHom (a : Multiplicative (Fin n → ZMod 3)) :
    (basisHom hx hc a : L) = basisProd x (Multiplicative.toAdd a) := by
  have : IsMulCommutative (closure (Set.range x)) :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  rw [basisProd]
  change ((∏ i, (⟨x i, subset_closure ⟨i, rfl⟩⟩ : closure (Set.range x)) ^
    (Multiplicative.toAdd a i).val : closure (Set.range x)) : L) = _
  rw [← Fin.prod_ofFn, ← (closure (Set.range x)).coe_subtype, map_list_prod, List.map_ofFn]
  rfl

theorem basisHom_single (i : Fin n) :
    basisHom hx hc (Multiplicative.ofAdd (Pi.single i 1)) = ⟨x i, subset_closure ⟨i, rfl⟩⟩ := by
  have : IsMulCommutative (closure (Set.range x)) :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  change ∏ j, (⟨x j, subset_closure ⟨j, rfl⟩⟩ : closure (Set.range x)) ^
    ((Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) j).val = _
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp [ZMod.val_one]

theorem basisHom_surjective : Function.Surjective (basisHom hx hc) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← map_subtype_le_map_subtype, ← MonoidHom.range_eq_map,
    range_subtype, closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨_, ⟨_, basisHom_single hx hc i⟩, rfl⟩

variable (hinj : Function.Injective (basisProd x))
include hinj

theorem basisHom_injective : Function.Injective (basisHom hx hc) := by
  intro a b hab
  have := congrArg Subtype.val hab
  rw [coe_basisHom, coe_basisHom] at this
  exact Multiplicative.toAdd.injective (hinj this)

@[expose] noncomputable def basisEquiv :
    Multiplicative (Fin n → ZMod 3) ≃* closure (Set.range x) :=
  MulEquiv.ofBijective (basisHom hx hc) ⟨basisHom_injective hx hc hinj, basisHom_surjective hx hc⟩

theorem coe_basisEquiv (a : Fin n → ZMod 3) :
    (basisEquiv hx hc hinj (Multiplicative.ofAdd a) : L) = basisProd x a :=
  coe_basisHom hx hc _

theorem basisEquiv_single (i : Fin n) :
    (basisEquiv hx hc hinj (Multiplicative.ofAdd (Pi.single i 1)) : L) = x i :=
  congrArg Subtype.val (basisHom_single hx hc i)

theorem card_closure_basis : Nat.card (closure (Set.range x)) = 3 ^ n := by
  rw [← Nat.card_congr (basisEquiv hx hc hinj).toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem rho_basis_eq (g : normalizer (closure (Set.range x) : Set L))
    (M : Matrix (Fin n) (Fin n) (ZMod 3))
    (hM : ∀ j, (g : L) * x j * (g : L)⁻¹ = basisProd x fun i => M i j) :
    ((rho (basisEquiv hx hc hinj) g : GL (Fin n) (ZMod 3)) :
      Matrix (Fin n) (Fin n) (ZMod 3)) = M := by
  refine rho_apply_eq _ g M fun j => ?_
  rw [basisEquiv_single, coe_basisEquiv]
  exact hM j

end Basis

end CFSG.RankThree.Asc83Table
