module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34GL

public section

namespace CFSG.Monster.B.TwoA

open CFSG

open scoped IsMulCommutative

section Conj

variable {G : Type*} [Group G]

@[expose] noncomputable def conjE (E : Subgroup G) :
    Subgroup.normalizer (E : Set G) →* MulAut E :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe E.le_normalizer)).toMonoidHom.comp
    (MulAut.conjNormal (H := E.subgroupOf (Subgroup.normalizer (E : Set G))))

theorem coe_conjE (E : Subgroup G) (g : Subgroup.normalizer (E : Set G)) (e : E) :
    ((conjE E g e : E) : G) = (g : G) * e * (g : G)⁻¹ := rfl

theorem centralizer_le_normalizer_sub (E : Subgroup G) :
    Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
  Subgroup.centralizer_le_normalizer _

theorem conjE_eq_one_iff (E : Subgroup G) (g : Subgroup.normalizer (E : Set G)) :
    conjE E g = 1 ↔ (g : G) ∈ Subgroup.centralizer (E : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 : ((conjE E g ⟨e, he⟩ : E) : G) = e := by rw [h]; rfl
    rw [coe_conjE, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · intro h
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [coe_conjE, MulAut.one_apply, ← (Subgroup.mem_centralizer_iff.1 h) e e.2,
      mul_inv_cancel_right]

theorem ker_conjE (E : Subgroup G) :
    (conjE E).ker =
      (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, conjE_eq_one_iff]

abbrev Esharp (E : Subgroup G) : Type _ := {d : G // d ∈ E ∧ d ≠ 1}

theorem conj_mem_of_normalizer {E : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) {d : G} (hd : d ∈ E) : g * d * g⁻¹ ∈ E :=
  (Subgroup.mem_normalizer_iff.1 hg d).1 hd

@[expose, instance_reducible] noncomputable def sharpAction (E : Subgroup G) :
    MulAction (Subgroup.normalizer (E : Set G)) (Esharp E) where
  smul g v := ⟨(g : G) * v * (g : G)⁻¹, conj_mem_of_normalizer g.2 v.2.1, fun h =>
    v.2.2 (by
      have := congrArg (fun d => (g : G)⁻¹ * d * g) h
      simpa [mul_assoc] using this)⟩
  one_smul v := Subtype.ext (by
    change ((1 : Subgroup.normalizer (E : Set G)) : G) * v *
      ((1 : Subgroup.normalizer (E : Set G)) : G)⁻¹ = v
    simp)
  mul_smul g h v := Subtype.ext (by
    change ((g * h : Subgroup.normalizer (E : Set G)) : G) * v *
      ((g * h : Subgroup.normalizer (E : Set G)) : G)⁻¹ =
      (g : G) * ((h : G) * v * (h : G)⁻¹) * (g : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

theorem natCard_Esharp [Finite G] (E : Subgroup G) : Nat.card (Esharp E) = Nat.card E - 1 := by
  classical
  have e : Esharp E ≃ {x : E // x ≠ 1} :=
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, fun h => v.2.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨x.1, x.1.2, fun h => x.2 (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Fintype E := Fintype.ofFinite E
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]

end Conj

theorem mem_normalizer_of_closure {G : Type*} [Group G] [Finite G] {S : Set G} {g : G}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

section Elem

variable {A : Type*} [Group A] [Finite A]

theorem finrank_additive_of_card [CFSG.IsElementaryAbelian 2 A] {n : ℕ}
    (h : Nat.card A = 2 ^ n) : Module.finrank (ZMod 2) (Additive A) = n := by
  have h2 := FiniteField.pow_finrank_eq_natCard 2 (Additive A)
  rw [show Nat.card (Additive A) = Nat.card A from Nat.card_congr Additive.toMul, h] at h2
  exact Nat.pow_right_injective le_rfl h2

@[expose] noncomputable def mulAutEquivLinear (A : Type*) [Group A]
    [CFSG.IsElementaryAbelian 2 A] : MulAut A ≃* (Additive A ≃ₗ[ZMod 2] Additive A) where
  toFun f := { MulEquiv.toAdditive f with
    map_smul' := ZMod.map_smul (MulEquiv.toAdditive f).toAddMonoidHom }
  invFun g := MulEquiv.toAdditive.symm g.toAddEquiv
  left_inv _ := MulEquiv.ext fun _ => rfl
  right_inv _ := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

@[expose] noncomputable def mulAutEquivGL [CFSG.IsElementaryAbelian 2 A] {n : ℕ}
    (h : Nat.card A = 2 ^ n) : MulAut A ≃* GL (Fin n) (ZMod 2) :=
  haveI : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  ((mulAutEquivLinear A).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm).trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Module.finBasisOfFinrankEq (ZMod 2) (Additive A) (finrank_additive_of_card h))).toMulEquiv)

theorem natCard_GL_three : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem natCard_GL_four : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 :=
  CFSG.OddStandard.Seitz77.card_GL_four_two

theorem natCard_GL_five : Nat.card (GL (Fin 5) (ZMod 2)) = 9999360 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_five]
  rfl

instance finite_mulAut : Finite (MulAut A) :=
  Finite.of_injective (fun f : MulAut A => (f : A → A)) fun _ _ h => MulEquiv.ext (congrFun h)

end Elem

theorem natCard_range_mul_ker {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H) :
    Nat.card f.range * Nat.card f.ker = Nat.card G := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem conjE_surjective_of_card {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (h : Nat.card (Subgroup.normalizer (E : Set G)) =
      Nat.card (MulAut E) * Nat.card (Subgroup.centralizer (E : Set G))) :
    Function.Surjective (conjE E) := by
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  have h1 := natCard_range_mul_ker (conjE E)
  rw [ker_conjE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (centralizer_le_normalizer_sub E)).toEquiv, h] at h1
  have hpos : 0 < Nat.card (Subgroup.centralizer (E : Set G)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

end CFSG.Monster.B.TwoA
