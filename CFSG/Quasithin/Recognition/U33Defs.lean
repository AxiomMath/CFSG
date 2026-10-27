module

public import CFSG.Open.Catalog

public section

namespace CFSG.Quasithin

open scoped MatrixGroups
open CFSG.Open (WreathedTwoGroup)

@[expose] def z4Q8Identification : Multiplicative (ZMod 4) × QuaternionGroup 2 :=
  (Multiplicative.ofAdd 2, QuaternionGroup.a 2)

private theorem z4Q8Identification_central (g : Multiplicative (ZMod 4) × QuaternionGroup 2) :
    g * z4Q8Identification = z4Q8Identification * g := by
  revert g
  decide

instance : (Subgroup.zpowers z4Q8Identification).Normal where
  conj_mem n hn g := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcomm : Commute g z4Q8Identification := z4Q8Identification_central g
    have h : g * z4Q8Identification ^ k = z4Q8Identification ^ k * g :=
      (hcomm.zpow_right k).eq
    rw [h, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

abbrev Z4StarQ8 : Type :=
  (Multiplicative (ZMod 4) × QuaternionGroup 2) ⧸ Subgroup.zpowers z4Q8Identification

@[ext] structure Z4StarQ8Model where
  a : ZMod 4
  b : ZMod 2
  c : ZMod 2
  deriving DecidableEq

instance : Fintype Z4StarQ8Model :=
  Fintype.ofEquiv (ZMod 4 × ZMod 2 × ZMod 2)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun x => (x.a, x.b, x.c)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Mul Z4StarQ8Model where
  mul x y := ⟨x.a + y.a + 2 * ((x.c.val * y.b.val : ℕ) : ZMod 4), x.b + y.b, x.c + y.c⟩

instance : One Z4StarQ8Model := ⟨⟨0, 0, 0⟩⟩

instance : Inv Z4StarQ8Model where
  inv x := ⟨-x.a - 2 * ((x.c.val * x.b.val : ℕ) : ZMod 4), x.b, x.c⟩

instance : Group Z4StarQ8Model where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

private def ofQuaternion : QuaternionGroup 2 → Z4StarQ8Model
  | .a k => ⟨k, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) k, 0⟩
  | .xa k => ⟨1 - k, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) k, 1⟩

private theorem ofQuaternion_mul (x y : QuaternionGroup 2) :
    ofQuaternion (x * y) = ofQuaternion x * ofQuaternion y := by
  revert x y
  decide

private def z4Q8Hom : Multiplicative (ZMod 4) × QuaternionGroup 2 →* Z4StarQ8Model where
  toFun t := ⟨(Multiplicative.toAdd t.1), 0, 0⟩ * ofQuaternion t.2
  map_one' := by decide
  map_mul' := by decide

private theorem z4Q8Hom_surjective : Function.Surjective z4Q8Hom := by decide

private theorem z4Q8Hom_eq_one_iff (x : Multiplicative (ZMod 4) × QuaternionGroup 2) :
    z4Q8Hom x = 1 ↔ x = 1 ∨ x = z4Q8Identification := by
  revert x
  decide

private theorem zpowers_z4Q8Identification_eq_ker :
    Subgroup.zpowers z4Q8Identification = z4Q8Hom.ker := by
  ext x
  rw [MonoidHom.mem_ker, z4Q8Hom_eq_one_iff]
  have h2 : z4Q8Identification ^ 2 = 1 := by decide
  constructor
  · rintro ⟨k, rfl⟩
    have key : z4Q8Identification ^ k = 1 ∨ z4Q8Identification ^ k = z4Q8Identification := by
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        obtain ⟨m, rfl⟩ : (2 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero h
        rw [zpow_mul]
        simp [h2]
      · right
        have hk : k = 2 * (k / 2) + 1 := by omega
        rw [hk, zpow_add, zpow_mul]
        simp [h2]
    exact key
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

noncomputable def z4StarQ8EquivModel : Z4StarQ8 ≃* Z4StarQ8Model :=
  (QuotientGroup.quotientMulEquivOfEq zpowers_z4Q8Identification_eq_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective z4Q8Hom z4Q8Hom_surjective)

private theorem model_card : Fintype.card Z4StarQ8Model = 16 := by decide

private theorem model_card_involutions :
    Fintype.card {s : Z4StarQ8Model // s * s = 1 ∧ s ≠ 1} = 7 := by decide

private theorem model_card_noncentral :
    ∀ z : Z4StarQ8Model, (∀ q, q * z = z * q) → z * z = 1 → z ≠ 1 →
      Fintype.card {s : Z4StarQ8Model // s * s = 1 ∧ s ≠ 1 ∧ s ≠ z} = 6 := by decide

private theorem model_exists_conj :
    ∀ z s : Z4StarQ8Model, (∀ q, q * z = z * q) → z * z = 1 → z ≠ 1 → s * s = 1 → s ≠ 1 →
      s ≠ z → ∃ b : Z4StarQ8Model, b * s * b⁻¹ = s * z := by decide

private theorem model_exists_product :
    ∀ q : Z4StarQ8Model, ∃ u₁ u₂ u₃ : Z4StarQ8Model,
      u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₃ * u₃ = 1 ∧ q = u₁ * u₂ * u₃ := by decide

section Transport

variable {Q : Type*} [Group Q]

theorem Z4StarQ8.natCard_of_equiv (e : Q ≃* Z4StarQ8Model) : Nat.card Q = 16 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, model_card]

theorem Z4StarQ8.natCard_involutions_of_equiv (e : Q ≃* Z4StarQ8Model) :
    Nat.card {s : Q // s * s = 1 ∧ s ≠ 1} = 7 := by
  rw [Nat.card_congr (e.toEquiv.subtypeEquiv (q := fun m : Z4StarQ8Model => m * m = 1 ∧ m ≠ 1)
      (fun s => by
        simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_mul, ne_eq,
          map_eq_one_iff e e.injective])),
    Nat.card_eq_fintype_card, model_card_involutions]

theorem Z4StarQ8.natCard_noncentral_of_equiv (e : Q ≃* Z4StarQ8Model) {z : Q}
    (hzc : ∀ q, q * z = z * q) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card {s : Q // s * s = 1 ∧ s ≠ 1 ∧ s ≠ z} = 6 := by
  have hc : ∀ q : Z4StarQ8Model, q * e z = e z * q := fun q => by
    obtain ⟨q', rfl⟩ := e.surjective q
    rw [← map_mul, ← map_mul, hzc]
  have h2 : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
  have h1 : e z ≠ 1 := fun h => hz1 (e.injective (by rw [h, map_one]))
  rw [Nat.card_congr (e.toEquiv.subtypeEquiv (q := fun m : Z4StarQ8Model =>
      m * m = 1 ∧ m ≠ 1 ∧ m ≠ e z)
      (fun s => by
        simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_mul, ne_eq,
          map_eq_one_iff e e.injective, e.injective.eq_iff])),
    Nat.card_eq_fintype_card, model_card_noncentral (e z) hc h2 h1]

theorem Z4StarQ8.exists_conj_eq_mul_of_equiv (e : Q ≃* Z4StarQ8Model) {z s : Q}
    (hzc : ∀ q, q * z = z * q) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hsz : s ≠ z) : ∃ b : Q, b * s * b⁻¹ = s * z := by
  have hc : ∀ q : Z4StarQ8Model, q * e z = e z * q := fun q => by
    obtain ⟨q', rfl⟩ := e.surjective q
    rw [← map_mul, ← map_mul, hzc]
  obtain ⟨b, hb⟩ := model_exists_conj (e z) (e s) hc
    (by rw [← map_mul, hz2, map_one]) (fun h => hz1 (e.injective (by rw [h, map_one])))
    (by rw [← map_mul, hs2, map_one]) (fun h => hs1 (e.injective (by rw [h, map_one])))
    (fun h => hsz (e.injective h))
  refine ⟨e.symm b, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hb, map_mul]

theorem Z4StarQ8.exists_product_of_equiv (e : Q ≃* Z4StarQ8Model) (q : Q) :
    ∃ u₁ u₂ u₃ : Q, u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₃ * u₃ = 1 ∧ q = u₁ * u₂ * u₃ := by
  obtain ⟨u₁, u₂, u₃, h₁, h₂, h₃, h⟩ := model_exists_product (e q)
  refine ⟨e.symm u₁, e.symm u₂, e.symm u₃, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h₁, map_one]
  · rw [← map_mul, h₂, map_one]
  · rw [← map_mul, h₃, map_one]
  · apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, ← h]

end Transport

private instance : Fintype (WreathedTwoGroup 2) :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd (Multiplicative (ZMod (2 ^ 2)))
    (Multiplicative (ZMod 2))).symm

private instance : DecidableEq (WreathedTwoGroup 2) := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

theorem wreathedTwoGroup_natCard_two : Nat.card (WreathedTwoGroup 2) = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem wreathedTwoGroup_natCard_involutions_two :
    Nat.card {x : WreathedTwoGroup 2 // x * x = 1 ∧ x ≠ 1} = 7 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem wreathedTwoGroup_natCard_of_equiv {P : Type*} [Group P] (e : P ≃* WreathedTwoGroup 2) :
    Nat.card P = 32 := by
  rw [Nat.card_congr e.toEquiv, wreathedTwoGroup_natCard_two]

theorem wreathedTwoGroup_natCard_involutions_of_equiv {P : Type*} [Group P]
    (e : P ≃* WreathedTwoGroup 2) : Nat.card {x : P // x * x = 1 ∧ x ≠ 1} = 7 := by
  rw [Nat.card_congr (e.toEquiv.subtypeEquiv (q := fun m : WreathedTwoGroup 2 => m * m = 1 ∧ m ≠ 1)
      (fun s => by
        simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_mul, ne_eq,
          map_eq_one_iff e e.injective])),
    wreathedTwoGroup_natCard_involutions_two]

@[expose] def ABGWreathedRecognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) → ∀ P : Sylow 2 G,
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((P : Subgroup G) ≃* WreathedTwoGroup n)) →
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* PSL(3, GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* CFSG.Open.PSU3 p k))

end CFSG.Quasithin
