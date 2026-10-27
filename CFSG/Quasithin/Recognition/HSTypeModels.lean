module

public import CFSG.Quasithin.Recognition.HSTypeDefs
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.Quasithin.HSType

@[ext] structure Pauli2 where
  a : ZMod 4
  b : ZMod 2
  c : ZMod 2
  d : ZMod 2
  e : ZMod 2
  deriving DecidableEq

namespace Pauli2

@[expose] def equivTuple : Pauli2 ≃ ZMod 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 where
  toFun x := (x.a, x.b, x.c, x.d, x.e)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Pauli2 := Fintype.ofEquiv _ equivTuple.symm

@[expose] def dbl (t : ZMod 2) : ZMod 4 := 2 * (t.val : ZMod 4)

instance : Mul Pauli2 where
  mul x y := ⟨x.a + y.a + dbl (x.c * y.b + x.e * y.d), x.b + y.b, x.c + y.c, x.d + y.d,
    x.e + y.e⟩

instance : One Pauli2 := ⟨⟨0, 0, 0, 0, 0⟩⟩

instance : Inv Pauli2 where
  inv x := ⟨-x.a + dbl (x.c * x.b + x.e * x.d), x.b, x.c, x.d, x.e⟩

theorem mul_assoc_aux (x y w : Pauli2) : x * y * w = x * (y * w) := by
  have key : ∀ (xc xe yb yd yc ye wb wd : ZMod 2),
      dbl (xc * yb + xe * yd) + dbl ((xc + yc) * wb + (xe + ye) * wd) =
        dbl (yc * wb + ye * wd) + dbl (xc * (yb + wb) + xe * (yd + wd)) := by
    decide
  ext
  · show x.a + y.a + dbl (x.c * y.b + x.e * y.d) + w.a +
        dbl ((x.c + y.c) * w.b + (x.e + y.e) * w.d) =
      x.a + (y.a + w.a + dbl (y.c * w.b + y.e * w.d)) +
        dbl (x.c * (y.b + w.b) + x.e * (y.d + w.d))
    have := key x.c x.e y.b y.d y.c y.e w.b w.d
    linear_combination this
  all_goals (show _ + _ + _ = _ + (_ + _); ring)

instance : Group Pauli2 where
  mul_assoc := mul_assoc_aux
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel x := by
    have key : ∀ (b c d e : ZMod 2), dbl (c * b + e * d) + dbl (c * b + e * d) = 0 := by
      decide
    ext
    · show -x.a + dbl (x.c * x.b + x.e * x.d) + x.a + dbl (x.c * x.b + x.e * x.d) = 0
      have := key x.b x.c x.d x.e
      linear_combination this
    all_goals (show _ + _ = 0; decide +revert)

theorem card : Nat.card Pauli2 = 64 := by
  rw [Nat.card_congr equivTuple]
  simp

@[expose] def z0 : Pauli2 := ⟨2, 0, 0, 0, 0⟩

@[expose] def vec (x : Pauli2) : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 := (x.b, x.c, x.d, x.e)

theorem vec_mul (x y : Pauli2) : (x * y).vec = x.vec + y.vec := rfl

private theorem vec_add_self : ∀ u : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2, u + u = 0 := by
  decide

end Pauli2

@[expose] def omega4 (u v : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) : ZMod 2 :=
  u.2.1 * v.1 + u.1 * v.2.1 + u.2.2.2 * v.2.2.1 + u.2.2.1 * v.2.2.2

namespace Pauli2

theorem mul_comm_iff (x y : Pauli2) : x * y = y * x ↔ omega4 x.vec y.vec = 0 := by
  have key : ∀ b c d e b' c' d' e' : ZMod 2,
      dbl (c * b' + e * d') = dbl (c' * b + e' * d) ↔
        c * b' + b * c' + e * d' + d * e' = 0 := by
    decide
  rw [Pauli2.ext_iff]
  show (x.a + y.a + dbl (x.c * y.b + x.e * y.d) = y.a + x.a + dbl (y.c * x.b + y.e * x.d) ∧
      x.b + y.b = y.b + x.b ∧ x.c + y.c = y.c + x.c ∧ x.d + y.d = y.d + x.d ∧
      x.e + y.e = y.e + x.e) ↔ x.c * y.b + x.b * y.c + x.e * y.d + x.d * y.e = 0
  rw [add_comm x.a y.a, add_right_inj, ← key x.b x.c x.d x.e y.b y.c y.d y.e]
  exact ⟨fun h => h.1, fun h => ⟨h, add_comm _ _, add_comm _ _, add_comm _ _, add_comm _ _⟩⟩

private theorem omega4_nondeg : ∀ b c d e : ZMod 2,
    (∀ b' c' d' e' : ZMod 2, c * b' + b * c' + e * d' + d * e' = 0) →
      b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  decide

theorem mem_center_iff (x : Pauli2) : (∀ y : Pauli2, x * y = y * x) ↔ x.vec = 0 := by
  constructor
  · intro h
    have h' : ∀ b' c' d' e' : ZMod 2, x.c * b' + x.b * c' + x.e * d' + x.d * e' = 0 :=
      fun b' c' d' e' => (mul_comm_iff x ⟨0, b', c', d', e'⟩).mp (h _)
    obtain ⟨hb, hc, hd, he⟩ := omega4_nondeg x.b x.c x.d x.e h'
    simp [vec, hb, hc, hd, he]
  · intro h y
    rw [mul_comm_iff]
    obtain ⟨hb, hc, hd, he⟩ : x.b = 0 ∧ x.c = 0 ∧ x.d = 0 ∧ x.e = 0 := by
      simpa [vec, Prod.ext_iff] using h
    show x.c * y.b + x.b * y.c + x.e * y.d + x.d * y.e = 0
    simp [hb, hc, hd, he]

private theorem sq_one_aux : ∀ a : ZMod 4, a + a + dbl (0 * 0 + 0 * 0) = 0 → a = 0 ∨ a = 2 := by
  decide

theorem eq_one_or_eq_z0 (x : Pauli2) (hv : x.vec = 0) (hx : x * x = 1) : x = 1 ∨ x = z0 := by
  obtain ⟨hb, hc, hd, he⟩ : x.b = 0 ∧ x.c = 0 ∧ x.d = 0 ∧ x.e = 0 := by
    simpa [vec, Prod.ext_iff] using hv
  have ha : x.a + x.a + dbl (x.c * x.b + x.e * x.d) = 0 := congrArg Pauli2.a hx
  rw [hb, hc, hd, he] at ha
  rcases sq_one_aux x.a ha with h | h
  · left
    ext <;> simp_all [Pauli2.ext_iff] <;> rfl
  · right
    ext <;> simp_all [z0]

private def bad3 (u v w : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) : Bool :=
  decide (u ≠ 0 ∧ v ≠ 0 ∧ v ≠ u ∧ w ≠ 0 ∧ w ≠ u ∧ w ≠ v ∧ w ≠ u + v ∧
    omega4 u v = 0 ∧ omega4 u w = 0 ∧ omega4 v w = 0)

private theorem bad3_eq_false : ∀ u v w : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2,
    bad3 u v w = false := by
  decide +kernel

theorem omega4_no_three (u v w : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    ¬ (u ≠ 0 ∧ v ≠ 0 ∧ v ≠ u ∧ w ≠ 0 ∧ w ≠ u ∧ w ≠ v ∧ w ≠ u + v ∧
      omega4 u v = 0 ∧ omega4 u w = 0 ∧ omega4 v w = 0) :=
  decide_eq_false_iff_not.mp (bad3_eq_false u v w)

theorem card_image_vec_le_four (E : Finset Pauli2) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    (E.image vec).card ≤ 4 := by
  classical
  set S := E.image vec with hS
  have hSomega : ∀ u ∈ S, ∀ v ∈ S, omega4 u v = 0 := by
    intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact (mul_comm_iff x y).mp (hcomm x hx y hy)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨u, huS, hu0⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {0}) (t := S) (by rw [Finset.card_singleton]; omega)
  obtain ⟨v, hvS, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {0, u}) (t := S) (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨w, hwS, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {0, u, v, u + v}) (t := S) (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu0 hv hw
  exact omega4_no_three u v w ⟨hu0, hv.1, hv.2, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2,
    hSomega u huS v hvS, hSomega u huS w hwS, hSomega v hvS w hwS⟩

theorem card_le_eight (E : Finset Pauli2) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) (hmul : ∀ x ∈ E, ∀ y ∈ E, x * y ∈ E) : E.card ≤ 8 := by
  classical
  have hS4 := card_image_vec_le_four E hcomm
  have hfib : ∀ b ∈ E.image vec, (E.filter fun x => x.vec = b).card ≤ 2 := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    refine (Finset.card_le_card (t := {x, x * z0}) fun y hy => ?_).trans Finset.card_le_two
    rw [Finset.mem_filter] at hy
    obtain ⟨hyE, hyv⟩ := hy
    have hxy : (x * y).vec = 0 := by
      rw [vec_mul, hyv]
      exact vec_add_self _
    have hxy2 : x * y * (x * y) = 1 := hsq _ (hmul x hx y hyE)
    have hxx : x * x = 1 := hsq x hx
    have hy' : y = x * (x * y) := by
      rw [← mul_assoc, hxx, one_mul]
    rcases eq_one_or_eq_z0 _ hxy hxy2 with h | h
    · rw [hy', h, mul_one]
      exact Finset.mem_insert_self _ _
    · rw [hy', h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  calc E.card ≤ 2 * (E.image vec).card := Finset.card_le_mul_card_image (f := vec) E 2 hfib
    _ ≤ 8 := by omega

theorem vec_inv (x : Pauli2) : x⁻¹.vec = x.vec := rfl

theorem card_vec_eq_zero : (Finset.univ.filter fun c : Pauli2 => c.vec = 0).card = 4 := by
  decide

theorem card_le_sixteen (E : Finset Pauli2) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    E.card ≤ 16 := by
  classical
  have hS4 := card_image_vec_le_four E hcomm
  have hfib : ∀ b ∈ E.image vec, (E.filter fun x => x.vec = b).card ≤ 4 := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    refine (Finset.card_le_card
      (t := (Finset.univ.filter fun c : Pauli2 => c.vec = 0).image (x * ·)) fun y hy => ?_).trans
      (Finset.card_image_le.trans card_vec_eq_zero.le)
    rw [Finset.mem_filter] at hy
    refine Finset.mem_image.mpr ⟨x⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by
      simp⟩
    rw [vec_mul, vec_inv, hy.2]
    exact vec_add_self _
  calc E.card ≤ 4 * (E.image vec).card := Finset.card_le_mul_card_image (f := vec) E 4 hfib
    _ ≤ 16 := by omega

theorem card_le_eight_of_isElemAbelian (E : Subgroup Pauli2)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 8 := by
  classical
  have h := card_le_eight (Finset.univ.filter (· ∈ E))
    (fun x hx y hy => hcomm x (Finset.mem_filter.mp hx).2 y (Finset.mem_filter.mp hy).2)
    (fun x hx => hsq x (Finset.mem_filter.mp hx).2)
    (fun x hx y hy => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, E.mul_mem (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2⟩)
  have hcard : Nat.card E = (Finset.univ.filter (· ∈ E)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype (· ∈ E)
  rw [hcard]
  exact h

theorem mul_comm_or_z0 : ∀ x y : Pauli2, x * y = y * x ∨ x * y = y * x * z0 := by
  decide +kernel

theorem z0_central : ∀ y : Pauli2, z0 * y = y * z0 := by decide

theorem z0_ne_one : z0 ≠ 1 := by decide

theorem z0_mul_self : z0 * z0 = 1 := by decide

theorem eq_z0_of_central (x : Pauli2) (hx : ∀ y : Pauli2, x * y = y * x) (h2 : x * x = 1)
    (h1 : x ≠ 1) : x = z0 :=
  (eq_one_or_eq_z0 x ((mem_center_iff x).mp hx) h2).resolve_left h1

theorem card_le_sixteen_of_comm (E : Subgroup Pauli2)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ 16 := by
  classical
  have h := card_le_sixteen (Finset.univ.filter (· ∈ E))
    (fun x hx y hy => hcomm x (Finset.mem_filter.mp hx).2 y (Finset.mem_filter.mp hy).2)
  have hcard : Nat.card E = (Finset.univ.filter (· ∈ E)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype (· ∈ E)
  rw [hcard]
  exact h

@[expose] def ofQ1 : QuaternionGroup 2 → Pauli2
  | .a k => ⟨k, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) k, 0, 0, 0⟩
  | .xa k => ⟨1 - k, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) k, 1, 0, 0⟩

@[expose] def ofQ2 : QuaternionGroup 2 → Pauli2
  | .a k => ⟨k, 0, 0, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) k, 0⟩
  | .xa k => ⟨1 - k, 0, 0, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) k, 1⟩

@[expose] def ofZ4 (k : ZMod 4) : Pauli2 := ⟨k, 0, 0, 0, 0⟩

private theorem ofQ1_mul : ∀ x y : QuaternionGroup 2, ofQ1 (x * y) = ofQ1 x * ofQ1 y := by
  decide

private theorem ofQ2_mul : ∀ x y : QuaternionGroup 2, ofQ2 (x * y) = ofQ2 x * ofQ2 y := by
  decide

private theorem ofZ4_add : ∀ x y : ZMod 4, ofZ4 (x + y) = ofZ4 x * ofZ4 y := by decide

private theorem ofQ12_comm : ∀ x y : QuaternionGroup 2, ofQ1 x * ofQ2 y = ofQ2 y * ofQ1 x := by
  decide

private theorem ofZ4_central : ∀ (k : ZMod 4) (p : Pauli2), ofZ4 k * p = p * ofZ4 k := by
  decide

private theorem rearr {N : Type*} [Group N] (s₁ q₁ r₁ s₂ q₂ r₂ : N) (h1 : q₁ * s₂ = s₂ * q₁)
    (h2 : r₁ * s₂ = s₂ * r₁) (h3 : r₁ * q₂ = q₂ * r₁) :
    s₁ * s₂ * (q₁ * q₂) * (r₁ * r₂) = s₁ * q₁ * r₁ * (s₂ * q₂ * r₂) := by
  calc s₁ * s₂ * (q₁ * q₂) * (r₁ * r₂) = s₁ * (s₂ * q₁) * q₂ * r₁ * r₂ := by group
    _ = s₁ * (q₁ * s₂) * q₂ * r₁ * r₂ := by rw [h1]
    _ = s₁ * q₁ * s₂ * (q₂ * r₁) * r₂ := by group
    _ = s₁ * q₁ * s₂ * (r₁ * q₂) * r₂ := by rw [h3]
    _ = s₁ * q₁ * (s₂ * r₁) * q₂ * r₂ := by group
    _ = s₁ * q₁ * (r₁ * s₂) * q₂ * r₂ := by rw [h2]
    _ = s₁ * q₁ * r₁ * (s₂ * q₂ * r₂) := by group

@[expose] def prodHom :
    Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2 →* Pauli2 where
  toFun t := ofZ4 (Multiplicative.toAdd t.1) * ofQ1 t.2.1 * ofQ2 t.2.2
  map_one' := by decide
  map_mul' x y := by
    obtain ⟨x₁, x₂, x₃⟩ := x
    obtain ⟨y₁, y₂, y₃⟩ := y
    simp only [Prod.mk_mul_mk, toAdd_mul, ofZ4_add, ofQ1_mul, ofQ2_mul]
    exact rearr _ _ _ _ _ _ (ofZ4_central _ _).symm (ofZ4_central _ _).symm
      (ofQ12_comm _ _).symm

@[expose] def pre (p : Pauli2) : Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2 :=
  let q₁ : QuaternionGroup 2 :=
    if p.c = 0 then .a (p.b.val : ZMod 4) else .xa (p.b.val : ZMod 4)
  let q₂ : QuaternionGroup 2 :=
    if p.e = 0 then .a (p.d.val : ZMod 4) else .xa (p.d.val : ZMod 4)
  (Multiplicative.ofAdd (p.a - (ofQ1 q₁).a - (ofQ2 q₂).a), q₁, q₂)

private theorem prodHom_pre : ∀ p : Pauli2, prodHom (pre p) = p := by decide

private theorem prodHom_eq_one : ∀ (k : ZMod 4) (q₁ q₂ : QuaternionGroup 2),
    prodHom (Multiplicative.ofAdd k, q₁, q₂) = 1 →
      (k = 0 ∧ q₁ = 1 ∧ q₂ = 1) ∨ (k = 2 ∧ q₁ = .a 2 ∧ q₂ = 1) ∨
        (k = 2 ∧ q₁ = 1 ∧ q₂ = .a 2) ∨ (k = 0 ∧ q₁ = .a 2 ∧ q₂ = .a 2) := by
  decide

private theorem prodHom_gen₁ :
    prodHom (Multiplicative.ofAdd 2, QuaternionGroup.a 2, 1) = 1 := by decide

private theorem prodHom_gen₂ :
    prodHom (Multiplicative.ofAdd 2, 1, QuaternionGroup.a 2) = 1 := by decide

theorem prodHom_surjective : Function.Surjective prodHom := fun p => ⟨pre p, prodHom_pre p⟩

theorem ker_prodHom : prodHom.ker = z4Q8Q8Ident := by
  apply le_antisymm
  · intro t ht
    obtain ⟨k, q₁, q₂⟩ := t
    have h1 := prodHom_eq_one (Multiplicative.toAdd k) q₁ q₂ ht
    have hg₁ : (Multiplicative.ofAdd (2 : ZMod 4), QuaternionGroup.a 2, (1 : QuaternionGroup 2))
        ∈ z4Q8Q8Ident := Subgroup.subset_closure (Set.mem_insert _ _)
    have hg₂ : (Multiplicative.ofAdd (2 : ZMod 4), (1 : QuaternionGroup 2), QuaternionGroup.a 2)
        ∈ z4Q8Q8Ident := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rcases h1 with ⟨hk, h₁, h₂⟩ | ⟨hk, h₁, h₂⟩ | ⟨hk, h₁, h₂⟩ | ⟨hk, h₁, h₂⟩
    · have : k = 1 := by rw [← ofAdd_toAdd k, hk]; rfl
      subst this h₁ h₂
      exact z4Q8Q8Ident.one_mem
    · have : k = Multiplicative.ofAdd 2 := by rw [← ofAdd_toAdd k, hk]
      subst this h₁ h₂
      exact hg₁
    · have : k = Multiplicative.ofAdd 2 := by rw [← ofAdd_toAdd k, hk]
      subst this h₁ h₂
      exact hg₂
    · have : k = 1 := by rw [← ofAdd_toAdd k, hk]; rfl
      subst this h₁ h₂
      have h12 : ((1 : Multiplicative (ZMod 4)), QuaternionGroup.a (2 : ZMod (2 * 2)),
          QuaternionGroup.a (2 : ZMod (2 * 2))) =
          (Multiplicative.ofAdd (2 : ZMod 4), QuaternionGroup.a 2, (1 : QuaternionGroup 2)) *
            (Multiplicative.ofAdd (2 : ZMod 4), (1 : QuaternionGroup 2), QuaternionGroup.a 2) := by
        decide
      rw [h12]
      exact z4Q8Q8Ident.mul_mem hg₁ hg₂
  · rw [z4Q8Q8Ident, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact prodHom_gen₁
    · exact prodHom_gen₂

end Pauli2

noncomputable def z4Q8Q8EquivPauli2 : Z4Q8Q8 ≃* Pauli2 :=
  (QuotientGroup.quotientMulEquivOfEq Pauli2.ker_prodHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ Pauli2.prodHom_surjective)

theorem card_Z4Q8Q8 : Nat.card Z4Q8Q8 = 64 := by
  rw [Nat.card_congr z4Q8Q8EquivPauli2.toEquiv, Pauli2.card]

theorem card_of_isZ4Q8Q8 {P : Type*} [Group P] (h : IsZ4Q8Q8 P) : Nat.card P = 64 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_Z4Q8Q8]

theorem card_le_eight_of_isZ4Q8Q8 {P : Type*} [Group P] (h : IsZ4Q8Q8 P) (E : Subgroup P)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 8 := by
  obtain ⟨e⟩ := h
  set f := e.trans z4Q8Q8EquivPauli2
  have hc := Pauli2.card_le_eight_of_isElemAbelian (E.map f.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hsq x hx, map_one])
  rwa [Subgroup.card_map_of_injective f.injective] at hc

theorem mul_comm_or_of_isZ4Q8Q8 {P : Type*} [Group P] (h : IsZ4Q8Q8 P) {z : P}
    (hz : ∀ y : P, z * y = y * z) (hz2 : z * z = 1) (hz1 : z ≠ 1) (x y : P) :
    x * y = y * x ∨ x * y = y * x * z := by
  obtain ⟨e⟩ := h
  set f := e.trans z4Q8Q8EquivPauli2
  have hfz : f z = Pauli2.z0 := by
    refine Pauli2.eq_z0_of_central _ (fun w => ?_) (by rw [← map_mul, hz2, map_one])
      (by rwa [ne_eq, MulEquiv.map_eq_one_iff])
    obtain ⟨y, rfl⟩ := f.surjective w
    rw [← map_mul, ← map_mul, hz y]
  rcases Pauli2.mul_comm_or_z0 (f x) (f y) with hc | hc
  · left
    apply f.injective
    rw [map_mul, map_mul, hc]
  · right
    apply f.injective
    rw [map_mul, map_mul, map_mul, hc, hfz]

theorem Pauli2.card_center : Nat.card (Subgroup.center Pauli2) = 4 := by
  classical
  have hset : (Subgroup.center Pauli2 : Set Pauli2) = {x | x.vec = 0} := by
    ext x
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    show _ ↔ x.vec = 0
    rw [← Pauli2.mem_center_iff]
    exact ⟨fun h y => (h y).symm, fun h y => (h y).symm⟩
  rw [← SetLike.coe_sort_coe, hset, Nat.card_eq_fintype_card, Fintype.card_ofFinset]
  decide

theorem Pauli2.card_noncentral_invol :
    (Finset.univ.filter fun x : Pauli2 => x * x = 1 ∧ x.vec ≠ 0).card = 30 := by
  decide

theorem Pauli2.card_centralizer : ∀ x : Pauli2, x.vec ≠ 0 →
    (Finset.univ.filter fun y : Pauli2 => x * y = y * x).card = 32 := by
  decide +kernel

theorem Pauli2.sq_eq : ∀ x : Pauli2, x * x = 1 ∨ x * x = z0 := by decide

theorem card_center_of_isZ4Q8Q8 {P : Type*} [Group P] (h : IsZ4Q8Q8 P) :
    Nat.card (Subgroup.center P) = 4 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr (Subgroup.centerCongr (e.trans z4Q8Q8EquivPauli2)).toEquiv,
    Pauli2.card_center]

theorem eq_of_central_of_isZ4Q8Q8 {P : Type*} [Group P] (h : IsZ4Q8Q8 P) {x y : P}
    (hx : ∀ w : P, x * w = w * x) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hy : ∀ w : P, y * w = w * y) (hy2 : y * y = 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨e⟩ := h
  set f := e.trans z4Q8Q8EquivPauli2
  have key : ∀ u : P, (∀ w : P, u * w = w * u) → u * u = 1 → u ≠ 1 → f u = Pauli2.z0 := by
    intro u hu hu2 hu1
    refine Pauli2.eq_z0_of_central _ (fun w => ?_) (by rw [← map_mul, hu2, map_one])
      (by rwa [ne_eq, MulEquiv.map_eq_one_iff])
    obtain ⟨v, rfl⟩ := f.surjective w
    rw [← map_mul, ← map_mul, hu v]
  exact f.injective ((key x hx hx2 hx1).trans (key y hy hy2 hy1).symm)

theorem card_noncentral_invol_of_isZ4Q8Q8 {P : Type*} [Group P] [Fintype P] [DecidableEq P]
    (h : IsZ4Q8Q8 P) :
    (Finset.univ.filter fun x : P => x * x = 1 ∧ x ∉ Subgroup.center P).card = 30 := by
  classical
  obtain ⟨e⟩ := h
  set f := e.trans z4Q8Q8EquivPauli2
  rw [← Pauli2.card_noncentral_invol]
  refine Finset.card_bij (fun x _ => f x) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, by rw [← map_mul, hx.2.1, map_one], fun hv => hx.2.2 ?_⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have hc := (Pauli2.mem_center_iff (f x)).mpr hv (f g)
    apply f.injective
    rw [map_mul, map_mul, hc]
  · intro a _ b _ hab
    exact f.injective hab
  · intro y hy
    rw [Finset.mem_filter] at hy
    refine ⟨f.symm y, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, by rw [← map_mul, hy.2.1, map_one], fun hc => hy.2.2 ?_⟩
    rw [← Pauli2.mem_center_iff]
    intro w
    have := Subgroup.mem_center_iff.mp hc (f.symm w)
    have h2 := congrArg f this
    simpa using h2.symm

theorem card_centralizer_of_isZ4Q8Q8 {P : Type*} [Group P] (h : IsZ4Q8Q8 P) {x : P}
    (hx : x ∉ Subgroup.center P) : Nat.card (Subgroup.centralizer ({x} : Set P)) = 32 := by
  classical
  obtain ⟨e⟩ := h
  set f := e.trans z4Q8Q8EquivPauli2
  have hv : (f x).vec ≠ 0 := by
    intro hv
    apply hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hc := (Pauli2.mem_center_iff (f x)).mpr hv (f g)
    apply f.injective
    rw [map_mul, map_mul, hc]
  rw [← Pauli2.card_centralizer (f x) hv, ← Fintype.card_subtype]
  rw [Nat.card_congr ((Subgroup.equivMapOfInjective _ f.toMonoidHom f.injective).toEquiv)]
  rw [Nat.card_eq_fintype_card]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  constructor
  · rintro ⟨w, hw, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hw
    show f x * f w = f w * f x
    rw [← map_mul, ← map_mul, this]
  · intro hy
    refine ⟨f.symm y, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy.symm

theorem sq_eq_of_isZ4Q8Q8 {P : Type*} [Group P] (h : IsZ4Q8Q8 P) {z : P}
    (hz : ∀ y : P, z * y = y * z) (hz2 : z * z = 1) (hz1 : z ≠ 1) (x : P) :
    x * x = 1 ∨ x * x = z := by
  obtain ⟨e⟩ := h
  set f := e.trans z4Q8Q8EquivPauli2
  have hfz : f z = Pauli2.z0 := by
    refine Pauli2.eq_z0_of_central _ (fun w => ?_) (by rw [← map_mul, hz2, map_one])
      (by rwa [ne_eq, MulEquiv.map_eq_one_iff])
    obtain ⟨y, rfl⟩ := f.surjective w
    rw [← map_mul, ← map_mul, hz y]
  rcases Pauli2.sq_eq (f x) with hc | hc
  · left
    apply f.injective
    rw [map_mul, hc, map_one]
  · right
    apply f.injective
    rw [map_mul, hc, hfz]

theorem card_SL_zmod_two_eq_card_GL (n : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = Nat.card (GL (Fin n) (ZMod 2)) := by
  refine Nat.card_eq_of_bijective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2))
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => ?_⟩
  have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
    have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
    simpa using h2
  refine ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hdet⟩, ?_⟩
  apply Units.ext
  rfl

theorem card_SL_three_two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [card_SL_zmod_two_eq_card_GL, Matrix.card_GL_field, ZMod.card]
  decide

theorem isSimpleGroup_SL_three_two :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have key : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
    have hr1 : r = 1 := key r (by rwa [Fintype.card_fin] at hr)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by rw [← hrA, hr1]; simp)
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  have e : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact (MulEquiv.isSimpleGroup_congr e).mpr hs

theorem card_le_sixteen_of_isZ4Q8Q8 {P : Type*} [Group P] (h : IsZ4Q8Q8 P) (E : Subgroup P)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ 16 := by
  obtain ⟨e⟩ := h
  set f := e.trans z4Q8Q8EquivPauli2
  have hc := Pauli2.card_le_sixteen_of_comm (E.map f.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
  rwa [Subgroup.card_map_of_injective f.injective] at hc

abbrev Z4Cube : Type :=
  Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

theorem Z4Cube.pow_four : ∀ x : Z4Cube, x * x * (x * x) = 1 := by decide

theorem Z4Cube.card_sq_eq_one :
    (Finset.univ.filter fun x : Z4Cube => x * x = 1).card = 8 := by
  decide

end CFSG.Quasithin.HSType
