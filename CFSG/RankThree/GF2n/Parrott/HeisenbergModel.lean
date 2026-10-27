module

public import CFSG.LargeExtraspecial.Timmesfeld.FStar

@[expose] public section

namespace CFSG.RankThree.GF2n.Parrott

open scoped commutatorElement

@[ext]
structure E8 where
  x : Fin 4 → ZMod 2
  y : Fin 4 → ZMod 2
  a : ZMod 2
deriving DecidableEq, Fintype

namespace E8

theorem neg_one_eq_one : (-1 : ZMod 2) = 1 := by decide

@[simp]
theorem neg_one_smul (a : ZMod 2) : (-1 : ZMod 2) • a = a := by
  rw [neg_one_eq_one]
  simp

def q (x y : Fin 4 → ZMod 2) : ZMod 2 :=
  ∑ i, x i * y i

def b (x y x' y' : Fin 4 → ZMod 2) : ZMod 2 :=
  q x y' + q x' y

@[expose] def mulE8 (g h : E8) : E8 :=
  ⟨g.x + h.x, g.y + h.y, g.a + h.a + q g.x h.y⟩

@[expose] def oneE8 : E8 :=
  ⟨0, 0, 0⟩

@[expose] def invE8 (g : E8) : E8 :=
  ⟨-g.x, -g.y, -g.a + q g.x g.y⟩

@[simp]
theorem mulE8_x (g h : E8) : (mulE8 g h).x = g.x + h.x := rfl

@[simp]
theorem mulE8_y (g h : E8) : (mulE8 g h).y = g.y + h.y := rfl

@[simp]
theorem mulE8_a (g h : E8) : (mulE8 g h).a = g.a + h.a + q g.x h.y := rfl

@[simp]
theorem oneE8_x : oneE8.x = 0 := rfl

@[simp]
theorem oneE8_y : oneE8.y = 0 := rfl

@[simp]
theorem oneE8_a : oneE8.a = 0 := rfl

@[simp]
theorem invE8_x (g : E8) : (invE8 g).x = -g.x := rfl

@[simp]
theorem invE8_y (g : E8) : (invE8 g).y = -g.y := rfl

@[simp]
theorem invE8_a (g : E8) : (invE8 g).a = -g.a + q g.x g.y := rfl

def equivProd : E8 ≃ (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) × ZMod 2 where
  toFun g := (g.x, g.y, g.a)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem q_zero_left (y : Fin 4 → ZMod 2) : q 0 y = 0 := by
  change (∑ i, (0 : Fin 4 → ZMod 2) i * y i) = 0
  simp

@[simp]
theorem q_zero_right (x : Fin 4 → ZMod 2) : q x 0 = 0 := by
  change (∑ i, x i * (0 : Fin 4 → ZMod 2) i) = 0
  simp

theorem q_add_left (x x' y : Fin 4 → ZMod 2) : q (x + x') y = q x y + q x' y := by
  change (∑ i, (x i + x' i) * y i) = (∑ i, x i * y i) + ∑ i, x' i * y i
  simp [add_mul, Finset.sum_add_distrib]

theorem q_add_right (x y y' : Fin 4 → ZMod 2) : q x (y + y') = q x y + q x y' := by
  change (∑ i, x i * (y i + y' i)) = (∑ i, x i * y i) + ∑ i, x i * y' i
  simp [mul_add, Finset.sum_add_distrib]

theorem q_neg_left (x y : Fin 4 → ZMod 2) : q (-x) y = -q x y := by
  change (∑ i, (-x i) * y i) = -(∑ i, x i * y i)
  have h : (∑ i, -(x i * y i)) = -(∑ i, x i * y i) :=
    Finset.sum_neg_distrib (f := fun i => x i * y i)
  calc (∑ i, (-x i) * y i) = ∑ i, -(x i * y i) :=
        Finset.sum_congr rfl fun i _ => neg_mul (x i) (y i)
    _ = -(∑ i, x i * y i) := h

theorem q_neg_right (x y : Fin 4 → ZMod 2) : q x (-y) = -q x y := by
  change (∑ i, x i * (-y i)) = -(∑ i, x i * y i)
  have h : (∑ i, -(x i * y i)) = -(∑ i, x i * y i) :=
    Finset.sum_neg_distrib (f := fun i => x i * y i)
  calc (∑ i, x i * (-y i)) = ∑ i, -(x i * y i) :=
        Finset.sum_congr rfl fun i _ => mul_neg (x i) (y i)
    _ = -(∑ i, x i * y i) := h

theorem sum_single_mul (i : Fin 4) (c : ZMod 2) (y : Fin 4 → ZMod 2) :
    (∑ j, (Pi.single i c : Fin 4 → ZMod 2) j * y j) = c * y i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro hi
    simp at hi

theorem sum_mul_single (i : Fin 4) (c : ZMod 2) (x : Fin 4 → ZMod 2) :
    (∑ j, x j * (Pi.single i c : Fin 4 → ZMod 2) j) = x i * c := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro hi
    simp at hi

instance : Mul E8 := ⟨mulE8⟩
instance : One E8 := ⟨oneE8⟩
instance : Inv E8 := ⟨invE8⟩

@[simp]
theorem mul_apply (g h : E8) : g * h = mulE8 g h := rfl

@[simp]
theorem inv_apply (g : E8) : g⁻¹ = invE8 g := rfl

@[simp]
theorem one_eq : (1 : E8) = oneE8 := rfl

@[simp]
theorem one_x : (1 : E8).x = 0 := rfl

@[simp]
theorem one_y : (1 : E8).y = 0 := rfl

@[simp]
theorem one_a : (1 : E8).a = 0 := rfl

@[simp]
theorem mul_x (g h : E8) : (g * h).x = g.x + h.x := by
  simp [mul_apply]

@[simp]
theorem mul_y (g h : E8) : (g * h).y = g.y + h.y := by
  simp [mul_apply]

@[simp]
theorem mul_a (g h : E8) : (g * h).a = g.a + h.a + q g.x h.y := by
  simp [mul_apply]

@[simp]
theorem inv_x (g : E8) : (g⁻¹).x = -g.x := by
  simp [inv_apply]

@[simp]
theorem inv_y (g : E8) : (g⁻¹).y = -g.y := by
  simp [inv_apply]

@[simp]
theorem inv_a (g : E8) : (g⁻¹).a = -g.a + q g.x g.y := by
  simp [inv_apply]

@[expose] instance : Group E8 :=
  Group.ofLeftAxioms
    (fun g h k => by
      ext <;>
        simp [mulE8, q_add_left, q_add_right, Finset.sum_add_distrib, add_mul, mul_add] <;>
        ring)
    (fun g => by
      ext <;> simp [mulE8, oneE8])
    (fun g => by
      ext <;> simp [mulE8, invE8, q_neg_left] <;> abel)

theorem card_E8 : Nat.card E8 = 2 ^ 9 := by
  rw [Nat.card_congr equivProd]
  simp [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem mem_center_iff {z : E8} :
    z ∈ Subgroup.center E8 ↔ z.x = 0 ∧ z.y = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hz
    have hy : z.y = 0 := by
      funext i
      have h := congrArg E8.a (hz ⟨Pi.single i 1, 0, 0⟩)
      simp [mulE8, q, sum_single_mul, add_assoc] at h
      have h' : z.a + z.y i = z.a + 0 := by simpa using h
      simpa using add_left_cancel h'
    have hx : z.x = 0 := by
      funext i
      have h := congrArg E8.a (hz ⟨0, Pi.single i 1, 0⟩)
      simp [mulE8, q, sum_mul_single, add_assoc] at h
      have h' : z.a + 0 = z.a + z.x i := by simpa using h
      simpa using (add_left_cancel h').symm
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩ g
    ext
    · simp [hx]
    · simp [hy]
    · simp [q, hx, hy, add_assoc, add_comm, add_left_comm]

theorem center_eq : (Subgroup.center E8 : Set E8) = {z | z.x = 0 ∧ z.y = 0} := by
  ext z
  exact mem_center_iff

def centerEquiv : Subgroup.center E8 ≃ ZMod 2 where
  toFun z := z.1.a
  invFun a := ⟨⟨0, 0, a⟩, by rw [mem_center_iff]; exact ⟨rfl, rfl⟩⟩
  left_inv z := by
    apply Subtype.ext
    obtain ⟨z, hz⟩ := z
    rw [mem_center_iff] at hz
    ext <;> simp [hz.1, hz.2]
  right_inv _ := rfl

theorem card_center : Nat.card (Subgroup.center E8) = 2 := by
  rw [Nat.card_congr centerEquiv, Nat.card_zmod]

def zent : E8 :=
  ⟨0, 0, 1⟩

@[simp]
theorem zent_x : zent.x = 0 := rfl

@[simp]
theorem zent_y : zent.y = 0 := rfl

@[simp]
theorem zent_a : zent.a = 1 := rfl

theorem zent_mem_center : zent ∈ Subgroup.center E8 := by
  rw [mem_center_iff]
  exact ⟨rfl, rfl⟩

theorem orderOf_zent : orderOf zent = 2 := by
  apply orderOf_eq_prime
  · show zent ^ 2 = (1 : E8)
    rw [pow_two]
    ext <;> simp [mulE8, zent, q, CharTwo.add_self_eq_zero]
  · intro h
    have h1 : (1 : ZMod 2) = 0 := by
      simpa [zent] using congrArg E8.a h
    exact one_ne_zero h1

theorem zpowers_zent_eq_center : Subgroup.zpowers zent = Subgroup.center E8 := by
  have hle : Subgroup.zpowers zent ≤ Subgroup.center E8 := by
    rw [Subgroup.zpowers_le]
    exact zent_mem_center
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_center, Nat.card_zpowers, orderOf_zent]

theorem commutatorElement_eq (g h : E8) :
    ⁅g, h⁆ = ⟨0, 0, q g.x h.y - q h.x g.y⟩ := by
  rw [commutatorElement_def]
  ext
  · simp [q_add_left, q_add_right, q_neg_left, q_neg_right] <;> abel
  · simp [q_add_left, q_add_right, q_neg_left, q_neg_right] <;> abel
  · simp [q_add_left, q_add_right, q_neg_left, q_neg_right, sub_eq_add_neg]
    abel
    simp [neg_one_smul, one_smul, add_zero]
    exact congrArg (fun x : ZMod 2 => x + 0) (ZMod.neg_eq_self_mod_two (q h.x g.y))

theorem commutator_eq_center :
    ⁅(⊤ : Subgroup E8), (⊤ : Subgroup E8)⁆ = Subgroup.center E8 := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g _ h _
    rw [mem_center_iff, commutatorElement_eq]
    exact ⟨rfl, rfl⟩
  · intro z hz
    rw [mem_center_iff] at hz
    have hz_eq : z = ⁅(⟨Pi.single 0 1, 0, 0⟩ : E8), (⟨0, Pi.single 0 z.a, 0⟩ : E8)⁆ := by
      rw [commutatorElement_eq]
      ext
      · rename_i i
        simpa using congrFun hz.1 i
      · rename_i i
        simpa using congrFun hz.2 i
      · simp [q, sum_single_mul, sum_mul_single, sub_eq_add_neg, add_zero]
    rw [hz_eq]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem card_commutator :
    Nat.card ↥(⁅(⊤ : Subgroup E8), (⊤ : Subgroup E8)⁆ : Subgroup E8) = 2 := by
  rw [commutator_eq_center, card_center]

theorem commutator_eq_zpowers_zent :
    ⁅(⊤ : Subgroup E8), (⊤ : Subgroup E8)⁆ = Subgroup.zpowers zent := by
  rw [commutator_eq_center, zpowers_zent_eq_center]

theorem mul_self (g : E8) : g * g = ⟨0, 0, q g.x g.y⟩ := by
  ext <;> simp [CharTwo.add_self_eq_zero]

theorem sq_mem_center (g : E8) : g ^ 2 ∈ Subgroup.center E8 := by
  rw [mem_center_iff]
  rw [pow_two, mul_self]
  exact ⟨rfl, rfl⟩

theorem q_mul (g h : E8) :
    q (g * h).x (g * h).y = q g.x g.y + q h.x h.y + b g.x g.y h.x h.y := by
  simp [b, q_add_left, q_add_right, add_assoc, add_comm, add_left_comm]

theorem b_self (g : E8) : b g.x g.y g.x g.y = 0 := by
  simpa [b] using CharTwo.add_self_eq_zero (q g.x g.y)

theorem isPGroup_E8 : IsPGroup 2 E8 :=
  IsPGroup.of_card (n := 9) card_E8

theorem frattini_eq_center : _root_.frattini E8 = Subgroup.center E8 := by
  haveI : Fact (IsPGroup 2 E8) := ⟨isPGroup_E8⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · rw [CFSG.frattini_eq_closure_commutator_union_powers (R := E8) (p := 2)]
    rw [Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · rw [_root_.commutator_def] at hx
      rw [commutator_eq_center] at hx
      exact hx
    · exact sq_mem_center y
  · rw [← commutator_eq_center]
    exact CFSG.commutator_le_frattini_of_isPGroup (R := E8) (p := 2)

theorem isExtraspecialPGroup : CFSG.IsExtraspecialPGroup 2 E8 := by
  refine ⟨isPGroup_E8, ?_, frattini_eq_center, card_center⟩
  simpa [_root_.commutator_def] using commutator_eq_center

theorem isExtraspecial2_top :
    CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 (⊤ : Subgroup E8) := by
  have hcenter_top :
      (Subgroup.center ↥(⊤ : Subgroup E8)).map (⊤ : Subgroup E8).subtype =
        Subgroup.center E8 :=
    Subgroup.map_center_eq (Subgroup.topEquiv (G := E8))
  refine ⟨isPGroup_E8.to_subgroup (⊤ : Subgroup E8), ?_, ?_⟩
  · rw [commutator_eq_center, ← hcenter_top]
  · rw [commutator_eq_center, card_center]

def proj (g : E8) : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) :=
  (g.x, g.y)

theorem proj_eq_zero_iff (g : E8) : proj g = (0, 0) ↔ g ∈ Subgroup.center E8 := by
  rw [mem_center_iff]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨hx, hy⟩
    ext <;> simp [proj, hx, hy]

theorem card_quotient_center :
    Nat.card (E8 ⧸ Subgroup.center E8) = 2 ^ 8 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center E8)
  rw [card_E8, card_center] at h
  have h' : Nat.card (E8 ⧸ Subgroup.center E8) * 2 = 2 ^ 8 * 2 := by
    rw [← h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

end E8

end CFSG.RankThree.GF2n.Parrott
