module

public import CFSG.Monster.B.E6.StdF4RadicalLevi

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4

instance radicalZCommGroup :
    CommGroup radicalZ :=
  { (inferInstance : Group radicalZ) with
    mul_comm := fun a b => Subtype.ext (mul_comm_of_mem_radicalZ a.2 b.2) }

@[expose] def zBZ
    (j : Fin 7) : radicalZ := ⟨zB j, zB_mem_radicalZ j.2⟩

@[expose] def tZ :
    radicalZ := ⟨rootInvM, rootInvM_mem_radicalZ⟩

theorem zBZ_zero :
    zBZ 0 = tZ := Subtype.ext zB_zero

theorem zBZ_mul_self
    (j : Fin 7) : zBZ j * zBZ j = 1 := Subtype.ext (zB_mul_self j.2)

theorem val_zero_two : (0 : ZMod 2).val = 0 := rfl

theorem val_one_two : (1 : ZMod 2).val = 1 := rfl

theorem one_add_one_two : (1 : ZMod 2) + 1 = 0 := rfl

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem pow_val_add {M : Type*} [Monoid M] {x : M} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [one_add_one_two, val_zero_two, val_one_two, pow_zero, pow_one, hx]

@[expose] def zMap :
    Multiplicative (Fin 7 → ZMod 2) →* radicalZ where
  toFun v := ∏ j, zBZ j ^ (v.toAdd j).val
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, pow_val_add (zBZ_mul_self _), Finset.prod_mul_distrib]

theorem zMap_apply
    (v : Multiplicative (Fin 7 → ZMod 2)) :
    zMap v = ∏ j, zBZ j ^ (v.toAdd j).val := rfl

theorem zMap_single
    (j : Fin 7) : zMap (Multiplicative.ofAdd (Pi.single j 1)) = zBZ j := by
  rw [zMap_apply, Finset.prod_eq_single j]
  · simp [val_one_two]
  · intro i _ hij
    simp [hij]
  · simp

theorem zMap_surjective :
    Function.Surjective zMap := by
  intro g
  have hg : (g : ModGL Tag.E6 K) ∈ Subgroup.closure {g | ∃ j < 7, g = zB j} :=
    radicalZ_eq_closure ▸ g.2
  suffices h : ∀ x (hx : x ∈ Subgroup.closure {g | ∃ j < 7, g = zB j}),
      ∃ (h : x ∈ radicalZ), (⟨x, h⟩ : radicalZ) ∈ zMap.range by
    obtain ⟨_, v, hv⟩ := h g.1 hg
    exact ⟨v, hv⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨zB_mem_radicalZ hj, ⟨_, zMap_single ⟨j, hj⟩⟩⟩
  | one => exact ⟨one_mem _, one_mem _⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨hx', hxr⟩ := ihx
    obtain ⟨hy', hyr⟩ := ihy
    exact ⟨mul_mem hx' hy', mul_mem hxr hyr⟩
  | inv x _ ihx =>
    obtain ⟨hx', hxr⟩ := ihx
    exact ⟨inv_mem hx', inv_mem hxr⟩

theorem zMap_bijective :
    Function.Bijective zMap := by
  refine zMap_surjective.bijective_of_nat_card_le ?_
  have : Nat.card (Multiplicative (Fin 7 → ZMod 2)) = 2 ^ 7 := by
    rw [show Nat.card (Multiplicative (Fin 7 → ZMod 2)) = Nat.card (Fin 7 → ZMod 2) from rfl,
      Nat.card_fun]
    simp
  rw [card_radicalZ, this]

@[expose] def zEquiv :
    Multiplicative (Fin 7 → ZMod 2) ≃* radicalZ :=
  MulEquiv.ofBijective zMap zMap_bijective

theorem zEquiv_apply
    (v : Multiplicative (Fin 7 → ZMod 2)) : zEquiv v = zMap v := rfl

@[expose] def signU (e : ZMod 2) : ℂˣ := (-1) ^ e.val

theorem signU_add (a b : ZMod 2) : signU (a + b) = signU a * signU b :=
  pow_val_add (by simp) a b

theorem signU_zero : signU 0 = 1 := rfl

theorem signU_one : signU 1 = -1 := by rw [signU, val_one_two, pow_one]

@[expose] def signChar (a : Fin 7 → ZMod 2) : Multiplicative (Fin 7 → ZMod 2) →* ℂˣ where
  toFun v := signU (∑ j, a j * v.toAdd j)
  map_one' := by simp [signU]
  map_mul' v w := by
    rw [← signU_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [toAdd_mul, Pi.add_apply, mul_add]

@[expose] def charOfMask
    (a : Fin 7 → ZMod 2) : radicalZ →* ℂˣ :=
  (signChar a).comp zEquiv.symm.toMonoidHom

theorem zEquiv_symm_zBZ
    (j : Fin 7) :
    zEquiv.symm (zBZ j) = Multiplicative.ofAdd (Pi.single j 1) := by
  rw [MulEquiv.symm_apply_eq, zEquiv_apply, zMap_single]

theorem charOfMask_zBZ
    (a : Fin 7 → ZMod 2) (j : Fin 7) : charOfMask a (zBZ j) = signU (a j) := by
  simp only [charOfMask, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, zEquiv_symm_zBZ]
  simp only [signChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

theorem char_ext
    {χ ψ : radicalZ →* ℂˣ} (h : ∀ j, χ (zBZ j) = ψ (zBZ j)) : χ = ψ := by
  refine MonoidHom.ext fun g => ?_
  obtain ⟨v, rfl⟩ := zMap_surjective g
  simp only [zMap_apply, map_prod, map_pow, h]

theorem char_zBZ
    (χ : radicalZ →* ℂˣ) (j : Fin 7) : χ (zBZ j) = 1 ∨ χ (zBZ j) = -1 := by
  have h : χ (zBZ j) * χ (zBZ j) = 1 := by rw [← map_mul, zBZ_mul_self, map_one]
  have h' : ((χ (zBZ j) : ℂˣ) : ℂ) * (χ (zBZ j) : ℂ) = 1 := by
    rw [← Units.val_mul, h, Units.val_one]
  rcases mul_self_eq_one_iff.1 h' with e | e
  · exact Or.inl (Units.ext e)
  · exact Or.inr (Units.ext (by rw [e, Units.val_neg, Units.val_one]))

@[expose] def maskOfChar
    (χ : radicalZ →* ℂˣ) : Fin 7 → ZMod 2 :=
  fun j => if χ (zBZ j) = 1 then 0 else 1

theorem neg_one_ne_one_units : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have := congrArg Units.val h
  norm_num at this

theorem charOfMask_maskOfChar
    (χ : radicalZ →* ℂˣ) : charOfMask (maskOfChar χ) = χ := by
  refine char_ext fun j => ?_
  rw [charOfMask_zBZ, maskOfChar]
  rcases char_zBZ χ j with h | h
  · rw [ite_eq_left h, h, signU_zero]
  · rw [ite_eq_right (by rw [h]; exact neg_one_ne_one_units), h, signU_one]

theorem maskOfChar_charOfMask
    (a : Fin 7 → ZMod 2) : maskOfChar (charOfMask a) = a := by
  funext j
  rw [maskOfChar, charOfMask_zBZ]
  rcases zmod_two_cases (a j) with h | h <;> rw [h]
  · rw [signU_zero, ite_eq_left rfl]
  · rw [signU_one, ite_eq_right neg_one_ne_one_units]

@[expose] def charEquiv :
    (radicalZ →* ℂˣ) ≃ (Fin 7 → ZMod 2) where
  toFun := maskOfChar
  invFun := charOfMask
  left_inv := charOfMask_maskOfChar
  right_inv := maskOfChar_charOfMask

theorem charOfMask_injective :
    Function.Injective charOfMask := charEquiv.symm.injective

theorem char_tZ_eq_neg_one_iff
    (χ : radicalZ →* ℂˣ) : χ tZ = -1 ↔ maskOfChar χ 0 = 1 := by
  rw [← zBZ_zero, maskOfChar]
  rcases char_zBZ χ 0 with h | h
  · rw [h, ite_eq_left rfl]
    exact ⟨fun e => absurd e.symm neg_one_ne_one_units, fun e => absurd e (by decide)⟩
  · rw [h, ite_eq_right neg_one_ne_one_units]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem charOfMask_tZ
    (a : Fin 7 → ZMod 2) : charOfMask a tZ = -1 ↔ a 0 = 1 := by
  rw [char_tZ_eq_neg_one_iff, maskOfChar_charOfMask]

theorem card_negChars :
    Nat.card {χ : radicalZ →* ℂˣ // χ tZ = -1} = 64 := by
  have e : {χ : radicalZ →* ℂˣ // χ tZ = -1} ≃ {a : Fin 7 → ZMod 2 // a 0 = 1} :=
    charEquiv.subtypeEquiv fun χ => char_tZ_eq_neg_one_iff χ
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

abbrev NZ :
    Type := Subgroup.normalizer (radicalZ : Set (ModGL Tag.E6 K))

theorem conj_mem_radicalZ
    (g : NZ) (z : radicalZ) :
    (g : ModGL Tag.E6 K)⁻¹ * z * g ∈ radicalZ := by
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem g.2) z).1 z.2
  rwa [inv_inv] at this

@[expose] def charConj
    (g : NZ) (χ : radicalZ →* ℂˣ) : radicalZ →* ℂˣ :=
  χ.comp (radicalZ.normalizerMonoidHom g).symm.toMonoidHom

theorem charConj_apply
    (g : NZ) (χ : radicalZ →* ℂˣ) (z : radicalZ) :
    charConj g χ z = χ ⟨(g : ModGL Tag.E6 K)⁻¹ * z * g, conj_mem_radicalZ g z⟩ := by
  simp only [charConj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  congr 1

theorem charConj_mul
    (g h : NZ) (χ : radicalZ →* ℂˣ) :
    charConj (g * h) χ = charConj g (charConj h χ) := by
  refine MonoidHom.ext fun z => ?_
  rw [charConj_apply, charConj_apply, charConj_apply]
  congr 1

theorem charConj_one
    (χ : radicalZ →* ℂˣ) : charConj 1 χ = χ := by
  refine MonoidHom.ext fun z => ?_
  rw [charConj_apply]
  congr 1

@[expose] def leviOrbit
    (χ : radicalZ →* ℂˣ) : Set (radicalZ →* ℂˣ) :=
  {ψ | ∃ g : NZ, (g : ModGL Tag.E6 K) ∈ leviL0 ∧ ψ = charConj g χ}

@[expose] def leviN
    (k : Fin 6) : NZ :=
  ⟨leviGen k, leviL0_le_normalizer_radicalZ (Subgroup.subset_closure ⟨k, rfl⟩)⟩

@[expose] def colBit (k : Fin 6) (i j : Fin 7) : ZMod 2 :=
  if (centerCols k i).testBit j then 1 else 0

@[expose] def actMask (k : Fin 6) (a : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 :=
  fun i => ∑ j, a j * colBit k i j

theorem coe_zMap
    (v : Multiplicative (Fin 7 → ZMod 2)) :
    ((zMap v : radicalZ) : ModGL Tag.E6 K) =
      (List.ofFn fun j : Fin 7 => zB j ^ (v.toAdd j).val).prod := by
  rw [zMap_apply, ← Fin.prod_ofFn, Subgroup.val_list_prod, List.map_ofFn]
  rfl

theorem ofFn_eq_range_map {M : Type*} (g : ℕ → M) :
    ∀ n : ℕ, List.ofFn (fun j : Fin n => g j) = (List.range n).map g
  | 0 => rfl
  | n + 1 => by
    rw [List.ofFn_succ', List.range_succ, List.map_append, ← ofFn_eq_range_map g n]
    simp

theorem zMap_colBit
    (k : Fin 6) (i : Fin 7) :
    ((zMap (Multiplicative.ofAdd (colBit k i)) : radicalZ) : ModGL Tag.E6 K) =
      zProdM (centerCols k i) := by
  have h : ∀ j : Fin 7, zB j ^ ((Multiplicative.ofAdd (colBit k i)).toAdd j).val =
      if (centerCols k i).testBit j then zB j else 1 := by
    intro j
    rw [toAdd_ofAdd, colBit]
    split_ifs
    · rw [val_one_two, pow_one]
    · rw [val_zero_two, pow_zero]
  rw [coe_zMap, zProdM]
  simp only [h]
  rw [ofFn_eq_range_map (fun j => if (centerCols k i).testBit j then zB j else 1) 7]

theorem charConj_leviN
    (k : Fin 6) (a : Fin 7 → ZMod 2) :
    charConj (leviN k) (charOfMask a) = charOfMask (actMask k a) := by
  refine char_ext fun i => ?_
  rw [charConj_apply, charOfMask_zBZ]
  have e : (⟨((leviN k : NZ) : ModGL Tag.E6 K)⁻¹ * (zBZ i : ModGL Tag.E6 K) * (leviN k : NZ),
      conj_mem_radicalZ _ _⟩ : radicalZ) = zMap (Multiplicative.ofAdd (colBit k i)) := by
    refine Subtype.ext ?_
    rw [zMap_colBit, ← leviGen_conj_zB]
    change (leviGen k)⁻¹ * zB i * leviGen k = leviGen k * zB i * (leviGen k)⁻¹
    rw [leviGen_inv]
  rw [e, charOfMask, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← zEquiv_apply,
    MulEquiv.symm_apply_apply]
  simp only [signChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, actMask]

@[expose] def maskVec (m : ℕ) : Fin 7 → ZMod 2 := fun j => if m.testBit j then 1 else 0

@[expose] def vecMask (a : Fin 7 → ZMod 2) : ℕ := ∑ j : Fin 7, 2 ^ (j : ℕ) * (a j).val

theorem vecMask_spec : ∀ a : Fin 7 → ZMod 2,
    maskVec (vecMask a) = a ∧ vecMask a < 128 ∧ (a 0 = 1 → vecMask a % 2 = 1) := by
  decide +kernel

theorem vecMask_maskVec : (List.range 128).all (fun m => vecMask (maskVec m) == m) = true := by
  decide +kernel

theorem maskVec_injOn {m m' : ℕ} (hm : m < 128) (hm' : m' < 128) (h : maskVec m = maskVec m') :
    m = m' := by
  have e := vecMask_maskVec
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
  rw [← e m hm, ← e m' hm', h]

theorem maskVec_zero_of_odd : (List.range 128).all (fun m => m % 2 == 0 || maskVec m 0 == 1) =
    true := by decide +kernel

@[expose] def centerColsL : List (List ℕ) :=
  [[1, 2, 4, 25, 16, 32, 64], [1, 2, 4, 8, 25, 32, 64], [1, 2, 12, 8, 48, 32, 64],
    [1, 2, 4, 12, 16, 48, 64], [1, 6, 4, 8, 16, 96, 64], [1, 2, 6, 8, 16, 32, 96]]

@[expose] def parityN (m : ℕ) : ℕ := ((List.range 7).filter fun j => m.testBit j).length % 2

@[expose] def actN (k m : ℕ) : ℕ :=
  ((List.range 7).map fun i => 2 ^ i * parityN (m &&& (centerColsL.getD k []).getD i 0)).sum

theorem actN_check : (List.range 6).all (fun k => (List.range 128).all fun m =>
    if hk : k < 6 then decide (maskVec (actN k m) = actMask ⟨k, hk⟩ (maskVec m)) &&
      decide (actN k m < 128) else false) = true := by decide +kernel

theorem actN_spec (k : Fin 6) {m : ℕ} (hm : m < 128) :
    maskVec (actN k m) = actMask k (maskVec m) ∧ actN k m < 128 := by
  have h := actN_check
  simp only [List.all_eq_true, List.mem_range] at h
  have := h k k.2 m hm
  simp only [k.2, dite_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

@[expose] def levW
    (w : List ℕ) : NZ :=
  (w.map fun k => if h : k < 6 then leviN ⟨k, h⟩ else 1).reverse.prod

theorem levW_mem
    (w : List ℕ) : ((levW w : NZ) : ModGL Tag.E6 K) ∈ leviL0 := by
  rw [levW]
  induction w with
  | nil => exact one_mem _
  | cons k w ih =>
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
      Subgroup.coe_mul]
    refine mul_mem ih ?_
    split_ifs with h
    · exact Subgroup.subset_closure ⟨⟨k, h⟩, rfl⟩
    · exact one_mem _

theorem charConj_levW :
    ∀ (w : List ℕ), (∀ k ∈ w, k < 6) → ∀ m < 128,
    charConj (levW w) (charOfMask (maskVec m)) =
      charOfMask (maskVec (w.foldl (fun x k => actN k x) m)) ∧
      w.foldl (fun x k => actN k x) m < 128
  | [], _, m, hm => by simp [levW, charConj_one, hm]
  | k :: w, hw, m, hm => by
    have hk := hw k (List.mem_cons_self ..)
    have hw' : ∀ j ∈ w, j < 6 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    obtain ⟨h1, h2⟩ := actN_spec ⟨k, hk⟩ hm
    obtain ⟨h3, h4⟩ := charConj_levW w hw' (actN k m) h2
    have e : levW (k :: w) = levW w * leviN ⟨k, hk⟩ := by
      rw [levW, List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
        dite_eq_left hk]
      rfl
    rw [e, charConj_mul, charConj_leviN, ← h1, List.foldl_cons]
    exact ⟨h3, h4⟩

@[expose] def orb36 : List (ℕ × List ℕ) :=
  [(1, []), (3, [0, 2, 0, 4, 5]), (5, [0, 2, 0]), (7, [0, 2, 0, 4]), (9, [0]), (11, [0, 2, 4, 2]),
    (13, [0, 2]), (15, [0, 2, 4]), (17, [1]), (19, [0, 2, 0, 1, 4, 5]), (21, [0, 2, 0, 1]),
    (23, [0, 2, 0, 1, 4]), (33, [1, 3, 1]), (35, [0, 2, 0, 1, 3, 4, 2, 0]), (41, [1, 3, 1, 0]),
    (43, [0, 2, 0, 1, 3, 4, 2]), (49, [1, 3]), (51, [0, 2, 0, 1, 4, 5, 3]),
    (61, [0, 2, 0, 1, 3]), (63, [0, 2, 0, 1, 3, 4]), (65, [1, 3, 1, 5, 4]),
    (69, [0, 2, 0, 1, 3, 5, 3, 1]), (73, [1, 3, 1, 0, 5, 4]), (77, [1, 3, 1, 0, 5, 4, 2]),
    (81, [1, 3, 5, 3]), (85, [0, 2, 0, 1, 3, 5, 3]), (91, [0, 2, 0, 1, 3, 4, 5, 3]),
    (95, [0, 2, 0, 1, 3, 5, 4]), (97, [1, 3, 1, 5]), (103, [0, 2, 0, 1, 3, 4, 2, 0, 5]),
    (105, [1, 3, 1, 0, 5]), (111, [0, 2, 0, 1, 3, 4, 2, 5]), (113, [1, 3, 5]),
    (119, [0, 2, 0, 1, 3, 5, 3, 4]), (123, [0, 2, 0, 1, 3, 4, 5]), (125, [0, 2, 0, 1, 3, 5])]

@[expose] def orb28 : List (ℕ × List ℕ) :=
  [(25, []), (27, [2, 4, 2]), (29, [2]), (31, [2, 4]), (37, [2, 3, 1]), (39, [2, 3, 1, 4]),
    (45, [3, 2]), (47, [3, 2, 4]), (53, [2, 3]), (55, [2, 3, 4]), (57, [3]), (59, [2, 4, 2, 3]),
    (67, [2, 3, 1, 4, 5, 4]), (71, [2, 3, 1, 5, 4]), (75, [3, 2, 4, 5, 4]), (79, [3, 2, 5, 4]),
    (83, [2, 3, 4, 5, 3]), (87, [2, 3, 5, 4]), (89, [3, 5, 3]), (93, [2, 3, 5, 3]),
    (99, [2, 3, 1, 4, 5]), (101, [2, 3, 1, 5]), (107, [3, 2, 4, 5]), (109, [3, 2, 5]),
    (115, [2, 3, 4, 5]), (117, [2, 3, 5]), (121, [3, 5]), (127, [2, 3, 5, 3, 4])]

@[expose] def orbCheck (L : List (ℕ × List ℕ)) (seed : ℕ) : Bool :=
  L.all (fun p => decide (p.1 < 128) && p.2.all (fun k => decide (k < 6)) &&
    p.2.foldl (fun x k => actN k x) seed == p.1) &&
  L.all (fun p => (List.range 6).all fun k => (L.map Prod.fst).contains (actN k p.1))

theorem orbCheck36 : orbCheck orb36 1 = true := by decide +kernel

theorem orbCheck28 : orbCheck orb28 25 = true := by decide +kernel

theorem orbCover : (List.range 128).all (fun m => m % 2 == 0 ||
    (orb36.map Prod.fst).contains m || (orb28.map Prod.fst).contains m) = true := by decide +kernel

theorem orbFacts : (orb36.map Prod.fst).Nodup ∧ (orb28.map Prod.fst).Nodup ∧
    (orb36.map Prod.fst).length = 36 ∧ (orb28.map Prod.fst).length = 28 ∧
    (orb36.map Prod.fst).all (fun m => m % 2 == 1 && !(orb28.map Prod.fst).contains m) ∧
    (orb28.map Prod.fst).all (fun m => m % 2 == 1) := by decide +kernel

@[expose] def charSet
    (L : List (ℕ × List ℕ)) : Set (radicalZ →* ℂˣ) :=
  {χ | ∃ m ∈ L.map Prod.fst, χ = charOfMask (maskVec m)}

theorem leviOrbit_eq
    {L : List (ℕ × List ℕ)} {seed : ℕ} (hc : orbCheck L seed = true)
    (hs : seed ∈ L.map Prod.fst) : leviOrbit (charOfMask (maskVec seed)) = charSet L := by
  simp only [orbCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range, List.contains_iff_mem] at hc
  obtain ⟨hw, hcl⟩ := hc
  have hlt : ∀ m ∈ L.map Prod.fst, m < 128 := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    exact (hw p hp).1.1
  ext ψ
  constructor
  · rintro ⟨g, hg, rfl⟩
    suffices key : ∀ x (hx : x ∈ Subgroup.closure (Set.range leviGen)),
        ∀ (hn : x ∈ Subgroup.normalizer (radicalZ : Set (ModGL Tag.E6 K))),
        ∀ χ ∈ charSet L, charConj ⟨x, hn⟩ χ ∈ charSet L from
      key g.1 hg g.2 _ ⟨seed, hs, rfl⟩
    intro x hx
    induction hx using Subgroup.closure_induction'' with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rintro hn _ ⟨m, hm, rfl⟩
      have e : (⟨leviGen k, hn⟩ : NZ) = leviN k := rfl
      rw [e, charConj_leviN, ← (actN_spec k (hlt m hm)).1]
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      exact ⟨_, hcl p hp k k.2, rfl⟩
    | inv_mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rintro hn _ ⟨m, hm, rfl⟩
      have e : (⟨(leviGen k)⁻¹, hn⟩ : NZ) = leviN k := Subtype.ext (leviGen_inv k)
      rw [e, charConj_leviN, ← (actN_spec k (hlt m hm)).1]
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      exact ⟨_, hcl p hp k k.2, rfl⟩
    | one =>
      intro hn χ hχ
      have e : (⟨1, hn⟩ : NZ) = 1 := rfl
      rwa [e, charConj_one]
    | mul x y hx hy ihx ihy =>
      intro hn χ hχ
      have hx' := leviL0_le_normalizer_radicalZ hx
      have hy' := leviL0_le_normalizer_radicalZ hy
      have e : (⟨x * y, hn⟩ : NZ) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
      rw [e, charConj_mul]
      exact ihx hx' _ (ihy hy' χ hχ)
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    obtain ⟨⟨-, hk⟩, hp'⟩ := hw p hp
    have hk' : ∀ k ∈ p.2, k < 6 := by simpa using hk
    have := charConj_levW p.2 hk' seed (hlt seed hs)
    rw [hp'] at this
    exact ⟨levW p.2, levW_mem p.2, this.1.symm⟩

theorem ncard_charSet
    {L : List (ℕ × List ℕ)} (hnd : (L.map Prod.fst).Nodup)
    (hlt : ∀ m ∈ L.map Prod.fst, m < 128) : (charSet L).ncard = (L.map Prod.fst).length := by
  have e : charSet L = (fun m => charOfMask (maskVec m)) '' {m | m ∈ L.map Prod.fst} := by
    ext χ
    simp only [charSet, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  have hinj : Set.InjOn (fun m => charOfMask (maskVec m)) {m | m ∈ L.map Prod.fst} :=
    fun m hm m' hm' h => maskVec_injOn (hlt m hm) (hlt m' hm') (charOfMask_injective h)
  rw [e, hinj.ncard_image,
    show {m | m ∈ L.map Prod.fst} = ((L.map Prod.fst).toFinset : Set ℕ) by ext; simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem orb_lt {L : List (ℕ × List ℕ)} {seed : ℕ} (hc : orbCheck L seed = true) :
    ∀ m ∈ L.map Prod.fst, m < 128 := by
  simp only [orbCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  intro m hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
  exact (hc.1 p hp).1.1

theorem leviOrbit_28 :
    leviOrbit (charOfMask (maskVec 25)) = charSet orb28 :=
  leviOrbit_eq orbCheck28 (by decide)

theorem leviOrbit_36 :
    leviOrbit (charOfMask (maskVec 1)) = charSet orb36 :=
  leviOrbit_eq orbCheck36 (by decide)

theorem charSet_tZ
    {L : List (ℕ × List ℕ)} (hodd : (L.map Prod.fst).all (fun m => m % 2 == 1))
    (hlt : ∀ m ∈ L.map Prod.fst, m < 128) {χ : radicalZ →* ℂˣ} (hχ : χ ∈ charSet L) :
    χ tZ = -1 := by
  obtain ⟨m, hm, rfl⟩ := hχ
  rw [charOfMask_tZ]
  have h := maskVec_zero_of_odd
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h hodd
  rcases h m (hlt m hm) with h' | h'
  · rw [hodd m hm] at h'
    exact absurd h' (by norm_num)
  · exact h'

theorem levi_char_orbits :
    ∃ χ₁ χ₂ : radicalZ →* ℂˣ, χ₁ tZ = -1 ∧ χ₂ tZ = -1 ∧
      (leviOrbit χ₁).ncard = 28 ∧ (leviOrbit χ₂).ncard = 36 ∧
      Disjoint (leviOrbit χ₁) (leviOrbit χ₂) ∧
      ∀ χ : radicalZ →* ℂˣ, χ tZ = -1 ↔ χ ∈ leviOrbit χ₁ ∨ χ ∈ leviOrbit χ₂ := by
  obtain ⟨hnd36, hnd28, hl36, hl28, h36, h28⟩ := orbFacts
  have hlt36 := orb_lt orbCheck36
  have hlt28 := orb_lt orbCheck28
  have hodd36 : (orb36.map Prod.fst).all (fun m => m % 2 == 1) := by
    simp only [List.all_eq_true, Bool.and_eq_true] at h36 ⊢
    exact fun m hm => (h36 m hm).1
  refine ⟨charOfMask (maskVec 25), charOfMask (maskVec 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [charOfMask_tZ]
    decide
  · rw [charOfMask_tZ]
    decide
  · rw [leviOrbit_28, ncard_charSet hnd28 hlt28, hl28]
  · rw [leviOrbit_36, ncard_charSet hnd36 hlt36, hl36]
  · rw [leviOrbit_28, leviOrbit_36, Set.disjoint_left]
    rintro χ ⟨m, hm, rfl⟩ ⟨m', hm', he⟩
    have := maskVec_injOn (hlt28 m hm) (hlt36 m' hm') (charOfMask_injective he)
    subst this
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h36
    have h' := (h36 m hm').2
    exact absurd (List.contains_iff_mem.2 hm) (by rw [h']; decide)
  · intro χ
    rw [leviOrbit_28, leviOrbit_36]
    constructor
    · intro hχ
      obtain ⟨hv, hlt, hodd⟩ := vecMask_spec (maskOfChar χ)
      have h0 : maskOfChar χ 0 = 1 := (char_tZ_eq_neg_one_iff χ).1 hχ
      have hc := orbCover
      simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
        List.contains_iff_mem] at hc
      have hχ' : χ = charOfMask (maskVec (vecMask (maskOfChar χ))) := by
        rw [hv, charOfMask_maskOfChar]
      rcases hc _ hlt with (h | h) | h
      · rw [hodd h0] at h
        exact absurd h (by norm_num)
      · exact Or.inr ⟨_, h, hχ'⟩
      · exact Or.inl ⟨_, h, hχ'⟩
    · rintro (h | h)
      exacts [charSet_tZ h28 hlt28 h, charSet_tZ hodd36 hlt36 h]

end CFSG.Monster.B.E6.StdF4Radical
