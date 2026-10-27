module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.A6.S7C

open Equiv

@[expose] def enc (l : List ℕ) : ℕ := l.foldr (fun a r => a + 8 * r) 0

@[expose] def cd (σ : Perm (Fin 7)) : ℕ := enc (List.ofFn fun i => (σ i).val)

@[expose] def dg (x i : ℕ) : ℕ := x / 8 ^ i % 8

@[expose] def cm (x y : ℕ) : ℕ := enc (List.ofFn fun i : Fin 7 => dg x (dg y i))

@[expose] def pos (x j : ℕ) : ℕ :=
  (if dg x 1 = j then 1 else 0) + (if dg x 2 = j then 2 else 0) + (if dg x 3 = j then 3 else 0) +
    (if dg x 4 = j then 4 else 0) + (if dg x 5 = j then 5 else 0) + (if dg x 6 = j then 6 else 0)

@[expose] def cinv (x : ℕ) : ℕ := enc (List.ofFn fun j : Fin 7 => pos x j)

@[expose] def idc : ℕ := 1754760

@[expose] def valid (n : ℕ) : Bool :=
  (List.ofFn fun i : Fin 7 => dg n i).all (· < 7) &&
    decide (List.ofFn fun i : Fin 7 => dg n i).Nodup && enc (List.ofFn fun i : Fin 7 => dg n i) == n

theorem cd_eq (σ : Perm (Fin 7)) : cd σ = (σ 0).val + 8 * ((σ 1).val + 8 * ((σ 2).val +
    8 * ((σ 3).val + 8 * ((σ 4).val + 8 * ((σ 5).val + 8 * ((σ 6).val + 8 * 0)))))) := by
  simp [cd, enc, List.ofFn_succ]

theorem dg_cd (σ : Perm (Fin 7)) (i : Fin 7) : dg (cd σ) i = (σ i).val := by
  have h0 := (σ 0).isLt; have h1 := (σ 1).isLt; have h2 := (σ 2).isLt; have h3 := (σ 3).isLt
  have h4 := (σ 4).isLt; have h5 := (σ 5).isLt; have h6 := (σ 6).isLt
  rw [cd_eq]
  fin_cases i <;> simp only [dg] <;> norm_num <;> omega

theorem cd_mul (σ τ : Perm (Fin 7)) : cd (σ * τ) = cm (cd σ) (cd τ) := by
  rw [show cd (σ * τ) = enc (List.ofFn fun i => ((σ * τ) i).val) from rfl, cm]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  rw [dg_cd, dg_cd, Perm.mul_apply]

theorem cd_one : cd 1 = idc := by
  rw [cd_eq]
  rfl

theorem cd_injective : Function.Injective cd := by
  intro σ τ h
  ext i
  rw [← dg_cd, ← dg_cd, h]

theorem mem_permutations' (σ : Perm (Fin 7)) :
    (List.ofFn fun i => (σ i).val) ∈ (List.range 7).permutations' := by
  rw [List.mem_permutations']
  have h := Equiv.Perm.ofFn_comp_perm σ (fun i : Fin 7 => i.val)
  have e : (List.ofFn fun i : Fin 7 => i.val) = List.range 7 := by
    rw [List.ofFn_eq_map, List.map_coe_finRange_eq_range]
  rw [e] at h
  exact h

theorem forall_cd {P : ℕ → Bool}
    (h : ((List.range 7).permutations'.all fun l => P (enc l)) = true) (σ : Perm (Fin 7)) :
    P (cd σ) = true :=
  List.all_eq_true.mp h _ (mem_permutations' σ)

theorem valid_lt {n : ℕ} (h : valid n = true) (i : Fin 7) : dg n i < 7 := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem valid_inj {n : ℕ} (h : valid n = true) : Function.Injective fun i : Fin 7 => dg n i := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact List.nodup_ofFn.mp h.1.2

theorem valid_enc {n : ℕ} (h : valid n = true) : enc (List.ofFn fun i : Fin 7 => dg n i) = n := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.2

@[expose] def dmap (n : ℕ) (i : Fin 7) : Fin 7 := ⟨dg n i % 7, Nat.mod_lt _ (by norm_num)⟩

theorem dmap_bij {n : ℕ} (h : valid n = true) : Function.Bijective (dmap n) := by
  refine Finite.injective_iff_bijective.mp fun i j hij => ?_
  have e := congrArg Fin.val hij
  simp only [dmap, Nat.mod_eq_of_lt (valid_lt h i), Nat.mod_eq_of_lt (valid_lt h j)] at e
  exact valid_inj h e

noncomputable def dec (n : ℕ) : Perm (Fin 7) :=
  if h : valid n = true then Equiv.ofBijective (dmap n) (dmap_bij h) else 1

theorem dec_apply {n : ℕ} (h : valid n = true) (i : Fin 7) : ((dec n) i).val = dg n i := by
  simp only [dec, h, ↓reduceDIte, Equiv.ofBijective_apply, dmap]
  exact Nat.mod_eq_of_lt (valid_lt h i)

theorem cd_dec {n : ℕ} (h : valid n = true) : cd (dec n) = n := by
  conv_rhs => rw [← valid_enc h]
  simp only [cd]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  exact dec_apply h i

theorem dec_cd (σ : Perm (Fin 7)) (h : valid (cd σ) = true) : dec (cd σ) = σ :=
  cd_injective (cd_dec h)

theorem valid_cd (σ : Perm (Fin 7)) : valid (cd σ) = true := by
  have e : (List.ofFn fun i : Fin 7 => dg (cd σ) i) = List.ofFn fun i => (σ i).val :=
    List.ofFn_inj.mpr (funext fun i => dg_cd σ i)
  simp only [valid, e, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨fun a ha => ?_, ?_⟩, rfl⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (σ i).isLt
  · exact List.nodup_ofFn.mpr fun i j h => σ.injective (Fin.ext h)

theorem pos_cd (σ : Perm (Fin 7)) (j : Fin 7) : pos (cd σ) j = (σ⁻¹ j).val := by
  have e : pos (cd σ) j = ∑ i : Fin 7, if dg (cd σ) i = j then (i : ℕ) else 0 := by
    rw [Fin.sum_univ_seven]
    simp only [pos, Fin.val_zero, ite_self, zero_add]
    rfl
  rw [e]
  simp only [dg_cd]
  have e : ∀ i : Fin 7, ((σ i).val = j.val) ↔ i = σ⁻¹ j := fun i => by
    rw [Fin.val_inj, Perm.eq_inv_iff_eq]
  simp only [e]
  rw [Finset.sum_ite_eq' Finset.univ (σ⁻¹ j) (fun i : Fin 7 => (i : ℕ))]
  simp

theorem cd_inv (σ : Perm (Fin 7)) : cd σ⁻¹ = cinv (cd σ) := by
  rw [show cd σ⁻¹ = enc (List.ofFn fun j => (σ⁻¹ j).val) from rfl, cinv]
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  rw [pos_cd]


@[expose] def relSub (R : ℕ → ℕ → Bool) : Subgroup (Perm (Fin 7)) where
  carrier := {σ | ∀ x y : Fin 7, R (σ x) (σ y) = R x y}
  mul_mem' {σ τ} hσ hτ x y := by
    simp only [Set.mem_ofPred_eq] at hσ hτ
    rw [Perm.mul_apply, Perm.mul_apply, hσ, hτ]
  one_mem' x y := rfl
  inv_mem' {σ} hσ x y := by
    simp only [Set.mem_ofPred_eq] at hσ
    rw [← hσ (σ⁻¹ x) (σ⁻¹ y)]
    simp

theorem mem_relSub {R : ℕ → ℕ → Bool} {σ : Perm (Fin 7)} :
    σ ∈ relSub R ↔ ∀ x y : Fin 7, R (σ x) (σ y) = R x y := Iff.rfl

@[expose] def relB (R : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  (List.range 7).all fun i => (List.range 7).all fun j => R (dg n i) (dg n j) == R i j

theorem mem_relSub_iff {R : ℕ → ℕ → Bool} {σ : Perm (Fin 7)} :
    σ ∈ relSub R ↔ relB R (cd σ) = true := by
  simp only [mem_relSub, relB, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h i hi j hj
    have e1 := dg_cd σ ⟨i, hi⟩
    have e2 := dg_cd σ ⟨j, hj⟩
    simp only at e1 e2
    rw [e1, e2]
    exact h ⟨i, hi⟩ ⟨j, hj⟩
  · intro h x y
    have := h x x.isLt y y.isLt
    rwa [dg_cd, dg_cd] at this

@[expose] def rS4 (x _ : ℕ) : Bool := decide (x < 4)
@[expose] def rBl (x y : ℕ) : Bool := x / 2 == y / 2
@[expose] def r6 (x _ : ℕ) : Bool := x == 6
@[expose] def rBl3 (x y : ℕ) : Bool := min (x / 2) 2 == min (y / 2) 2
@[expose] def rB0 (x _ : ℕ) : Bool := x / 2 == 0
@[expose] def rB1 (x _ : ℕ) : Bool := x / 2 == 1
@[expose] def r4 (x _ : ℕ) : Bool := x == 4
@[expose] def r5 (x _ : ℕ) : Bool := x == 5
@[expose] def rM2 (x y : ℕ) : Bool :=
  x == y || (decide (x < 4) && decide (y < 4) && x % 2 == y % 2)

@[expose] def S43 : Subgroup (Perm (Fin 7)) := relSub rS4
@[expose] def PA : Subgroup (Perm (Fin 7)) := relSub rBl
@[expose] def T0 : Subgroup (Perm (Fin 7)) := relSub rBl ⊓ relSub rS4
@[expose] def D7 : Subgroup (Perm (Fin 7)) := relSub rS4 ⊓ relSub r6
@[expose] def C7 : Subgroup (Perm (Fin 7)) := relSub rS4 ⊓ relSub rBl3
@[expose] def E8 : Subgroup (Perm (Fin 7)) :=
  relSub rBl ⊓ relSub rB0 ⊓ relSub rB1 ⊓ relSub r6
@[expose] def V4 : Subgroup (Perm (Fin 7)) :=
  relSub rBl ⊓ relSub rM2 ⊓ relSub r4 ⊓ relSub r5 ⊓ relSub r6

@[expose] def T0f (g : Fin 7 → ℕ) : Bool :=
  g 6 == 6 && g 4 / 2 == 2 && g 5 / 2 == 2 && g 0 / 2 == g 1 / 2
@[expose] def PAf (g : Fin 7 → ℕ) : Bool := g 6 == 6 && g 0 / 2 == g 1 / 2 && g 2 / 2 == g 3 / 2
@[expose] def S4f (g : Fin 7 → ℕ) : Bool := g 0 < 4 && g 1 < 4 && g 2 < 4 && g 3 < 4
@[expose] def Df (g : Fin 7 → ℕ) : Bool := S4f g && g 6 == 6
@[expose] def Cf (g : Fin 7 → ℕ) : Bool := S4f g && g 0 / 2 == g 1 / 2
@[expose] def E8f (g : Fin 7 → ℕ) : Bool :=
  g 0 / 2 == 0 && g 1 / 2 == 0 && g 2 / 2 == 1 && g 3 / 2 == 1 && g 6 == 6
@[expose] def V4f (g : Fin 7 → ℕ) : Bool :=
  g 4 == 4 && g 5 == 5 && g 6 == 6 && (g 0 ^^^ g 1) == 1 && (g 0 ^^^ g 2) == 2

@[expose] def inT0 (x : ℕ) : Bool := T0f fun i => dg x i
@[expose] def inPA (x : ℕ) : Bool := PAf fun i => dg x i
@[expose] def inS4 (x : ℕ) : Bool := S4f fun i => dg x i
@[expose] def inD (x : ℕ) : Bool := Df fun i => dg x i
@[expose] def inC (x : ℕ) : Bool := Cf fun i => dg x i
@[expose] def inE8 (x : ℕ) : Bool := E8f fun i => dg x i
@[expose] def inV4 (x : ℕ) : Bool := V4f fun i => dg x i

@[expose] def bridge (x : ℕ) : Bool :=
  (inS4 x == relB rS4 x) && (inPA x == relB rBl x) &&
  (inT0 x == (relB rBl x && relB rS4 x)) && (inD x == (relB rS4 x && relB r6 x)) &&
  (inC x == (relB rS4 x && relB rBl3 x)) &&
  (inE8 x == (relB rBl x && relB rB0 x && relB rB1 x && relB r6 x)) &&
  (inV4 x == (relB rBl x && relB rM2 x && relB r4 x && relB r5 x && relB r6 x))

theorem bridge_all (σ : Perm (Fin 7)) : bridge (cd σ) = true :=
  forall_cd (P := bridge) (by decide +kernel) σ

theorem mem_S43_iff {σ : Perm (Fin 7)} : σ ∈ S43 ↔ inS4 (cd σ) = true := by
  have h := bridge_all σ
  simp only [bridge, Bool.and_eq_true, beq_iff_eq] at h
  rw [S43, mem_relSub_iff, h.1.1.1.1.1.1]

theorem mem_PA_iff {σ : Perm (Fin 7)} : σ ∈ PA ↔ inPA (cd σ) = true := by
  have h := bridge_all σ
  simp only [bridge, Bool.and_eq_true, beq_iff_eq] at h
  rw [PA, mem_relSub_iff, h.1.1.1.1.1.2]

theorem mem_T0_iff {σ : Perm (Fin 7)} : σ ∈ T0 ↔ inT0 (cd σ) = true := by
  have h := bridge_all σ
  simp only [bridge, Bool.and_eq_true, beq_iff_eq] at h
  rw [T0, Subgroup.mem_inf, mem_relSub_iff, mem_relSub_iff, h.1.1.1.1.2, Bool.and_eq_true]

theorem mem_D7_iff {σ : Perm (Fin 7)} : σ ∈ D7 ↔ inD (cd σ) = true := by
  have h := bridge_all σ
  simp only [bridge, Bool.and_eq_true, beq_iff_eq] at h
  rw [D7, Subgroup.mem_inf, mem_relSub_iff, mem_relSub_iff, h.1.1.1.2, Bool.and_eq_true]

theorem mem_C7_iff {σ : Perm (Fin 7)} : σ ∈ C7 ↔ inC (cd σ) = true := by
  have h := bridge_all σ
  simp only [bridge, Bool.and_eq_true, beq_iff_eq] at h
  rw [C7, Subgroup.mem_inf, mem_relSub_iff, mem_relSub_iff, h.1.1.2, Bool.and_eq_true]

theorem mem_E8_iff {σ : Perm (Fin 7)} : σ ∈ E8 ↔ inE8 (cd σ) = true := by
  have h := bridge_all σ
  simp only [bridge, Bool.and_eq_true, beq_iff_eq] at h
  rw [E8, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf, mem_relSub_iff, mem_relSub_iff,
    mem_relSub_iff, mem_relSub_iff, h.1.2]
  simp only [Bool.and_eq_true, and_assoc]

theorem mem_V4_iff {σ : Perm (Fin 7)} : σ ∈ V4 ↔ inV4 (cd σ) = true := by
  have h := bridge_all σ
  simp only [bridge, Bool.and_eq_true, beq_iff_eq] at h
  rw [V4, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf, mem_relSub_iff,
    mem_relSub_iff, mem_relSub_iff, mem_relSub_iff, mem_relSub_iff, h.2]
  simp only [Bool.and_eq_true, and_assoc]

@[expose] def T0L : List ℕ :=
  [1724499, 1724506, 1724947, 1724954, 1725633, 1725640, 1726081, 1726088, 1753171, 1753178,
    1753619, 1753626, 1754305, 1754312, 1754753, 1754760]

@[expose] def PAL : List ℕ :=
  [1578213, 1578220, 1578661, 1578668, 1579347, 1579354, 1579795, 1579802, 1606885, 1606892,
    1607333, 1607340, 1608019, 1608026, 1608467, 1608474, 1650789, 1650796, 1651237, 1651244,
    1653057, 1653064, 1653505, 1653512, 1679461, 1679468, 1679909, 1679916, 1681729, 1681736,
    1682177, 1682184, 1724499, 1724506, 1724947, 1724954, 1725633, 1725640, 1726081, 1726088,
    1753171, 1753178, 1753619, 1753626, 1754305, 1754312, 1754753, 1754760]

@[expose] def S43L : List ℕ :=
  [1237075, 1237082, 1237131, 1237145, 1237194, 1237201, 1237523, 1237530, 1237635, 1237656,
    1237698, 1237712, 1238027, 1238041, 1238083, 1238104, 1238209, 1238216, 1238538, 1238545,
    1238594, 1238608, 1238657, 1238664, 1265747, 1265754, 1265803, 1265817, 1265866, 1265873,
    1266195, 1266202, 1266307, 1266328, 1266370, 1266384, 1266699, 1266713, 1266755, 1266776,
    1266881, 1266888, 1267210, 1267217, 1267266, 1267280, 1267329, 1267336, 1466451, 1466458,
    1466507, 1466521, 1466570, 1466577, 1466899, 1466906, 1467011, 1467032, 1467074, 1467088,
    1467403, 1467417, 1467459, 1467480, 1467585, 1467592, 1467914, 1467921, 1467970, 1467984,
    1468033, 1468040, 1523795, 1523802, 1523851, 1523865, 1523914, 1523921, 1524243, 1524250,
    1524355, 1524376, 1524418, 1524432, 1524747, 1524761, 1524803, 1524824, 1524929, 1524936,
    1525258, 1525265, 1525314, 1525328, 1525377, 1525384, 1724499, 1724506, 1724555, 1724569,
    1724618, 1724625, 1724947, 1724954, 1725059, 1725080, 1725122, 1725136, 1725451, 1725465,
    1725507, 1725528, 1725633, 1725640, 1725962, 1725969, 1726018, 1726032, 1726081, 1726088,
    1753171, 1753178, 1753227, 1753241, 1753290, 1753297, 1753619, 1753626, 1753731, 1753752,
    1753794, 1753808, 1754123, 1754137, 1754179, 1754200, 1754305, 1754312, 1754634, 1754641,
    1754690, 1754704, 1754753, 1754760]

@[expose] def DL : List ℕ :=
  [1724499, 1724506, 1724555, 1724569, 1724618, 1724625, 1724947, 1724954, 1725059, 1725080,
    1725122, 1725136, 1725451, 1725465, 1725507, 1725528, 1725633, 1725640, 1725962, 1725969,
    1726018, 1726032, 1726081, 1726088, 1753171, 1753178, 1753227, 1753241, 1753290, 1753297,
    1753619, 1753626, 1753731, 1753752, 1753794, 1753808, 1754123, 1754137, 1754179, 1754200,
    1754305, 1754312, 1754634, 1754641, 1754690, 1754704, 1754753, 1754760]

@[expose] def CL : List ℕ :=
  [1237075, 1237082, 1237523, 1237530, 1238209, 1238216, 1238657, 1238664, 1265747, 1265754,
    1266195, 1266202, 1266881, 1266888, 1267329, 1267336, 1466451, 1466458, 1466899, 1466906,
    1467585, 1467592, 1468033, 1468040, 1523795, 1523802, 1524243, 1524250, 1524929, 1524936,
    1525377, 1525384, 1724499, 1724506, 1724947, 1724954, 1725633, 1725640, 1726081, 1726088,
    1753171, 1753178, 1753619, 1753626, 1754305, 1754312, 1754753, 1754760]

@[expose] def E8L : List ℕ :=
  [1725633, 1725640, 1726081, 1726088, 1754305, 1754312, 1754753, 1754760]

@[expose] def V4L : List ℕ :=
  [1753171, 1753626, 1754305, 1754760]

@[expose] def listsOK (x : ℕ) : Bool :=
  (!inT0 x || T0L.contains x) && (!inPA x || PAL.contains x) && (!inS4 x || S43L.contains x) &&
    (!inD x || DL.contains x) && (!inC x || CL.contains x) && (!inE8 x || E8L.contains x) &&
    (!inV4 x || V4L.contains x)

theorem listsOK_all (σ : Perm (Fin 7)) : listsOK (cd σ) = true :=
  forall_cd (P := listsOK) (by decide +kernel) σ

theorem card_eq_of_codes {X : Subgroup (Perm (Fin 7))} {l : List ℕ} (hl : l.Nodup)
    (h1 : ∀ σ ∈ X, cd σ ∈ l) (h2 : ∀ n ∈ l, valid n = true ∧ dec n ∈ X) :
    Nat.card X = l.length := by
  have e : X ≃ {n // n ∈ l} :=
    { toFun := fun σ => ⟨cd σ, h1 σ σ.2⟩
      invFun := fun n => ⟨dec n, (h2 n n.2).2⟩
      left_inv := fun σ => Subtype.ext (dec_cd σ (valid_cd σ))
      right_inv := fun n => Subtype.ext (cd_dec (h2 n n.2).1) }
  rw [Nat.card_congr e, ← List.toFinset_card_of_nodup hl, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun n => List.mem_toFinset.symm)

theorem card_T0 : Nat.card T0 = 16 := by
  refine card_eq_of_codes (l := T0L) (by decide +kernel) (fun σ hσ => ?_) (fun n hn => ?_)
  · have h := listsOK_all σ
    simp only [listsOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.contains_iff_mem] at h
    exact h.1.1.1.1.1.1.resolve_left (by rw [mem_T0_iff.mp hσ]; simp)
  · have hv : (T0L.all fun n => valid n && inT0 n) = true := by decide +kernel
    have h := List.all_eq_true.mp hv n hn
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, mem_T0_iff.mpr (by rw [cd_dec h.1]; exact h.2)⟩

theorem card_S43 : Nat.card S43 = 144 := by
  refine card_eq_of_codes (l := S43L) (by decide +kernel) (fun σ hσ => ?_) (fun n hn => ?_)
  · have h := listsOK_all σ
    simp only [listsOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.contains_iff_mem] at h
    exact h.1.1.1.1.2.resolve_left (by rw [mem_S43_iff.mp hσ]; simp)
  · have hv : (S43L.all fun n => valid n && inS4 n) = true := by decide +kernel
    have h := List.all_eq_true.mp hv n hn
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, mem_S43_iff.mpr (by rw [cd_dec h.1]; exact h.2)⟩

theorem isPGroup_T0 : IsPGroup 2 T0 :=
  IsPGroup.of_card (n := 4) (by rw [card_T0]; norm_num)

end CFSG.Quasithin.H13.A6.S7C
