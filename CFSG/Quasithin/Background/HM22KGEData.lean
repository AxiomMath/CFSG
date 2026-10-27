module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.H12OneHatM22PfModelBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.MatNCert Matrix
open scoped commutatorElement

theorem not_isSolvable_of_perfect {M : Type*} [Group M] {S P : Subgroup M} (hPS : P ≤ S)
    (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥) : ¬ Group.IsSolvable ↥S := by
  intro hS
  have hsolv : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPS)
  have htop : commutator ↥P = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hP]
  have hds : ∀ n, derivedSeries ↥P n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨n, hn⟩ := (Group.isSolvable_def (G := ↥P)).mp hsolv
  rw [hds n] at hn
  apply hP1
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : ↥P) ∈ (⊤ : Subgroup ↥P) := Subgroup.mem_top _
  rw [hn, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem commutator_closure_eq {M : Type*} [Group M] {a b : M}
    (ha : a ∈ ⁅Subgroup.closure {a, b}, Subgroup.closure {a, b}⁆)
    (hb : b ∈ ⁅Subgroup.closure {a, b}, Subgroup.closure {a, b}⁆) :
    ⁅Subgroup.closure {a, b}, Subgroup.closure {a, b}⁆ = Subgroup.closure {a, b} := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
      (Subgroup.inv_mem _ h₂)
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ha
  · exact hb

@[expose] def pw2 {M : Type*} [Monoid M] (a b : M) (w : List ℕ) : M :=
  (w.map fun i => if i = 0 then a else if i = 1 then b else 1).prod

theorem pw2_mem {M : Type*} [Group M] (a b : M) (w : List ℕ) :
    pw2 a b w ∈ Subgroup.closure {a, b} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih =>
    simp only [pw2, List.map_cons, List.prod_cons] at ih ⊢
    refine Subgroup.mul_mem _ ?_ ih
    split_ifs
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.one_mem _

theorem pw2_val {a b : GL (Fin 12) (ZMod 2)} {ac bc : List ℕ}
    (ha : (a : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 ac)
    (hb : (b : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 bc) (hac : ValidN 12 ac)
    (hbc : ValidN 12 bc) (w : List ℕ) :
    ((pw2 a b w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      decN 12 (evalW 12 [ac, bc] w) := by
  have hv : ∀ g ∈ [ac, bc], ValidN 12 g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hac
    · exact hbc
  induction w with
  | nil =>
    simp only [pw2, List.map_nil, List.prod_nil, Units.val_one]
    exact decN_oneN.symm
  | cons i w ih =>
    simp only [pw2, List.map_cons, List.prod_cons, Units.val_mul] at ih ⊢
    rw [ih, evalW_cons, decN_mulN (validN_getD hv i).1 (length_evalW _ w)]
    congr 1
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · simp [ha]
      · simp [hb]
    · rw [List.getD_eq_default _ _ (by simp; omega), decN_oneN]
      simp [show i ≠ 0 by omega, show i ≠ 1 by omega]

theorem mem_commutator_of_mul {M : Type*} [Group M] {P : Subgroup M} {s u v : M} (hu : u ∈ P)
    (hv : v ∈ P) (h : u * v = v * u * s) : s ∈ ⁅P, P⁆ := by
  have hs : s = ⁅u⁻¹, v⁻¹⁆ := by
    rw [commutatorElement_def, inv_inv, inv_inv]
    calc s = (v * u)⁻¹ * (v * u * s) := by group
      _ = (v * u)⁻¹ * (u * v) := by rw [h]
      _ = u⁻¹ * v⁻¹ * u * v := by group
  rw [hs]
  exact Subgroup.commutator_mem_commutator (P.inv_mem hu) (P.inv_mem hv)

@[expose] def y0W : List ℕ := [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]

@[expose] def y0pW : List ℕ :=
  [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0]

@[expose] def y0C : List ℕ := [887, 409, 3168, 1200, 1458, 2771, 3722, 1999, 16, 32, 2087, 3129]

@[expose] def y0pC : List ℕ :=
  [3975, 1481, 1486, 2631, 2743, 4057, 1419, 2765, 2261, 3178, 1944, 2540]

theorem yw_facts : H12Cert.tW y0W = y0C ∧ H12Cert.tW y0pW = y0pC ∧
    mulN (H12Cert.gG.getD 0 H12Cert.one12) (mulN y0C (H12Cert.gG.getD 0 H12Cert.one12)) =
      mulN y0C y0C ∧
    mulN y0C (mulN y0C y0C) = H12Cert.one12 ∧
    mulN y0pC y0C = mulN (mulN y0C (mulN H12Cert.z12 H12Cert.z12)) y0pC ∧
    mulN (H12Cert.gG.getD 0 H12Cert.one12) (H12Cert.gG.getD 0 H12Cert.one12) = H12Cert.one12 ∧
    H12Cert.gG.getD 0 H12Cert.one12 ≠ H12Cert.one12 := by
  decide +kernel

abbrev k0 : GL (Fin 12) (ZMod 2) := H12Cert.gU 0

abbrev y0 : GL (Fin 12) (ZMod 2) := H12Cert.tU y0W

abbrev y0' : GL (Fin 12) (ZMod 2) := H12Cert.tU y0pW

theorem validN_y0C : ValidN 12 y0C := yw_facts.1 ▸ validN_evalW _ H12Cert.validN_gG _

theorem validN_y0pC : ValidN 12 y0pC := yw_facts.2.1 ▸ validN_evalW _ H12Cert.validN_gG _

theorem y0_val :
    ((y0 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 y0C := by
  rw [H12Cert.tU_val, yw_facts.1]

theorem y0'_val :
    ((y0' : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 y0pC := by
  rw [H12Cert.tU_val, yw_facts.2.1]

theorem k0_val : ((k0 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
    decN 12 (H12Cert.gG.getD 0 H12Cert.one12) := H12Cert.gU_val 0

theorem k0_mul_self : k0 * k0 = 1 := by
  apply Units.ext
  rw [Units.val_mul, k0_val, ← decN_mulN (H12Cert.length_gG 0) (H12Cert.length_gG 0),
    yw_facts.2.2.2.2.2.1, Units.val_one, decN_oneN]

theorem k0_ne_one : k0 ≠ 1 := by
  intro h
  apply yw_facts.2.2.2.2.2.2
  have h1 := congrArg (fun u : GL (Fin 12) (ZMod 2) =>
    colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) h
  simp only [k0_val, Units.val_one, colsN_one] at h1
  rwa [colsN_decN (validN_getD H12Cert.validN_gG 0)] at h1

theorem orderOf_k0 : orderOf k0 = 2 :=
  orderOf_eq_prime (by rw [pow_two, k0_mul_self]) k0_ne_one

theorem k0_mem : k0 ∈ H12Cert.G := H12Cert.gU_mem 0

theorem y0_mem : y0 ∈ H12Cert.G := H12Cert.tU_mem _

theorem y0'_mem : y0' ∈ H12Cert.G := H12Cert.tU_mem _

theorem y0_pow_three : y0 ^ 3 = 1 := by
  apply Units.ext
  rw [pow_three, Units.val_mul, Units.val_mul, y0_val,
    ← decN_mulN validN_y0C.1 validN_y0C.1,
    ← decN_mulN validN_y0C.1 (by rw [length_mulN]; exact validN_y0C.1),
    yw_facts.2.2.2.1, Units.val_one, decN_oneN]

theorem k0_conj_y0 : k0 * y0 * k0⁻¹ = y0⁻¹ := by
  have h1 : k0 * y0 * k0 = y0 * y0 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, k0_val, y0_val, Matrix.mul_assoc,
      ← decN_mulN validN_y0C.1 (H12Cert.length_gG 0),
      ← decN_mulN (H12Cert.length_gG 0) (by rw [length_mulN]; exact H12Cert.length_gG 0),
      ← decN_mulN validN_y0C.1 validN_y0C.1, yw_facts.2.2.1]
  have hk : k0⁻¹ = k0 := inv_eq_of_mul_eq_one_right k0_mul_self
  have hy : y0 * y0 = y0⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three', y0_pow_three]
  rw [hk, h1, hy]

theorem y0'_conj_y0 : y0' * y0 * y0'⁻¹ = y0 * H12Cert.zU⁻¹ := by
  have h1 : y0' * y0 = y0 * (H12Cert.zU * H12Cert.zU) * y0' := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, y0'_val, y0_val,
      H12Cert.zU_val, ← decN_mulN validN_y0pC.1 validN_y0C.1,
      ← decN_mulN H12Cert.z12_facts.1 H12Cert.z12_facts.1,
      ← decN_mulN validN_y0C.1 (by rw [length_mulN]; exact H12Cert.z12_facts.1),
      ← decN_mulN (by rw [length_mulN, length_mulN]; exact H12Cert.z12_facts.1) validN_y0pC.1,
      yw_facts.2.2.2.2.1]
  have hz : H12Cert.zU * H12Cert.zU = H12Cert.zU⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three', H12Cert.zU_pow_three]
  rw [h1, hz, mul_inv_cancel_right]

@[expose] def commL : List ℕ :=
  [0, 5, 10, 15, 272, 277, 282, 287, 544, 549, 554, 559, 816, 821, 826, 831]

theorem commL_spec : (List.range 4096).all
    (fun v => commL.contains (mvN (H12Cert.gG.getD 0 H12Cert.one12) v ^^^ v)) = true := by
  decide +kernel

theorem mem_commL (v : Fin 12 → ZMod 2) :
    ∃ c ∈ commL, ((k0 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v + v =
      vecN 12 c := by
  have hc := codeN_lt v
  have h := List.all_eq_true.mp commL_spec (codeN v) (List.mem_range.mpr hc)
  rw [List.contains_iff_mem] at h
  refine ⟨_, h, ?_⟩
  rw [vecN_xor, ← decN_mulVec (H12Cert.length_gG 0), vecN_codeN, ← k0_val]

@[expose] def fixSub (v : Fin 12 → ZMod 2) : Subgroup (GL (Fin 12) (ZMod 2)) where
  carrier := {g | ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v = v}
  mul_mem' {g h} (hg : _ = v) (hh : _ = v) := by
    show ((g * h : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v = v
    rw [Units.val_mul, ← mulVec_mulVec, hh, hg]
  one_mem' := by
    show ((1 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v = v
    rw [Units.val_one, one_mulVec]
  inv_mem' {g} (hg : _ = v) := by
    show ((g⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v = v
    conv_lhs => rw [← hg]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mem_fixSub {v : Fin 12 → ZMod 2} {g : GL (Fin 12) (ZMod 2)} :
    g ∈ fixSub v ↔ ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v = v :=
  Iff.rfl

theorem fixSub_mulVec (c : GL (Fin 12) (ZMod 2)) (v : Fin 12 → ZMod 2) :
    fixSub (((c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v) =
      (fixSub v).map (MulAut.conj c).toMonoidHom := by
  ext g
  simp only [mem_fixSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hg
    refine ⟨c⁻¹ * g * c, ?_, by group⟩
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hg,
      mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  · rintro ⟨h, hh, rfl⟩
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec _
      ((c⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)), ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mulVec, mem_fixSub.mp hh]

@[expose] def repData : List (ℕ × ℕ × List ℕ) :=
  [(5, 5, []), (10, 5, [1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]),
    (15, 5, [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1]),
    (272, 5, [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]),
    (277, 19, [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1]),
    (282, 19, [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]),
    (287, 5, [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]),
    (544, 5, [1, 1, 1, 0, 1, 0, 1, 1, 1]),
    (549, 5, [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1]),
    (554, 19, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0]),
    (559, 19, [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]),
    (816, 5, [1, 0, 1, 0, 1, 1, 0, 1, 0, 1]), (821, 19, [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
    (826, 5, [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
    (831, 19, [1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1])]

theorem repData_spec : (commL.all fun x => x == 0 || repData.any fun d => d.1 == x) = true ∧
    repData.all (fun d => (d.2.1 == 5 || d.2.1 == 19) && mvN (H12Cert.tW d.2.2) d.2.1 == d.1) =
      true := by
  decide +kernel

structure PerfWit where
  r : ℕ
  sw : List ℕ
  sw2 : List ℕ
  sC : List ℕ
  s2C : List ℕ
  c1 : List ℕ × List ℕ
  c2 : List ℕ × List ℕ

@[expose] def PerfWit.ok (d : PerfWit) : Bool :=
  H12Cert.tW d.sw == d.sC && H12Cert.tW d.sw2 == d.s2C && mvN d.sC d.r == d.r &&
    mvN d.s2C d.r == d.r && d.sC != H12Cert.one12 &&
    mulN (evalW 12 [d.sC, d.s2C] d.c1.1) (evalW 12 [d.sC, d.s2C] d.c1.2) ==
      mulN (mulN (evalW 12 [d.sC, d.s2C] d.c1.2) (evalW 12 [d.sC, d.s2C] d.c1.1)) d.sC &&
    mulN (evalW 12 [d.sC, d.s2C] d.c2.1) (evalW 12 [d.sC, d.s2C] d.c2.2) ==
      mulN (mulN (evalW 12 [d.sC, d.s2C] d.c2.2) (evalW 12 [d.sC, d.s2C] d.c2.1)) d.s2C

@[expose] def wit5 : PerfWit where
  r := 5
  sw := [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0,
    0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1]
  sw2 := [1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0]
  sC := [707, 833, 710, 843, 3960, 1436, 2361, 3614, 3281, 1122, 1867, 2445]
  s2C := [3276, 1092, 3273, 1102, 111, 181, 3805, 1894, 3842, 1283, 534, 811]
  c1 := ([0], [1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1])
  c2 := ([0, 0, 1, 0, 1, 0], [1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1])

@[expose] def wit19 : PerfWit where
  r := 19
  sw := [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]
  sw2 := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0,
    0, 1, 1, 1, 0]
  sC := [3823, 1909, 3157, 1194, 2441, 3790, 2227, 3281, 1691, 3053, 3252, 1240]
  s2C := [1531, 2653, 3934, 1447, 4021, 1498, 1349, 2698, 1274, 2143, 2906, 3503]
  c1 := ([0, 0], [1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1])
  c2 := ([0, 0, 1, 0], [1, 0, 1, 0, 0])

theorem wit5_ok : wit5.ok = true := by decide +kernel

theorem wit19_ok : wit19.ok = true := by decide +kernel

theorem not_isSolvable_of_ok {d : PerfWit} (hd : d.ok = true) :
    ¬ Group.IsSolvable ↥(H12Cert.G ⊓ fixSub (vecN 12 d.r)) := by
  simp only [PerfWit.ok, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hd
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hd
  set s := H12Cert.tU d.sw
  set s2 := H12Cert.tU d.sw2
  have hs : ((s : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 d.sC := by
    rw [H12Cert.tU_val, h1]
  have hs2 : ((s2 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 d.s2C := by
    rw [H12Cert.tU_val, h2]
  have hvs : ValidN 12 d.sC := h1 ▸ validN_evalW _ H12Cert.validN_gG _
  have hvs2 : ValidN 12 d.s2C := h2 ▸ validN_evalW _ H12Cert.validN_gG _
  have hv : ∀ g ∈ [d.sC, d.s2C], ValidN 12 g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hvs
    · exact hvs2
  set P := Subgroup.closure ({s, s2} : Set (GL (Fin 12) (ZMod 2)))
  have hPS : P ≤ H12Cert.G ⊓ fixSub (vecN 12 d.r) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_inf.mpr ⟨H12Cert.tU_mem _, mem_fixSub.mpr (by
        rw [hs, decN_mulVec hvs.1, h3])⟩
    · exact Subgroup.mem_inf.mpr ⟨H12Cert.tU_mem _, mem_fixSub.mpr (by
        rw [hs2, decN_mulVec hvs2.1, h4])⟩
  have hmem : ∀ {t : GL (Fin 12) (ZMod 2)} {tc : List ℕ}
      (_ : (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 tc) (_ : ValidN 12 tc)
      (c : List ℕ × List ℕ),
      mulN (evalW 12 [d.sC, d.s2C] c.1) (evalW 12 [d.sC, d.s2C] c.2) =
        mulN (mulN (evalW 12 [d.sC, d.s2C] c.2) (evalW 12 [d.sC, d.s2C] c.1)) tc → t ∈ ⁅P, P⁆ := by
    intro t tc ht htc c hc
    refine mem_commutator_of_mul (pw2_mem s s2 c.1) (pw2_mem s s2 c.2) (Units.ext ?_)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, pw2_val hs hs2 hvs hvs2,
      pw2_val hs hs2 hvs hvs2, ht, ← decN_mulN (length_evalW _ _) (length_evalW _ _),
      ← decN_mulN (length_evalW _ _) (length_evalW _ _),
      ← decN_mulN (by rw [length_mulN]; exact length_evalW _ _) htc.1, hc]
  have hPP : ⁅P, P⁆ = P := commutator_closure_eq (hmem hs hvs d.c1 h6) (hmem hs2 hvs2 d.c2 h7)
  have hP1 : P ≠ ⊥ := by
    intro h
    apply h5
    have hsP : s ∈ P := Subgroup.subset_closure (by simp)
    rw [h, Subgroup.mem_bot] at hsP
    have := congrArg (fun u : GL (Fin 12) (ZMod 2) =>
      colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) hsP
    simp only [hs, Units.val_one, colsN_one] at this
    rwa [colsN_decN hvs] at this
  exact not_isSolvable_of_perfect hPS hPP hP1

theorem isSolvable_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [Group.IsSolvable B] : Group.IsSolvable A :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem not_isSolvable_fix {x : ℕ} (hx : x ∈ commL) (hx0 : x ≠ 0) :
    ¬ Group.IsSolvable ↥(H12Cert.G ⊓ fixSub (vecN 12 x)) := by
  obtain ⟨hcov, hdat⟩ := repData_spec
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true]
    at hcov hdat
  rcases hcov x hx with h | ⟨d, hd, hdx⟩
  · exact absurd h hx0
  obtain ⟨hr, hmv⟩ := hdat d hd
  set t := H12Cert.tU d.2.2
  have hmv' : ((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ vecN 12 d.2.1 =
      vecN 12 x := by
    rw [H12Cert.tU_val, decN_mulVec (length_evalW _ _), hmv, hdx]
  have hrep : ¬ Group.IsSolvable ↥(H12Cert.G ⊓ fixSub (vecN 12 d.2.1)) := by
    rcases hr with h | h
    · rw [h]
      exact not_isSolvable_of_ok (d := wit5) wit5_ok
    · rw [h]
      exact not_isSolvable_of_ok (d := wit19) wit19_ok
  have hconj : H12Cert.G ⊓ fixSub (vecN 12 x) =
      (H12Cert.G ⊓ fixSub (vecN 12 d.2.1)).map (MulAut.conj t).toMonoidHom := by
    rw [← hmv', fixSub_mulVec, Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective]
    congr 1
    ext g
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hg
      exact ⟨t⁻¹ * g * t, H12Cert.G.mul_mem (H12Cert.G.mul_mem (H12Cert.G.inv_mem
        (H12Cert.tU_mem _)) hg) (H12Cert.tU_mem _), by group⟩
    · rintro ⟨h, hh, rfl⟩
      exact H12Cert.G.mul_mem (H12Cert.G.mul_mem (H12Cert.tU_mem _) hh)
        (H12Cert.G.inv_mem (H12Cert.tU_mem _))
  intro hsolv
  apply hrep
  rw [hconj] at hsolv
  exact isSolvable_of_mulEquiv' ((H12Cert.G ⊓ fixSub (vecN 12 d.2.1)).equivMapOfInjective
    (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)

end CFSG.Quasithin.H.Mathieu.M22Link
