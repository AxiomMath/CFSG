module

public import CFSG.Quasithin.Background.Harris.R1.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Background.Harris.R1.GramAbel

open CFSG.Quasithin.SzR1

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

section LinAlg

variable {ι : Type} [Fintype ι]

@[expose] def gramForm (ι : Type) [Fintype ι] : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => (∑ i, x i) * (∑ i, y i) + ∑ i, x i * y i)
    (by
      intro x x' y
      simp only [Pi.add_apply, Finset.sum_add_distrib, add_mul]
      try ring)
    (by
      intro c x y
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
      try ring)
    (by
      intro x y y'
      simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
      ring)
    (by
      intro c x y
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum]
      try ring)

theorem gramForm_apply (x y : ι → ZMod 2) :
    gramForm ι x y = (∑ i, x i) * (∑ i, y i) + ∑ i, x i * y i := rfl

theorem eq_zero_of_gramForm_eq_zero [DecidableEq ι] (hc : Even (Fintype.card ι))
    {x : ι → ZMod 2} (hx : ∀ y, gramForm ι x y = 0) : x = 0 := by
  have h1 : ∀ j, x j = ∑ i, x i := by
    intro j
    have h := hx (Pi.single j 1)
    simp [gramForm_apply, Pi.single_apply] at h
    exact (CharTwo.add_eq_zero.mp h).symm
  have h2 : ∑ i, x i = 0 := by
    have h3 : ∑ i, x i = ∑ _i : ι, ∑ i, x i := Finset.sum_congr rfl (fun j _ => h1 j)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      (ZMod.natCast_eq_zero_iff_even).mpr hc, zero_mul] at h3
    exact h3
  funext j
  rw [h1 j, h2]
  rfl

theorem two_mul_finrank_le [DecidableEq ι] (hc : Even (Fintype.card ι))
    (U : Submodule (ZMod 2) (ι → ZMod 2)) (hU : ∀ u ∈ U, ∀ v ∈ U, gramForm ι u v = 0) :
    2 * Module.finrank (ZMod 2) U ≤ Fintype.card ι := by
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := gramForm ι) U
  have hker : LinearMap.ker (gramForm ι) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact eq_zero_of_gramForm_eq_zero hc (fun y => by simpa using LinearMap.congr_fun hx y)
  rw [hker, inf_bot_eq, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card] at h
  have hle : U ≤ (gramForm ι).orthogonal U := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact hU n hn u hu
  have := Submodule.finrank_mono hle
  omega

end LinAlg

section Group

variable {P : Type} [Group P]

@[expose] def zz (z : P) (a : ZMod 2) : P := if a = 0 then 1 else z

theorem zz_zero (z : P) : zz z 0 = 1 := by simp [zz]

theorem zz_one (z : P) : zz z 1 = z := by simp [zz]

theorem zz_add {z : P} (hz : z * z = 1) (a b : ZMod 2) : zz z (a + b) = zz z a * zz z b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · simp [zz_zero]
  · simp [zz_zero, zz_one]
  · simp [zz_zero, zz_one]
  · have : (1 : ZMod 2) + 1 = 0 := by decide
    rw [this, zz_zero, zz_one, hz]

theorem zz_mul_self {z : P} (hz : z * z = 1) (a : ZMod 2) : zz z a * zz z a = 1 := by
  rw [← zz_add hz, CharTwo.add_self_eq_zero, zz_zero]

theorem zz_eq_one_iff {z : P} (hz : z ≠ 1) (a : ZMod 2) : zz z a = 1 ↔ a = 0 := by
  rcases zmod_two_cases a with rfl | rfl
  · simp [zz_zero]
  · rw [zz_one]
    exact ⟨fun h => absurd h hz, fun h => absurd h zmod_one_ne_zero⟩

theorem zz_inj {z : P} (hz2 : z * z = 1) (hz : z ≠ 1) {a b : ZMod 2} (h : zz z a = zz z b) :
    a = b := by
  have h1 : zz z (a + b) = 1 := by rw [zz_add hz2, h, zz_mul_self hz2]
  have h2 := (zz_eq_one_iff hz _).mp h1
  exact (CharTwo.add_eq_zero.mp h2)

theorem zz_comm {z : P} (hc : ∀ g, g * z = z * g) (g : P) (a : ZMod 2) :
    g * zz z a = zz z a * g := by
  rcases zmod_two_cases a with rfl | rfl
  · simp [zz_zero]
  · rw [zz_one]
    exact hc g

theorem zz_pow {z : P} (hz : z * z = 1) (k : ℕ) : z ^ k = zz z (k : ZMod 2) := by
  induction k with
  | zero => simp [zz_zero]
  | succ k ih => rw [pow_succ, ih, Nat.cast_succ, zz_add hz, zz_one]

theorem mul_zz_mul {z : P} (hc : ∀ g, g * z = z * g) (g : P) (a : ZMod 2) (y : P) :
    g * (zz z a * y) = zz z a * (g * y) := by
  have h := zz_comm hc g a
  calc g * (zz z a * y) = (g * zz z a) * y := (mul_assoc _ _ _).symm
    _ = (zz z a * g) * y := by rw [h]
    _ = zz z a * (g * y) := mul_assoc _ _ _

theorem zz_mul_zz_mul {z : P} (hz : z * z = 1) (a b : ZMod 2) (y : P) :
    zz z a * (zz z b * y) = zz z (a + b) * y := by
  rw [zz_add hz, mul_assoc]

theorem eq_zz_mul_swap {z : P} (hz : z * z = 1) {u v : P} {a : ZMod 2} (h : u = zz z a * v) :
    v = zz z a * u := by
  rw [h, ← mul_assoc, zz_mul_self hz, one_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {z : P} {w : ι → P}

@[expose] def supp (x : ι → ZMod 2) : Finset ι := Finset.univ.filter fun i => x i = 1

omit [DecidableEq ι] in
@[simp] theorem mem_supp {x : ι → ZMod 2} {i : ι} : i ∈ supp x ↔ x i = 1 := by
  simp [supp]

@[expose] noncomputable def psi (w : ι → P) (x : ι → ZMod 2) : P := gprod w (supp x).toList

omit [DecidableEq ι] in
theorem supp_zero : supp (0 : ι → ZMod 2) = ∅ := by
  ext i
  simp

omit [DecidableEq ι] in
theorem psi_zero (w : ι → P) : psi w 0 = 1 := by
  simp [psi, supp_zero]

theorem supp_add_single {x : ι → ZMod 2} {j : ι} (hj : x j = 0) :
    supp (x + Pi.single j 1) = insert j (supp x) := by
  ext i
  by_cases hi : i = j
  · subst hi
    simp [hj]
  · simp [hi]

omit [Fintype ι] [DecidableEq ι] in
theorem add_self_pi (x : ι → ZMod 2) : x + x = 0 := by
  ext i
  simp [CharTwo.add_self_eq_zero]

omit [Fintype ι] in
theorem exists_gprod_insert (h : GramRel z w) {s : Finset ι} {j : ι} (hj : j ∉ s) :
    ∃ a : ZMod 2, gprod w (insert j s).toList = zz z a * (w j * gprod w s.toList) := by
  obtain ⟨k, hk⟩ := h.gprod_perm (Finset.toList_insert hj)
  exact ⟨k, by rw [hk, gprod_cons, zz_pow h.z_sq]⟩

theorem w_mul_psi_of_eq_zero (h : GramRel z w) {x : ι → ZMod 2} {j : ι} (hj : x j = 0) :
    ∃ a : ZMod 2, w j * psi w x = zz z a * psi w (x + Pi.single j 1) := by
  have hnot : j ∉ supp x := by simp [hj]
  obtain ⟨a, ha⟩ := exists_gprod_insert h hnot
  refine ⟨a, eq_zz_mul_swap h.z_sq ?_⟩
  simp only [psi, supp_add_single hj]
  exact ha

theorem w_mul_psi (h : GramRel z w) (x : ι → ZMod 2) (j : ι) :
    ∃ a : ZMod 2, w j * psi w x = zz z a * psi w (x + Pi.single j 1) := by
  rcases zmod_two_cases (x j) with hj | hj
  · exact w_mul_psi_of_eq_zero h hj
  · obtain ⟨x', hx'⟩ : ∃ x', x' = x + Pi.single j (1 : ZMod 2) := ⟨_, rfl⟩
    have hj' : x' j = 0 := by
      rw [hx']
      simp [hj]
      decide
    have hback : x' + Pi.single j 1 = x := by
      rw [hx', add_assoc, add_self_pi, add_zero]
    obtain ⟨a, ha⟩ := w_mul_psi_of_eq_zero h hj'
    rw [hback] at ha
    have hpsi : psi w x = zz z a * (w j * psi w x') := eq_zz_mul_swap h.z_sq ha
    refine ⟨a, ?_⟩
    rw [← hx', hpsi, mul_zz_mul h.z_comm, ← mul_assoc (w j), h.w_sq, one_mul]

theorem psi_mul_w (h : GramRel z w) (x : ι → ZMod 2) (j : ι) :
    ∃ a : ZMod 2, psi w x * w j = zz z a * psi w (x + Pi.single j 1) := by
  obtain ⟨k, hk⟩ := h.gprod_perm (List.perm_append_singleton j (supp x).toList)
  obtain ⟨a, ha⟩ := w_mul_psi h x j
  have ha' : w j * gprod w (supp x).toList = zz z a * psi w (x + Pi.single j 1) := ha
  refine ⟨(k : ZMod 2) + a, ?_⟩
  have h1 : psi w x * w j = gprod w ((supp x).toList ++ [j]) := by
    simp [psi, gprod_append]
  rw [h1, hk, gprod_cons, ha', zz_pow h.z_sq, zz_mul_zz_mul h.z_sq]

theorem psi_mul_gprod (h : GramRel z w) (l : List ι) :
    ∀ x : ι → ZMod 2, ∃ a : ZMod 2, psi w x * gprod w l =
      zz z a * psi w (x + (l.map fun i => Pi.single i (1 : ZMod 2)).sum) := by
  induction l with
  | nil => intro x; exact ⟨0, by simp [zz_zero]⟩
  | cons i l ih =>
    intro x
    obtain ⟨a, ha⟩ := psi_mul_w h x i
    obtain ⟨b, hb⟩ := ih (x + Pi.single i 1)
    refine ⟨a + b, ?_⟩
    calc psi w x * gprod w (i :: l) = (psi w x * w i) * gprod w l := by
          rw [gprod_cons, mul_assoc]
      _ = zz z a * (psi w (x + Pi.single i 1) * gprod w l) := by rw [ha, mul_assoc]
      _ = zz z a * (zz z b * psi w (x + Pi.single i 1 +
            (l.map fun i => Pi.single i (1 : ZMod 2)).sum)) := by rw [hb]
      _ = zz z (a + b) * psi w (x + (Pi.single i 1 +
            (l.map fun i => Pi.single i (1 : ZMod 2)).sum)) := by
          rw [zz_mul_zz_mul h.z_sq, add_assoc]
      _ = _ := by simp

theorem sum_single_supp (y : ι → ZMod 2) :
    ((supp y).toList.map fun i => Pi.single i (1 : ZMod 2)).sum = y := by
  rw [Finset.sum_map_toList]
  ext j
  rw [Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_ite_eq, mem_supp]
  rcases zmod_two_cases (y j) with hj | hj <;> simp [hj]

theorem psi_mul_psi (h : GramRel z w) (x y : ι → ZMod 2) :
    ∃ a : ZMod 2, psi w x * psi w y = zz z a * psi w (x + y) := by
  obtain ⟨a, ha⟩ := psi_mul_gprod h (supp y).toList x
  rw [sum_single_supp] at ha
  exact ⟨a, ha⟩

omit [DecidableEq ι] in
theorem sum_eq_card_supp (x : ι → ZMod 2) : ∑ i, x i = ((supp x).card : ZMod 2) := by
  have h1 : ∀ i, x i = if x i = 1 then 1 else 0 := by
    intro i
    rcases zmod_two_cases (x i) with h | h <;> simp [h]
  calc ∑ i, x i = ∑ i, (if x i = 1 then (1 : ZMod 2) else 0) :=
        Finset.sum_congr rfl (fun i _ => h1 i)
    _ = _ := by
        rw [Finset.sum_boole]
        rfl

theorem countP_supp (x : ι → ZMod 2) (j : ι) :
    ((((supp x).toList.countP fun i => decide (i ≠ j) : ℕ)) : ZMod 2) = (∑ i, x i) + x j := by
  have h1 := countP_ne_add_count j (supp x).toList
  have h2 : (supp x).toList.count j = if x j = 1 then 1 else 0 := by
    by_cases hj : x j = 1
    · simp only [hj, ↓reduceIte]
      exact List.count_eq_one_of_mem (Finset.nodup_toList _) (by simpa using hj)
    · simp only [hj, ↓reduceIte]
      exact List.count_eq_zero_of_not_mem (by simpa using hj)
  rw [Finset.length_toList] at h1
  have h4 : (((supp x).toList.count j : ℕ) : ZMod 2) = x j := by
    rw [h2]
    rcases zmod_two_cases (x j) with hj | hj <;> simp [hj]
  have h5 : ((((supp x).toList.countP fun i => decide (i ≠ j) : ℕ)) : ZMod 2) + x j =
      ∑ i, x i := by
    rw [← h4, sum_eq_card_supp, ← Nat.cast_add, h1]
  rw [← h5, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem w_mul_psi_comm (h : GramRel z w) (x : ι → ZMod 2) (j : ι) :
    w j * psi w x = zz z ((∑ i, x i) + x j) * (psi w x * w j) := by
  have := h.mul_gprod j (supp x).toList
  rw [← countP_supp, ← zz_pow h.z_sq]
  exact this

theorem gprod_mul_psi (h : GramRel z w) (l : List ι) (x : ι → ZMod 2) :
    gprod w l * psi w x =
      zz z ((l.map fun j => (∑ i, x i) + x j).sum) * (psi w x * gprod w l) := by
  induction l with
  | nil => simp [zz_zero]
  | cons j l ih =>
    obtain ⟨S, hS⟩ : ∃ S, S = (l.map fun j => (∑ i, x i) + x j).sum := ⟨_, rfl⟩
    rw [← hS] at ih
    calc gprod w (j :: l) * psi w x = w j * (gprod w l * psi w x) := by
          rw [gprod_cons, mul_assoc]
      _ = w j * (zz z S * (psi w x * gprod w l)) := by rw [ih]
      _ = zz z S * (w j * (psi w x * gprod w l)) := mul_zz_mul h.z_comm _ _ _
      _ = zz z S * ((w j * psi w x) * gprod w l) := by rw [mul_assoc (w j)]
      _ = zz z S * ((zz z ((∑ i, x i) + x j) * (psi w x * w j)) * gprod w l) := by
          rw [w_mul_psi_comm h]
      _ = zz z S * (zz z ((∑ i, x i) + x j) * (psi w x * (w j * gprod w l))) := by
          simp only [mul_assoc]
      _ = zz z (((∑ i, x i) + x j) + S) * (psi w x * gprod w (j :: l)) := by
          rw [zz_mul_zz_mul h.z_sq S, add_comm S, gprod_cons]
      _ = _ := by rw [List.map_cons, List.sum_cons, hS]

omit [DecidableEq ι] in
theorem sum_supp_eq (x y : ι → ZMod 2) :
    ∑ j ∈ supp x, ((∑ i, y i) + y j) = gramForm ι x y := by
  rw [gramForm_apply, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← sum_eq_card_supp]
  congr 1
  simp only [supp]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases zmod_two_cases (x i) with hi | hi <;> simp [hi]

theorem psi_mul_psi_comm (h : GramRel z w) (x y : ι → ZMod 2) :
    psi w x * psi w y = zz z (gramForm ι x y) * (psi w y * psi w x) := by
  have := gprod_mul_psi h (supp x).toList y
  rw [Finset.sum_map_toList, sum_supp_eq] at this
  exact this

theorem eq_zero_of_psi_eq_zz (h : GramRel z w) (hz : z ≠ 1) (hc : Even (Fintype.card ι))
    {x : ι → ZMod 2} {t : ZMod 2} (hx : psi w x = zz z t) : x = 0 := by
  refine eq_zero_of_gramForm_eq_zero hc fun v => ?_
  have h1 := psi_mul_psi_comm h x v
  rw [hx, zz_comm h.z_comm (psi w v) t] at h1
  have h2 : 1 * (zz z t * psi w v) = zz z (gramForm ι x v) * (zz z t * psi w v) := by
    rw [one_mul]
    exact h1
  exact ((zz_eq_one_iff hz _).mp (mul_right_cancel h2).symm)

theorem zz_mul_psi_injective (h : GramRel z w) (hz : z ≠ 1) (hc : Even (Fintype.card ι)) :
    Function.Injective (fun p : ZMod 2 × (ι → ZMod 2) => zz z p.1 * psi w p.2) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ hab
  simp only at hab
  have h1 : psi w x = zz z (a + b) * psi w y := by
    calc psi w x = zz z a * (zz z a * psi w x) := by
          rw [← mul_assoc, zz_mul_self h.z_sq, one_mul]
      _ = zz z a * (zz z b * psi w y) := by rw [hab]
      _ = zz z (a + b) * psi w y := by rw [zz_mul_zz_mul h.z_sq]
  obtain ⟨c, hc'⟩ := psi_mul_psi h x y
  obtain ⟨d, hd⟩ := psi_mul_psi h y y
  rw [add_self_pi, psi_zero, mul_one] at hd
  have h2 : psi w x * psi w y = zz z (a + b + d) := by
    rw [h1, mul_assoc, hd, ← zz_add h.z_sq]
  have h3 : psi w (x + y) = zz z (c + (a + b + d)) := by
    rw [zz_add h.z_sq, ← h2]
    exact eq_zz_mul_swap h.z_sq hc'
  have h4 := eq_zero_of_psi_eq_zz h hz hc h3
  have h5 : x = y := by
    funext i
    have := congrFun h4 i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    exact CharTwo.add_eq_zero.mp this
  subst h5
  have h6 : zz z a = zz z b := mul_right_cancel hab
  rw [zz_inj h.z_sq hz h6]

omit [DecidableEq ι] in
theorem zz_mul_psi_mem (h : GramRel z w) (a : ZMod 2) (v : ι → ZMod 2) :
    zz z a * psi w v ∈ Subgroup.closure (insert z (Set.range w)) := by
  refine Subgroup.mul_mem _ ?_ ?_
  · unfold zz
    split_ifs
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact (h.mem_closure_iff).mpr ⟨0, (supp v).toList, by simp [psi]⟩

theorem exists_zz_mul_psi (h : GramRel z w) {g : P}
    (hg : g ∈ Subgroup.closure (insert z (Set.range w))) :
    ∃ (a : ZMod 2) (v : ι → ZMod 2), g = zz z a * psi w v := by
  obtain ⟨k, l, rfl⟩ := h.mem_closure_iff.mp hg
  obtain ⟨a, ha⟩ := psi_mul_gprod h l 0
  rw [psi_zero, one_mul, zero_add] at ha
  exact ⟨(k : ZMod 2) + a, (l.map fun i => Pi.single i (1 : ZMod 2)).sum, by
    rw [ha, zz_pow h.z_sq, zz_mul_zz_mul h.z_sq]⟩

theorem two_pow_le_card_closure [Finite P] (h : GramRel z w) (hz : z ≠ 1)
    (hc : Even (Fintype.card ι)) :
    2 ^ (Fintype.card ι + 1) ≤ Nat.card (Subgroup.closure (insert z (Set.range w))) := by
  let f : ZMod 2 × (ι → ZMod 2) → Subgroup.closure (insert z (Set.range w)) :=
    fun p => ⟨zz z p.1 * psi w p.2, zz_mul_psi_mem h p.1 p.2⟩
  have hf : Function.Injective f := by
    intro p q hpq
    exact zz_mul_psi_injective h hz hc (congrArg Subtype.val hpq)
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (ZMod 2 × (ι → ZMod 2)) = 2 ^ (Fintype.card ι + 1) := by
    simp [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card, pow_succ,
      mul_comm]
  rwa [h2] at h1

omit [DecidableEq ι] in
theorem zz_mul_psi_mul (h : GramRel z w) (a b : ZMod 2) (x y : ι → ZMod 2) :
    (zz z a * psi w x) * (zz z b * psi w y) = zz z (a + b) * (psi w x * psi w y) := by
  calc (zz z a * psi w x) * (zz z b * psi w y)
      = zz z a * (psi w x * (zz z b * psi w y)) := mul_assoc _ _ _
    _ = zz z a * (zz z b * (psi w x * psi w y)) := by rw [mul_zz_mul h.z_comm]
    _ = zz z (a + b) * (psi w x * psi w y) := by rw [zz_mul_zz_mul h.z_sq]

theorem card_le_of_abelian [Finite P] (h : GramRel z w) (hz : z ≠ 1) {m : ℕ}
    (hm : Fintype.card ι = 2 * m) (Y : Subgroup P)
    (hY : Y ≤ Subgroup.closure (insert z (Set.range w)))
    (hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) : Nat.card Y ≤ 2 ^ (m + 1) := by
  have hzero : (0 : ι → ZMod 2) ∈ {x : ι → ZMod 2 | ∃ a, zz z a * psi w x ∈ Y} :=
    ⟨0, by simp [zz_zero, psi_zero]⟩
  let U : Submodule (ZMod 2) (ι → ZMod 2) :=
    { carrier := {x | ∃ a, zz z a * psi w x ∈ Y}
      add_mem' := by
        rintro x x' ⟨a, ha⟩ ⟨a', ha'⟩
        obtain ⟨c, hc⟩ := psi_mul_psi h x x'
        refine ⟨a + a' + c, ?_⟩
        have := Y.mul_mem ha ha'
        rw [zz_mul_psi_mul h, hc, ← mul_assoc, ← zz_add h.z_sq] at this
        exact this
      zero_mem' := hzero
      smul_mem' := by
        intro c x hx
        rcases zmod_two_cases c with rfl | rfl
        · simpa using hzero
        · simpa using hx }
  have hiso : ∀ u ∈ U, ∀ v ∈ U, gramForm ι u v = 0 := by
    rintro u ⟨a, hu⟩ v ⟨b, hv⟩
    have h1 := hab _ hu _ hv
    rw [zz_mul_psi_mul h, zz_mul_psi_mul h, psi_mul_psi_comm h, add_comm b a,
      ← mul_assoc, ← zz_add h.z_sq] at h1
    have h2 := zz_inj h.z_sq hz (mul_right_cancel h1)
    have h3 : gramForm ι u v = 0 := by
      have := add_left_cancel (a := a + b) (b := gramForm ι u v) (c := 0) (by rw [add_zero]; exact h2)
      exact this
    exact h3
  have hex : ∀ y : Y, ∃ p : ZMod 2 × U, (y : P) = zz z p.1 * psi w (p.2 : ι → ZMod 2) := by
    intro y
    obtain ⟨a, v, hv⟩ := exists_zz_mul_psi h (hY y.2)
    exact ⟨(a, ⟨v, ⟨a, by rw [← hv]; exact y.2⟩⟩), hv⟩
  choose f hf using hex
  have hinj : Function.Injective f := fun y y' hyy' => Subtype.ext (by rw [hf y, hf y', hyy'])
  have h1 := Nat.card_le_card_of_injective f hinj
  have hU : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U), Nat.card_zmod]
  rw [Nat.card_prod, Nat.card_zmod, hU] at h1
  have h2 : 2 * Module.finrank (ZMod 2) U ≤ Fintype.card ι :=
    two_mul_finrank_le ⟨m, by omega⟩ U hiso
  have h3 : Module.finrank (ZMod 2) U ≤ m := by omega
  calc Nat.card Y ≤ 2 * 2 ^ Module.finrank (ZMod 2) U := h1
    _ ≤ 2 * 2 ^ m := by gcongr
    _ = 2 ^ (m + 1) := by ring

end Group

end CFSG.Quasithin.Background.Harris.R1.GramAbel

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin.Background.Harris.R1.GramAbel

theorem gramAbel_holds : GramAbelStmt := by
  classical
  intro P _ _ Ω _ z w hrel hz hodd _ A hA
  obtain ⟨m, hm⟩ := hodd
  have hdiv : Fintype.card Ω / 2 = m := by omega
  obtain ⟨i0⟩ : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  let ι := {i : Ω // i ≠ i0}
  let w' : ι → P := fun i => w i
  have hrel' : SzR1.GramRel z w' :=
    ⟨hrel.z_sq, hrel.z_comm, fun i => hrel.w_sq _,
      fun i j hij => hrel.w_comm _ _ (fun h => hij (Subtype.ext h))⟩
  have hcard : Fintype.card ι = 2 * m := by
    have h1 := Fintype.card_subtype_compl (fun x : Ω => x = i0)
    rw [Fintype.card_subtype_eq] at h1
    have h2 : Fintype.card ι = Fintype.card {x // ¬ x = i0} := Fintype.card_congr (Equiv.refl _)
    omega
  have hev : Even (Fintype.card ι) := ⟨m, by omega⟩
  have h1 : 2 ^ (2 * m + 1) ≤ Nat.card (Subgroup.closure (insert z (Set.range w'))) := by
    have := two_pow_le_card_closure hrel' hz hev
    rwa [hcard] at this
  set P' := Subgroup.closure (insert z (Set.range w')) with hP'
  have h2 : Nat.card (P' ⊓ A :) ≤ 2 ^ (m + 1) :=
    card_le_of_abelian hrel' hz hcard (P' ⊓ A) inf_le_left
      (fun a ha b hb => hA a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2)
  have h3 : P'.relIndex A ≤ P'.index := by
    rw [← Subgroup.relIndex_top_right]
    refine Subgroup.relIndex_le_of_le_right le_top ?_
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have h4 := Subgroup.relIndex_mul_card (H := P') (K := A)
  have h5 := Subgroup.card_mul_index P'
  rw [hdiv]
  calc 2 ^ m * Nat.card A = 2 ^ m * (P'.relIndex A * Nat.card (P' ⊓ A :)) := by rw [h4]
    _ ≤ 2 ^ m * (P'.index * 2 ^ (m + 1)) := by gcongr
    _ = 2 ^ (2 * m + 1) * P'.index := by ring
    _ ≤ Nat.card P' * P'.index := by gcongr
    _ = Nat.card P := h5

end CFSG.Quasithin.Background.Harris.R1
