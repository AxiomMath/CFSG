
module

public import CFSG.Quasithin.H13.L32NMatNGen
public import CFSG.Quasithin.Background.H12OneHatM22PfInputs

@[expose] public section

namespace CFSG.Quasithin.H.Mathieu.H12Cert

open CFSG.Quasithin.H13.MatNCert

theorem validN_gG : ∀ g ∈ gG, ValidN 12 g := by
  have h : gG.all (validB 12) = true := by decide +kernel
  intro g hg
  exact validB_iff.mp (List.all_eq_true.mp h g hg)

theorem validN_gInv : ∀ g ∈ gInv, ValidN 12 g := by
  have h : gInv.all (validB 12) = true := by decide +kernel
  intro g hg
  exact validB_iff.mp (List.all_eq_true.mp h g hg)

theorem gG_inv : ∀ i < 2, mulN (gG.getD i one12) (gInv.getD i one12) = one12 ∧
    mulN (gInv.getD i one12) (gG.getD i one12) = one12 := by
  decide +kernel

theorem length_gG (i : ℕ) : (gG.getD i one12).length = 12 := (validN_getD validN_gG i).1

theorem length_gInv (i : ℕ) : (gInv.getD i one12).length = 12 := (validN_getD validN_gInv i).1

@[expose] def gU (i : ℕ) : GL (Fin 12) (ZMod 2) :=
  if h : i < 2 then
    ⟨decN 12 (gG.getD i one12), decN 12 (gInv.getD i one12),
      by rw [← decN_mulN (length_gG i) (length_gInv i), (gG_inv i h).1, decN_oneN],
      by rw [← decN_mulN (length_gInv i) (length_gG i), (gG_inv i h).2, decN_oneN]⟩
  else 1

@[expose] def tU (w : List ℕ) : GL (Fin 12) (ZMod 2) := (w.map gU).prod

theorem gU_val (i : ℕ) : ((gU i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
    decN 12 (gG.getD i one12) := by
  by_cases h : i < 2
  · simp only [gU, h, dite_true]
  · rw [List.getD_eq_default _ _ (by simp [gG]; omega), decN_oneN]
    simp only [gU, h, dite_false, Units.val_one]

theorem tU_cons (i : ℕ) (w : List ℕ) : tU (i :: w) = gU i * tU w := by
  simp only [tU, List.map_cons, List.prod_cons]

theorem tU_val (w : List ℕ) :
    ((tU w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 (tW w) := by
  induction w with
  | nil =>
    simp only [tU, List.map_nil, List.prod_nil, Units.val_one]
    exact decN_oneN.symm
  | cons i w ih =>
    rw [tU_cons, Units.val_mul, ih, gU_val]
    show _ = decN 12 (evalW 12 gG (i :: w))
    rw [evalW_cons, decN_mulN (validN_getD validN_gG i).1 (length_evalW gG w)]

@[expose] def G : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 gG

theorem getD_mem_gG {i : ℕ} (hi : i < 2) : gG.getD i one12 ∈ gG := by
  rw [List.getD_eq_getElem _ _ (by simp [gG]; omega)]
  exact List.getElem_mem _

theorem gU_mem (i : ℕ) : gU i ∈ G := by
  by_cases h : i < 2
  · exact mem_genSubN_of_mem validN_gG (getD_mem_gG h) (gU_val i)
  · simp only [gU, h, dite_false]
    exact one_mem _

theorem tU_mem (w : List ℕ) : tU w ∈ G := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih =>
    rw [tU_cons]
    exact mul_mem (gU_mem i) ih

theorem exists_gU_eq {x : GL (Fin 12) (ZMod 2)}
    (hx : colsN (x : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ gG) : ∃ i < 2, x = gU i := by
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  have hi2 : i < 2 := by simpa [gG] using hi
  refine ⟨i, hi2, eq_of_colsN_eq ?_⟩
  rw [gU_val, colsN_decN (validN_getD validN_gG i), List.getD_eq_getElem _ _ hi, hxi]

theorem G_induction {p : GL (Fin 12) (ZMod 2) → Prop} (h1 : p 1)
    (hstep : ∀ i < 2, ∀ y, p y → p (gU i * y)) {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ G) :
    p x := by
  have hpow : ∀ i < 2, ∀ m : ℕ, ∀ y, p y → p (gU i ^ m * y) := by
    intro i hi m
    induction m with
    | zero => intro y hy; rwa [pow_zero, one_mul]
    | succ m ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hstep i hi _ (ih y hy)
  refine Subgroup.closure_induction_left (p := fun x _ => p x) h1 ?_ ?_ hx
  · intro x hx y _ hy
    obtain ⟨i, hi, rfl⟩ := exists_gU_eq hx
    exact hstep i hi y hy
  · intro x hx y _ hy
    obtain ⟨i, hi, rfl⟩ := exists_gU_eq hx
    have hfin : IsOfFinOrder (gU i) := isOfFinOrder_of_finite _
    have hinv : (gU i)⁻¹ = gU i ^ (orderOf (gU i) - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
    rw [hinv]
    exact hpow i hi _ y hy

theorem z12_facts : z12.length = 12 ∧ tW zW = z12 ∧ (∀ g ∈ gG, mulN z12 g = mulN g z12) ∧
    mulN z12 (mulN z12 z12) = one12 ∧ z12 ≠ one12 ∧ f0 = [0, 5, 10, 15] := by
  decide +kernel

theorem validN_z12 : ValidN 12 z12 := z12_facts.2.1 ▸ validN_evalW gG validN_gG zW

@[expose] def zU : GL (Fin 12) (ZMod 2) := tU zW

theorem zU_val :
    ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 z12 := by
  rw [zU, tU_val, z12_facts.2.1]

theorem zU_mem : zU ∈ G := tU_mem zW

theorem gU_mul_zU (i : ℕ) : gU i * zU = zU * gU i := by
  by_cases hi : i < 2
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, gU_val, zU_val, ← decN_mulN (length_gG i) z12_facts.1,
      ← decN_mulN z12_facts.1 (length_gG i), z12_facts.2.2.1 _ (getD_mem_gG hi)]
  · simp only [gU, hi, dite_false, one_mul, mul_one]

theorem zU_comm {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ G) : x * zU = zU * x :=
  G_induction (p := fun x => x * zU = zU * x) (by rw [one_mul, mul_one])
    (fun i _ y hy => by rw [mul_assoc, hy, ← mul_assoc, gU_mul_zU, mul_assoc]) hx

theorem zU_pow_three : zU ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, zU_val, Units.val_one, pow_three,
    ← decN_mulN z12_facts.1 z12_facts.1, ← decN_mulN z12_facts.1 (by rw [length_mulN, z12_facts.1]),
    z12_facts.2.2.2.1, decN_oneN]

theorem zU_ne_one : zU ≠ 1 := by
  intro h
  apply z12_facts.2.2.2.2.1
  have := congrArg (fun u : GL (Fin 12) (ZMod 2) =>
    colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2))) h
  simp only [zU_val, Units.val_one, colsN_one] at this
  rwa [colsN_decN validN_z12] at this

theorem orderOf_zU : orderOf zU = 3 :=
  orderOf_eq_prime zU_pow_three zU_ne_one

@[expose] def S0 : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 s0G

theorem s0G_unit : ∀ g ∈ s0G, ∃ u : GL (Fin 12) (ZMod 2),
    (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact ⟨tU w, tU_val w⟩

theorem validN_s0G : ∀ g ∈ s0G, ValidN 12 g := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact validN_evalW gG validN_gG w

theorem S0_le : S0 ≤ G := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨w, -, hw⟩ := List.mem_map.mp (show colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈
    s0G from hu)
  have : u = tU w := by
    apply Units.ext
    rw [tU_val, hw, decN_colsN]
  rw [this]
  exact tU_mem w

abbrev w0 : Fin 12 → ZMod 2 := vecN 12 v0

@[expose] def F0v : Set (Fin 12 → ZMod 2) := {v | ∃ c ∈ f0, v = vecN 12 c}

theorem zU_mulVec_vecN (c : ℕ) :
    ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 c) =
      vecN 12 (mvN z12 c) := by
  rw [zU_val, decN_mulVec z12_facts.1]

theorem mvN_z12_f0 : ∀ c ∈ f0, mvN z12 c ∈ f0 := by decide +kernel

theorem f0_lt : ∀ c ∈ f0, c < 2 ^ 12 := by decide +kernel

theorem w0_mem_F0v : w0 ∈ F0v := ⟨v0, by decide, rfl⟩

theorem zero_mem_F0v : (0 : Fin 12 → ZMod 2) ∈ F0v := ⟨0, by decide, vecN_zero.symm⟩

theorem zU_mem_F0v {v : Fin 12 → ZMod 2} (hv : v ∈ F0v) :
    ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v ∈ F0v := by
  obtain ⟨c, hc, rfl⟩ := hv
  exact ⟨_, mvN_z12_f0 c hc, zU_mulVec_vecN c⟩

theorem mem_F0v_iff (v : Fin 12 → ZMod 2) :
    v ∈ F0v ↔ v = 0 ∨ v = w0 ∨
      v = ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 ∨
      v = ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0) := by
  have h10 : mvN z12 v0 = 10 := by decide +kernel
  have h15 : mvN z12 10 = 15 := by decide +kernel
  rw [zU_mulVec_vecN, h10, zU_mulVec_vecN, h15]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [z12_facts.2.2.2.2.2] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact Or.inl vecN_zero
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact zero_mem_F0v
    · exact w0_mem_F0v
    · exact ⟨10, by rw [z12_facts.2.2.2.2.2]; simp, rfl⟩
    · exact ⟨15, by rw [z12_facts.2.2.2.2.2]; simp, rfl⟩

@[expose] def T0 : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 tG

theorem mulVec_zU_comm {g : GL (Fin 12) (ZMod 2)} (hg : g * zU = zU * g)
    (x : Fin 12 → ZMod 2) :
    ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec x) =
      ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hg]

theorem mapsTo_F0v {g : GL (Fin 12) (ZMod 2)} (h1 : g * zU = zU * g)
    (h2 : ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 ∈ F0v)
    {v : Fin 12 → ZMod 2} (hv : v ∈ F0v) :
    ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v ∈ F0v := by
  rcases (mem_F0v_iff v).mp hv with rfl | rfl | rfl | rfl
  · rw [Matrix.mulVec_zero]
    exact zero_mem_F0v
  · exact h2
  · rw [mulVec_zU_comm h1]
    exact zU_mem_F0v h2
  · rw [mulVec_zU_comm h1, mulVec_zU_comm h1]
    exact zU_mem_F0v (zU_mem_F0v h2)

@[expose] def lineStabM : Submonoid (GL (Fin 12) (ZMod 2)) where
  carrier := {g | g * zU = zU * g ∧
    ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 ∈ F0v}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨by rw [mul_assoc, hb1, ← mul_assoc, ha1, mul_assoc], ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact mapsTo_F0v ha1 ha2 hb2
  one_mem' := ⟨by rw [one_mul, mul_one], by rw [Units.val_one, Matrix.one_mulVec]; exact w0_mem_F0v⟩

@[expose] def lineStab : Subgroup (GL (Fin 12) (ZMod 2)) :=
  { lineStabM with
    inv_mem' := fun {g} hg => by
      have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
      have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
          Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
      rw [hinv]
      exact lineStabM.pow_mem hg _ }

theorem zU_mem_lineStab : zU ∈ lineStab := ⟨rfl, zU_mem_F0v w0_mem_F0v⟩

theorem mulVec_of_inv_mul_mem {x y : GL (Fin 12) (ZMod 2)} (hx : x ∈ G)
    (h : x⁻¹ * y ∈ lineStab) :
    ((y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 = 0 ∨
    ((y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 =
      ((x : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 ∨
    ((y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 =
      ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (((x : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0) ∨
    ((y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 =
      ((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (((zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
          (((x : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0)) := by
  have hy : y = x * (x⁻¹ * y) := by group
  have key : ((y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 =
      ((x : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (((x⁻¹ * y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0) := by
    conv_lhs => rw [hy]
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [key]
  rcases (mem_F0v_iff _).mp h.2 with h1 | h1 | h1 | h1 <;> rw [h1]
  · exact Or.inl (Matrix.mulVec_zero _)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl (mulVec_zU_comm (zU_comm hx) _)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [mulVec_zU_comm (zU_comm hx), mulVec_zU_comm (zU_comm hx)]

theorem inv_mul_not_mem_of_lineNe {x y : GL (Fin 12) (ZMod 2)}
    (hx : x ∈ G) {a b : ℕ} (ha : a < 2 ^ 12) (hb : b < 2 ^ 12) (hb0 : b ≠ 0)
    (hxa : ((x : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 =
      vecN 12 a)
    (hyb : ((y : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 =
      vecN 12 b) (hab : lineNe a b = true) : x⁻¹ * y ∉ lineStab := by
  intro h
  simp only [lineNe, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  obtain ⟨⟨h1, h2⟩, h3⟩ := hab
  have hz1 := mvN_lt validN_z12.2 a
  have hz2 := mvN_lt validN_z12.2 (mvN z12 a)
  rcases mulVec_of_inv_mul_mem hx h with h0 | h0 | h0 | h0
  · rw [hyb] at h0
    exact hb0 (vecN_inj hb (by norm_num) (h0.trans vecN_zero.symm))
  · rw [hyb, hxa] at h0
    exact h1 (vecN_inj hb ha h0)
  · rw [hyb, hxa, zU_mulVec_vecN] at h0
    exact h2 (vecN_inj hb hz1 h0)
  · rw [hyb, hxa, zU_mulVec_vecN, zU_mulVec_vecN] at h0
    exact h3 (vecN_inj hb hz2 h0)

@[expose] def R0 : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 rG

@[expose] def y0U : GL (Fin 12) (ZMod 2) := tU y0W

theorem T0_le_R0 : T0 ≤ R0 := Subgroup.closure_mono fun _ hu => List.mem_append_left _ hu

theorem validN_rP : ∀ r ∈ rP, ValidN 12 r.1 ∧ ValidN 12 r.2 := by
  have h : ∀ r ∈ rP, validB 12 r.1 = true ∧ validB 12 r.2 = true := by decide +kernel
  intro r hr
  exact ⟨validB_iff.mp (h r hr).1, validB_iff.mp (h r hr).2⟩

theorem four_le_index {R : Subgroup (GL (Fin 12) (ZMod 2))} (m : Fin 4 → ↥R)
    (hm : ∀ i j, ((m i : GL (Fin 12) (ZMod 2))⁻¹ * m j) ∈ lineStab → i = j) :
    4 ≤ ((R ⊓ lineStab).subgroupOf R).index := by
  have hinj : Function.Injective fun i =>
      (QuotientGroup.mk (m i) : ↥R ⧸ (R ⊓ lineStab).subgroupOf R) := by
    intro i j h
    apply hm
    have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
    simpa using h1.2
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Subgroup.index] using this

theorem not_four_lines {R : Subgroup (GL (Fin 12) (ZMod 2))}
    (hRG : R ≤ G) (hidx : ((R ⊓ lineStab).subgroupOf R).index ≤ 3) (m : Fin 4 → ↥R)
    (c : Fin 4 → ℕ)
    (hc : ∀ i, ((m i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec w0 =
      vecN 12 (c i))
    (hc12 : ∀ i, c i < 2 ^ 12) (hc0 : ∀ i, c i ≠ 0)
    (hne : ∀ i j, i < j → lineNe (c i) (c j) = true) : False := by
  have hlt : ∀ i j, i < j → ((m i : GL (Fin 12) (ZMod 2))⁻¹ * m j) ∉ lineStab :=
    fun i j hij => inv_mul_not_mem_of_lineNe (hRG (m i).2) (hc12 i) (hc12 j) (hc0 j) (hc i) (hc j)
      (hne i j hij)
  have hdist : ∀ i j, ((m i : GL (Fin 12) (ZMod 2))⁻¹ * m j) ∈ lineStab → i = j := by
    intro i j hij
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hlt i j h hij
    · apply hlt j i h
      have := lineStab.inv_mem hij
      rwa [mul_inv_rev, inv_inv] at this
  have := four_le_index m hdist
  omega

end CFSG.Quasithin.H.Mathieu.H12Cert
