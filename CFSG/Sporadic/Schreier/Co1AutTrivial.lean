module

public import CFSG.Sporadic.Schreier.Co1AutCheck
public import CFSG.Sporadic.Schreier.Co1Chain
public import CFSG.Sporadic.Schreier.Co1StabFix
public import CFSG.GroupActions.AutomorphismStabilizerPermutation

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_xor toVecD_injective toVecD_zero)
open CFSG.Sporadic.SmallF2.Native Matrix CFSG.GroupActions

@[expose] noncomputable def stabDagL : List GL24 := dagG [stabH0, stabH1] Data.stabDerivs

theorem stab_tower_facts :
    Native.stabDag.2.2 = true ∧ Native.stabDag.1.length = 85 ∧
    Native.vTowerOK Native.stabColsT Data.stabTowerBase Data.stabTowerGens
      Data.stabTowerSizes = true := by
  have h := stab_tower_check
  simp only [Native.stabTowerCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem stabDag_rep :
    List.Forall₂ MRep Native.stabDag.1 stabDagL :=
  dag_rep (.cons stabH0_rep (.cons stabH1_rep .nil)) Data.stabDerivs stab_tower_facts.1

theorem stabColsT_getD {j : ℕ} (hj : j < 85) :
    Native.stabColsT.getD j #[] = transposeRows 24 (Native.stabDag.1.getD j Native.one) := by
  rw [Native.stabColsT, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hj, ↓reduceDIte, Option.getD_some]

theorem stabDagL_mem (j : ℕ) : stabDagL.getD j 1 ∈ stabH := by
  refine getD_mem_of_forall (dagG_mem (fun g hg => ?_) Data.stabDerivs) j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | hg
  · rw [hg]
    exact stabH0_mem
  · rw [hg]
    exact stabH1_mem

theorem card_stabH_ge :
    42305421312000 ≤ Nat.card stabH := by
  have hsize : Native.stabColsT.size = 85 := Array.size_ofFn
  have h := card_ge_of_towerOK (G := stabH) (L := fun j => stabDagL.getD j 1)
    (cols := Native.stabColsT) (fun j _ => stabDagL_mem j) (fun j hj => by
      rw [hsize] at hj
      rw [stabColsT_getD hj]
      exact MRep.actsBy (getD_rep stabDag_rep MRep.one j)) stab_tower_facts.2.2
  have hp : ∏ i ∈ Finset.range Data.stabTowerBase.length, Data.stabTowerSizes.getD i 0 =
      42305421312000 := by
    simp only [Data.stabTowerBase, Data.stabTowerSizes, List.length_cons, List.length_nil,
      Finset.prod_range_succ, Finset.prod_range_zero]
    rfl
  rw [hp] at h
  exact h

theorem card_GA_eq : Nat.card GA = 4157776806543360000 := by
  have h := CFSG.Sporadic.SmallF2.card_lvl CFSG.Sporadic.Co1.co1Facts (i := 0) (Nat.zero_le _)
  rw [CFSG.Sporadic.SmallF2.lvl_zero CFSG.Sporadic.Co1.co1Facts, Subgroup.card_top] at h
  exact h.trans (by decide)

theorem co1X_eq_kOrbit :
    co1X = kOrbit GA (stabVecOf 0) := by
  have hz := stabVecOf_mem_X (k := 0) (by norm_num)
  rw [← gaOrbit_two] at hz ⊢
  exact (kOrbit_eq_of_mem hz).symm

theorem mem_co1X_smul
    {g : GL24} (hg : g ∈ GA) {x : Vec24} (hx : x ∈ co1X) :
    ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x ∈ co1X := by
  rw [co1X_eq_kOrbit] at hx ⊢
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨g * h, GA.mul_mem hg hh, by rw [Units.val_mul, ← mulVec_mulVec]⟩

@[expose, instance_reducible] def xAct :
    MulAction GA co1X where
  smul g x := ⟨((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x, mem_co1X_smul g.2 x.2⟩
  one_smul x := Subtype.ext (by
    show (((1 : GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (x : Vec24) = x
    rw [OneMemClass.coe_one, Units.val_one, one_mulVec])
  mul_smul g h x := Subtype.ext (by
    show (((g * h : GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (x : Vec24) =
      ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        (((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (x : Vec24))
    rw [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec])

attribute [local instance] xAct

theorem xAct_val (g : GA) (x : co1X) :
    ((g • x : co1X) : Vec24) = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x := rfl

theorem mem_kOrbit_of_mem_co1X
    {v : Vec24} (hv : v ∈ co1X) : v ∈ kOrbit GA (stabVecOf 0) := by
  rw [co1X_eq_kOrbit] at hv
  exact hv

theorem xAct_pretransitive :
    MulAction.IsPretransitive GA co1X := ⟨fun x y => by
  have hx := mem_kOrbit_of_mem_co1X x.2
  have hy := mem_kOrbit_of_mem_co1X y.2
  rw [← kOrbit_eq_of_mem hx] at hy
  obtain ⟨g, hg, hgy⟩ := hy
  exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩⟩

theorem stabVecOf_zero_ne : stabVecOf 0 ≠ 0 := by
  intro h
  rw [stabVecOf, ← toVecD_zero 24] at h
  have := toVecD_injective (stabVec_lt 0 (by norm_num)) (by norm_num) h
  exact absurd this (by decide)

theorem span_co1X :
    Submodule.span (ZMod 2) co1X = ⊤ := by
  have hinv : ∀ g ∈ GA, ∀ v ∈ Submodule.span (ZMod 2) co1X,
      ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ Submodule.span (ZMod 2) co1X := by
    intro g hg v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (mem_co1X_smul hg hx)
    | zero =>
      rw [mulVec_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [mulVec_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [mulVec_smul]
      exact Submodule.smul_mem _ a hx
  rcases invariant_eq hinv with h | h
  · exfalso
    have hz : stabVecOf 0 ∈ Submodule.span (ZMod 2) co1X :=
      Submodule.subset_span (stabVecOf_mem_X (by norm_num))
    rw [h, Submodule.mem_bot] at hz
    exact stabVecOf_zero_ne hz
  · exact h

@[expose] def eqSub (M N : Matrix (Fin 24) (Fin 24) (ZMod 2)) : Submodule (ZMod 2) Vec24 where
  carrier := {v | M *ᵥ v = N *ᵥ v}
  add_mem' {v w} hv hw := by
    show M *ᵥ (v + w) = N *ᵥ (v + w)
    rw [mulVec_add, mulVec_add, hv, hw]
  zero_mem' := by
    show M *ᵥ 0 = N *ᵥ 0
    rw [mulVec_zero, mulVec_zero]
  smul_mem' c v hv := by
    show M *ᵥ (c • v) = N *ᵥ (c • v)
    rw [mulVec_smul, mulVec_smul, hv]

theorem xAct_faithful :
    FaithfulSMul GA co1X := ⟨fun {g g'} h => by
  apply Subtype.ext
  apply Units.ext
  have hker : Submodule.span (ZMod 2) co1X ≤ eqSub ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))
      ((g' : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    rw [Submodule.span_le]
    intro x hx
    have := congrArg Subtype.val (h ⟨x, hx⟩)
    rw [xAct_val, xAct_val] at this
    exact this
  rw [span_co1X] at hker
  refine Matrix.ext_of_mulVec_single fun i => ?_
  exact hker (Submodule.mem_top (x := Pi.single i 1))⟩

@[expose] noncomputable def xz :
    co1X := ⟨stabVecOf 0, stabVecOf_mem_X (by norm_num)⟩

theorem card_co1X_type :
    Nat.card co1X = 98280 := by
  rw [Nat.card_coe_set_eq, ncard_co1X]

theorem stabilizer_eq :
    MulAction.stabilizer GA xz = stabH.subgroupOf GA := by
  have hle : stabH.subgroupOf GA ≤ MulAction.stabilizer GA xz := by
    intro h hh
    rw [MulAction.mem_stabilizer_iff]
    exact Subtype.ext (stabH_fix_z (Subgroup.mem_subgroupOf.mp hh))
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hpre := xAct_pretransitive
  have horb : Nat.card (MulAction.orbit GA xz) * Nat.card (MulAction.stabilizer GA xz) =
      Nat.card GA := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup GA xz)
  have horbit : Nat.card (MulAction.orbit GA xz) = 98280 := by
    rw [MulAction.orbit_eq_univ GA xz, Nat.card_coe_set_eq, Set.ncard_univ, card_co1X_type]
  rw [horbit, card_GA_eq] at horb
  have hs : Nat.card (MulAction.stabilizer GA xz) = 42305421312000 := by omega
  have hH : Nat.card (stabH.subgroupOf GA) = Nat.card stabH :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe stabH_le_GA).toEquiv
  rw [hs, hH]
  exact card_stabH_ge

theorem mem_stab_iff
    {g : GA} : g ∈ MulAction.stabilizer GA xz ↔ (g : GL24) ∈ stabH := by
  rw [stabilizer_eq, Subgroup.mem_subgroupOf]

@[expose] noncomputable def toStab
    {h : GL24} (hh : h ∈ stabH) : MulAction.stabilizer GA xz :=
  ⟨⟨h, stabH_le_GA hh⟩, mem_stab_iff.mpr hh⟩

theorem val_orbit
    (y : co1X) :
    Subtype.val '' MulAction.orbit (MulAction.stabilizer GA xz) y = kOrbit stabH y := by
  ext v
  constructor
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨_, mem_stab_iff.mp h.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨toStab hg • y, ⟨toStab hg, rfl⟩, rfl⟩

theorem mem_orbit_stab_iff
    {y y' : co1X} :
    y' ∈ MulAction.orbit (MulAction.stabilizer GA xz) y ↔ (y' : Vec24) ∈ kOrbit stabH y := by
  rw [← val_orbit]
  constructor
  · intro h
    exact ⟨y', h, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    rwa [Subtype.ext hwv] at hw

theorem card_orbit_stab
    (y : co1X) :
    Nat.card (MulAction.orbit (MulAction.stabilizer GA xz) y) = (kOrbit stabH y).ncard := by
  rw [← val_orbit, Set.ncard_image_of_injective _ Subtype.val_injective, Nat.card_coe_set_eq]

@[expose] noncomputable def ptX
    (k : Fin 4) : co1X := ⟨stabVecOf k, stabVecOf_mem_X k.isLt⟩

theorem mem_union_of_mem_co1X
    {v : Vec24} (hv : v ∈ co1X) :
    v ∈ kOrbit stabH (stabVecOf 0) ∪ kOrbit stabH (stabVecOf 1) ∪
      kOrbit stabH (stabVecOf 2) ∪ kOrbit stabH (stabVecOf 3) := by
  rw [co1X_eq_union] at hv
  exact hv

theorem exists_orbit
    (w : co1X) :
    ∃ k : Fin 4, w ∈ MulAction.orbit (MulAction.stabilizer GA xz) (ptX k) := by
  have hw := mem_union_of_mem_co1X w.2
  simp only [Set.mem_union] at hw
  rcases hw with ((h | h) | h) | h
  · exact ⟨0, mem_orbit_stab_iff.mpr h⟩
  · exact ⟨1, mem_orbit_stab_iff.mpr h⟩
  · exact ⟨2, mem_orbit_stab_iff.mpr h⟩
  · exact ⟨3, mem_orbit_stab_iff.mpr h⟩

theorem card_orbit_ptX
    (k : Fin 4) :
    Nat.card (MulAction.orbit (MulAction.stabilizer GA xz) (ptX k)) = Native.stabSize k := by
  rw [card_orbit_stab]
  exact ncard_kOrbit_stabH k.isLt

theorem z_add_mem
    {u : Vec24} (hu : u ∈ kOrbit stabH (stabVecOf 3)) :
    stabVecOf 0 + u ∈ kOrbit stabH (stabVecOf 3) := by
  have hzv : stabVecOf 0 + stabVecOf 3 ∈ kOrbit stabH (stabVecOf 3) := by
    have h := (fixPts_eq (m := 2) (by norm_num))
    simp only [↓reduceIte] at h
    have hm : stabVecOf 0 + stabVecOf 3 ∈ fixPts (stabVecOf 3) := by
      rw [h]
      exact Set.mem_insert_of_mem _ rfl
    exact hm.1
  obtain ⟨h, hh, rfl⟩ := hu
  obtain ⟨h', hh', hh'v⟩ := hzv
  refine ⟨h * h', stabH.mul_mem hh hh', ?_⟩
  rw [Units.val_mul, ← mulVec_mulVec, hh'v, mulVec_add, stabH_fix_z hh]

open Classical in
@[expose] noncomputable def tauX
    (y : co1X) : co1X :=
  if h : (y : Vec24) ∈ kOrbit stabH (stabVecOf 3) then
    ⟨stabVecOf 0 + y, kOrbit_stabH_subset (by norm_num) (z_add_mem h)⟩
  else y

theorem tauX_of_mem
    {y : co1X} (h : (y : Vec24) ∈ kOrbit stabH (stabVecOf 3)) :
    (tauX y : Vec24) = stabVecOf 0 + y := by
  unfold tauX
  simp only [h, ↓reduceDIte]

theorem tauX_of_not_mem
    {y : co1X} (h : (y : Vec24) ∉ kOrbit stabH (stabVecOf 3)) :
    tauX y = y := by
  unfold tauX
  simp only [h, ↓reduceDIte]

theorem vec24_add_self (q : Vec24) : q + q = 0 := funext fun i => by
  show q i + q i = 0
  generalize q i = z
  revert z
  decide

theorem tauX_involutive :
    Function.Involutive tauX := by
  intro y
  by_cases h : (y : Vec24) ∈ kOrbit stabH (stabVecOf 3)
  · have h' : (tauX y : Vec24) ∈ kOrbit stabH (stabVecOf 3) := by
      rw [tauX_of_mem h]
      exact z_add_mem h
    apply Subtype.ext
    rw [tauX_of_mem h', tauX_of_mem h, ← add_assoc, vec24_add_self, zero_add]
  · rw [tauX_of_not_mem h, tauX_of_not_mem h]

@[expose] noncomputable def tauPerm :
    Equiv.Perm co1X := tauX_involutive.toPerm tauX

theorem stab_smul_mem
    {h : MulAction.stabilizer GA xz} {y : co1X} :
    ((h • y : co1X) : Vec24) ∈ kOrbit stabH (stabVecOf 3) ↔
      (y : Vec24) ∈ kOrbit stabH (stabVecOf 3) := by
  have hh := mem_stab_iff.mp h.2
  constructor
  · intro hy
    obtain ⟨g, hg, hgy⟩ := hy
    refine ⟨(((h : GA) : GL24))⁻¹ * g, stabH.mul_mem (stabH.inv_mem hh) hg, ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec, hgy]
    show (((h : GA) : GL24)⁻¹ : GL24).val *ᵥ (((h : GA) : GL24).val *ᵥ (y : Vec24)) = y
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  · rintro ⟨g, hg, hgy⟩
    exact ⟨((h : GA) : GL24) * g, stabH.mul_mem hh hg, by
      rw [Units.val_mul, ← mulVec_mulVec, hgy]
      rfl⟩

theorem tauPerm_comm
    (h : MulAction.stabilizer GA xz) (y : co1X) :
    tauPerm (h • y) = h • tauPerm y := by
  show tauX (h • y) = h • tauX y
  have hh := mem_stab_iff.mp h.2
  by_cases hy : (y : Vec24) ∈ kOrbit stabH (stabVecOf 3)
  · apply Subtype.ext
    rw [tauX_of_mem (stab_smul_mem.mpr hy)]
    show stabVecOf 0 + ((h : GA) : GL24).val *ᵥ (y : Vec24) =
      ((h : GA) : GL24).val *ᵥ (tauX y : Vec24)
    rw [tauX_of_mem hy, mulVec_add, stabH_fix_z hh]
  · rw [tauX_of_not_mem (fun h' => hy (stab_smul_mem.mp h')), tauX_of_not_mem hy]

theorem nonlin_facts :
    Data.nonlinVecs.foldl (· ^^^ ·) 0 = Native.stabVec 3 ∧
    (∀ w ∈ Data.nonlinVecs, w < 2 ^ 24 ∧ Native.act Native.aR w < 2 ^ 24 ∧
      Native.inEnum (Native.fullOrb 2) 98280 w = true ∧
      Native.inEnum (Native.stabOrb 3) 4600 w = false ∧
      Native.inEnum (Native.stabOrb 3) 4600 (Native.act Native.aR w) = false) ∧
    Native.inEnum (Native.stabOrb 3) 4600 (Native.stabVec 0 ^^^ Native.stabVec 3) = true ∧
    Native.act Native.aR (Native.stabVec 0 ^^^ Native.stabVec 3) < 2 ^ 24 ∧
    Data.nonlinVecs.foldl (fun s w => s ^^^ Native.act Native.aR w) 0 = 11752856 ∧
    Native.tauOf (Native.stabOrb 3) (Native.act Native.aR (Native.stabVec 0 ^^^ Native.stabVec 3)) =
      15263478 := by
  have h := nonlin_check
  simp only [Native.nonlinCheck, Native.nonlinCheckOf, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc] at h
  exact h

theorem co1X_eq_enum :
    co1X = enumSet (Native.fullOrb 2) (Native.fullSize 2) :=
  gaOrbit_two.symm.trans (gaOrbit_root (k := 2) (by norm_num))

theorem mem_X61_iff
    {u : ℕ} (hu : u < 2 ^ 24) :
    toVecD 24 u ∈ kOrbit stabH (stabVecOf 3) ↔ Native.inEnum (Native.stabOrb 3) 4600 u = true := by
  rw [kOrbit_stabH (by norm_num)]
  exact mem_enumSet_iff (stab_facts.2.2.2.2 3 (by norm_num)) hu

theorem mem_X_of_inEnum
    {u : ℕ} (hu : u < 2 ^ 24)
    (h : Native.inEnum (Native.fullOrb 2) 98280 u = true) : toVecD 24 u ∈ co1X := by
  rw [co1X_eq_enum]
  simp only [Native.inEnum, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i, hi, by rw [he]⟩

theorem tauX_val
    {y : co1X} {u : ℕ} (hu : u < 2 ^ 24) (hy : (y : Vec24) = toVecD 24 u) :
    (tauX y : Vec24) = toVecD 24 (Native.tauOf (Native.stabOrb 3) u) := by
  unfold Native.tauOf
  by_cases h : Native.inEnum (Native.stabOrb 3) 4600 u = true
  · have hm : (y : Vec24) ∈ kOrbit stabH (stabVecOf 3) := by
      rw [hy]
      exact (mem_X61_iff hu).mpr h
    rw [tauX_of_mem hm, hy]
    simp only [h, ↓reduceIte]
    rw [toVecD_xor]
    rfl
  · have hm : (y : Vec24) ∉ kOrbit stabH (stabVecOf 3) := by
      rw [hy, mem_X61_iff hu]
      exact h
    rw [tauX_of_not_mem hm, hy]
    simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem vec_foldl_xor (l : List ℕ) : ∀ acc : ℕ,
    toVecD 24 (l.foldl (· ^^^ ·) acc) = toVecD 24 acc + (l.map (toVecD 24)).sum := by
  induction l with
  | nil => intro acc; rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons w l ih =>
    intro acc
    rw [List.foldl_cons, ih, toVecD_xor, List.map_cons, List.sum_cons, add_assoc]

theorem vec_foldl_xor_map (l : List ℕ) (f : ℕ → ℕ) : ∀ acc : ℕ,
    toVecD 24 (l.foldl (fun s w => s ^^^ f w) acc) =
      toVecD 24 acc + (l.map fun w => toVecD 24 (f w)).sum := by
  induction l with
  | nil => intro acc; rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons w l ih =>
    intro acc
    rw [List.foldl_cons, ih, toVecD_xor, List.map_cons, List.sum_cons, add_assoc]

theorem mulVec_list_sum (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) (l : List Vec24) :
    M *ᵥ l.sum = (l.map (M *ᵥ ·)).sum := by
  induction l with
  | nil => rw [List.sum_nil, mulVec_zero, List.map_nil, List.sum_nil]
  | cons v l ih => rw [List.sum_cons, mulVec_add, ih, List.map_cons, List.sum_cons]

theorem not_linear_tau
    {M : Matrix (Fin 24) (Fin 24) (ZMod 2)}
    (hM : ∀ y : co1X, M *ᵥ (y : Vec24) =
      (tauX ((⟨A₁, A₁_mem⟩ : GA) • tauX y : co1X) : Vec24)) : False := by
  obtain ⟨hsum, hvecs, hzv, hzvlt, hsumA, htau⟩ := nonlin_facts
  have hlin : ∀ w ∈ Data.nonlinVecs, M *ᵥ toVecD 24 w = toVecD 24 (Native.act Native.aR w) := by
    intro w hw
    obtain ⟨hwlt, hawlt, hwX, hw61, haw61⟩ := hvecs w hw
    have hy := hM ⟨toVecD 24 w, mem_X_of_inEnum hwlt hwX⟩
    have h1 : tauX (⟨toVecD 24 w, mem_X_of_inEnum hwlt hwX⟩ : co1X) =
        ⟨toVecD 24 w, mem_X_of_inEnum hwlt hwX⟩ := tauX_of_not_mem (by
      rw [mem_X61_iff hwlt, hw61]
      decide)
    rw [h1] at hy
    have h2 : (((⟨A₁, A₁_mem⟩ : GA) • (⟨toVecD 24 w, mem_X_of_inEnum hwlt hwX⟩ : co1X) :
        co1X) : Vec24) = toVecD 24 (Native.act Native.aR w) := by
      rw [xAct_val]
      exact MRep.mulVec rep_A₁ w
    rw [tauX_val hawlt h2] at hy
    rw [hy]
    unfold Native.tauOf
    simp only [haw61, Bool.false_eq_true, ↓reduceIte]
  have h3 := hM (ptX 3)
  have h4 : (tauX (ptX 3) : Vec24) = toVecD 24 (Native.stabVec 0 ^^^ Native.stabVec 3) := by
    rw [tauX_of_mem (mem_kOrbit_self _ _), toVecD_xor]
    rfl
  have h5 : (((⟨A₁, A₁_mem⟩ : GA) • tauX (ptX 3) : co1X) : Vec24) =
      toVecD 24 (Native.act Native.aR (Native.stabVec 0 ^^^ Native.stabVec 3)) := by
    rw [xAct_val, h4]
    exact MRep.mulVec rep_A₁ _
  rw [tauX_val hzvlt h5, htau] at h3
  have h6 : (ptX 3 : Vec24) = (Data.nonlinVecs.map (toVecD 24)).sum := by
    have := vec_foldl_xor Data.nonlinVecs 0
    rw [hsum, toVecD_zero, zero_add] at this
    exact this
  rw [h6, mulVec_list_sum, List.map_map] at h3
  have h7 : (Data.nonlinVecs.map ((M *ᵥ ·) ∘ toVecD 24)).sum =
      (Data.nonlinVecs.map fun w => toVecD 24 (Native.act Native.aR w)).sum :=
    congrArg List.sum (List.map_congr_left fun w hw => hlin w hw)
  rw [h7] at h3
  have h8 := vec_foldl_xor_map Data.nonlinVecs (Native.act Native.aR) 0
  rw [hsumA, toVecD_zero, zero_add] at h8
  rw [← h8] at h3
  have h9 := toVecD_injective (by norm_num) (by norm_num) h3
  exact absurd h9 (by decide)

theorem ptX_val
    (k : Fin 4) : (ptX k : Vec24) = stabVecOf k := rfl

theorem toStab_smul_val
    {h : GL24} (hh : h ∈ stabH) (y : co1X) :
    ((toStab hh • y : co1X) : Vec24) = (h : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (y : Vec24) :=
  rfl

theorem tauPerm_apply
    (y : co1X) : tauPerm y = tauX y := rfl

theorem mem_fixPts_of
    {σ : Equiv.Perm co1X} {k : Fin 4}
    (hmo : σ (ptX k) ∈ MulAction.orbit (MulAction.stabilizer GA xz) (ptX k))
    (hst : ∀ h ∈ MulAction.stabilizer (MulAction.stabilizer GA xz) (ptX k),
      h • σ (ptX k) = σ (ptX k)) :
    (σ (ptX k) : Vec24) ∈ fixPts (stabVecOf k) := by
  have h1 := mem_orbit_stab_iff.mp hmo
  rw [ptX_val] at h1
  refine Set.mem_inter h1 ?_
  intro h hh hv
  have hs : toStab hh ∈ MulAction.stabilizer (MulAction.stabilizer GA xz) (ptX k) := by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [toStab_smul_val, ptX_val]
    exact hv
  rw [← toStab_smul_val hh]
  exact congrArg Subtype.val (hst (toStab hh) hs)

theorem tauPerm_inv :
    tauPerm⁻¹ = tauPerm := by
  rw [Equiv.Perm.inv_def]
  exact Function.Involutive.toPerm_symm tauX_involutive

theorem not_tau_realized
    {β : GA ≃* GA}
    (h : ∀ (g : GA) (y : co1X), tauPerm (g • tauPerm⁻¹ y) = β g • y) : False := by
  refine not_linear_tau
    (M := (((β (⟨A₁, A₁_mem⟩ : GA) : GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    fun y => ?_
  have hy := h (⟨A₁, A₁_mem⟩ : GA) y
  rw [tauPerm_inv, tauPerm_apply, tauPerm_apply] at hy
  rw [← xAct_val, ← hy]

theorem mem_subgroupStabAut_of_fix {G : Type*} [Group G] {H : Subgroup G} {α : MulAut G}
    (h : ∀ x ∈ H, α x = x) : α ∈ subgroupStabAut H := by
  show H.map α.toMonoidHom = H
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, h x hx]
    exact hx
  · intro hg
    exact ⟨g, hg, by rw [MulEquiv.coe_toMonoidHom, h g hg]⟩

theorem pointwise_Co2_automorphism_stabilizer_trivial
    (α : GA ≃* GA)
    (hα : ∀ h : GA, (h : GL24) ∈ stabH → α h = h) : α = MulEquiv.refl GA := by
  have hpre := xAct_pretransitive
  have hfai := xAct_faithful
  have hfix : ∀ h ∈ MulAction.stabilizer GA xz, α h = h := fun h hh => hα h (mem_stab_iff.mp hh)
  have hmem : α ∈ subgroupStabAut (MulAction.stabilizer GA xz) :=
    mem_subgroupStabAut_of_fix hfix
  obtain ⟨⟨-, hA2, hinj, hconj, hcent⟩, hB⟩ :=
    faithful_transitive_action_automorphism_stabilizer (G := GA) xz (MulAction.stabilizer GA xz)
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm co1X, σ = stabAutPoint (G := GA) xz ⟨α, hmem⟩ :=
    ⟨_, rfl⟩
  have hσc : ∀ (h : MulAction.stabilizer GA xz) (y : co1X), σ (h • y) = h • σ y := fun h y => by
    rw [hσ]
    exact hcent ⟨α, hmem⟩ hfix h h.2 y
  obtain ⟨hB1, hB2, hB3⟩ := hB σ hσc
  have hpres : ∀ k : Fin 4, σ (ptX k) ∈ MulAction.orbit (MulAction.stabilizer GA xz) (ptX k) := by
    intro k
    obtain ⟨-, hcard⟩ := hB1 (ptX k)
    obtain ⟨k', hk'⟩ := exists_orbit (σ (ptX k))
    rw [MulAction.orbit_eq_iff.mpr hk', card_orbit_ptX, card_orbit_ptX] at hcard
    have hkk : k' = k := by
      revert hcard
      fin_cases k <;> fin_cases k' <;> decide
    rw [hkk] at hk'
    exact hk'
  have himg : ∀ k : Fin 4, σ '' MulAction.orbit (MulAction.stabilizer GA xz) (ptX k) =
      MulAction.orbit (MulAction.stabilizer GA xz) (ptX k) := fun k => by
    rw [(hB1 (ptX k)).1, MulAction.orbit_eq_iff.mpr (hpres k)]
  have hfixpt : ∀ k : Fin 4, (σ (ptX k) : Vec24) ∈ fixPts (stabVecOf k) := fun k =>
    mem_fixPts_of (hB2 (ptX k) (himg k)).1 (hB2 (ptX k) (himg k)).2
  have hid : ∀ k : Fin 4, σ (ptX k) = ptX k →
      ∀ w ∈ MulAction.orbit (MulAction.stabilizer GA xz) (ptX k), σ w = w :=
    fun k hk w hw => hB3 1 (fun _ _ => rfl) (ptX k) hk w hw
  obtain ⟨h1, h2, h3⟩ := (show fixPts (stabVecOf 1) = {stabVecOf 1} ∧
      fixPts (stabVecOf 2) = {stabVecOf 2} ∧
      fixPts (stabVecOf 3) = {stabVecOf 3, stabVecOf 0 + stabVecOf 3} from
    ⟨two_point_stabilizer_fixed_vector_spaces.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      two_point_stabilizer_fixed_vector_spaces.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      two_point_stabilizer_fixed_vector_spaces.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩)
  have hk0 : σ (ptX 0) = ptX 0 := by
    rw [hσ]
    exact hA2 ⟨α, hmem⟩
  have hk1 : σ (ptX 1) = ptX 1 := by
    have := hfixpt 1
    rw [show ((1 : Fin 4) : ℕ) = 1 from rfl, h1, Set.mem_singleton_iff] at this
    apply Subtype.ext
    rw [ptX_val, show ((1 : Fin 4) : ℕ) = 1 from rfl]
    exact this
  have hk2 : σ (ptX 2) = ptX 2 := by
    have := hfixpt 2
    rw [show ((2 : Fin 4) : ℕ) = 2 from rfl, h2, Set.mem_singleton_iff] at this
    apply Subtype.ext
    rw [ptX_val, show ((2 : Fin 4) : ℕ) = 2 from rfl]
    exact this
  have hk3 := hfixpt 3
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl, h3, Set.mem_insert_iff, Set.mem_singleton_iff] at hk3
  have hp3 : (ptX 3 : Vec24) = stabVecOf 3 := by
    rw [ptX_val, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  rcases hk3 with hk3 | hk3
  ·
    have hk3' : σ (ptX 3) = ptX 3 := by
      apply Subtype.ext
      rw [hp3]
      exact hk3
    have hall : ∀ w, σ w = w := by
      intro w
      obtain ⟨k, hk⟩ := exists_orbit w
      fin_cases k
      · exact hid 0 hk0 w hk
      · exact hid 1 hk1 w hk
      · exact hid 2 hk2 w hk
      · exact hid 3 hk3' w hk
    have hσ1 : stabAutPoint (G := GA) xz ⟨α, hmem⟩ = stabAutPoint (G := GA) xz 1 := by
      rw [← hσ, map_one]
      exact Equiv.ext hall
    have := congrArg Subtype.val (hinj hσ1)
    exact this
  ·
    exfalso
    have hm3 : (ptX 3 : Vec24) ∈ kOrbit stabH (stabVecOf 3) := by
      rw [hp3]
      exact mem_kOrbit_self _ _
    have hτ3 : σ (ptX 3) = tauPerm (ptX 3) := by
      apply Subtype.ext
      rw [hk3, tauPerm_apply, tauX_of_mem hm3, hp3]
    have hστ : ∀ w, σ w = tauPerm w := by
      intro w
      obtain ⟨k, hk⟩ := exists_orbit w
      have hnot : ∀ j : Fin 4, j ≠ 3 → w ∈ MulAction.orbit (MulAction.stabilizer GA xz) (ptX j) →
          tauPerm w = w := by
        intro j hj hw
        rw [tauPerm_apply]
        refine tauX_of_not_mem fun hw3 => ?_
        have hd := kOrbit_stabH_disjoint (j := j) (k := 3) j.isLt (by norm_num)
          (fun h => hj (Fin.ext h))
        have hw' := mem_orbit_stab_iff.mp hw
        rw [ptX_val] at hw'
        exact Set.disjoint_left.mp hd hw' hw3
      fin_cases k
      · rw [hid 0 hk0 w hk, hnot 0 (by decide) hk]
      · rw [hid 1 hk1 w hk, hnot 1 (by decide) hk]
      · rw [hid 2 hk2 w hk, hnot 2 (by decide) hk]
      · exact hB3 tauPerm tauPerm_comm (ptX 3) hτ3 w hk
    have hστ' : σ = tauPerm := Equiv.ext hστ
    refine not_tau_realized (β := α) fun g y => ?_
    have := hconj ⟨α, hmem⟩ g y
    rw [← hσ, hστ'] at this
    exact this

end CFSG.Sporadic.Co1Schreier
