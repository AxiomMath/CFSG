module

public import CFSG.Sporadic.Fi22.Transpositions
public import CFSG.Sporadic.Fi22.ClassesCert
public import CFSG.Fischer.Pairs

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev LJ : Array Table := chainLetters orb

noncomputable abbrev LS : Array Table := sylLetters LJ

noncomputable abbrev TS : Array Tree := chainTrees 3510 LS sylBase

noncomputable abbrev tabS (i : ℕ) : Array Table := treeTabs 3510 TS[i]! LS

theorem classes_parts :
    (∀ w ∈ sylWords, ∀ z ∈ w, z.toNat < LJ.size) ∧
    chainOK 3510 LS sylBase chainQ sylQb TS 3 = true ∧ orbitSizes TS = [1024, 128] ∧
    (∀ W ∈ conjTabs orb, invOK 3510 W.1 W.2 = true) ∧
    ∀ k < (tabS 0).size, ∀ B ∈ tabS 1,
      leafOK orb.alpha (conjTabs orb) (compT 3510 (tabS 0)[k]! B) = true := by
  have h : sylChecks orb 3 = true := classes_certificate
  unfold sylChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true',
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun k hk => Array.all_eq_true'.1 (parAll_eq_true h5 k hk)⟩

@[expose] noncomputable def jG (z : ℤ) : J := pairG gs z.toNat

theorem rep_jGen
    {z : ℤ} (hz : z.toNat < LJ.size) : Rep 3510 (jGen LJ z) (jG z) :=
  rep_pairG_all _ hz

@[expose] noncomputable def sylG (j : ℕ) : J := wordG jG sylWords[j]!

theorem LS_size : LS.size = 2 * sylWords.size := by
  unfold LS sylLetters buildLetters; simp

theorem LS_even {j : ℕ} (hj : j < sylWords.size) :
    LS[2 * j]! = wordT 3510 (jGen LJ) sylWords[j]! := by
  unfold LS sylLetters buildLetters
  rw [getElem!_pos _ (2 * j) (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [ite_eq_left (by omega)]
  congr 2
  omega

theorem rep_LS :
    ∀ j < LS.size / 2, Rep 3510 LS[2 * j]! (sylG j) := by
  intro j hj
  rw [LS_size] at hj
  have hj' : j < sylWords.size := by omega
  have hmem : sylWords[j]! ∈ sylWords := by
    rw [getElem!_pos sylWords j hj']; exact Array.getElem_mem hj'
  rw [LS_even hj']
  exact Rep.wordT (by norm_num) _ fun z hz => rep_jGen (classes_parts.1 _ hmem z hz)

theorem LS_parts : LS.size % 2 = 0 ∧
    ∀ j < LS.size / 2, invOK 3510 LS[2 * j]! LS[2 * j + 1]! = true :=
  ⟨(chainOK_parts classes_parts.2.1).1, (chainOK_parts classes_parts.2.1).2.1⟩

theorem rep_LS_all :
    ∀ l < LS.size, Rep 3510 LS[l]! (pairG sylG l) :=
  rep_pairG rep_LS LS_parts.1 LS_parts.2

noncomputable abbrev slvl
    (i : ℕ) : Subgroup J := levelGroup LS sylBase (pairG sylG) i

theorem syl_facts :
    (∀ i < sylBase.size, TreeFacts 3510 TS[i]! (levelLetters LS sylBase i) (pairG sylG)
      sylBase[i]!) ∧
      (∀ i < sylBase.size, ∀ g ∈ slvl i,
        idx 3510 g sylBase[i]! = sylBase[i]! ↔ g ∈ slvl (i + 1)) ∧
      ∀ i ≤ sylBase.size, Nat.card (slvl i) =
        ∏ l ∈ Finset.Ico i sylBase.size, TS[l]!.pts.size :=
  chain_facts rep_LS sep classes_parts.2.1

theorem sylBase_size : sylBase.size = 2 := rfl

theorem TS_size
    {l v : ℕ} (hv : [1024, 128][l]? = some v) : TS[l]!.pts.size = v := by
  have h2 := congrArg (fun L : List ℕ => L[l]?) classes_parts.2.2.1
  simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList] at h2
  rw [hv] at h2
  have hl : l < TS.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h2
    simp at h2
  rw [Array.getElem?_eq_getElem hl] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  rw [getElem!_pos TS l hl]
  exact h2

theorem card_slvl_zero :
    Nat.card (slvl 0) = 131072 := by
  rw [syl_facts.2.2 0 (by rw [sylBase_size]; norm_num), sylBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 2, TS[l]!.pts.size = [1024, 128].getD l 0 := fun l hl =>
    TS_size (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem slvl_two : slvl 2 = ⊥ := by
  have h := syl_facts.2.2 2 (by rw [sylBase_size])
  rw [sylBase_size, Finset.Ico_self, Finset.prod_empty] at h
  exact Subgroup.eq_bot_of_card_eq _ h

theorem exists_tree_mul
    {i : ℕ} (hi : i < sylBase.size) {g : J} (hg : g ∈ slvl i) :
    ∃ k < TS[i]!.pts.size, ∃ h ∈ slvl (i + 1), g = treeG TS[i]! (pairG sylG) k * h := by
  have hT := syl_facts.1 i hi
  obtain ⟨k, hk, hkp⟩ := (hT.mem_orbit_iff (g • (⟨sylBase[i]!, hT.r_lt⟩ : Fin 3510))).1
    ⟨⟨g, hg⟩, rfl⟩
  set t := treeG TS[i]! (pairG sylG) k with ht
  refine ⟨k, hk, t⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hmem : t⁻¹ * g ∈ slvl i := (slvl i).mul_mem ((slvl i).inv_mem (hT.treeG_mem hk)) hg
  refine (syl_facts.2.1 i hi _ hmem).1 ?_
  have e : idx 3510 g sylBase[i]! = idx 3510 t sylBase[i]! := by
    rw [ht, hT.elt k hk, hkp]
    exact (smul_val_eq_idx (n := 3510) g ⟨sylBase[i]!, hT.r_lt⟩).symm
  rw [idx_mul, e, idx_inv_idx]

theorem walkFacts_TS
    {i : ℕ} (hi : i < sylBase.size) : WalkFacts 3510 TS[i]! LS (pairG sylG) := by
  intro k hk hk0
  obtain ⟨hpar, hlab⟩ := (syl_facts.1 i hi).par k hk hk0
  have hl := levelLetters_lt hlab
  refine ⟨hpar, rep_LS_all _ hl, ?_⟩
  rw [← pairG_invL]
  exact rep_LS_all _ (invL_lt LS_parts.1 hl)

theorem range_get_3510 {t : ℕ} (ht : t < 3510) : (Array.range 3510)[t]! = t := by
  rw [getElem!_pos _ t (by simpa using ht), Array.getElem_range]

theorem tabS_size (i : ℕ) : (tabS i).size = TS[i]!.pts.size := by
  unfold tabS treeTabs; simp

theorem rep_tabS
    {i : ℕ} (hi : i < sylBase.size) {k : ℕ} (hk : k < TS[i]!.pts.size) :
    Rep 3510 (tabS i)[k]! (treeG TS[i]! (pairG sylG) k) := by
  obtain ⟨hs, he⟩ := walk_spec (walkFacts_TS hi) hk (Array.range 3510)
    (fun t ht => by rw [range_get_3510 (by simpa using ht)]; simpa using ht)
  have e1 : (tabS i)[k]! = (walk TS[i]! LS k (Array.range 3510)).map UInt32.ofNat := by
    unfold tabS treeTabs
    rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  intro j hj
  have hj' : j < (Array.range 3510).size := by simpa using hj
  have hw := he j hj'
  rw [range_get_3510 hj] at hw
  rw [e1]
  unfold ap
  rw [getElem!_pos _ j (by simp [hs]; exact hj), Array.getElem_map,
    ← getElem!_pos _ j (by rw [hs]; exact hj'), hw, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (lt_trans (idx_lt _ hj) (by norm_num))]

@[expose] def InvClass (g : J) : Prop :=
  g ^ 2 = 1 → g ≠ 1 → g ∈ D ∨ ∃ w : J, orderOf (g * (w * g * w⁻¹)) ∉ ({1, 2, 3} : Set ℕ)

theorem eq_one_of_idx
    {g : J} (h : ∀ i < 3510, idx 3510 g i = i) : g = 1 :=
  eq_one_of_fix_all fun i => Fin.ext ((smul_val_eq_idx g i).trans (h i.val i.isLt))

theorem eq_one_of_idOK
    {P : Table} {g : J} (hP : Rep 3510 P g) (h : idOK 3510 P = true) :
    g = 1 := by
  apply eq_one_of_idx
  intro i hi
  have := allIn_eq_true.1 h i (Nat.zero_le _) hi
  rw [beq_iff_eq, hP i hi] at this
  exact this

theorem idOK_of_eq_one
    {P : Table} {g : J} (hP : Rep 3510 P g) (h : g = 1) :
    idOK 3510 P = true := by
  unfold idOK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, h, idx_one]

theorem invoOK_of_sq
    {P : Table} {g : J} (hP : Rep 3510 P g) (h : g ^ 2 = 1) :
    invoOK 3510 P = true := by
  unfold invoOK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, hP _ (idx_lt g hi), ← idx_mul, ← pow_two, h, idx_one]

theorem order3OK_of_cube
    {P : Table} {g : J} (hP : Rep 3510 P g) (h : g ^ 3 = 1) :
    order3OK 3510 P = true := by
  unfold order3OK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, hP _ (idx_lt g hi), hP _ (idx_lt g (idx_lt g hi)), ← idx_mul,
    ← idx_mul, ← pow_three', h, idx_one]

theorem cube_of_order3OK
    {P : Table} {g : J} (hP : Rep 3510 P g) (h : order3OK 3510 P = true) :
    g ^ 3 = 1 :=
  eq_one_of_idx (idx_cube_of_order3OK hP h)

theorem mem_D_of_cube
    {g c : J} (hc : c ∈ D) (hg : g ^ 2 = 1) (h : (g * c) ^ 3 = 1) : g ∈ D := by
  have hc2 : c * c = 1 := by rw [← pow_two, ← orderOf_of_mem_D hc, pow_orderOf_eq_one]
  have hg2 : g * g = 1 := by rw [← pow_two, hg]
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have h3 : g * c * g * c * g * c = 1 := by
    rw [← h]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e : g = (c * g) * c * (c * g)⁻¹ := by
    rw [mul_inv_rev, hgi, hci]
    calc g = g * (g * c * g * c * g * c) := by rw [h3, mul_one]
      _ = g * g * c * g * c * g * c := by simp only [mul_assoc]
      _ = c * g * c * (g * c) := by rw [hg2]; simp only [one_mul, mul_assoc]
  rw [e]
  exact IsConj.trans hc (isConj_iff.2 ⟨c * g, rfl⟩)

theorem orderOf_notMem
    {y : J} (h1 : y ≠ 1) (h2 : y ^ 2 ≠ 1) (h3 : y ^ 3 ≠ 1) :
    orderOf y ∉ ({1, 2, 3} : Set ℕ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h | h)
  · exact h1 (orderOf_eq_one_iff.1 h)
  · have := pow_orderOf_eq_one y
    rw [h] at this
    exact h2 this
  · have := pow_orderOf_eq_one y
    rw [h] at this
    exact h3 this

theorem rep_conjTabs
    {W : Table × Table} (hW : W ∈ conjTabs orb) :
    ∃ w : J, Rep 3510 W.1 w ∧ Rep 3510 W.2 w⁻¹ := by
  have hinv := classes_parts.2.2.2.1 W hW
  unfold conjTabs at hW
  obtain ⟨u, -, rfl⟩ := Array.mem_map.1 hW
  have h1 : Rep 3510 (wordT 3510 (genTables orb) u) (wordG genG u) :=
    Rep.wordT (by norm_num) _ fun l _ => rep_gen l
  exact ⟨_, h1, Rep.inv_of_invOK h1 hinv⟩

theorem invClass_of_leafOK
    {P : Table} {g : J} (hP : Rep 3510 P g)
    (h : leafOK orb.alpha (conjTabs orb) P = true) : InvClass g := by
  intro hg2 hg1
  unfold leafOK at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', Array.any_eq_true', Bool.and_eq_true] at h
  rcases h with ((h | h) | h) | ⟨W, hW, h⟩
  · rw [invoOK_of_sq hP hg2] at h; exact absurd h (by decide)
  · exact absurd (eq_one_of_idOK hP h) hg1
  · exact Or.inl (mem_D_of_cube a_mem_D hg2 (cube_of_order3OK (Rep.compT hP rep_alpha) h))
  · right
    obtain ⟨w, hw1, hw2⟩ := rep_conjTabs hW
    have hR := Rep.compT hP (Rep.compT (Rep.compT hw1 hP) hw2)
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨w, orderOf_notMem (fun e => ?_) (fun e => ?_) (fun e => ?_)⟩
    · rw [idOK_of_eq_one hR e] at h1; exact absurd h1 (by decide)
    · rw [invoOK_of_sq hR e] at h2; exact absurd h2 (by decide)
    · rw [order3OK_of_cube hR e] at h3; exact absurd h3 (by decide)

theorem invClass_of_mem
    {g : J} (hg : g ∈ slvl 0) : InvClass g := by
  obtain ⟨k0, hk0, h, hh, rfl⟩ := exists_tree_mul (i := 0) (by rw [sylBase_size]; norm_num) hg
  obtain ⟨k1, hk1, h', hh', rfl⟩ := exists_tree_mul (i := 1) (by rw [sylBase_size]; norm_num) hh
  have hh'' : h' ∈ slvl 2 := hh'
  rw [slvl_two, Subgroup.mem_bot] at hh''
  rw [hh'', mul_one]
  have hmem : (tabS 1)[k1]! ∈ tabS 1 := by
    rw [getElem!_pos _ k1 (by rw [tabS_size]; exact hk1)]; exact Array.getElem_mem _
  exact invClass_of_leafOK
    (Rep.compT (rep_tabS (by rw [sylBase_size]; norm_num) hk0)
      (rep_tabS (by rw [sylBase_size]; norm_num) hk1))
    (classes_parts.2.2.2.2 k0 (by rw [tabS_size]; exact hk0) _ hmem)

theorem slvl_index :
    (slvl 0).index = 492567075 := by
  have h := (slvl 0).card_mul_index
  rw [card_slvl_zero, card_J] at h
  omega

open scoped Pointwise in
theorem exists_conj_mem_slvl
    {e : J} (he : orderOf e = 2) : ∃ g : J, g * e * g⁻¹ ∈ slvl 0 := by
  have hT : IsPGroup 2 (slvl 0) := IsPGroup.of_card (n := 17) (by rw [card_slvl_zero]; norm_num)
  have hidx : ¬ 2 ∣ (slvl 0).index := by rw [slvl_index]; decide
  have hE : IsPGroup 2 (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he, pow_one])
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J Q (hT.toSylow hidx)
  refine ⟨g, ?_⟩
  have h1 : MulAut.conj g • e ∈ MulAut.conj g • (Q : Subgroup J) :=
    Subgroup.smul_mem_pointwise_smul e _ _ (hQ (Subgroup.mem_zpowers e))
  rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe, MulAut.smul_def,
    MulAut.conj_apply] at h1
  exact h1

theorem pair_D : CFSG.Blueprint.Fischer.Pair J D :=
  ⟨inferInstance, ⟨a, rfl⟩, fun _ hx => orderOf_of_mem_D hx,
    fun _ hx _ hy => orderOf_mul_mem_D hx hy, closure_D⟩

theorem pair_eq_D
    (E : Set J) (hE : CFSG.Blueprint.Fischer.Pair J E) : E = D := by
  obtain ⟨-, ⟨e, rfl⟩, h2, h3, -⟩ := hE
  have he : orderOf e = 2 := h2 e (IsConj.refl e)
  obtain ⟨g, hg⟩ := exists_conj_mem_slvl he
  have hte : IsConj e (g * e * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have hto : orderOf (g * e * g⁻¹) = 2 := by rw [orderOf_conj']; exact he
  have ht2 : (g * e * g⁻¹) ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one _
  have ht1 : g * e * g⁻¹ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hto; exact absurd hto (by norm_num)
  rcases invClass_of_mem hg ht2 ht1 with hD | ⟨w, hw⟩
  · have hae : IsConj a e := IsConj.trans hD hte.symm
    ext x
    exact ⟨fun h => hae.trans h, fun h => hae.symm.trans h⟩
  · exact absurd (h3 _ hte _ (hte.trans (isConj_iff.2 ⟨w, rfl⟩))) hw

theorem pair_iff
    (E : Set J) : CFSG.Blueprint.Fischer.Pair J E ↔ E = D :=
  ⟨pair_eq_D E, fun h => h ▸ pair_D⟩

theorem pair_eq_D_native
    (E : Set Blueprint.NativeSporadic.Fi22)
    (hE : CFSG.Blueprint.Fischer.Pair _ E) : E = fi22EquivJ.symm '' D := by
  have h := pair_eq_D _ (@CFSG.Fischer.pair_map Blueprint.NativeSporadic.Fi22 (↥J) inferInstance
    inferInstance E hE fi22EquivJ)
  calc E = fi22EquivJ.symm '' (fi22EquivJ '' E) := (CFSG.Fischer.image_symm_image _ _).symm
    _ = fi22EquivJ.symm '' D := by rw [h]

theorem pair_iff_native
    (E : Set Blueprint.NativeSporadic.Fi22) :
    CFSG.Blueprint.Fischer.Pair _ E ↔ E = fi22EquivJ.symm '' D :=
  ⟨pair_eq_D_native E, fun h => h ▸ @CFSG.Fischer.pair_map (↥J) Blueprint.NativeSporadic.Fi22
    inferInstance inferInstance D pair_D fi22EquivJ.symm⟩

end CFSG.Sporadic.Fi22
