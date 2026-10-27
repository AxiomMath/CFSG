module

public import CFSG.Sporadic.Fi23.Pair
public import CFSG.Sporadic.Fi23.ClassesCert
public import CFSG.Fischer.Pairs

public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev LS : Array Table := sylLetters letters

noncomputable abbrev TS : Array Tree := chainTrees 31671 LS sylBase

noncomputable abbrev tabS (i : ℕ) : Array Table := treeTabs 31671 TS[i]! LS

noncomputable abbrev WS : Array (Table × Table × Table) := conjTabs orb (dTab orb)

theorem classes_parts :
    (∀ w ∈ sylWords, ∀ z ∈ w, z.toNat < letters.size) ∧
    chainOK 31671 LS sylBase chainQ sylQb TS 3 = true ∧ orbitSizes TS = [512, 512] ∧
    (∀ W ∈ WS, invOK 31671 W.1 W.2.1 = true) ∧
    ∀ k < (tabS 0).size, ∀ B ∈ tabS 1, pairOK WS (tabS 0)[k]! B = true := by
  have h : sylChecks orb 3 = true := classes_certificate
  unfold sylChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true',
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun k hk => Array.all_eq_true'.1 (parAll_eq_true h5 k hk)⟩

@[expose] noncomputable def jG (z : ℤ) : J := pairG gs z.toNat

theorem rep_jGen
    {z : ℤ} (hz : z.toNat < letters.size) : Rep 31671 (jGen letters z) (jG z) :=
  rep_pairG_all _ hz

@[expose] noncomputable def sylG (j : ℕ) : J := wordG jG sylWords[j]!

theorem LS_size : LS.size = 2 * sylWords.size := by
  unfold LS sylLetters buildLetters; simp

theorem LS_even {j : ℕ} (hj : j < sylWords.size) :
    LS[2 * j]! = wordT 31671 (jGen letters) sylWords[j]! := by
  unfold LS sylLetters buildLetters
  rw [getElem!_pos _ (2 * j) (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [ite_eq_left (by omega)]
  congr 2
  omega

theorem rep_LS :
    ∀ j < LS.size / 2, Rep 31671 LS[2 * j]! (sylG j) := by
  intro j hj
  rw [LS_size] at hj
  have hj' : j < sylWords.size := by omega
  have hmem : sylWords[j]! ∈ sylWords := by
    rw [getElem!_pos sylWords j hj']; exact Array.getElem_mem hj'
  rw [LS_even hj']
  exact Rep.wordT (by norm_num) _ fun z hz => rep_jGen (classes_parts.1 _ hmem z hz)

theorem LS_parts : LS.size % 2 = 0 ∧
    ∀ j < LS.size / 2, invOK 31671 LS[2 * j]! LS[2 * j + 1]! = true :=
  ⟨(chainOK_parts classes_parts.2.1).1, (chainOK_parts classes_parts.2.1).2.1⟩

theorem rep_LS_all :
    ∀ l < LS.size, Rep 31671 LS[l]! (pairG sylG l) :=
  rep_pairG rep_LS LS_parts.1 LS_parts.2

noncomputable abbrev slvl
    (i : ℕ) : Subgroup J := levelGroup LS sylBase (pairG sylG) i

theorem syl_facts :
    (∀ i < sylBase.size, TreeFacts 31671 TS[i]! (levelLetters LS sylBase i) (pairG sylG)
      sylBase[i]!) ∧
      (∀ i < sylBase.size, ∀ g ∈ slvl i,
        idx 31671 g sylBase[i]! = sylBase[i]! ↔ g ∈ slvl (i + 1)) ∧
      ∀ i ≤ sylBase.size, Nat.card (slvl i) =
        ∏ l ∈ Finset.Ico i sylBase.size, TS[l]!.pts.size :=
  chain_facts rep_LS sep classes_parts.2.1

theorem sylBase_size : sylBase.size = 2 := rfl

theorem TS_size
    {l v : ℕ} (hv : [512, 512][l]? = some v) : TS[l]!.pts.size = v := by
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
    Nat.card (slvl 0) = 262144 := by
  rw [syl_facts.2.2 0 (by rw [sylBase_size]; norm_num), sylBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 2, TS[l]!.pts.size = [512, 512].getD l 0 := fun l hl =>
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
  obtain ⟨k, hk, hkp⟩ := (hT.mem_orbit_iff (g • (⟨sylBase[i]!, hT.r_lt⟩ : Fin 31671))).1
    ⟨⟨g, hg⟩, rfl⟩
  set t := treeG TS[i]! (pairG sylG) k with ht
  refine ⟨k, hk, t⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hmem : t⁻¹ * g ∈ slvl i := (slvl i).mul_mem ((slvl i).inv_mem (hT.treeG_mem hk)) hg
  refine (syl_facts.2.1 i hi _ hmem).1 ?_
  have e : idx 31671 g sylBase[i]! = idx 31671 t sylBase[i]! := by
    rw [ht, hT.elt k hk, hkp]
    exact (smul_val_eq_idx (n := 31671) g ⟨sylBase[i]!, hT.r_lt⟩).symm
  rw [idx_mul, e, idx_inv_idx]

theorem walkFacts_TS
    {i : ℕ} (hi : i < sylBase.size) :
    WalkFacts 31671 TS[i]! LS (pairG sylG) := by
  intro k hk hk0
  obtain ⟨hpar, hlab⟩ := (syl_facts.1 i hi).par k hk hk0
  have hl := levelLetters_lt hlab
  refine ⟨hpar, rep_LS_all _ hl, ?_⟩
  rw [← pairG_invL]
  exact rep_LS_all _ (invL_lt LS_parts.1 hl)

theorem range_get_31671 {t : ℕ} (ht : t < 31671) : (Array.range 31671)[t]! = t := by
  rw [getElem!_pos _ t (by simpa using ht), Array.getElem_range]

theorem tabS_size (i : ℕ) : (tabS i).size = TS[i]!.pts.size := by
  unfold tabS treeTabs; simp

theorem rep_tabS
    {i : ℕ} (hi : i < sylBase.size) {k : ℕ} (hk : k < TS[i]!.pts.size) :
    Rep 31671 (tabS i)[k]! (treeG TS[i]! (pairG sylG) k) := by
  obtain ⟨hs, he⟩ := walk_spec (walkFacts_TS hi) hk (Array.range 31671)
    (fun t ht => by rw [range_get_31671 (by simpa using ht)]; simpa using ht)
  have e1 : (tabS i)[k]! = (walk TS[i]! LS k (Array.range 31671)).map UInt32.ofNat := by
    unfold tabS treeTabs
    rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  intro j hj
  have hj' : j < (Array.range 31671).size := by simpa using hj
  have hw := he j hj'
  rw [range_get_31671 hj] at hw
  rw [e1]
  unfold ap
  rw [getElem!_pos _ j (by simp [hs]; exact hj), Array.getElem_map,
    ← getElem!_pos _ j (by rw [hs]; exact hj'), hw, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (lt_trans (idx_lt _ hj) (by norm_num))]

@[expose] def InvClass (g : J) : Prop :=
  g ^ 2 = 1 → g ≠ 1 → IsConj d g ∨ ∃ w : J, orderOf (g * (w * g * w⁻¹)) ∉ ({1, 2, 3} : Set ℕ)

theorem isIdT_of_eq_one
    {P : Table} {g : J} (hP : Rep 31671 P g) (h : g = 1) :
    isIdT P = true := by
  unfold isIdT
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, h, idx_one]

theorem invoOK_of_sq
    {P : Table} {g : J} (hP : Rep 31671 P g) (h : g ^ 2 = 1) :
    invoOK 31671 P = true := by
  unfold invoOK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, hP _ (idx_lt g hi), ← idx_mul, ← pow_two, h, idx_one]

theorem order3OK_of_cube
    {P : Table} {g : J} (hP : Rep 31671 P g) (h : g ^ 3 = 1) :
    order3OK 31671 P = true := by
  unfold order3OK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, hP _ (idx_lt g hi), hP _ (idx_lt g (idx_lt g hi)), ← idx_mul,
    ← idx_mul, ← pow_three', h, idx_one]

theorem cube_of_order3OK {P : Table} {g : J} (hP : Rep 31671 P g)
    (h : order3OK 31671 P = true) : g ^ 3 = 1 :=
  eq_one_of_fix_all fun i => Fin.ext <| (smul_val_eq_idx (n := 31671) (g ^ 3) i).trans
    (idx_cube_of_order3OK hP h i.val i.isLt)

theorem invo2OK_of_sq
    {A B : Table} {x y : J} (hA : Rep 31671 A x) (hB : Rep 31671 B y)
    (h : (x * y) ^ 2 = 1) : invo2OK 31671 A B = true := by
  unfold invo2OK
  rw [allIn_eq_true]
  intro i _ hi
  have h1 := idx_lt y hi
  have h2 := idx_lt x h1
  have h3 := idx_lt y h2
  have e : x * y * x * y = 1 := by rw [← h, pow_two]; simp only [mul_assoc]
  rw [beq_iff_eq, hB i hi, hA _ h1, hB _ h2, hA _ h3, ← idx_mul, ← idx_mul, ← idx_mul, e,
    idx_one]

theorem isConj_of_cube
    {g c : J} (hc : IsConj d c) (hg : g ^ 2 = 1) (h : (g * c) ^ 3 = 1) :
    IsConj d g := by
  have hc2 : c * c = 1 := by
    rw [← pow_two, ← orderOf_of_isConj hc, pow_orderOf_eq_one]
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

theorem wordG_dLetters : wordG genG dLetters = wordJ dWord := by
  unfold wordG dLetters wordJ
  rw [List.map_map]
  exact congrArg List.prod
    (List.map_congr_left fun x _ => by by_cases hx : x = 0 <;> simp [hx, genG])

theorem rep_dTab : Rep 31671 (dTab orb) d := by
  have h := Rep.powT (by norm_num)
    (Rep.wordT (n := 31671) (by norm_num) dLetters fun l _ => rep_gen l) 7
  rw [wordG_dLetters] at h
  exact h

theorem rep_WS
    {W : Table × Table × Table} (hW : W ∈ WS) :
    ∃ w : J, Rep 31671 W.1 w ∧ Rep 31671 W.2.1 w⁻¹ ∧ Rep 31671 W.2.2 (w * d * w⁻¹) := by
  have hinv := classes_parts.2.2.2.1 W hW
  unfold WS conjTabs at hW
  obtain ⟨u, -, rfl⟩ := Array.mem_map.1 hW
  dsimp only at hinv ⊢
  have h1 : Rep 31671 (wordT 31671 (genTables orb) u) (wordG genG u) :=
    Rep.wordT (by norm_num) _ fun l _ => rep_gen l
  have h2 : Rep 31671 (invT 31671 (wordT 31671 (genTables orb) u)) (wordG genG u)⁻¹ :=
    Rep.inv_of_invOK h1 hinv
  have h3 : Rep 31671 (compT 31671 (wordT 31671 (genTables orb) u)
      (compT 31671 (dTab orb) (invT 31671 (wordT 31671 (genTables orb) u))))
      (wordG genG u * d * (wordG genG u)⁻¹) := by
    rw [mul_assoc]
    exact Rep.compT h1 (Rep.compT rep_dTab h2)
  exact ⟨_, h1, h2, h3⟩

theorem invClass_of_leafOK
    {P : Table} {g : J} (hP : Rep 31671 P g)
    (h : leafOK WS P = true) : InvClass g := by
  intro hg2 hg1
  unfold leafOK at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', Array.any_eq_true', Bool.and_eq_true] at h
  rcases h with h | ⟨W, hW, h | ⟨⟨h1, h2⟩, h3⟩⟩
  · exact absurd (eq_one_of_isIdT hP h) hg1
  · obtain ⟨w, -, -, hw3⟩ := rep_WS hW
    exact Or.inl (isConj_of_cube (isConj_iff.2 ⟨w, rfl⟩) hg2
      (cube_of_order3OK (Rep.compT hP hw3) h))
  · right
    obtain ⟨w, hw1, hw2, -⟩ := rep_WS hW
    have hR := Rep.compT hP (Rep.compT (Rep.compT hw1 hP) hw2)
    refine ⟨w, orderOf_notMem (fun e => ?_) (fun e => ?_) (fun e => ?_)⟩
    · rw [isIdT_of_eq_one hR e] at h1; exact absurd h1 (by decide)
    · rw [invoOK_of_sq hR e] at h2; exact absurd h2 (by decide)
    · rw [order3OK_of_cube hR e] at h3; exact absurd h3 (by decide)

theorem invClass_of_pairOK
    {A B : Table} {x y : J} (hA : Rep 31671 A x) (hB : Rep 31671 B y)
    (h : pairOK WS A B = true) : InvClass (x * y) := by
  intro hg2 hg1
  unfold pairOK at h
  rw [invo2OK_of_sq hA hB hg2, Bool.not_true, Bool.false_or] at h
  exact invClass_of_leafOK (Rep.compT hA hB) h hg2 hg1

theorem invClass_of_mem
    {g : J} (hg : g ∈ slvl 0) : InvClass g := by
  obtain ⟨k0, hk0, h, hh, rfl⟩ := exists_tree_mul (i := 0) (by rw [sylBase_size]; norm_num) hg
  obtain ⟨k1, hk1, h', hh', rfl⟩ := exists_tree_mul (i := 1) (by rw [sylBase_size]; norm_num) hh
  have hh'' : h' ∈ slvl 2 := hh'
  rw [slvl_two, Subgroup.mem_bot] at hh''
  rw [hh'', mul_one]
  have hmem : (tabS 1)[k1]! ∈ tabS 1 := by
    rw [getElem!_pos _ k1 (by rw [tabS_size]; exact hk1)]; exact Array.getElem_mem _
  exact invClass_of_pairOK (rep_tabS (by rw [sylBase_size]; norm_num) hk0)
    (rep_tabS (by rw [sylBase_size]; norm_num) hk1)
    (classes_parts.2.2.2.2 k0 (by rw [tabS_size]; exact hk0) _ hmem)

theorem slvl_index :
    (slvl 0).index = 15600091832325 := by
  have h := (slvl 0).card_mul_index
  rw [card_slvl_zero, card_J] at h
  omega

open scoped Pointwise in
theorem exists_conj_mem_slvl
    {e : J} (he : orderOf e = 2) : ∃ g : J, g * e * g⁻¹ ∈ slvl 0 := by
  have hT : IsPGroup 2 (slvl 0) := IsPGroup.of_card (n := 18) (by rw [card_slvl_zero]; norm_num)
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

theorem pair_eq_D23
    (E : Set J) (hE : CFSG.Blueprint.Fischer.Pair J E) :
    E = {x : J | IsConj d x} := by
  obtain ⟨-, ⟨e, rfl⟩, h2, h3, -⟩ := hE
  have he : orderOf e = 2 := h2 e (IsConj.refl e)
  obtain ⟨g, hg⟩ := exists_conj_mem_slvl he
  have hte : IsConj e (g * e * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have hto : orderOf (g * e * g⁻¹) = 2 := by rw [orderOf_conj]; exact he
  have ht2 : (g * e * g⁻¹) ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one _
  have ht1 : g * e * g⁻¹ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hto; exact absurd hto (by norm_num)
  rcases invClass_of_mem hg ht2 ht1 with hD | ⟨w, hw⟩
  · have hde : IsConj d e := IsConj.trans hD hte.symm
    ext x
    exact ⟨fun h => hde.trans h, fun h => hde.symm.trans h⟩
  · exact absurd (h3 _ hte _ (hte.trans (isConj_iff.2 ⟨w, rfl⟩))) hw

theorem pair_iff_D23 (E : Set J) :
    CFSG.Blueprint.Fischer.Pair J E ↔ E = {x : J | IsConj d x} :=
  ⟨pair_eq_D23 E, fun h => h ▸ pair_J⟩

theorem pair_eq_D23_native
    (E : Set Blueprint.NativeSporadic.Fi23)
    (hE : CFSG.Blueprint.Fischer.Pair _ E) : E = {x | IsConj dFi23 x} := by
  have h := pair_eq_D23 _ (@CFSG.Fischer.pair_map Blueprint.NativeSporadic.Fi23 (↥J) inferInstance
    inferInstance E hE fi23EquivJ)
  ext x
  show x ∈ E ↔ IsConj (fi23EquivJ.toEquiv.symm d) x
  rw [isConj_symm_iff fi23EquivJ.toEquiv (map_mul fi23EquivJ) d x]
  have hx : fi23EquivJ.toEquiv x ∈ fi23EquivJ '' E ↔ x ∈ E :=
    ⟨fun ⟨y, hy, e⟩ => fi23EquivJ.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  rw [← hx, h]
  rfl

theorem pair_iff_D23_native
    (E : Set Blueprint.NativeSporadic.Fi23) :
    CFSG.Blueprint.Fischer.Pair _ E ↔ E = {x | IsConj dFi23 x} :=
  ⟨pair_eq_D23_native E, fun h => h ▸ pair_Fi23⟩

end CFSG.Sporadic.Fi23
