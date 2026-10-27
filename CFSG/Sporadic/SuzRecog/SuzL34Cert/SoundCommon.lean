
module

public import CFSG.Sporadic.SuzRecog.SuzL34Cert.ChecksBase
public import CFSG.Monster.B.Co2.IsInvA
public import CFSG.Sporadic.SuzRecog.C1ModelT0
public import CFSG.Sporadic.SuzRecog.ModelGroupsKit

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert
open CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0
  CFSG.ComponentClassification.PSL3Four CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem permOK_of_tabRep {n : ℕ} {t : Tab} {g : Equiv.Perm (Fin n)} (ht : TabRep t g) :
    permOK n t = true := by
  have hrep : CFSG.Monster.B.Co2.Rep n t g := ht.2
  have hinv : CFSG.Monster.B.Co2.Rep n (CFSG.Monster.B.Co2.Native.invCand n t) g⁻¹ :=
    CFSG.Sporadic.SuzRecog.ModelGroups.rep_invCand hrep
  rw [permOK, ht.1]
  simp only [beq_self_eq_true, Bool.true_and]
  unfold CFSG.Monster.B.Co2.Native.isInvA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rw [hrep.apply hi]
    exact (g ⟨i, hi⟩).isLt
  · rw [hrep.apply hi, hinv.apply (g ⟨i, hi⟩).isLt]
    simp

theorem fixedCard_eq_filter (p : Equiv.Perm (Fin 1782)) :
    fixedCard p = (Finset.univ.filter fun x : Fin 1782 => p x = x).card := by
  rw [fixedCard, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

theorem tabRep_eq_idTab {t : Tab} {g : Equiv.Perm (Fin 1782)} (ht : TabRep t g) :
    t = idTab 1782 ↔ g = 1 :=
  @TabRep.eq_iff 1782 t (idTab 1782) g 1 ht (TabRep.idTab (n := 1782))

private theorem tabRep_comp_beq_idTab {t : Tab} {g : Equiv.Perm (Fin 1782)} (ht : TabRep t g) :
    (comp 1782 t t == idTab 1782) = true ↔ g * g = 1 :=
  @TabRep.beq_iff 1782 (comp 1782 t t) (idTab 1782) (g * g) 1
    (ht.comp ht) (TabRep.idTab (n := 1782))

theorem isInv_iff {t : Tab} {g : Equiv.Perm (Fin 1782)} (ht : TabRep t g) :
    isInv t = true ↔ g * g = 1 ∧ g ≠ 1 := by
  unfold isInv
  rw [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
  exact ⟨fun h => ⟨(tabRep_comp_beq_idTab ht).1 h.1,
      fun hg => h.2 ((tabRep_eq_idTab ht).2 hg)⟩,
    fun h => ⟨(tabRep_comp_beq_idTab ht).2 h.1,
      fun h' => h.2 ((tabRep_eq_idTab ht).1 h')⟩⟩

private theorem t0EnumOK :
    enumOK 1782 t0Tabs t0Enum = true :=
  t0_parts.1

private theorem v0EnumOK :
    enumOK 1782 v0Tabs v0Enum = true :=
  v0_parts.1

theorem t0Tabs_permOK :
    ∀ j < t0Tabs.size, permOK 1782 t0Tabs[j]! = true := by
  intro j hj
  have hsize : t0Tabs.size = 4 := Array.size_ofFn
  have hj4 : j < 4 := by simpa [hsize] using hj
  rw [t0Tabs_get hj4]
  exact permOK_of_tabRep (tabRep_t0Tab hj4)

theorem v0Tabs_permOK :
    ∀ j < v0Tabs.size, permOK 1782 v0Tabs[j]! = true := by
  intro j hj
  have hsize : v0Tabs.size = 7 := Array.size_ofFn
  have hj7 : j < 7 := by simpa [hsize] using hj
  have hget : v0Tabs[j]! = v0Tab j := by
    unfold v0Tabs
    rw [getElem!_pos _ _ (by simpa using hj7), Array.getElem_ofFn]
  rw [hget]
  exact permOK_of_tabRep (tabRep_v0Tab j)

theorem enumerates_t0Tabs :
    Enumerates (tabSubgroup t0Tabs) t0Enum.tabs.toList := by
  have hperm : ∀ j < t0Tabs.size, TabRep t0Tabs[j]! (permC 1782 t0Tabs[j]!) :=
    fun j hj => tabRep_of_permOK (t0Tabs_permOK j hj)
  have hA : ∀ a ∈ Set.range (fun i : Fin t0Tabs.size => permC 1782 t0Tabs[i.val]!),
      ∃ j < t0Tabs.size, TabRep t0Tabs[j]! a := by
    rintro a ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, hperm i.val i.isLt⟩
  have hgens : ∀ j < t0Tabs.size,
      ∃ a ∈ Set.range (fun i : Fin t0Tabs.size => permC 1782 t0Tabs[i.val]!),
        TabRep t0Tabs[j]! a := by
    intro j hj
    exact ⟨permC 1782 t0Tabs[j]!, ⟨⟨j, hj⟩, rfl⟩, hperm j hj⟩
  have h := enumerates_closure (E := t0Enum) (gens := t0Tabs)
    (A := Set.range fun i : Fin t0Tabs.size => permC 1782 t0Tabs[i.val]!) hA hgens t0EnumOK
  simpa [tabSubgroup] using h

theorem enumerates_v0Tabs :
    Enumerates (tabSubgroup v0Tabs) v0Enum.tabs.toList := by
  have hperm : ∀ j < v0Tabs.size, TabRep v0Tabs[j]! (permC 1782 v0Tabs[j]!) :=
    fun j hj => tabRep_of_permOK (v0Tabs_permOK j hj)
  have hA : ∀ a ∈ Set.range (fun i : Fin v0Tabs.size => permC 1782 v0Tabs[i.val]!),
      ∃ j < v0Tabs.size, TabRep v0Tabs[j]! a := by
    rintro a ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, hperm i.val i.isLt⟩
  have hgens : ∀ j < v0Tabs.size,
      ∃ a ∈ Set.range (fun i : Fin v0Tabs.size => permC 1782 v0Tabs[i.val]!),
        TabRep v0Tabs[j]! a := by
    intro j hj
    exact ⟨permC 1782 v0Tabs[j]!, ⟨⟨j, hj⟩, rfl⟩, hperm j hj⟩
  have h := enumerates_closure (E := v0Enum) (gens := v0Tabs)
    (A := Set.range fun i : Fin v0Tabs.size => permC 1782 v0Tabs[i.val]!) hA hgens v0EnumOK
  simpa [tabSubgroup] using h

private def idxFold (T : Array Tab) (m : ℕ) : Std.HashMap Tab Nat :=
  (List.range m).foldl (fun (r : Std.HashMap Tab Nat) k => r.insert T[k]! k)
    (Std.HashMap.emptyWithCapacity T.size)

private theorem idxFold_succ (T : Array Tab) (m : ℕ) :
    idxFold T (m + 1) = (idxFold T m).insert T[m]! m := by
  unfold idxFold
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem indexOf_eq_idxFold (T : Array Tab) : indexOf T = idxFold T T.size := by
  unfold indexOf idxFold
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem found_indexOf_of_mem {T : Array Tab} {x : Tab} (hx : x ∈ T.toList) :
    found (indexOf T) T x = true := by
  obtain ⟨k, hk, hkx⟩ := exists_getElem!_of_mem hx
  have key : ∀ m ≤ T.size, ∀ p < m,
      (idxFold T m).getD T[p]! T.size < m ∧
        T[(idxFold T m).getD T[p]! T.size]! = T[p]! := by
    intro m
    induction m with
    | zero => intro _ p hp; omega
    | succ m ih =>
      intro hm p hp
      have hm' : m ≤ T.size := by omega
      rw [idxFold_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
      · have hprev := ih hm' p hp
        have hins := Std.HashMap.getD_insert (m := idxFold T m) (k := T[m]!) (a := T[p]!)
          (v := m) (fallback := T.size)
        by_cases hbeq : T[m]! == T[p]!
        · rw [if_pos hbeq] at hins
          rw [hins]
          exact ⟨by omega, by rwa [beq_iff_eq] at hbeq⟩
        · rw [if_neg hbeq] at hins
          rw [hins]
          exact ⟨by omega, hprev.2⟩
      · rw [Std.HashMap.getD_insert_self]
        exact ⟨by omega, rfl⟩
  have hkey := key T.size le_rfl k hk
  rw [hkx] at hkey
  rw [indexOf_eq_idxFold]
  unfold found posOf
  rw [decide_eq_true_eq.mpr hkey.1, beq_iff_eq.mpr hkey.2]
  rfl

theorem mem_set_normalizer_of_finite {G : Type*} [Group G] {S : Set G} {g : G}
    (hfin : S.Finite) (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) :
    g ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    let f : G ↪ G :=
      ⟨fun y => g * y * g⁻¹, fun a b hab => by
        have := congrArg (fun z => g⁻¹ * z * g) hab
        simpa [mul_assoc] using this⟩
    have hsub : (f '' S) ⊆ S := by
      rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    have heq : f '' S = S := Set.map_eq_of_subset hsub hfin
    have hx' : f x ∈ f '' S := by rw [heq]; exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := f.injective hyx
    rwa [this] at hy

private def tbarInvs : Array Tab :=
  #[#[0, 1, 5, 4, 3, 2, 6, 7, 9, 8, 12, 13, 10, 11, 15, 14],
    #[0, 1, 4, 5, 2, 3, 6, 7, 15, 14, 11, 10, 13, 12, 9, 8]]

private theorem tbarIsInvA (k : ℕ) (hk : k < 2) :
    isInvA 16 (tbarTabs[k]!) (tbarInvs[k]!) = true := by
  interval_cases k <;>
    (apply isInvA_iff.2; intro j hj; interval_cases j <;> decide)

private theorem tbSize (k : ℕ) (hk : k < 2) : (tbarTabs[k]!).size = 16 := by
  interval_cases k <;> rfl

theorem f9_tabRep_tbar (k : ℕ) (hk : k < 2) :
    TabRep (tbarTabs[k]!) (tabPerm16 (tbarTabs[k]!)) :=
  ⟨tbSize k hk, (rep_permC (tbarIsInvA k hk)).1⟩

private theorem countP_range_getElem! {α : Type} [Inhabited α] (l : List α) (p : α → Bool) :
    (List.range l.length).countP (fun k => p l[k]!) = l.countP p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
      List.countP_cons]
    have h : ((fun k => p (a :: l)[k]!) ∘ Nat.succ) = (fun k => p l[k]!) := by
      funext k
      simp
    rw [h, ih]
    simp

theorem countBelow_eq_filter_size (T : Array Tab) (p : Tab → Bool) :
    countBelow T.size (fun k => p T[k]!) = (T.filter p).size := by
  rw [← Array.countP_eq_size_filter (p := p) (xs := T), ← Array.countP_toList]
  unfold countBelow
  rw [← List.countP_eq_length_filter, ← Array.length_toList]
  have h : (fun (k : Nat) => p T[k]!) = (fun k => p T.toList[k]!) := by
    funext k
    exact congrArg p (Array.getElem!_toList (xs := T) (i := k)).symm
  rw [h]
  exact countP_range_getElem! T.toList p

class L1TabsClosure : Prop where
  two_pow : allBelow 4
    (fun k => (l1Tabs ())[2 ^ k]! == (decs l1Decs)[k]!) = true
  permOK : allBelow (l1Tabs ()).size
    (fun k => permOK 1782 (l1Tabs ())[k]!) = true
  has_id : anyBelow (l1Tabs ()).size
    (fun k => (l1Tabs ())[k]! == idTab 1782) = true
  mul : allBelow (l1Tabs ()).size fun i =>
    allBelow (l1Tabs ()).size fun j =>
      anyBelow (l1Tabs ()).size fun k =>
        (l1Tabs ())[k]! == comp 1782 (l1Tabs ())[i]! (l1Tabs ())[j]!
  inv : allBelow (l1Tabs ()).size fun i =>
    anyBelow (l1Tabs ()).size fun k =>
      comp 1782 (l1Tabs ())[i]! (l1Tabs ())[k]! == idTab 1782
  nodup : (l1Tabs ()).toList.Nodup
  found : allBelow (l1Tabs ()).size
    (fun k => found (indexOf (l1Tabs ())) (l1Tabs ()) (l1Tabs ())[k]!) = true

private theorem l1TabsClosure_parts :
    (allBelow 4 (fun k => (l1Tabs ())[2 ^ k]! == (decs l1Decs)[k]!) = true) ∧
      (allBelow (l1Tabs ()).size (fun k => permOK 1782 (l1Tabs ())[k]!) = true) ∧
      (anyBelow (l1Tabs ()).size (fun k => (l1Tabs ())[k]! == idTab 1782) = true) ∧
      (allBelow (l1Tabs ()).size fun i =>
        allBelow (l1Tabs ()).size fun j =>
          anyBelow (l1Tabs ()).size fun k =>
            (l1Tabs ())[k]! == comp 1782 (l1Tabs ())[i]! (l1Tabs ())[j]!) ∧
      (allBelow (l1Tabs ()).size fun i =>
        anyBelow (l1Tabs ()).size fun k =>
          comp 1782 (l1Tabs ())[i]! (l1Tabs ())[k]! == idTab 1782) ∧
      (l1Tabs ()).toList.Nodup ∧
      (allBelow (l1Tabs ()).size
        (fun k => found (indexOf (l1Tabs ())) (l1Tabs ()) (l1Tabs ())[k]!) = true) := by
  have h := l1TabsClosureCheck_holds
  simpa only [l1TabsClosureCheck, Bool.and_eq_true, and_assoc, decide_eq_true_eq] using h

instance : L1TabsClosure where
  two_pow := l1TabsClosure_parts.1
  permOK := l1TabsClosure_parts.2.1
  has_id := l1TabsClosure_parts.2.2.1
  mul := l1TabsClosure_parts.2.2.2.1
  inv := l1TabsClosure_parts.2.2.2.2.1
  nodup := l1TabsClosure_parts.2.2.2.2.2.1
  found := l1TabsClosure_parts.2.2.2.2.2.2

theorem all_letter_bounds_l1Decs : l1Decs.all (fun d => d.1.all fun k => k < 10) = true := by
  decide

theorem all_coords_l1Decs : l1Decs.all (fun d => decide (d.2 < 128)) = true := by
  decide

theorem all_permOK_l1Decs :
    l1Decs.all (fun d => permOK 1782 (decTab d)) = true := by
  rw [List.all_eq_true]
  intro d hd
  exact permOK_of_tabRep (tabRep_decTab
    (fun k hk => of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp all_letter_bounds_l1Decs d hd) k hk))
    (of_decide_eq_true (List.all_eq_true.mp all_coords_l1Decs d hd)))

theorem all_letter_bounds_m1Decs : m1Decs.all (fun d => d.1.all fun k => k < 10) = true := by
  decide

theorem all_coords_m1Decs : m1Decs.all (fun d => decide (d.2 < 128)) = true := by
  decide

theorem all_permOK_m1Decs :
    m1Decs.all (fun d => permOK 1782 (decTab d)) = true := by
  rw [List.all_eq_true]
  intro d hd
  exact permOK_of_tabRep (tabRep_decTab
    (fun k hk => of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp all_letter_bounds_m1Decs d hd) k hk))
    (of_decide_eq_true (List.all_eq_true.mp all_coords_m1Decs d hd)))

theorem all_letter_bounds_nl1Decs : nl1Decs.all (fun d => d.1.all fun k => k < 10) = true := by
  decide

theorem all_coords_nl1Decs : nl1Decs.all (fun d => decide (d.2 < 128)) = true := by
  decide

theorem all_permOK_nl1Decs :
    nl1Decs.all (fun d => permOK 1782 (decTab d)) = true := by
  rw [List.all_eq_true]
  intro d hd
  exact permOK_of_tabRep (tabRep_decTab
    (fun k hk => of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp all_letter_bounds_nl1Decs d hd) k hk))
    (of_decide_eq_true (List.all_eq_true.mp all_coords_nl1Decs d hd)))

theorem tabRep_decTab_of_mem
    {l : List Dec}
    (h10 : l.all (fun d => d.1.all fun k => k < 10) = true)
    (h128 : l.all (fun d => decide (d.2 < 128)) = true)
    {d : Dec} (hd : d ∈ l) : TabRep (decTab d) (decPerm d) :=
  tabRep_decTab
    (fun k hk => of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h10 d hd) k hk))
    (of_decide_eq_true (List.all_eq_true.mp h128 d hd))

private theorem permOK_decTab_of_mem {l : List Dec}
    (hp : l.all (fun d => permOK 1782 (decTab d)) = true)
    {d : Dec} (hd : d ∈ l) : permOK 1782 (decTab d) = true :=
  List.all_eq_true.mp hp d hd

theorem permOK_decs_of_all {l : List Dec}
    (hp : l.all (fun d => permOK 1782 (decTab d)) = true)
    {j : Nat} (hj : j < (decs l).size) : permOK 1782 (decs l)[j]! = true := by
  have hmem : (decs l)[j]! ∈ l.map decTab := by
    simpa only [decs, List.toList_toArray] using getElem!_mem hj
  obtain ⟨d, hd, hdec⟩ := List.mem_map.mp hmem
  rw [← hdec]
  exact permOK_decTab_of_mem hp hd

theorem permC_eq_decPerm
    {l : List Dec}
    (h10 : l.all (fun d => d.1.all fun k => k < 10) = true)
    (h128 : l.all (fun d => decide (d.2 < 128)) = true)
    (hp : l.all (fun d => permOK 1782 (decTab d)) = true)
    {d : Dec} (hd : d ∈ l) : permC 1782 (decTab d) = decPerm d :=
  (tabRep_of_permOK (permOK_decTab_of_mem hp hd)).perm_eq
    (tabRep_decTab_of_mem h10 h128 hd)

theorem decTab_mem_decs {l : List Dec} {d : Dec} (hd : d ∈ l) :
    ∃ i < (decs l).size, (decs l)[i]! = decTab d := by
  have hmem : decTab d ∈ (decs l).toList := by
    simp only [decs, List.toList_toArray]
    exact List.mem_map_of_mem hd
  exact exists_getElem!_of_mem hmem

private theorem range_decs_eq_decPerm_image {l : List Dec}
    (h : ∀ d ∈ l, permC 1782 (decTab d) = decPerm d) :
    Set.range (fun i : Fin (decs l).size => permC 1782 (decs l)[i]!) =
      decPerm '' {d : Dec | d ∈ l} := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    have hmem : (decs l)[i.val]! ∈ (decs l).toList := getElem!_mem i.isLt
    have hmem' : (decs l)[i.val]! ∈ l.map decTab := by
      simpa only [decs, List.toList_toArray] using hmem
    obtain ⟨d, hd, hdec⟩ := List.mem_map.mp hmem'
    exact ⟨d, hd, by
      change decPerm d = permC 1782 (decs l)[i.val]!
      rw [← hdec, h d hd]⟩
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨i, hi, hdi⟩ := decTab_mem_decs hd
    exact ⟨⟨i, hi⟩, by
      change permC 1782 (decs l)[i]! = decPerm d
      rw [hdi, h d hd]⟩

theorem decSubgroup_eq_tabSubgroup {l : List Dec}
    (h : ∀ d ∈ l, permC 1782 (decTab d) = decPerm d) :
    decSubgroup l = tabSubgroup (decs l) := by
  change Subgroup.closure (decPerm '' {d : Dec | d ∈ l}) =
    Subgroup.closure (Set.range fun i : Fin (decs l).size => permC 1782 (decs l)[i]!)
  exact congrArg Subgroup.closure (range_decs_eq_decPerm_image (l := l) h).symm

private theorem decs_getElem {l : List Dec} {i : ℕ} (hi : i < l.length) :
    (decs l)[i]! = decTab l[i] := by
  have hsize : (decs l).size = l.length := by simp [decs]
  rw [getElem!_pos _ _ (by simpa [hsize] using hi)]
  simp only [decs]
  rw [List.getElem_toArray]
  simp

theorem decs_getD {l : List Dec} {i : ℕ} (d : Dec) (hi : i < l.length) :
    (decs l)[i]! = decTab (l.getD i d) := by
  rw [decs_getElem hi, ← List.getD_eq_getElem l d hi]

theorem comm_of_tab_comm {t s : Tab} {g h : Equiv.Perm (Fin 1782)}
    (ht : TabRep t g) (hs : TabRep s h) (hc : comp 1782 t s = comp 1782 s t) :
    g * h = h * g := by
  refine (ht.comp hs).perm_eq ?_
  rw [hc]
  exact hs.comp ht

theorem commAll_iff {t : Tab} {g : Equiv.Perm (Fin 1782)} (ht : TabRep t g)
    {gens : Array Tab} {f : ℕ → Equiv.Perm (Fin 1782)}
    (hf : ∀ i < gens.size, TabRep gens[i]! (f i)) :
    commAll t gens = true ↔ ∀ i < gens.size, g * f i = f i * g := by
  rw [commAll, ← Array.all_toList, List.all_eq_true]
  constructor
  · intro h i hi
    exact comm_of_tab_comm ht (hf i hi) (beq_iff_eq.mp (h gens[i]! (getElem!_mem hi))).symm
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem hx
    exact (((hf i hi).comp ht).beq_iff (ht.comp (hf i hi))).2 (h i hi).symm

theorem enumerates_decSubgroup
    {l : List Dec} {E : Enum}
    (h10 : l.all (fun d => d.1.all fun k => k < 10) = true)
    (h128 : l.all (fun d => decide (d.2 < 128)) = true)
    (hp : l.all (fun d => permOK 1782 (decTab d)) = true)
    (hE : enumOK 1782 (decs l) E = true) :
    Enumerates (decSubgroup l) E.tabs.toList := by
  have hperm : ∀ j < (decs l).size, TabRep (decs l)[j]! (permC 1782 (decs l)[j]!) :=
    fun j hj => tabRep_of_permOK (permOK_decs_of_all hp hj)
  have hbridge : ∀ d ∈ l, permC 1782 (decTab d) = decPerm d :=
    fun d hd => permC_eq_decPerm h10 h128 hp hd
  have hcl := enumerates_closure (E := E) (gens := decs l)
    (A := Set.range fun i : Fin (decs l).size => permC 1782 (decs l)[i]!)
    (fun a ha => by
      obtain ⟨i, rfl⟩ := ha
      exact ⟨i.val, i.isLt, hperm i.val i.isLt⟩)
    (fun j hj => ⟨permC 1782 (decs l)[j]!, ⟨⟨j, hj⟩, rfl⟩, hperm j hj⟩) hE
  change Enumerates (tabSubgroup (decs l)) E.tabs.toList at hcl
  rwa [← decSubgroup_eq_tabSubgroup hbridge] at hcl

theorem getElem!_ofFn_gen {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

theorem tabRep_basis_l1
    {k : Nat} (hk : k < (decs l1Decs).size) :
    TabRep (decs l1Decs)[k]! (permC 1782 (decs l1Decs)[k]!) :=
  tabRep_of_permOK (permOK_decs_of_all all_permOK_l1Decs hk)

private theorem mem_basis_l1
    {k : Nat} (hk : k < (decs l1Decs).size) :
    permC 1782 (decs l1Decs)[k]! ∈ decSubgroup l1Decs := by
  have hmem : (decs l1Decs)[k]! ∈ l1Decs.map decTab := by
    simpa only [decs, List.toList_toArray] using getElem!_mem hk
  obtain ⟨d, hd, hdec⟩ := List.mem_map.mp hmem
  rw [← hdec, permC_eq_decPerm all_letter_bounds_l1Decs all_coords_l1Decs
    all_permOK_l1Decs hd]
  exact Subgroup.subset_closure ⟨d, hd, rfl⟩

private theorem bitProd_foldl_mem
    (i : Nat) (r : Tab) (g : Equiv.Perm (Fin 1782))
    (hr : TabRep r g) (hg : g ∈ decSubgroup l1Decs) :
    ∀ ks : List Nat, (∀ k ∈ ks, k < (decs l1Decs).size) →
      ∃ g' ∈ decSubgroup l1Decs,
        TabRep (ks.foldl (fun r k => if i.testBit k then comp 1782 r (decs l1Decs)[k]! else r) r) g'
  | [], _ => ⟨g, hg, hr⟩
  | k :: ks, hk => by
    rw [List.foldl_cons]
    have hk' := hk k (List.mem_cons_self ..)
    by_cases hb : i.testBit k = true
    · rw [if_pos hb]
      exact bitProd_foldl_mem i (comp 1782 r (decs l1Decs)[k]!)
        (g * permC 1782 (decs l1Decs)[k]!) (hr.comp (tabRep_basis_l1 hk'))
        (mul_mem hg (mem_basis_l1 hk')) ks
        (fun j hj => hk j (List.mem_cons_of_mem k hj))
    · rw [if_neg hb]
      exact bitProd_foldl_mem i r g hr hg ks
        (fun j hj => hk j (List.mem_cons_of_mem k hj))

private theorem bitProd_mem
    (i : Nat) :
    ∃ g ∈ decSubgroup l1Decs, TabRep (bitProd (decs l1Decs) i) g := by
  unfold bitProd
  exact bitProd_foldl_mem i (idTab 1782) 1 TabRep.idTab (Subgroup.one_mem _)
    (List.range (decs l1Decs).size) (fun k hk => List.mem_range.mp hk)

theorem l1Tabs_size : (l1Tabs ()).size = 16 := Array.size_ofFn

theorem l1Tabs_getElem! {i : Nat} (hi : i < (l1Tabs ()).size) :
    (l1Tabs ())[i]! = bitProd (decs l1Decs) i := by
  have hi16 : i < 16 := by simpa [l1Tabs_size] using hi
  unfold l1Tabs
  rw [getElem!_ofFn_gen (fun i : Fin 16 => bitProd (decs l1Decs) i.val) hi16]

private theorem l1Tabs_two_pow (k : Nat) (hk : k < 4) :
    (l1Tabs ())[2 ^ k]! = (decs l1Decs)[k]! := by
  have := allBelow_eq_true.mp (L1TabsClosure.two_pow (self := inferInstance)) k hk
  rwa [beq_iff_eq] at this

private theorem l1Tabs_permOK : allBelow (l1Tabs ()).size
    (fun k => permOK 1782 (l1Tabs ())[k]!) = true :=
  L1TabsClosure.permOK

private theorem l1Tabs_tabRep (k : Nat) (hk : k < (l1Tabs ()).size) :
    TabRep (l1Tabs ())[k]! (permC 1782 (l1Tabs ())[k]!) :=
  tabRep_of_permOK (allBelow_eq_true.mp l1Tabs_permOK k hk)

private theorem l1Tabs_has_id : anyBelow (l1Tabs ()).size
    (fun k => (l1Tabs ())[k]! == idTab 1782) = true :=
  L1TabsClosure.has_id

private theorem l1Tabs_mul : allBelow (l1Tabs ()).size fun i =>
    allBelow (l1Tabs ()).size fun j =>
      anyBelow (l1Tabs ()).size fun k =>
        (l1Tabs ())[k]! == comp 1782 (l1Tabs ())[i]! (l1Tabs ())[j]! :=
  L1TabsClosure.mul

private theorem l1Tabs_inv : allBelow (l1Tabs ()).size fun i =>
    anyBelow (l1Tabs ()).size fun k =>
      comp 1782 (l1Tabs ())[i]! (l1Tabs ())[k]! == idTab 1782 :=
  L1TabsClosure.inv

private theorem l1Tabs_nodup : (l1Tabs ()).toList.Nodup :=
  L1TabsClosure.nodup

private theorem l1Tabs_found :
    allBelow (l1Tabs ()).size
      (fun k => found (indexOf (l1Tabs ())) (l1Tabs ()) (l1Tabs ())[k]!) = true :=
  L1TabsClosure.found

theorem enumerates_l1Tabs :
    Enumerates (decSubgroup l1Decs) (l1Tabs ()).toList := by
  have hid : ∃ t ∈ (l1Tabs ()).toList, TabRep t (1 : Equiv.Perm (Fin 1782)) := by
    obtain ⟨k, hk, hkEq⟩ := anyBelow_eq_true.mp l1Tabs_has_id
    rw [beq_iff_eq] at hkEq
    exact ⟨(l1Tabs ())[k]!, getElem!_mem hk, by rw [hkEq]; exact TabRep.idTab⟩
  refine ⟨?_, ?_, l1Tabs_nodup⟩
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
    rw [l1Tabs_getElem! hi]
    exact bitProd_mem i
  · intro g hg
    refine Subgroup.closure_induction (p := fun g _ => ∃ t ∈ (l1Tabs ()).toList, TabRep t g)
      ?_ hid ?_ ?_ hg
    · rintro g ⟨d, hd, rfl⟩
      obtain ⟨i, hi, hdi⟩ := decTab_mem_decs (l := l1Decs) hd
      have hi4 : i < 4 := by
        have hlen : l1Decs.length = 4 := rfl
        simpa [decs, hlen] using hi
      have h2i : 2 ^ i < (l1Tabs ()).size := by
        rw [l1Tabs_size]; interval_cases i <;> norm_num
      refine ⟨(l1Tabs ())[2 ^ i]!, getElem!_mem h2i, ?_⟩
      rw [l1Tabs_two_pow i hi4, hdi]
      exact tabRep_decTab_of_mem all_letter_bounds_l1Decs all_coords_l1Decs hd
    · rintro a b _ _ ⟨ta, hta, hra⟩ ⟨tb, htb, hrb⟩
      obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem hta
      obtain ⟨j, hj, rfl⟩ := exists_getElem!_of_mem htb
      obtain ⟨k, hk, hkEq⟩ :=
        anyBelow_eq_true.mp (allBelow_eq_true.mp (allBelow_eq_true.mp l1Tabs_mul i hi) j hj)
      rw [beq_iff_eq] at hkEq
      exact ⟨(l1Tabs ())[k]!, getElem!_mem hk, by
        rw [hkEq]; exact hra.comp hrb⟩
    · rintro a _ ⟨ta, hta, hra⟩
      obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem hta
      obtain ⟨k, hk, hkEq⟩ := anyBelow_eq_true.mp (allBelow_eq_true.mp l1Tabs_inv i hi)
      rw [beq_iff_eq] at hkEq
      refine ⟨(l1Tabs ())[k]!, getElem!_mem hk, ?_⟩
      have hcomp : TabRep (comp 1782 (l1Tabs ())[i]! (l1Tabs ())[k]!)
          (a * permC 1782 (l1Tabs ())[k]!) :=
        hra.comp (l1Tabs_tabRep k hk)
      rw [hkEq] at hcomp
      have hone : a * permC 1782 (l1Tabs ())[k]! = 1 :=
        (tabRep_eq_idTab hcomp).1 rfl
      have haeq : a = (permC 1782 (l1Tabs ())[k]!)⁻¹ :=
        eq_inv_of_mul_eq_one_left hone
      rw [haeq, inv_inv]
      exact l1Tabs_tabRep k hk

theorem found_l1Tabs_of_mem
    {t : Tab} {g : Equiv.Perm (Fin 1782)} (hrep : TabRep t g)
    (hg : g ∈ decSubgroup l1Decs) :
    found (indexOf (l1Tabs ())) (l1Tabs ()) t = true := by
  obtain ⟨t', ht', hrep'⟩ := enumerates_l1Tabs.complete g hg
  have htt : t = t' := hrep.tab_eq hrep'
  obtain ⟨k, hk, hk'eq⟩ := exists_getElem!_of_mem ht'
  have hf := allBelow_eq_true.mp l1Tabs_found k hk
  rwa [hk'eq, ← htt] at hf

theorem mem_of_found_l1Tabs
    {t : Tab} {g : Equiv.Perm (Fin 1782)} (hrep : TabRep t g)
    (h : found (indexOf (l1Tabs ())) (l1Tabs ()) t = true) :
    g ∈ decSubgroup l1Decs := by
  obtain ⟨g', hg', hrep'⟩ := enumerates_l1Tabs.sound t (mem_of_found h)
  rwa [← hrep.perm_eq hrep'] at hg'

end CFSG.Sporadic.SuzRecog.SuzL34Cert
