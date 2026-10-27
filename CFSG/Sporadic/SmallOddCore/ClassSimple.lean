
module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutionsBase

public noncomputable section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def wordTabS (m : Nat) (gs : Array Tab) (w : List Nat) : Tab :=
  w.foldr (fun j acc => comp m gs[j]! acc) (idTab m)

@[expose] def coverAllOK (T : Array Tab) (O : Array Enum) : Bool :=
  let idxs := O.map fun e => indexOf e.tabs
  allBelow T.size fun k => anyBelow O.size fun l => found idxs[l]! O[l]!.tabs T[k]!

@[expose] def commAll (n : Nat) (gs : Array Tab) (t : Tab) : Bool :=
  allBelow gs.size fun i => comp n t gs[i]! == comp n gs[i]! t

theorem getElem!_map_eq {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (A : Array α)
    {l : ℕ} (hl : l < A.size) : (A.map f)[l]! = f A[l]! := by
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, ← getElem!_pos A l hl]

theorem cover_of_coverAllOK {T : Array Tab} {O : Array Enum} (h : coverAllOK T O = true) :
    ∀ k < T.size, ∃ l < O.size, found (indexOf O[l]!.tabs) O[l]!.tabs T[k]! = true := by
  intro k hk
  simp only [coverAllOK, allBelow_eq_true, anyBelow_eq_true] at h
  obtain ⟨l, hl, hf⟩ := h k hk
  rw [getElem!_map_eq _ _ hl] at hf
  exact ⟨l, hl, hf⟩

theorem tabRep_wordTabS {m : ℕ} {gs : Array Tab} {f : ℕ → Equiv.Perm (Fin m)}
    (hgs : ∀ j < gs.size, TabRep gs[j]! (f j)) :
    ∀ w : List ℕ, (∀ j ∈ w, j < gs.size) → TabRep (wordTabS m gs w) ((w.map f).prod)
  | [], _ => by simpa [wordTabS] using (TabRep.idTab (n := m))
  | j :: w, hw => by
    have h1 : wordTabS m gs (j :: w) = comp m gs[j]! (wordTabS m gs w) := by
      simp only [wordTabS, List.foldr_cons]
    rw [h1, List.map_cons, List.prod_cons]
    exact (hgs j (hw j (List.mem_cons_self))).comp
      (tabRep_wordTabS hgs w fun i hi => hw i (List.mem_cons_of_mem _ hi))

structure ClassCert (m : ℕ) (gens ginv : Array Tab) (E : Enum) (c : ℕ) (words : List (List ℕ))
    (sizes : List ℕ) (orbits : Array Enum) : Prop where
  enum : enumOK m gens E = true
  words_lt : ∀ l < c, ∀ j ∈ words.getD l [], j < gens.size
  rep0 : wordTabS m gens (words.getD 0 []) = idTab m
  orbit : ∀ l < c, orbitOK m gens ginv (wordTabS m gens (words.getD l [])) orbits[l]! = true ∧
    orbits[l]!.tabs.size = sizes.getD l 0
  notIn : ∀ l < c, ∀ l' < c, l ≠ l' →
    notInOK orbits[l]!.tabs (wordTabS m gens (words.getD l' [])) = true
  cover : ∀ k < E.tabs.size, ∃ l < c,
    found (indexOf orbits[l]!.tabs) orbits[l]!.tabs E.tabs[k]! = true

section Classes

variable {m : ℕ} {gens ginv : Array Tab} {f : ℕ → Equiv.Perm (Fin m)} {E : Enum} {c : ℕ}
  {words : List (List ℕ)} {sizes : List ℕ} {orbits : Array Enum}

abbrev genGroup (m : ℕ) (gens : Array Tab) (f : ℕ → Equiv.Perm (Fin m)) :
    Subgroup (Equiv.Perm (Fin m)) :=
  Subgroup.closure {g | ∃ j < gens.size, f j = g}

theorem genGroup_hA (hgs : ∀ j < gens.size, TabRep gens[j]! (f j)) :
    ∀ a ∈ {g | ∃ j < gens.size, f j = g}, ∃ j < gens.size, TabRep gens[j]! a := by
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j, hj, hgs j hj⟩

theorem genGroup_hgens (hgs : ∀ j < gens.size, TabRep gens[j]! (f j)) :
    ∀ j < gens.size, ∃ a ∈ {g | ∃ j < gens.size, f j = g},
    TabRep gens[j]! a := fun j hj => ⟨_, ⟨j, hj, rfl⟩, hgs j hj⟩

theorem genGroup_enumerates (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    (h : ClassCert m gens ginv E c words sizes orbits) :
    Enumerates (genGroup m gens f) E.tabs.toList :=
  enumerates_closure (genGroup_hA hgs) (genGroup_hgens hgs) h.enum

@[expose] def classRepPerm (f : ℕ → Equiv.Perm (Fin m)) (words : List (List ℕ)) (l : ℕ) :
    Equiv.Perm (Fin m) :=
  ((words.getD l []).map f).prod

theorem tabRep_classRep (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    (h : ClassCert m gens ginv E c words sizes orbits) {l : ℕ} (hl : l < c) :
    TabRep (wordTabS m gens (words.getD l [])) (classRepPerm f words l) :=
  tabRep_wordTabS hgs _ (h.words_lt l hl)

theorem classRep_mem (h : ClassCert m gens ginv E c words sizes orbits) {l : ℕ} (hl : l < c) :
    classRepPerm f words l ∈ genGroup m gens f := by
  refine (genGroup m gens f).list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨j, h.words_lt l hl j hj, rfl⟩

theorem class_orbit' (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    (h : ClassCert m gens ginv E c words sizes orbits) {l : ℕ} (hl : l < c) :
    (∀ t ∈ orbits[l]!.tabs.toList, ∃ d ∈ genGroup m gens f,
        TabRep t (d * classRepPerm f words l * d⁻¹)) ∧
      (∀ d ∈ genGroup m gens f, ∃ t ∈ orbits[l]!.tabs.toList,
        TabRep t (d * classRepPerm f words l * d⁻¹)) ∧
      orbits[l]!.tabs.toList.Nodup :=
  conj_orbit (genGroup_hA hgs) (genGroup_hgens hgs) (tabRep_classRep hgs h hl) (h.orbit l hl).1

@[expose] def classFunS (h : ClassCert m gens ginv E c words sizes orbits) (l : Fin c) :
    ConjClasses (genGroup m gens f) :=
  ConjClasses.mk ⟨classRepPerm f words l, classRep_mem h l.2⟩

theorem classFunS_injective (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    (h : ClassCert m gens ginv E c words sizes orbits) :
    Function.Injective (classFunS (f := f) h) := by
  intro l l' hll
  rw [classFunS, classFunS, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hll
  obtain ⟨d, hd⟩ := hll
  by_contra hne
  have hne' : (l : ℕ) ≠ l' := fun e => hne (Fin.ext e)
  have hcl := congrArg Subtype.val hd
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcl
  obtain ⟨t, ht, hrep⟩ := (class_orbit' hgs h l.2).2.1 d d.2
  rw [hcl] at hrep
  exact notInOK_spec (h.notIn l l.2 l' l'.2 hne') (tabRep_classRep hgs h l'.2) t ht hrep

theorem classFunS_surjective (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    (h : ClassCert m gens ginv E c words sizes orbits) :
    Function.Surjective (classFunS (f := f) h) := by
  intro C
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective C
  obtain ⟨t, ht, hrep⟩ := (genGroup_enumerates hgs h).complete x x.2
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem ht
  obtain ⟨l, hl, hf⟩ := h.cover k hk
  obtain ⟨d, hd, hrep'⟩ := (class_orbit' hgs h hl).1 _ (mem_of_found hf)
  refine ⟨⟨l, hl⟩, ?_⟩
  rw [classFunS, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact hrep'.perm_eq hrep

@[expose] def classEquivS (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    (h : ClassCert m gens ginv E c words sizes orbits) :
    Fin c ≃ ConjClasses (genGroup m gens f) :=
  Equiv.ofBijective (classFunS h) ⟨classFunS_injective hgs h, classFunS_surjective hgs h⟩

theorem card_classS (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    (h : ClassCert m gens ginv E c words sizes orbits) (l : Fin c) :
    Nat.card (classEquivS hgs h l).carrier = sizes.getD l 0 := by
  have hset : (Subtype.val '' (classEquivS hgs h l).carrier : Set (Equiv.Perm (Fin m))) =
      {y | ∃ d ∈ genGroup m gens f, d * classRepPerm f words l * d⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq] at hx
      have hx' : ConjClasses.mk x = classFunS h l := hx
      rw [classFunS, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hx'
      obtain ⟨d, hd⟩ := hx'
      refine ⟨(d : Equiv.Perm (Fin m))⁻¹, Subgroup.inv_mem _ d.2, ?_⟩
      have := congrArg Subtype.val hd
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this]
      group
    · rintro ⟨d, hd, rfl⟩
      refine ⟨⟨d * classRepPerm f words l * d⁻¹, Subgroup.mul_mem _
        (Subgroup.mul_mem _ hd (classRep_mem h l.2)) (Subgroup.inv_mem _ hd)⟩, ?_, rfl⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq]
      change ConjClasses.mk _ = classFunS h l
      rw [classFunS, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      refine ⟨⟨d, hd⟩⁻¹, Subtype.ext ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
  rw [← Nat.card_image_of_injective Subtype.val_injective, hset]
  obtain ⟨hs, hc, hn⟩ := class_orbit' hgs h l.2
  rw [card_set_of_tabs (L := orbits[(l : ℕ)]!.tabs.toList) (fun t ht => by
    obtain ⟨d, hd', hr⟩ := hs t ht
    exact ⟨_, ⟨d, hd', rfl⟩, hr⟩) (by rintro _ ⟨d, hd', rfl⟩; exact hc d hd') hn,
    Array.length_toList, (h.orbit l l.2).2]

theorem classEquivS_zero (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    (h : ClassCert m gens ginv E c words sizes orbits) (hc : 0 < c) :
    classEquivS hgs h ⟨0, hc⟩ = ConjClasses.mk 1 := by
  change classFunS h ⟨0, hc⟩ = ConjClasses.mk 1
  rw [classFunS]
  congr 1
  apply Subtype.ext
  have h0 := tabRep_classRep hgs h hc
  rw [h.rep0] at h0
  exact h0.perm_eq TabRep.idTab

theorem isSimpleGroup_of_classCert (hgs : ∀ j < gens.size, TabRep gens[j]! (f j))
    (h : ClassCert m gens ginv E c words sizes orbits) (hc : 0 < c) (h1 : 1 < E.tabs.size)
    (hsums : ∀ U : Finset (Fin c), ⟨0, hc⟩ ∈ U → (∑ l ∈ U, sizes.getD l 0) ∣ E.tabs.size →
      U = {⟨0, hc⟩} ∨ U = Finset.univ)
    (hbig : ∃ l : Fin c, sizes.getD l 0 ≠ 1) :
    IsSimpleGroup (genGroup m gens f) ∧ ∃ a b : genGroup m gens f, a * b ≠ b * a := by
  have hcard := (genGroup_enumerates hgs h).card
  rw [Array.length_toList] at hcard
  refine ⟨isSimpleGroup_of_classes (classEquivS hgs h) (fun l => sizes.getD l 0)
    (card_classS hgs h) ⟨0, hc⟩ (classEquivS_zero hgs h hc) (by rw [hcard]; exact h1)
    (by rw [hcard]; exact hsums), ?_⟩
  obtain ⟨l, hl⟩ := hbig
  exact exists_mul_ne_of_class (classEquivS hgs h l) (by rw [card_classS]; exact hl)

theorem commAll_iff {n : ℕ} {gs : Array Tab} {f : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ j < gs.size, TabRep gs[j]! (f j)) {t : Tab} {g : Equiv.Perm (Fin n)}
    (ht : TabRep t g) :
    commAll n gs t = true ↔
      g ∈ Subgroup.centralizer (genGroup n gs f : Set (Equiv.Perm (Fin n))) := by
  rw [commAll, allBelow_eq_true, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨j, hj, rfl⟩
    exact ((ht.comp (hgs j hj)).beq_iff ((hgs j hj).comp ht)).1 (h j hj) |>.symm
  · intro h j hj
    exact ((ht.comp (hgs j hj)).beq_iff ((hgs j hj).comp ht)).2 (h _ ⟨j, hj, rfl⟩).symm

theorem card_inf_centralizer_of_enum {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : List Tab}
    (hH : Enumerates H T) {gs : Array Tab} {f : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ j < gs.size, TabRep gs[j]! (f j)) :
    Nat.card ↥(H ⊓ Subgroup.centralizer (genGroup n gs f : Set (Equiv.Perm (Fin n)))) =
      (T.filter (commAll n gs)).length := by
  rw [inf_comm]
  exact (hH.filter (commAll n gs) fun t g ht => commAll_iff hgs ht).card

theorem closure_le_normalizer {G : Type*} [Group G] {A S : Set G}
    (h : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ Subgroup.closure S ∧
      a⁻¹ * s * a ∈ Subgroup.closure S) :
    Subgroup.closure A ≤ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  rw [Subgroup.closure_le]
  intro a ha
  have hmap : ∀ b : G, (∀ s ∈ S, b * s * b⁻¹ ∈ Subgroup.closure S) →
      (Subgroup.closure S).map (MulAut.conj b).toMonoidHom ≤ Subgroup.closure S := by
    intro b hb
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact hb s hs
  have h1 := hmap a fun s hs => (h a ha s hs).1
  have h2 := hmap a⁻¹ fun s hs => by simpa using (h a ha s hs).2
  show a ∈ Subgroup.normalizer _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1 ⟨x, hx, rfl⟩
  · intro hx
    have := h2 ⟨_, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem le_normalizer_of_normalOK {n : ℕ} {gens ginv gs : Array Tab}
    {fa fs : ℕ → Equiv.Perm (Fin n)} (hga : ∀ j < gens.size, TabRep gens[j]! (fa j))
    (hgs : ∀ j < gs.size, TabRep gs[j]! (fs j)) {T : Array Tab}
    (hH : Enumerates (genGroup n gs fs) T.toList) (h : normalOK n T gens ginv gs = true) :
    genGroup n gens fa ≤ Subgroup.normalizer (genGroup n gs fs : Set (Equiv.Perm (Fin n))) := by
  apply closure_le_normalizer
  rintro _ ⟨j, hj, rfl⟩ _ ⟨i, hi, rfl⟩
  exact conj_mem_of_normalOK hH h hj hi (hga j hj) (hgs i hi)

end Classes

end CFSG.Sporadic.SmallOddCore
