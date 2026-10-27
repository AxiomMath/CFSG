module

public import CFSG.Quasithin.H13.U3LagData
public import CFSG.Quasithin.H13.U3SixProfile

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin Matrix

@[expose] def HasMask (P : Submodule (ZMod 2) W6) (m : ℕ) : Prop :=
  ∀ c < 64, vecOf c ∈ P ↔ m.testBit c = true

theorem eq_of_hasMask {P P' : Submodule (ZMod 2) W6} {m : ℕ} (h : HasMask P m)
    (h' : HasMask P' m) : P = P' := by
  ext w
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  rw [h c hc, h' c hc]

theorem testBit_foldr_img (g : List ℕ) (m k : ℕ) (l : List ℕ) :
    (l.foldr (fun c acc => if m.testBit c then acc ||| 2 ^ vapp g c else acc) 0).testBit k =
        true ↔ ∃ c ∈ l, m.testBit c = true ∧ vapp g c = k := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.foldr_cons]
    by_cases h : m.testBit c = true
    · simp only [h, ↓reduceIte]
      rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro (⟨c', hc', hm', hg'⟩ | hk)
        · exact ⟨c', List.mem_cons_of_mem _ hc', hm', hg'⟩
        · exact ⟨c, List.mem_cons_self .., h, hk⟩
      · rintro ⟨c', hc', hm', hg'⟩
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact Or.inr hg'
        · exact Or.inl ⟨c', hc', hm', hg'⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      constructor
      · rintro ⟨c', hc', hm', hg'⟩
        exact ⟨c', List.mem_cons_of_mem _ hc', hm', hg'⟩
      · rintro ⟨c', hc', hm', hg'⟩
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact absurd hm' h
        · exact ⟨c', hc', hm', hg'⟩

theorem testBit_maskImg (g : List ℕ) (m k : ℕ) :
    (maskImg g m).testBit k = true ↔ ∃ c < 64, m.testBit c = true ∧ vapp g c = k := by
  rw [maskImg, testBit_foldr_img]
  simp only [List.mem_range]

theorem hasMask_map {P : Submodule (ZMod 2) W6} {m : ℕ} (hP : HasMask P m)
    {g : GL (Fin 6) (ZMod 2)} {code : List ℕ}
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat code)
    (hlt : ∀ c, vapp code c < 64) :
    HasMask (P.map (glLin g : W6 →ₗ[ZMod 2] W6)) (maskImg code m) := by
  intro k hk
  rw [testBit_maskImg, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, hxk⟩
    obtain ⟨c, hc, rfl⟩ := exists_vecOf x
    refine ⟨c, hc, (hP c hc).1 hx, ?_⟩
    rw [LinearEquiv.coe_coe, glLin_apply, hg, colMat_mulVec_vecOf] at hxk
    exact vecOf_injective (hlt c) hk hxk
  · rintro ⟨c, hc, hmc, rfl⟩
    refine ⟨vecOf c, (hP c hc).2 hmc, ?_⟩
    rw [LinearEquiv.coe_coe, glLin_apply, hg, colMat_mulVec_vecOf]

theorem vapp_lt_of_getD {code : List ℕ} (h : ∀ j < 6, code.getD j 0 < 64) (c : ℕ) :
    vapp code c < 64 :=
  vapp_lt_of_foldr c _ fun j hj => h j (List.mem_range.1 hj)

theorem gens7_getD_lt : ∀ g ∈ gens7, ∀ j < 6, g.getD j 0 < 64 := by
  decide +kernel

theorem vapp_gens7_lt {g : List ℕ} (hg : g ∈ gens7) (c : ℕ) : vapp g c < 64 :=
  vapp_lt_of_getD (gens7_getD_lt g hg) c

theorem testBit_spanMask3 (a b c k : ℕ) :
    (spanMask3 a b c).testBit k = true ↔ k = 0 ∨ k = a ∨ k = b ∨ k = c ∨ k = a ^^^ b ∨
      k = a ^^^ c ∨ k = b ^^^ c ∨ k = a ^^^ b ^^^ c := by
  simp only [spanMask3, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro (((((((h | h) | h) | h) | h) | h) | h) | h) <;> subst h <;> simp
  · rintro (h | h | h | h | h | h | h | h) <;> subst h <;> simp

theorem mem_span_three {a b c x : W6} :
    x ∈ Submodule.span (ZMod 2) {a, b, c} ↔ x = 0 ∨ x = a ∨ x = b ∨ x = c ∨ x = a + b ∨
      x = a + c ∨ x = b + c ∨ x = a + b + c := by
  rw [Submodule.mem_span_insert]
  simp only [Submodule.mem_span_pair]
  constructor
  · rintro ⟨r, z, ⟨s, t, rfl⟩, rfl⟩
    have h2 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
    rcases h2 r with rfl | rfl <;> rcases h2 s with rfl | rfl <;> rcases h2 t with rfl | rfl <;>
      simp [add_assoc]
  · rintro (h | h | h | h | h | h | h | h) <;> rw [h]
    · exact ⟨0, 0, ⟨0, 0, by simp⟩, by simp⟩
    · exact ⟨1, 0, ⟨0, 0, by simp⟩, by simp⟩
    · exact ⟨0, b, ⟨1, 0, by simp⟩, by simp⟩
    · exact ⟨0, c, ⟨0, 1, by simp⟩, by simp⟩
    · exact ⟨1, b, ⟨1, 0, by simp⟩, by simp⟩
    · exact ⟨1, c, ⟨0, 1, by simp⟩, by simp⟩
    · exact ⟨0, b + c, ⟨1, 1, by simp⟩, by simp⟩
    · exact ⟨1, b + c, ⟨1, 1, by simp⟩, by simp [add_assoc]⟩

theorem hasMask_span3 {a b c : ℕ} (ha : a < 64) (hb : b < 64) (hc : c < 64) :
    HasMask (Submodule.span (ZMod 2) {vecOf a, vecOf b, vecOf c}) (spanMask3 a b c) := by
  intro k hk
  have hab : a ^^^ b < 64 := Nat.xor_lt_two_pow (n := 6) ha hb
  have hac : a ^^^ c < 64 := Nat.xor_lt_two_pow (n := 6) ha hc
  have hbc : b ^^^ c < 64 := Nat.xor_lt_two_pow (n := 6) hb hc
  have habc : a ^^^ b ^^^ c < 64 := Nat.xor_lt_two_pow (n := 6) hab hc
  have e : ∀ {u v : ℕ}, u < 64 → v < 64 → (vecOf u = vecOf v ↔ u = v) := fun hu hv =>
    ⟨vecOf_injective hu hv, fun h => h ▸ rfl⟩
  rw [mem_span_three, testBit_spanMask3, ← vecOf_zero]
  simp only [← vecOf_xor]
  rw [e hk (by norm_num), e hk ha, e hk hb, e hk hc, e hk hab, e hk hac, e hk hbc, e hk habc]

@[expose] def IsTI (P : Submodule (ZMod 2) W6) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, b0 x y = 0

theorem dotB_eq_false_of_b0 {u v : ℕ} (h : b0 (vecOf u) (vecOf v) = 0) :
    dotB u (vapp b0c v) = false := by
  rw [b0_vecOf] at h
  cases hd : dotB u (vapp b0c v)
  · rfl
  · rw [hd] at h
    exact absurd h (by decide)

theorem lag_card : ∀ m ∈ lag3c ++ lagYc,
    ((Finset.range 64).filter fun c => m.testBit c = true).card = 8 := by
  decide +kernel

theorem lagY_maximal : ∀ t ∈ lagYtri, ∀ y < 64, dotB t.1 (vapp b0c y) = false →
    dotB t.2.1 (vapp b0c y) = false → dotB t.2.2 (vapp b0c y) = false →
      (spanMask3 t.1 t.2.1 t.2.2).testBit y = true := by
  decide +kernel

theorem card_of_hasMask {P : Submodule (ZMod 2) W6} {m : ℕ} (hP : HasMask P m) :
    Nat.card P = ((Finset.range 64).filter fun c => m.testBit c = true).card := by
  refine natCard_eq_of_vecOf (fun c hc => Finset.mem_range.1 (Finset.mem_filter.1 hc).1) ?_
  intro c hc
  rw [hP c hc, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩

theorem exists_sorted_basis {P : Submodule (ZMod 2) W6} (hP : Nat.card P = 8) :
    ∃ u₁ u₂ u₃ : ℕ, u₃ < 64 ∧ 0 < u₁ ∧ u₁ < u₂ ∧ u₂ < u₃ ∧ u₃ ≠ u₁ ^^^ u₂ ∧
      vecOf u₁ ∈ P ∧ vecOf u₂ ∈ P ∧ vecOf u₃ ∈ P := by
  classical
  set S := (Finset.range 64).filter (fun c => vecOf c ∈ P) with hSdef
  have hS : S.card = 8 := by
    rw [← hP]
    refine (natCard_eq_of_vecOf (fun c hc => Finset.mem_range.1 (Finset.mem_filter.1 hc).1)
      fun c hc => ?_).symm
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  have hmem : ∀ c, c ∈ S ↔ c < 64 ∧ vecOf c ∈ P := fun c => by
    rw [hSdef, Finset.mem_filter, Finset.mem_range]
  have h0 : 0 ∈ S := (hmem 0).2 ⟨by norm_num, by rw [vecOf_zero]; exact P.zero_mem⟩
  set S₁ := S.erase 0
  have hS₁ : S₁.card = 7 := by rw [Finset.card_erase_of_mem h0, hS]
  have hS₁ne : S₁.Nonempty := Finset.card_pos.1 (by rw [hS₁]; norm_num)
  set u₁ := S₁.min' hS₁ne
  have hu₁ : u₁ ∈ S₁ := Finset.min'_mem _ _
  set S₂ := S₁.erase u₁
  have hS₂ : S₂.card = 6 := by rw [Finset.card_erase_of_mem hu₁, hS₁]
  have hS₂ne : S₂.Nonempty := Finset.card_pos.1 (by rw [hS₂]; norm_num)
  set u₂ := S₂.min' hS₂ne
  have hu₂ : u₂ ∈ S₂ := Finset.min'_mem _ _
  have hS₃ : 4 ≤ ((S₂.erase u₂).erase (u₁ ^^^ u₂)).card := by
    have h1 : (S₂.erase u₂).card = 5 := by rw [Finset.card_erase_of_mem hu₂, hS₂]
    have h2 := Finset.pred_card_le_card_erase (s := S₂.erase u₂) (a := u₁ ^^^ u₂)
    omega
  set S₃ := (S₂.erase u₂).erase (u₁ ^^^ u₂)
  have hS₃ne : S₃.Nonempty := Finset.card_pos.1 (by omega)
  set u₃ := S₃.min' hS₃ne
  have hu₃ : u₃ ∈ S₃ := Finset.min'_mem _ _
  have hu₃' := Finset.mem_erase.1 hu₃
  have hu₃'' := Finset.mem_erase.1 hu₃'.2
  have hu₂' := Finset.mem_erase.1 hu₂
  have hu₁' := Finset.mem_erase.1 hu₁
  have hu₃S₂ : u₃ ∈ S₂ := hu₃''.2
  have hu₂S₁ : u₂ ∈ S₁ := hu₂'.2
  have hu₃S₁ : u₃ ∈ S₁ := (Finset.mem_erase.1 hu₃S₂).2
  have h12 : u₁ ≤ u₂ := Finset.min'_le _ _ hu₂S₁
  have h23 : u₂ ≤ u₃ := Finset.min'_le _ _ hu₃S₂
  have hu₃S := (Finset.mem_erase.1 hu₃S₁).2
  have hu₂S := (Finset.mem_erase.1 hu₂S₁).2
  refine ⟨u₁, u₂, u₃, ((hmem u₃).1 hu₃S).1, Nat.pos_of_ne_zero hu₁'.1,
    lt_of_le_of_ne h12 (Ne.symm hu₂'.1), lt_of_le_of_ne h23 (Ne.symm hu₃''.1), hu₃'.1,
    ((hmem u₁).1 hu₁'.2).2, ((hmem u₂).1 hu₂S).2, ((hmem u₃).1 hu₃S).2⟩

theorem exists_hasMask_lag {P : Submodule (ZMod 2) W6} (hti : IsTI P) (hP : Nat.card P = 8) :
    ∃ m, (m ∈ lag3c ∨ m ∈ lagYc) ∧ HasMask P m := by
  obtain ⟨u₁, u₂, u₃, hu₃, h0, h12, h23, hne, h₁, h₂, h₃⟩ := exists_sorted_basis hP
  have hu₂ : u₂ < 64 := h23.trans hu₃
  have hu₁ : u₁ < 64 := h12.trans hu₂
  have hcov := lag_cover u₁ hu₁ u₂ hu₂ h0 h12 (dotB_eq_false_of_b0 (hti _ h₁ _ h₂)) u₃ hu₃ h23
    (dotB_eq_false_of_b0 (hti _ h₁ _ h₃)) (dotB_eq_false_of_b0 (hti _ h₂ _ h₃)) hne
  refine ⟨_, hcov, ?_⟩
  have hsp := hasMask_span3 hu₁ hu₂ hu₃
  have hle : Submodule.span (ZMod 2) {vecOf u₁, vecOf u₂, vecOf u₃} ≤ P := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  have hcard : Nat.card (Submodule.span (ZMod 2) {vecOf u₁, vecOf u₂, vecOf u₃}) = 8 := by
    rw [card_of_hasMask hsp]
    exact lag_card _ (List.mem_append.2 hcov)
  have heq : Submodule.span (ZMod 2) {vecOf u₁, vecOf u₂, vecOf u₃} = P :=
    Submodule.toAddSubgroup_injective
      (AddSubgroup.eq_of_le_of_card_ge (H := (Submodule.span (ZMod 2) _).toAddSubgroup) hle
        (by change Nat.card P ≤ Nat.card (Submodule.span (ZMod 2) _); rw [hcard, hP]))
  rw [← heq]
  exact hsp

theorem N6_eq_closure
    : N6 = Subgroup.closure
    ({dGL, u6GL 0, u6GL 1, u6GL 2, u6GL 3, u6GL 4} : Set (GL (Fin 6) (ZMod 2))) := by
  show Subgroup.zpowers dGL ⊔ rho6.range = _
  rw [MonoidHom.range_eq_map, ← u33Data.gen, MonoidHom.map_closure, Subgroup.zpowers_eq_closure,
    ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.image_insert_eq, Set.image_singleton, rho6_abs.1, rho6_abs.2.1, rho6_abs.2.2.1,
    rho6_abs.2.2.2.1, rho6_abs.2.2.2.2, Set.singleton_union]

theorem map_glLin_mul (P : Submodule (ZMod 2) W6) (x y : GL (Fin 6) (ZMod 2)) :
    P.map (glLin (x * y) : W6 →ₗ[ZMod 2] W6) =
      (P.map (glLin y : W6 →ₗ[ZMod 2] W6)).map (glLin x : W6 →ₗ[ZMod 2] W6) := by
  ext w
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, map_mul, LinearEquiv.mul_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩

theorem map_glLin_one (P : Submodule (ZMod 2) W6) :
    P.map (glLin 1 : W6 →ₗ[ZMod 2] W6) = P := by
  ext w
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, map_one]
  exact ⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨w, h, rfl⟩⟩

theorem coe_gen_N6 {g : GL (Fin 6) (ZMod 2)}
    (hg : g ∈ ({dGL, u6GL 0, u6GL 1, u6GL 2, u6GL 3, u6GL 4} : Set (GL (Fin 6) (ZMod 2)))) :
    ∃ code ∈ gens7, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat code := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨dc, by simp [gens7], rfl⟩
  · exact ⟨u6c 0, by simp [gens7], rfl⟩
  · exact ⟨u6c 1, by simp [gens7], rfl⟩
  · exact ⟨u6c 2, by simp [gens7], rfl⟩
  · exact ⟨u6c 3, by simp [gens7], rfl⟩
  · exact ⟨u6c 4, by simp [gens7], rfl⟩

theorem exists_hasMask_map_of_closed
    {lst : List ℕ}
    (hcl : ∀ m ∈ lst, ∀ g ∈ gens7, maskImg g m ∈ lst) {n : GL (Fin 6) (ZMod 2)} (hn : n ∈ N6) :
    ∀ (P : Submodule (ZMod 2) W6) (m : ℕ), HasMask P m → m ∈ lst →
      ∃ m' ∈ lst, HasMask (P.map (glLin n : W6 →ₗ[ZMod 2] W6)) m' := by
  rw [N6_eq_closure] at hn
  have hn' : n ∈ Submonoid.closure
      ({dGL, u6GL 0, u6GL 1, u6GL 2, u6GL 3, u6GL 4} : Set (GL (Fin 6) (ZMod 2))) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hn
  clear hn
  induction hn' using Submonoid.closure_induction with
  | mem g hg =>
    intro P m hP hm
    obtain ⟨code, hcode, hgc⟩ := coe_gen_N6 hg
    exact ⟨_, hcl m hm code hcode, hasMask_map hP hgc (vapp_gens7_lt hcode)⟩
  | one =>
    intro P m hP hm
    exact ⟨m, hm, by rw [map_glLin_one]; exact hP⟩
  | mul x y _ _ ihx ihy =>
    intro P m hP hm
    obtain ⟨m₁, hm₁, h₁⟩ := ihy P m hP hm
    obtain ⟨m₂, hm₂, h₂⟩ := ihx _ m₁ h₁ hm₁
    exact ⟨m₂, hm₂, by rw [map_glLin_mul]; exact h₂⟩

noncomputable def V3sub : Submodule (ZMod 2) W6 :=
  Submodule.span (ZMod 2) {vecOf 15, vecOf 18, vecOf 39}

theorem hasMask_V3sub : HasMask V3sub (lag3c.getD 0 0) := by
  rw [lag3_length.2]
  exact hasMask_span3 (by norm_num) (by norm_num) (by norm_num)

theorem gens7_getD_fin : ∀ i : Fin 5, gens7.getD i [] = u6c i := by
  decide

theorem exists_J6_hasMask_lag3 : ∀ k < 63, ∃ j ∈ J6,
    HasMask (V3sub.map (glLin j : W6 →ₗ[ZMod 2] W6)) (lag3c.getD k 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨1, one_mem _, by rw [map_glLin_one]; exact hasMask_V3sub⟩
    · obtain ⟨hp, hg, heq⟩ := lag3_tree k hk hk0
      obtain ⟨j, hj, hmask⟩ := ih _ hp (hp.trans hk)
      set gi := (lag3Par.getD k (0, 0)).2
      refine ⟨u6GL ⟨gi, hg⟩ * j, mul_mem ⟨u33GenPG gi, rho6_gen' gi hg⟩ hj, ?_⟩
      rw [map_glLin_mul, ← heq]
      refine hasMask_map hmask (code := gens7.getD gi []) ?_ ?_
      · rw [show gens7.getD gi [] = u6c ⟨gi, hg⟩ from gens7_getD_fin ⟨gi, hg⟩]
        rfl
      · intro c
        rw [show gens7.getD gi [] = u6c ⟨gi, hg⟩ from gens7_getD_fin ⟨gi, hg⟩]
        exact vapp_u6c_lt _ c

theorem exists_eq_map_V3sub {P : Submodule (ZMod 2) W6} {m : ℕ} (hP : HasMask P m)
    (hm : m ∈ lag3c) : ∃ j ∈ J6, P = V3sub.map (glLin j : W6 →ₗ[ZMod 2] W6) := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  have hk' : k < 63 := lag3_length.1 ▸ hk
  obtain ⟨j, hj, hmask⟩ := exists_J6_hasMask_lag3 k hk'
  rw [List.getD_eq_getElem _ _ hk] at hmask
  exact ⟨j, hj, eq_of_hasMask hP hmask⟩

theorem lagYc_length : lagYc.length = 72 := by
  decide

theorem b0_glLin_of_mem_N6
    {n : GL (Fin 6) (ZMod 2)} (hn : n ∈ N6) (x y : W6) :
    b0 (glLin n x) (glLin n y) = b0 x y := by
  rw [glLin_apply, glLin_apply]
  exact b0_mulVec_of_mem_b0Stab (N6_le_b0Stab hn) x y

theorem W6_add_self (x : W6) : x + x = 0 := by
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = c
  revert c
  decide

theorem hasMask_lagYtri {k : ℕ} (hk : k < 72) :
    HasMask (Submodule.span (ZMod 2) {vecOf (lagYtri.getD k (0, 0, 0)).1,
      vecOf (lagYtri.getD k (0, 0, 0)).2.1, vecOf (lagYtri.getD k (0, 0, 0)).2.2})
      (lagYc.getD k 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := lagYtri_spec.2 k hk
  rw [← h1]
  exact hasMask_span3 h2 h3 h4

theorem lagYtri_mem {k : ℕ} (hk : k < 72) : lagYtri.getD k (0, 0, 0) ∈ lagYtri := by
  rw [List.getD_eq_getElem _ _ (by rw [lagYtri_spec.1]; exact hk)]
  exact List.getElem_mem _

theorem exists_lagYtri {P : Submodule (ZMod 2) W6} {m : ℕ} (hP : HasMask P m) (hm : m ∈ lagYc) :
    ∃ t ∈ lagYtri, t.1 < 64 ∧ t.2.1 < 64 ∧ t.2.2 < 64 ∧
      P = Submodule.span (ZMod 2) {vecOf t.1, vecOf t.2.1, vecOf t.2.2} := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  have hk' : k < 72 := lagYc_length ▸ hk
  have h := hasMask_lagYtri hk'
  rw [List.getD_eq_getElem _ _ hk] at h
  obtain ⟨-, h2, h3, h4⟩ := lagYtri_spec.2 k hk'
  exact ⟨_, lagYtri_mem hk', h2, h3, h4, eq_of_hasMask hP h⟩

theorem eq_one_of_fixes_lagY
    {P : Submodule (ZMod 2) W6} {m : ℕ} (hP : HasMask P m)
    (hm : m ∈ lagYc) {n : GL (Fin 6) (ZMod 2)} (hn : n ∈ N6) (hfix : ∀ x ∈ P, glLin n x = x) :
    n = 1 := by
  obtain ⟨t, ht, ht1, ht2, ht3, hPt⟩ := exists_lagYtri hP hm
  have hmemP : ∀ c ∈ ({t.1, t.2.1, t.2.2} : Set ℕ), vecOf c ∈ P := by
    intro c hc
    rw [hPt]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  have hmax : ∀ y : W6, b0 (vecOf t.1) y = 0 → b0 (vecOf t.2.1) y = 0 →
      b0 (vecOf t.2.2) y = 0 → y ∈ P := by
    intro y h1 h2 h3
    obtain ⟨c, hc, rfl⟩ := exists_vecOf y
    have := lagY_maximal t ht c hc (dotB_eq_false_of_b0 h1) (dotB_eq_false_of_b0 h2)
      (dotB_eq_false_of_b0 h3)
    rw [hPt]
    exact (hasMask_span3 ht1 ht2 ht3 c hc).2 this
  have horth : ∀ (x : W6) (c : ℕ), vecOf c ∈ P → b0 (vecOf c) (glLin n x - x) = 0 := by
    intro x c hc
    rw [map_sub, ← b0_glLin_of_mem_N6 hn (vecOf c) x, hfix _ hc, sub_self]
  have hn2 : n * n = 1 := by
    apply glLin.injective
    refine LinearEquiv.ext fun x => ?_
    have hy : glLin n x - x ∈ P := hmax _ (horth x _ (hmemP _ (by simp)))
      (horth x _ (hmemP _ (by simp))) (horth x _ (hmemP _ (by simp)))
    have h1 := hfix _ hy
    rw [map_sub, sub_eq_add_W6, sub_eq_add_W6] at h1
    rw [map_mul, map_one, LinearEquiv.mul_apply]
    change glLin n (glLin n x) = x
    have h2 : glLin n (glLin n x) = glLin n x + glLin n x + x := by
      calc glLin n (glLin n x) = glLin n (glLin n x) + (glLin n x + glLin n x) := by
            rw [W6_add_self, add_zero]
        _ = (glLin n (glLin n x) + glLin n x) + glLin n x := by abel
        _ = glLin n x + x + glLin n x := by rw [h1]
        _ = glLin n x + glLin n x + x := by abel
    rw [h2, W6_add_self, zero_add]
  have hz2 : IsPGroup 2 (Subgroup.zpowers n) := by
    have hord : orderOf n ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two, hn2])
    exact IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact hord)
  obtain ⟨k, hk, hconj⟩ := exists_conj_le_S0 (Subgroup.zpowers_le.2 hn) hz2
  obtain ⟨i, hi, hsi⟩ := eq_s0GL (hconj n (Subgroup.mem_zpowers n))
  obtain ⟨m', hm', hQ⟩ := exists_hasMask_map_of_closed lagY_closed (inv_mem hk) P m hP hm
  obtain ⟨t', ht', ht1', ht2', ht3', hQt⟩ := exists_lagYtri hQ hm'
  have hfixQ : ∀ c ∈ ({t'.1, t'.2.1, t'.2.2} : Set ℕ),
      glLin (s0GL i) (vecOf c) = vecOf c := by
    intro c hc
    have hcQ : vecOf c ∈ P.map (glLin k⁻¹ : W6 →ₗ[ZMod 2] W6) := by
      rw [hQt]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    obtain ⟨x, hx, hxc⟩ := Submodule.mem_map.1 hcQ
    rw [LinearEquiv.coe_coe] at hxc
    have hkk : glLin k (glLin k⁻¹ x) = x := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [← hsi, ← hxc, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hkk,
      hfix x hx]
  have hvapp : ∀ c ∈ ({t'.1, t'.2.1, t'.2.2} : Set ℕ), c < 64 → vapp (s0m i) c = c := by
    intro c hc hc64
    have h1 := hfixQ c hc
    rw [glLin_apply, coe_s0GL hi, colMat_mulVec_vecOf] at h1
    exact vecOf_injective (vapp_s0m_lt hi c) hc64 h1
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [s0GL_zero] at hsi
    have h1 : n = k * (k⁻¹ * n * k) * k⁻¹ := by group
    rw [h1, hsi, mul_one, mul_inv_cancel]
  · exfalso
    have hmem : s0m i ∈ s0c.tail := by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have h2 : j < s0c.tail.length := by rw [List.length_tail, s0c_spec.1]; omega
      have h3 := List.getElem_mem h2
      rw [List.getElem_tail] at h3
      rw [s0m, List.getD_eq_getElem _ _ (by rw [s0c_spec.1]; exact hi)]
      exact h3
    exact lagY_free _ hmem t' ht' ⟨hvapp _ (by simp) ht1', hvapp _ (by simp) ht2',
      hvapp _ (by simp) ht3'⟩

noncomputable def V2sub : Submodule (ZMod 2) W6 :=
  Submodule.span (ZMod 2) {vecOf 15, vecOf 53}

@[expose] def v2mask : ℕ := 2 ^ 0 ||| 2 ^ 15 ||| 2 ^ 53 ||| 2 ^ 58

theorem hasMask_V2sub : HasMask V2sub v2mask := by
  have h := hasMask_span3 (a := 15) (b := 53) (c := 0) (by norm_num) (by norm_num) (by norm_num)
  have hsp : Submodule.span (ZMod 2) ({vecOf 15, vecOf 53, vecOf 0} : Set W6) = V2sub := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · rw [vecOf_zero]
        exact zero_mem _
    · exact Submodule.span_mono (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        tauto)
  rw [← hsp]
  have he : spanMask3 15 53 0 = v2mask := by decide
  rw [← he]
  exact h

theorem s0gens_fix : ∀ g ∈ [dc, u6c 0, u6c 1, u6c 2],
    maskImg g v2mask = v2mask ∧ maskImg g (lag3c.getD 0 0) = lag3c.getD 0 0 := by
  decide +kernel

theorem hasMask_map_S0
    {m : ℕ} (hm : ∀ g ∈ [dc, u6c 0, u6c 1, u6c 2], maskImg g m = m)
    {s : GL (Fin 6) (ZMod 2)} (hs : s ∈ S0) :
    ∀ P : Submodule (ZMod 2) W6, HasMask P m → HasMask (P.map (glLin s : W6 →ₗ[ZMod 2] W6)) m := by
  rw [S0_eq_closure] at hs
  have hs' : s ∈ Submonoid.closure
      ({dGL, rho6 u33Data.a, rho6 u33Data.b, rho6 u33Data.s} : Set (GL (Fin 6) (ZMod 2))) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hs
  clear hs
  induction hs' using Submonoid.closure_induction with
  | mem g hg =>
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [← hm dc (by simp)]
      exact hasMask_map hP rfl (vapp_gens7_lt (by simp [gens7]))
    · rw [← hm (u6c 0) (by simp), rho6_abs.1]
      exact hasMask_map hP rfl (vapp_u6c_lt 0)
    · rw [← hm (u6c 1) (by simp), rho6_abs.2.1]
      exact hasMask_map hP rfl (vapp_u6c_lt 1)
    · rw [← hm (u6c 2) (by simp), rho6_abs.2.2.1]
      exact hasMask_map hP rfl (vapp_u6c_lt 2)
  | one =>
    intro P hP
    rw [map_glLin_one]
    exact hP
  | mul x y _ _ ihx ihy =>
    intro P hP
    rw [map_glLin_mul]
    exact ihx _ (ihy P hP)

theorem map_V2sub_of_mem_S0
    {s : GL (Fin 6) (ZMod 2)} (hs : s ∈ S0) :
    V2sub.map (glLin s : W6 →ₗ[ZMod 2] W6) = V2sub :=
  eq_of_hasMask (hasMask_map_S0 (fun g hg => (s0gens_fix g hg).1) hs V2sub hasMask_V2sub)
    hasMask_V2sub

theorem map_V3sub_of_mem_S0
    {s : GL (Fin 6) (ZMod 2)} (hs : s ∈ S0) :
    V3sub.map (glLin s : W6 →ₗ[ZMod 2] W6) = V3sub :=
  eq_of_hasMask (hasMask_map_S0 (fun g hg => (s0gens_fix g hg).2) hs V3sub hasMask_V3sub)
    hasMask_V3sub

theorem V2sub_le_V3sub : V2sub ≤ V3sub := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := exists_vecOf x
  rw [hasMask_V2sub c hc] at hx
  rw [hasMask_V3sub c hc]
  revert c hx
  decide

theorem vecOf_fifteen_mem_V2sub : vecOf 15 ∈ V2sub :=
  Submodule.subset_span (by simp)

theorem card_V2sub : Nat.card V2sub = 4 := by
  rw [card_of_hasMask hasMask_V2sub]
  decide

theorem card_V3sub : Nat.card V3sub = 8 := by
  rw [card_of_hasMask hasMask_V3sub]
  exact lag_card _ (List.mem_append.2 (Or.inl (by rw [lag3_length.2]; decide)))

theorem card_le_eight_of_isTI {P : Submodule (ZMod 2) W6} (hP : IsTI P) : Nat.card P ≤ 8 := by
  have hle : P ≤ b0.orthogonal P := fun y hy x hx => hP x hx y hy
  have h1 := LinearMap.BilinForm.finrank_orthogonal b0_nondegenerate P
  have h2 := Submodule.finrank_mono hle
  have h6 : Module.finrank (ZMod 2) W6 = 6 := Module.finrank_fin_fun _
  rw [h6] at h1
  have h3 : Module.finrank (ZMod 2) P ≤ 3 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  calc 2 ^ Module.finrank (ZMod 2) P ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) h3
    _ = 8 := by norm_num

end CFSG.Quasithin.H13.U3
