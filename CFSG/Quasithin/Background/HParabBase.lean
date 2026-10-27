module

public import CFSG.Quasithin.Background.HCocBase

public section

namespace CFSG.Quasithin.H.Parab

open CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H.ZTrans

section Stab

variable {W : Type*} [CommGroup W]

theorem map_eq_of_mem_stabSub {U : Subgroup W} {s : MulAut W} (hs : s ∈ stabSub U) :
    U.map s.toMonoidHom = U := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (hs u).2 hu
  · intro hx
    refine ⟨s⁻¹ x, (hs _).1 ?_, ?_⟩
    · show s (s⁻¹ x) ∈ U
      rw [MulAut.apply_inv_self]
      exact hx
    · show s (s⁻¹ x) = x
      rw [MulAut.apply_inv_self]

theorem map_mul_toMonoidHom (U : Subgroup W) (g h : MulAut W) :
    U.map (g * h).toMonoidHom = (U.map h.toMonoidHom).map g.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem card_stab_mul_le [Finite W] {G : Subgroup (MulAut W)} {U : Subgroup W} {k : ℕ}
    (g : Fin k → MulAut W) (hg : ∀ i, g i ∈ G)
    (hinj : ∀ i j, U.map (g i).toMonoidHom = U.map (g j).toMonoidHom → i = j) :
    k * Nat.card ↥(G ⊓ stabSub U) ≤ Nat.card ↥G := by
  have : Finite (MulAut W) := finite_mulAut_z (V := W)
  set K : Subgroup ↥G := (G ⊓ stabSub U).subgroupOf G with hK
  have hKc : Nat.card K = Nat.card ↥(G ⊓ stabSub U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hf : Function.Injective fun i : Fin k => (QuotientGroup.mk ⟨g i, hg i⟩ : ↥G ⧸ K) := by
    intro i j h
    have h1 := QuotientGroup.eq.1 h
    rw [hK, Subgroup.mem_subgroupOf] at h1
    have h2 : (g i)⁻¹ * g j ∈ stabSub U := h1.2
    refine hinj i j ?_
    have h3 : g j = g i * ((g i)⁻¹ * g j) := by group
    rw [h3, map_mul_toMonoidHom, map_eq_of_mem_stabSub h2]
  have h1 := Nat.card_le_card_of_injective _ hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  rw [hKc] at h2
  rw [h2]
  exact Nat.mul_le_mul_right _ h1

end Stab

variable {n : ℕ}

theorem combos_map {f : ℕ → ℕ} (hf : XorLin f) : ∀ l : List ℕ, combos (l.map f) = (combos l).map f
  | [] => by simp [combos, hf.map_zero]
  | a :: l => by
    rw [List.map_cons, combos, combos, combos_map hf l, List.map_append, List.map_map,
      List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    exact (hf x a).symm

theorem maskSub_map {g : MulAut (Wn n)} {c : List ℕ} (hg : ActsBy g c) (b : List ℕ) :
    (maskSub n b).map g.toMonoidHom = maskSub n (b.map (actM c)) := by
  ext v
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨actM c m, ?_, (hg m).symm⟩
    rw [combos_map (actM_xor c)]
    exact List.mem_map_of_mem hm
  · rintro ⟨m', hm', rfl⟩
    rw [combos_map (actM_xor c)] at hm'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm'
    exact ⟨toW n m, ⟨m, hm, rfl⟩, hg m⟩

@[expose] def maskKey (b : List ℕ) : ℕ := (combos b).foldr (fun m acc => acc ||| 2 ^ m) 0

theorem testBit_foldr_or : ∀ (l : List ℕ) (i : ℕ),
    (l.foldr (fun m acc => acc ||| 2 ^ m) 0).testBit i = true ↔ i ∈ l
  | [], i => by simp
  | a :: l, i => by
    rw [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, testBit_foldr_or l i,
      Nat.testBit_two_pow, decide_eq_true_iff, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

theorem maskKey_eq {b b' : List ℕ} (hb : ∀ x ∈ b, x < 2 ^ n) (hb' : ∀ x ∈ b', x < 2 ^ n)
    (h : maskSub n b = maskSub n b') : maskKey b = maskKey b' := by
  have key : ∀ {c c' : List ℕ}, (∀ x ∈ c, x < 2 ^ n) → (∀ x ∈ c', x < 2 ^ n) →
      maskSub n c = maskSub n c' → ∀ m ∈ combos c, m ∈ combos c' := by
    intro c c' hc hc' he m hm
    have hmem : toW n m ∈ maskSub n c' := he ▸ toW_mem_maskSub hm
    obtain ⟨m', hm', he'⟩ := hmem
    rwa [← toW_inj (combos_lt hc' m' hm') (combos_lt hc m hm) he']
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Bool.eq_iff_iff, maskKey, maskKey, testBit_foldr_or, testBit_foldr_or]
  exact ⟨key hb hb' h i, key hb' hb h.symm i⟩

@[expose] def orbBases (cs : List (List ℕ)) (d : List ℕ) :
    List (List ℕ) → List (ℕ × ℕ) → List (List ℕ)
  | bs, [] => bs
  | bs, (g, i) :: st => orbBases cs d (bs ++ [(bs.getD i d).map (actM (cs.getD g []))]) st

theorem mem_orbBases {G : Subgroup (MulAut (Wn n))} {gs : List (MulAut (Wn n))}
    {cs : List (List ℕ)} (hmem : ∀ i < gs.length, gs.getD i 1 ∈ G)
    (hact : ∀ i < gs.length, ActsBy (gs.getD i 1) (cs.getD i [])) (d : List ℕ) :
    ∀ (st : List (ℕ × ℕ)) (bs : List (List ℕ)), (∀ e ∈ st, e.1 < gs.length) →
      (∀ b ∈ bs, ∃ h ∈ G, (maskSub n d).map h.toMonoidHom = maskSub n b) →
      ∀ b ∈ orbBases cs d bs st, ∃ h ∈ G, (maskSub n d).map h.toMonoidHom = maskSub n b
  | [], bs, _, hbs => hbs
  | (g, i) :: st, bs, hst, hbs => by
    refine mem_orbBases hmem hact d st _ (fun e he => hst e (List.mem_cons_of_mem _ he)) ?_
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hbs b hb
    · rw [List.mem_singleton] at hb
      subst hb
      have hg := hst (g, i) List.mem_cons_self
      have hpar : ∃ h ∈ G, (maskSub n d).map h.toMonoidHom = maskSub n (bs.getD i d) := by
        by_cases hi : i < bs.length
        · rw [List.getD_eq_getElem _ _ hi]
          exact hbs _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega)]
          refine ⟨1, G.one_mem, ?_⟩
          ext v
          constructor
          · rintro ⟨u, hu, rfl⟩
            exact hu
          · intro hv
            exact ⟨v, hv, rfl⟩
      obtain ⟨h, hh, he⟩ := hpar
      refine ⟨gs.getD g 1 * h, G.mul_mem (hmem g hg) hh, ?_⟩
      exact (map_mul_toMonoidHom (maskSub n d) _ _).trans
        ((congrArg (fun U => U.map (gs.getD g 1).toMonoidHom) he).trans
          (maskSub_map (hact g hg) _))

theorem card_stab_le_of_orb [NeZero n] {G : Subgroup (MulAut (Wn n))}
    {gs : List (MulAut (Wn n))} {cs : List (List ℕ)} (hmem : ∀ i < gs.length, gs.getD i 1 ∈ G)
    (hact : ∀ i < gs.length, ActsBy (gs.getD i 1) (cs.getD i [])) {d : List ℕ}
    {st : List (ℕ × ℕ)} (hst : ∀ e ∈ st, e.1 < gs.length)
    (hlt : ∀ b ∈ orbBases cs d [d] st, ∀ x ∈ b, x < 2 ^ n)
    (hnd : ((orbBases cs d [d] st).map maskKey).Nodup) :
    (orbBases cs d [d] st).length * Nat.card ↥(G ⊓ stabSub (maskSub n d)) ≤ Nat.card ↥G := by
  set L := orbBases cs d [d] st with hL
  have hspec := mem_orbBases hmem hact d st [d] hst (fun b hb => by
    rw [List.mem_singleton] at hb
    subst hb
    refine ⟨1, G.one_mem, ?_⟩
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hv
      exact ⟨v, hv, rfl⟩)
  choose g hg hge using fun i : Fin L.length => hspec (L.get i) (List.get_mem L i)
  refine card_stab_mul_le g hg fun i j hij => ?_
  have h1 : maskSub n (L.get i) = maskSub n (L.get j) := (hge i).symm.trans (hij.trans (hge j))
  have h2 := maskKey_eq (hlt _ (List.get_mem L i)) (hlt _ (List.get_mem L j)) h1
  have h3 : (L.map maskKey).get ⟨i, by simp⟩ = (L.map maskKey).get ⟨j, by simp⟩ := by
    simpa using h2
  have h4 := (List.Nodup.get_inj_iff hnd).1 h3
  exact Fin.ext (by simpa using h4)

theorem le_card_of_keys {G : Type*} [Group G] {K : Subgroup G} [Finite K] (key : G → ℕ)
    {l : List ℕ} (hnd : l.Nodup) (hex : ∀ k ∈ l, ∃ g ∈ K, key g = k) : l.length ≤ Nat.card K := by
  choose g hg hge using fun i : Fin l.length => hex (l.get i) (List.get_mem l i)
  have hinj : Function.Injective fun i : Fin l.length => (⟨g i, hg i⟩ : K) := by
    intro i j h
    have h1 : l.get i = l.get j := by
      rw [← hge i, ← hge j]
      exact congrArg key (congrArg Subtype.val h)
    exact (List.Nodup.get_inj_iff hnd).1 h1
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h

theorem le_card_of_tree {G : Type*} [Group G] {K : Subgroup G} [Finite K] (key : G → ℕ)
    (act : ℕ → ℕ → ℕ) (hact : ∀ gi m, (∃ g ∈ K, key g = m) → ∃ g ∈ K, key g = act gi m)
    {start : ℕ} (hs : ∃ g ∈ K, key g = start) {tree : List (ℕ × ℕ × ℕ)}
    (htree : treeB act tree (1 <<< start) = true) : tree.length + 1 ≤ Nat.card K := by
  have hseen : ∀ m, (1 <<< start : ℕ).testBit m = true → ∃ g ∈ K, key g = m := by
    intro m hm
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hm
    rw [← of_decide_eq_true hm]
    exact hs
  obtain ⟨h1, h2, h3⟩ := treeB_spec act _ hact tree _ hseen htree
  have hnd : (start :: tree.map Prod.fst).Nodup := by
    refine List.nodup_cons.2 ⟨fun h => ?_, h2⟩
    obtain ⟨e, he, hes⟩ := List.mem_map.1 h
    have := h3 e he
    rw [hes, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at this
    exact Bool.noConfusion this
  have h := le_card_of_keys key hnd fun k hk => by
    rcases List.mem_cons.1 hk with rfl | hk
    · exact hs
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
      exact h1 e he
  simpa using h

theorem card_mul_le_of_keys {G : Type*} [Group G] {K C : Subgroup G} [Finite K] (hC : C ≤ K)
    (key : G → ℕ) (hkey : ∀ φ ∈ K, ∀ ψ ∈ C, key (φ * ψ) = key φ) {l : List ℕ} (hnd : l.Nodup)
    (hex : ∀ k ∈ l, ∃ g ∈ K, key g = k) : l.length * Nat.card C ≤ Nat.card K := by
  have : Finite C := Finite.of_injective _ (Subgroup.inclusion_injective hC)
  choose g hg hge using fun i : Fin l.length => hex (l.get i) (List.get_mem l i)
  have hinj : Function.Injective fun p : Fin l.length × C =>
      (⟨g p.1 * p.2, K.mul_mem (hg p.1) (hC p.2.2)⟩ : K) := by
    rintro ⟨i, ψ⟩ ⟨j, ψ'⟩ h
    have h1 : g i * ψ = g j * ψ' := congrArg Subtype.val h
    have h2 : l.get i = l.get j := by
      rw [← hge i, ← hge j, ← hkey _ (hg i) _ ψ.2, ← hkey _ (hg j) _ ψ'.2, h1]
    have hij : i = j := (List.Nodup.get_inj_iff hnd).1 h2
    subst hij
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h1))
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin l.length), Fintype.card_fin] at h

theorem card_mul_le_of_tree {G : Type*} [Group G] {K C : Subgroup G} [Finite K] (hC : C ≤ K)
    (key : G → ℕ) (hkey : ∀ φ ∈ K, ∀ ψ ∈ C, key (φ * ψ) = key φ) (act : ℕ → ℕ → ℕ)
    (hact : ∀ gi m, (∃ g ∈ K, key g = m) → ∃ g ∈ K, key g = act gi m) {start : ℕ}
    (hs : ∃ g ∈ K, key g = start) {tree : List (ℕ × ℕ × ℕ)}
    (htree : treeB act tree (1 <<< start) = true) :
    (tree.length + 1) * Nat.card C ≤ Nat.card K := by
  have hseen : ∀ m, (1 <<< start : ℕ).testBit m = true → ∃ g ∈ K, key g = m := by
    intro m hm
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hm
    rw [← of_decide_eq_true hm]
    exact hs
  obtain ⟨h1, h2, h3⟩ := treeB_spec act _ hact tree _ hseen htree
  have hnd : (start :: tree.map Prod.fst).Nodup := by
    refine List.nodup_cons.2 ⟨fun h => ?_, h2⟩
    obtain ⟨e, he, hes⟩ := List.mem_map.1 h
    have := h3 e he
    rw [hes, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at this
    exact Bool.noConfusion this
  have h := card_mul_le_of_keys hC key hkey hnd fun k hk => by
    rcases List.mem_cons.1 hk with rfl | hk
    · exact hs
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
      exact h1 e he
  simpa using h

@[expose] noncomputable def maskOf (n : ℕ) (w : Wn n) : ℕ := Classical.choose (toW_surj n w)

theorem maskOf_spec (w : Wn n) : maskOf n w < 2 ^ n ∧ toW n (maskOf n w) = w :=
  Classical.choose_spec (toW_surj n w)

theorem maskOf_toW {m : ℕ} (hm : m < 2 ^ n) : maskOf n (toW n m) = m :=
  toW_inj (maskOf_spec _).1 hm (maskOf_spec _).2

@[expose] noncomputable def tupKey (n k : ℕ) (D : List ℕ) (us : List ℕ) (φ : MulAut (Wn n)) : ℕ :=
  us.foldr (fun u acc => actM D (maskOf n (φ (toW n u))) + 2 ^ k * acc) 0

@[expose] def tupAct (k : ℕ) (D B c : List ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | len + 1, key =>
    actM D (actM c (actM B (key % 2 ^ k))) + 2 ^ k * tupAct k D B c len (key / 2 ^ k)

theorem tupKey_cons (k : ℕ) (D : List ℕ) (u : ℕ) (us : List ℕ) (φ : MulAut (Wn n)) :
    tupKey n k D (u :: us) φ = actM D (maskOf n (φ (toW n u))) + 2 ^ k * tupKey n k D us φ :=
  rfl

theorem tupKey_mul {k : ℕ} {D B c : List ℕ} {g φ : MulAut (Wn n)} (hg : ActsBy g c)
    (hc : ∀ x ∈ c, x < 2 ^ n) {M : ℕ → Prop} (hM : ∀ m, M m → actM B (actM D m) = m ∧
      actM D m < 2 ^ k) :
    ∀ us : List ℕ, (∀ u ∈ us, M (maskOf n (φ (toW n u)))) →
      tupKey n k D us (g * φ) = tupAct k D B c us.length (tupKey n k D us φ)
  | [], _ => rfl
  | u :: us, hu => by
    have h1 := hM _ (hu u List.mem_cons_self)
    rw [tupKey_cons, tupKey_cons, List.length_cons, tupAct,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1.2,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt h1.2, Nat.zero_add, h1.1,
      ← tupKey_mul hg hc hM us fun v hv => hu v (List.mem_cons_of_mem u hv)]
    congr 2
    rw [MulAut.mul_apply]
    conv_lhs => rw [← (maskOf_spec (φ (toW n u))).2, hg, maskOf_toW (actM_lt hc _)]

theorem tupKey_mul_fix {k : ℕ} {D : List ℕ} {φ ψ : MulAut (Wn n)} :
    ∀ us : List ℕ, (∀ u ∈ us, ψ (toW n u) = toW n u) →
      tupKey n k D us (φ * ψ) = tupKey n k D us φ
  | [], _ => rfl
  | u :: us, hu => by
    rw [tupKey_cons, tupKey_cons, MulAut.mul_apply, hu u List.mem_cons_self,
      tupKey_mul_fix us fun v hv => hu v (List.mem_cons_of_mem u hv)]

theorem tupKey_one {k : ℕ} {D : List ℕ} :
    ∀ us : List ℕ, (∀ u ∈ us, u < 2 ^ n) →
      tupKey n k D us 1 = us.foldr (fun u acc => actM D u + 2 ^ k * acc) 0
  | [], _ => rfl
  | u :: us, hu => by
    rw [tupKey_cons, List.foldr_cons, MulAut.one_apply, maskOf_toW (hu u List.mem_cons_self),
      tupKey_one us fun v hv => hu v (List.mem_cons_of_mem u hv)]

end CFSG.Quasithin.H.Parab
