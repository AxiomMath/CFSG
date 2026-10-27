module

public import CFSG.Sporadic.Fi23.Tr.Orbit

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem cs_ok :
    trCsOK orb dT biT cB tB = true := tr_parts.2.2.2.2.2.2.2.2.1

theorem dom_ok' :
    trDomOK orb dT biT cB tB trc.domW trc.ncW = true := tr_parts.2.2.2.2.2.2.2.1

theorem row_ok :
    trRowOK orb trc.orb tdd tbi tB trc.rowInv = true :=
  tr_parts.2.2.2.2.2.2.2.2.2.2.1

theorem far_ok :
    trFarOK orb trc.orb tdd tbi tB trc.rowInv phiT trc.v0 trc.farTree = true :=
  tr_parts.2.2.2.2.2.2.2.2.2.2.2.1

theorem mu_ok :
    trMuOK orb trc.orb tdd tbi trc.rowInv trc.v0 trc.mOrd trc.mPar trc.mWit trc.mH trc.muPos =
      true :=
  tr_parts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ed_ok :
    trEdOK orb trc.orb tdd tbi trc.rowInv trc.v0 trc.mOrd trc.edX trc.edK = true :=
  tr_parts.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem trData_lt
    {k : ℕ} (hk : k < 3240) : trData[k]! < 31671 := by
  obtain ⟨-, hinc, hlast⟩ := trIncOK_spec tr_parts.2.1
  have : ∀ m, k + m ≤ 3239 → trData[k]! + m ≤ trData[k + m]! := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hinc (k + m) (by omega)
      have e : k + (m + 1) = k + m + 1 := by omega
      rw [e]
      omega
  have := this (3239 - k) (by omega)
  rw [show k + (3239 - k) = 3239 by omega] at this
  have hl : trData[3239]! < 31671 := hlast
  omega

theorem ncard_trRoot :
    trRoot.ncard = 3240 := by
  obtain ⟨hsz, hinc, -⟩ := trIncOK_spec tr_parts.2.1
  set f : Fin 3240 → Fin 31671 := fun m => ⟨trData[m.val]!, trData_lt m.2⟩ with hf
  have hmono : StrictMono f := by
    rw [Fin.strictMono_iff_lt_succ]
    intro m
    exact hinc m.val m.2
  have hset : {k : Fin 31671 | k.val ∈ trData} = Set.range f := by
    ext k
    show k.val ∈ trData ↔ _
    rw [Array.mem_iff_getElem]
    constructor
    · rintro ⟨l, hl, hlk⟩
      refine ⟨⟨l, by omega⟩, Fin.ext ?_⟩
      show trData[l]! = k.val
      rw [getElem!_pos trData l hl, hlk]
    · rintro ⟨m, rfl⟩
      exact ⟨m.val, by omega, by rw [← getElem!_pos trData m.val (by omega)]⟩
  unfold trRoot
  rw [Set.ncard_image_of_injective _ ptD23.injective, hset,
    Set.ncard_range_of_injective hmono.injective, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_of_mem_trOrbit
    {T : Set D23} (hT : T ∈ trOrbit) : T.ncard = 3240 := by
  obtain ⟨g, rfl⟩ := hT
  rw [Set.ncard_image_of_injective _ (Pair.conjPerm pair_J g).injective, ncard_trRoot]

theorem conjPerm_tv (g : J) (f y : D23) :
    Pair.conjPerm pair_J g ((pairModel pair_J).tv f y) =
      (pairModel pair_J).tv (Pair.conjPerm pair_J g f) (Pair.conjPerm pair_J g y) :=
  Pair.conjPerm_tauE pair_J g f y

theorem conjPerm_image_tv (g : J) (f : D23) (U : Set D23) :
    ⇑(Pair.conjPerm pair_J g) '' ((pairModel pair_J).tv f '' U) =
      (pairModel pair_J).tv (Pair.conjPerm pair_J g f) '' (⇑(Pair.conjPerm pair_J g) '' U) := by
  rw [Set.image_image, Set.image_image]
  simp only [conjPerm_tv]

theorem tv_image_conjPerm (g : J) (f : D23) (U : Set D23) :
    (pairModel pair_J).tv f '' (⇑(Pair.conjPerm pair_J g) '' U) =
      ⇑(Pair.conjPerm pair_J g) '' ((pairModel pair_J).tv ((Pair.conjPerm pair_J g).symm f) '' U) :=
  by rw [conjPerm_image_tv, Equiv.apply_symm_apply]

theorem conjPerm_commute_iff (g : J) (x y : D23) :
    ((Pair.conjPerm pair_J g x : D23) : J) * Pair.conjPerm pair_J g y =
      Pair.conjPerm pair_J g y * Pair.conjPerm pair_J g x ↔ (x : J) * y = y * x := by
  rw [Pair.conjPerm_apply, Pair.conjPerm_apply, conj_commute_iff]

theorem notMem_conjPerm_image {g : J} {f : D23} {U : Set D23}
    (hf : f ∉ ⇑(Pair.conjPerm pair_J g) '' U) : (Pair.conjPerm pair_J g).symm f ∉ U :=
  fun hm => hf ⟨_, hm, Equiv.apply_symm_apply _ f⟩

theorem mem_tv_image_iff (v z : D23) (U : Set D23) :
    z ∈ (pairModel pair_J).tv v '' U ↔ (pairModel pair_J).tv v z ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [LocalModel.tv_tv]
  · intro h
    exact ⟨_, h, LocalModel.tv_tv _ v z⟩

theorem bitAt_tB_of_notMem
    {k : Fin 31671} (h : ptD23 k ∉ trRoot) : pBit tB k.val = false := by
  rw [ptD23_mem_trRoot] at h
  simpa using h

theorem tv_image_trRoot
    {k : ℕ} (hk : k < 31671) :
    (pairModel pair_J).tv (ptD23 ⟨k, hk⟩) '' trRoot = trSet (trAct orb trc.orb tdd tbi k 0) := by
  rw [← trSet_zero]
  exact tv_image_trSet ⟨k, hk⟩ (by norm_num)

theorem injOn_tv_image_root :
    Set.InjOn (fun f => (pairModel pair_J).tv f '' trRoot) trRootᶜ := by
  intro f₁ hf₁ f₂ hf₂ h
  obtain ⟨-, hrow, -⟩ := trRowOK_spec row_ok
  obtain ⟨k₁, rfl⟩ := ptD23.surjective f₁
  obtain ⟨k₂, rfl⟩ := ptD23.surjective f₂
  have hB₁ := bitAt_tB_of_notMem hf₁
  have hB₂ := bitAt_tB_of_notMem hf₂
  simp only at h
  rw [tv_image_trRoot k₁.2, tv_image_trRoot k₂.2] at h
  have e := trSet_inj (trAct_lt (by norm_num)) (trAct_lt (by norm_num)) h
  have e1 := (hrow _ k₁.2 hB₁).2
  have e2 := (hrow _ k₂.2 hB₂).2
  rw [e] at e1
  exact congrArg ptD23 (Fin.ext (e1.symm.trans e2))

theorem tv_image_ne_root
    {f : D23} (hf : f ∉ trRoot) :
    (pairModel pair_J).tv f '' trRoot ≠ trRoot := by
  obtain ⟨-, hrow, -⟩ := trRowOK_spec row_ok
  obtain ⟨k, rfl⟩ := ptD23.surjective f
  have hB := bitAt_tB_of_notMem hf
  rw [tv_image_trRoot k.2]
  intro h
  rw [← trSet_zero] at h
  exact (hrow _ k.2 hB).1 (trSet_inj (trAct_lt (by norm_num)) (by norm_num) h)

theorem injOn_tv_image
    {T : Set D23} (hT : T ∈ trOrbit) :
    Set.InjOn (fun f => (pairModel pair_J).tv f '' T) Tᶜ := by
  obtain ⟨g, rfl⟩ := hT
  intro f₁ hf₁ f₂ hf₂ h
  simp only [tv_image_conjPerm] at h
  have h' := Set.image_injective.2 (Pair.conjPerm pair_J g).injective h
  exact (Pair.conjPerm pair_J g).symm.injective
    (injOn_tv_image_root (notMem_conjPerm_image hf₁) (notMem_conjPerm_image hf₂) h')

theorem tv_image_ne
    {T : Set D23} (hT : T ∈ trOrbit) {f : D23} (hf : f ∉ T) :
    (pairModel pair_J).tv f '' T ≠ T := by
  obtain ⟨g, rfl⟩ := hT
  rw [tv_image_conjPerm]
  intro h
  exact tv_image_ne_root (notMem_conjPerm_image hf)
    (Set.image_injective.2 (Pair.conjPerm pair_J g).injective h)

theorem exists_not_commute_idx
    {k w : ℕ} (hk : k < 31671) (h1 : w < 31671)
    (h2 : pBit tB w = true) (h3 : tauAct orb dT biT w k ≠ k) :
    ∃ x ∈ trRoot, ¬ ((ptD23 ⟨k, hk⟩ : J) * x = x * ptD23 ⟨k, hk⟩) := by
  refine ⟨ptD23 ⟨w, h1⟩, (ptD23_mem_trRoot' h1).2 h2, fun hc => h3 ?_⟩
  exact (conjPt_commute_iff h1 hk).1 hc.symm

theorem exists_not_commute_root
    {k : ℕ} (hk : k < 31671) (hkB : pBit tB k = false) :
    ∃ x ∈ trRoot, ¬ ((ptD23 ⟨k, hk⟩ : J) * x = x * ptD23 ⟨k, hk⟩) := by
  obtain ⟨-, -, -, h1, h2, h3⟩ := trDomOK_spec dom_ok' hk hkB
  exact exists_not_commute_idx hk h1 h2 h3

theorem exists_not_commute
    {T : Set D23} (hT : T ∈ trOrbit) {f : D23} (hf : f ∉ T) :
    ∃ x ∈ T, ¬ ((f : J) * x = x * f) := by
  obtain ⟨g, rfl⟩ := hT
  have hf' := notMem_conjPerm_image hf
  obtain ⟨k, hk⟩ := ptD23.surjective ((Pair.conjPerm pair_J g).symm f)
  rw [← hk] at hf'
  have hkB := bitAt_tB_of_notMem hf'
  obtain ⟨x, hx, hxc⟩ := exists_not_commute_root k.2 hkB
  refine ⟨Pair.conjPerm pair_J g x, ⟨x, hx, rfl⟩, fun hc => hxc ?_⟩
  have hfk : f = Pair.conjPerm pair_J g (ptD23 k) := by rw [hk, Equiv.apply_symm_apply]
  rw [hfk, conjPerm_commute_iff] at hc
  exact hc

theorem cs_not_inj
    {Ω : Set D23} (hΩ : Ω ∈ cOrbit) : ∃ v w, v ∉ Ω ∧ w ∉ Ω ∧ v ≠ w ∧
    (pairModel pair_J).tv v '' Ω = (pairModel pair_J).tv w '' Ω := by
  obtain ⟨hvw, hv, hw, -, hvC, -, hwC, hall⟩ := trCsOK_spec cs_ok
  have hall' : ∀ y < 31671, pBit cB (act23 csV y) = pBit cB (act23 csW y) := hall
  have hvC' : ptD23 ⟨csV, hv⟩ ∉ cRoot := by rw [ptD23_mem_cRoot]; simpa using hvC
  have hwC' : ptD23 ⟨csW, hw⟩ ∉ cRoot := by rw [ptD23_mem_cRoot]; simpa using hwC
  have hvw' : ptD23 ⟨csV, hv⟩ ≠ ptD23 ⟨csW, hw⟩ := fun e =>
    hvw (congrArg Fin.val (ptD23.injective e))
  have himg : (pairModel pair_J).tv (ptD23 ⟨csV, hv⟩) '' cRoot =
      (pairModel pair_J).tv (ptD23 ⟨csW, hw⟩) '' cRoot := by
    ext z
    obtain ⟨j, rfl⟩ := ptD23.surjective z
    rw [mem_tv_image_iff, mem_tv_image_iff, tv_ptD23, tv_ptD23, ptD23_mem_cRoot',
      ptD23_mem_cRoot', hall' j.val j.2]
  obtain ⟨g, rfl⟩ := hΩ
  refine ⟨Pair.conjPerm pair_J g (ptD23 ⟨csV, hv⟩), Pair.conjPerm pair_J g (ptD23 ⟨csW, hw⟩), ?_,
    ?_, ?_, ?_⟩
  · rw [(Pair.conjPerm pair_J g).injective.mem_set_image]
    exact hvC'
  · rw [(Pair.conjPerm pair_J g).injective.mem_set_image]
    exact hwC'
  · exact fun e => hvw' ((Pair.conjPerm pair_J g).injective e)
  · rw [← conjPerm_image_tv, ← conjPerm_image_tv, himg]

noncomputable abbrev xi24 :
    SimpleGraph trOrbit := (pairModel pair_J).xi trOrbit

@[expose] noncomputable def xi24Vert
    (k : ℕ) : trOrbit :=
  ⟨trSet (k % 137632), trSet_mem_trOrbit (Nat.mod_lt _ (by norm_num))⟩

theorem xi24Vert_val
    {k : ℕ} (hk : k < 137632) : (xi24Vert k : Set D23) = trSet k := by
  show trSet (k % 137632) = trSet k
  rw [Nat.mod_eq_of_lt hk]

theorem xi24Vert_zero :
    xi24Vert 0 = xi24Root := by
  apply Subtype.ext
  rw [xi24Vert_val (by norm_num)]
  exact trSet_zero

theorem xi24Vert_inj
    {k m : ℕ} (hk : k < 137632) (hm : m < 137632)
    (h : xi24Vert k = xi24Vert m) : k = m := by
  have := congrArg Subtype.val h
  rw [xi24Vert_val hk, xi24Vert_val hm] at this
  exact trSet_inj hk hm this

theorem exists_xi24Vert
    (V : trOrbit) : ∃ k < 137632, V = xi24Vert k := by
  obtain ⟨k, hk, hV⟩ := mem_trOrbit_iff.1 V.2
  exact ⟨k, hk, Subtype.ext (by rw [xi24Vert_val hk]; exact hV)⟩

theorem xi24_adj {U V : trOrbit} :
    xi24.Adj U V ↔ U ≠ V ∧ ∃ f, f ∉ (U : Set D23) ∧ (pairModel pair_J).tv f '' (U : Set D23) = V :=
  Iff.rfl

theorem ptD23_notMem_trSet
    {m h : ℕ} (hh : h < 31671) (hnot : pBit trc.orb.sets[m]! h = false) :
    ptD23 ⟨h, hh⟩ ∉ trSet m := by
  unfold trSet
  rw [ptD23_mem_dsetP, Fin.val_mk, hnot]
  exact Bool.false_ne_true

theorem xi24_adj_of_wit
    {m m' h : ℕ} (hm : m < 137632) (hm' : m' < 137632) (hh : h < 31671)
    (hnot : pBit trc.orb.sets[m]! h = false) (hmap : trAct orb trc.orb tdd tbi h m = m') :
    xi24.Adj (xi24Vert m) (xi24Vert m') := by
  have hf := ptD23_notMem_trSet hh hnot
  have himg : (pairModel pair_J).tv (ptD23 ⟨h, hh⟩) '' trSet m = trSet m' := by
    rw [tv_image_trSet ⟨h, hh⟩ hm, Fin.val_mk, hmap]
  refine ⟨fun e => ?_, ptD23 ⟨h, hh⟩, by rw [xi24Vert_val hm]; exact hf, by
    rw [xi24Vert_val hm, xi24Vert_val hm', himg]⟩
  have e' := congrArg Subtype.val e
  rw [xi24Vert_val hm, xi24Vert_val hm'] at e'
  exact tv_image_ne (trSet_mem_trOrbit hm) hf (himg.trans e'.symm)

theorem xi24_adj_iff
    {m : ℕ} (hm : m < 137632) {V : trOrbit} :
    xi24.Adj (xi24Vert m) V ↔ ∃ h < 31671, pBit trc.orb.sets[m]! h = false ∧
      V = xi24Vert (trAct orb trc.orb tdd tbi h m) := by
  constructor
  · rintro ⟨-, f, hf, hfV⟩
    obtain ⟨h, rfl⟩ := ptD23.surjective f
    rw [xi24Vert_val hm] at hf hfV
    have hB : pBit trc.orb.sets[m]! h.val = false := by
      unfold trSet at hf
      rw [ptD23_mem_dsetP] at hf
      simpa using hf
    refine ⟨_, h.2, hB, Subtype.ext ?_⟩
    rw [xi24Vert_val (trAct_lt hm), ← hfV]
    exact tv_image_trSet h hm
  · rintro ⟨h, hh, hB, rfl⟩
    exact xi24_adj_of_wit hm (trAct_lt hm) hh hB rfl

theorem pBit_sets_zero
    {k : ℕ} (hk : k < 31671) : pBit trc.orb.sets[0]! k = pBit tB k :=
  (trOrbitOK_spec trOrb_ok).2.2.2.2.2.1 k hk

theorem xi24_adj_root_iff
    {V : trOrbit} :
    xi24.Adj xi24Root V ↔ ∃ k < 31671, pBit tB k = false ∧
      V = xi24Vert (trAct orb trc.orb tdd tbi k 0) := by
  rw [← xi24Vert_zero, xi24_adj_iff (by norm_num)]
  constructor
  · rintro ⟨h, hh, hB, rfl⟩
    exact ⟨h, hh, by rw [← pBit_sets_zero hh]; exact hB, rfl⟩
  · rintro ⟨h, hh, hB, rfl⟩
    exact ⟨h, hh, by rw [pBit_sets_zero hh]; exact hB, rfl⟩

theorem rowInv_ne_of_eq {k : ℕ} (hk : k < 31671) {m : ℕ} (h : ap trc.rowInv m = k) :
    trc.rowInv[m]! ≠ none32 := by
  intro e
  unfold ap at h
  rw [e] at h
  have : none32.toNat = 4294967295 := rfl
  omega

theorem far_iff
    {V : trOrbit} : (V ≠ xi24Root ∧ ¬ xi24.Adj xi24Root V) ↔
    ∃ m < 137632, trIsFar trc.rowInv m = true ∧ V = xi24Vert m := by
  obtain ⟨-, hrow, hinv⟩ := trRowOK_spec row_ok
  constructor
  · rintro ⟨hne, hadj⟩
    obtain ⟨m, hm, rfl⟩ := exists_xi24Vert V
    refine ⟨m, hm, ?_, rfl⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact hne xi24Vert_zero
    rcases hinv m hm with h | ⟨h1, h2, h3⟩
    · exact trIsFar_iff.2 ⟨hm0, h⟩
    · exact absurd (xi24_adj_root_iff.2 ⟨_, h1, h2, by rw [h3]⟩) hadj
  · rintro ⟨m, hm, hfar, rfl⟩
    obtain ⟨hm0, hnone⟩ := trIsFar_iff.1 hfar
    refine ⟨fun e => hm0 ?_, fun hadj => ?_⟩
    · rw [← xi24Vert_zero] at e
      exact xi24Vert_inj hm (by norm_num) e
    · obtain ⟨k, hk, hkB, e⟩ := xi24_adj_root_iff.1 hadj
      have := xi24Vert_inj hm (trAct_lt (by norm_num)) e
      have h4 := (hrow k hk hkB).2
      rw [← this] at h4
      exact rowInv_ne_of_eq hk h4 hnone

theorem rowInv_ne_of_adj
    {m : ℕ} (hm : m < 137632) (h : xi24.Adj xi24Root (xi24Vert m)) :
    trc.rowInv[m]! ≠ none32 := by
  obtain ⟨-, hrow, -⟩ := trRowOK_spec row_ok
  obtain ⟨k, hk, hkB, e⟩ := xi24_adj_root_iff.1 h
  have := xi24Vert_inj hm (trAct_lt (by norm_num)) e
  have h4 := (hrow k hk hkB).2
  rw [← this] at h4
  exact rowInv_ne_of_eq hk h4

theorem adj_of_rowInv_ne
    {m : ℕ} (hm : m < 137632) (h : trc.rowInv[m]! ≠ none32) :
    xi24.Adj xi24Root (xi24Vert m) := by
  obtain ⟨-, -, hinv⟩ := trRowOK_spec row_ok
  rcases hinv m hm with e | ⟨h1, h2, h3⟩
  · exact absurd e h
  · exact xi24_adj_root_iff.2 ⟨_, h1, h2, by rw [h3]⟩

theorem conjPerm_image_image (g h : J) (S : Set D23) :
    ⇑(Pair.conjPerm pair_J g) '' (⇑(Pair.conjPerm pair_J h) '' S) =
      ⇑(Pair.conjPerm pair_J (g * h)) '' S := by
  rw [← Set.image_comp, ← Equiv.Perm.coe_mul, ← map_mul]

@[expose] noncomputable def xiConj (g : J) : Equiv.Perm trOrbit where
  toFun V := ⟨⇑(Pair.conjPerm pair_J g) '' V, conjPerm_mem_trOrbit V.2 g⟩
  invFun V := ⟨⇑(Pair.conjPerm pair_J g⁻¹) '' V, conjPerm_mem_trOrbit V.2 g⁻¹⟩
  left_inv V := Subtype.ext (by
    dsimp only
    rw [conjPerm_image_image, inv_mul_cancel, map_one, Equiv.Perm.coe_one, Set.image_id])
  right_inv V := Subtype.ext (by
    dsimp only
    rw [conjPerm_image_image, mul_inv_cancel, map_one, Equiv.Perm.coe_one, Set.image_id])

theorem xiConj_val (g : J) (V : trOrbit) :
    (xiConj g V : Set D23) = ⇑(Pair.conjPerm pair_J g) '' V := rfl

theorem xi24_adj_xiConj
    (g : J) {U V : trOrbit} :
    xi24.Adj (xiConj g U) (xiConj g V) ↔ xi24.Adj U V := by
  rw [xi24_adj, xi24_adj, (xiConj g).injective.ne_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨f, hf, hfV⟩
    rw [xiConj_val] at hf
    rw [xiConj_val, xiConj_val, tv_image_conjPerm] at hfV
    exact ⟨(Pair.conjPerm pair_J g).symm f, notMem_conjPerm_image hf,
      Set.image_injective.2 (Pair.conjPerm pair_J g).injective hfV⟩
  · rintro ⟨f, hf, hfV⟩
    refine ⟨Pair.conjPerm pair_J g f, ?_, ?_⟩
    · rw [xiConj_val]
      rintro ⟨y, hy, hyf⟩
      rw [(Pair.conjPerm pair_J g).injective hyf] at hy
      exact hf hy
    · rw [xiConj_val, xiConj_val, ← conjPerm_image_tv, hfV]

@[expose] noncomputable def xiIso
    (g : J) : xi24 ≃g xi24 :=
  ⟨xiConj g, xi24_adj_xiConj g⟩

theorem xiIso_apply
    (g : J) (V : trOrbit) : xiIso g V = xiConj g V := rfl

theorem phiT_get
    {l : ℕ} (hl : l < 10) {m : ℕ} (hm : m < 137632) :
    ap phiT[l]! m = trAct orb trc.orb tdd tbi xiGens[l]! m := by
  have hs : l < (xiGens.map fun g => (Array.ofFn (n := 137632) fun m =>
      UInt32.ofNat (trAct orb trc.orb tdd tbi g m.val))).size := by
    rw [Array.size_map, xiGens_size]
    exact hl
  rw [phiT_eq, trPhi, getElem!_pos _ l hs, Array.getElem_map, ap_ofFn _ hm, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt ((trAct_lt hm).trans (by norm_num)),
    getElem!_pos xiGens l (by rw [xiGens_size]; exact hl)]

theorem xiConj_root
    {l : ℕ} (hl : l < 10) : xiConj (conjPt xiGens[l]!) xi24Root = xi24Root := by
  obtain ⟨h, -⟩ := trFarOK_spec far_ok
  apply Subtype.ext
  rw [xiConj_val]
  show ⇑(Pair.conjPerm pair_J (conjPt xiGens[l]!)) '' trRoot = trRoot
  rw [← trSet_zero, conjPerm_image_trSet_conjPt _ (by norm_num), (h l hl).2.2]

theorem xiConj_xi24Vert
    {l m : ℕ} (hl : l < 10) (hm : m < 137632) :
    xiConj (conjPt xiGens[l]!) (xi24Vert m) = xi24Vert (ap phiT[l]! m) := by
  apply Subtype.ext
  rw [xiConj_val, phiT_get hl hm, xi24Vert_val hm, xi24Vert_val (trAct_lt hm)]
  exact conjPerm_image_trSet_conjPt _ hm

@[expose] def MUat (v : trOrbit) : Prop :=
  (xi24.induce {x | xi24.Adj xi24Root x ∧ xi24.Adj x v}).Connected

@[expose] def EDat (v : trOrbit) : Prop :=
  ∀ w, w ≠ xi24Root → ¬ xi24.Adj xi24Root w → xi24.Adj v w →
    ∃ x, xi24.Adj xi24Root x ∧ xi24.Adj x v ∧ xi24.Adj x w

theorem MUat_iso
    (φ : xi24 ≃g xi24) (hφ : φ xi24Root = xi24Root) {v : trOrbit}
    (h : MUat v) : MUat (φ v) := by
  have hS : ∀ x, (xi24.Adj xi24Root x ∧ xi24.Adj x v) ↔
      (xi24.Adj xi24Root (φ x) ∧ xi24.Adj (φ x) (φ v)) := by
    intro x
    have e1 : xi24.Adj xi24Root (φ x) ↔ xi24.Adj xi24Root x := by
      conv_lhs => rw [← hφ]
      exact φ.map_adj_iff
    rw [e1, φ.map_adj_iff]
  let e : {x | xi24.Adj xi24Root x ∧ xi24.Adj x v} ≃
      {x | xi24.Adj xi24Root x ∧ xi24.Adj x (φ v)} :=
    φ.toEquiv.subtypeEquiv fun x => hS x
  let iso : xi24.induce {x | xi24.Adj xi24Root x ∧ xi24.Adj x v} ≃g
      xi24.induce {x | xi24.Adj xi24Root x ∧ xi24.Adj x (φ v)} :=
    { toEquiv := e
      map_rel_iff' := fun {a b} => by
        show xi24.Adj (φ a.1) (φ b.1) ↔ xi24.Adj a.1 b.1
        exact φ.map_adj_iff }
  exact iso.connected_iff.1 h

theorem EDat_iso
    (φ : xi24 ≃g xi24) (hφ : φ xi24Root = xi24Root) {v : trOrbit}
    (h : EDat v) : EDat (φ v) := by
  intro w hw hrw hvw
  have hw' : φ (φ.symm w) = w := φ.apply_symm_apply w
  obtain ⟨x, h1, h2, h3⟩ := h (φ.symm w)
    (fun e => hw (by rw [← hw', e, hφ]))
    (fun e => hrw (by rw [← hw', ← hφ]; exact φ.map_adj_iff.2 e))
    (φ.map_adj_iff.1 (by rw [hw']; exact hvw))
  refine ⟨φ x, ?_, φ.map_adj_iff.2 h2, ?_⟩
  · rw [← hφ]
    exact φ.map_adj_iff.2 h1
  · rw [← hw']
    exact φ.map_adj_iff.2 h3

theorem v0_facts :
    trc.v0 < 137632 ∧ trIsFar trc.rowInv trc.v0 = true :=
  ⟨(trFarOK_spec far_ok).2.1, (trFarOK_spec far_ok).2.2.1⟩

theorem mu_mem
    {k : ℕ} (hk : k < trc.mOrd.size) :
    xi24.Adj xi24Root (xi24Vert trc.mOrd[k]!) ∧
      xi24.Adj (xi24Vert trc.mOrd[k]!) (xi24Vert trc.v0) := by
  obtain ⟨-, hord, -, -⟩ := trMuOK_spec mu_ok
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hord k hk
  obtain ⟨hv0, -⟩ := v0_facts
  exact ⟨adj_of_rowInv_ne h1 h2, (xi24_adj_of_wit hv0 h1 h3 h4 h5).symm⟩

theorem MUat_v0 :
    MUat (xi24Vert trc.v0) := by
  obtain ⟨hpos, hord, htree, hcov⟩ := trMuOK_spec mu_ok
  obtain ⟨hv0, -⟩ := v0_facts
  unfold MUat
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have hmem : ∀ k (hk : k < trc.mOrd.size), xi24Vert trc.mOrd[k]! ∈
      {x | xi24.Adj xi24Root x ∧ xi24.Adj x (xi24Vert trc.v0)} := fun k hk => mu_mem hk
  have hreach : ∀ k (hk : k < trc.mOrd.size),
      (xi24.induce {x | xi24.Adj xi24Root x ∧ xi24.Adj x (xi24Vert trc.v0)}).Reachable
        ⟨_, hmem 0 hpos⟩ ⟨_, hmem k hk⟩ := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rfl
      · obtain ⟨hp, hwl, hnot, hmap⟩ := htree k hk0 hk
        have hpk : trc.mPar[k]! < trc.mOrd.size := by omega
        refine (ih _ hp hpk).trans (SimpleGraph.Adj.reachable ?_)
        rw [SimpleGraph.induce_adj]
        exact xi24_adj_of_wit (hord _ hpk).1 (hord k hk).1 hwl hnot hmap
  refine ⟨⟨_, hmem 0 hpos⟩, fun x => ?_⟩
  obtain ⟨V, h1, h2⟩ := x
  obtain ⟨m, hm, rfl⟩ := exists_xi24Vert V
  have hne := rowInv_ne_of_adj hm h1
  obtain ⟨h, hh, hB, hV⟩ := (xi24_adj_iff hv0).1 h2.symm
  have hmh := xi24Vert_inj hm (trAct_lt hv0) hV
  rw [hmh] at hne
  obtain ⟨hpos', hpts⟩ := hcov h hh hB hne
  have e : (⟨xi24Vert m, h1, h2⟩ : {x | xi24.Adj xi24Root x ∧ xi24.Adj x (xi24Vert trc.v0)}) =
      ⟨_, hmem _ hpos'⟩ := by
    apply Subtype.ext
    show xi24Vert m = xi24Vert trc.mOrd[ap trc.muPos (trAct orb trc.orb tdd tbi h trc.v0)]!
    rw [hpts, hmh]
  rw [e]
  exact hreach _ hpos'

theorem EDat_v0 :
    EDat (xi24Vert trc.v0) := by
  obtain ⟨hv0, -⟩ := v0_facts
  obtain ⟨-, hord, -, -⟩ := trMuOK_spec mu_ok
  intro w hw0 hrw hvw
  obtain ⟨h, hh, hB, rfl⟩ := (xi24_adj_iff hv0).1 hvw
  obtain ⟨m, hm, hfar, hwm⟩ := far_iff.1 ⟨hw0, hrw⟩
  have := xi24Vert_inj (trAct_lt hv0) hm hwm
  rw [← this] at hfar
  obtain ⟨g1, g2, g3, g4⟩ := trEdOK_spec ed_ok hh hB hfar
  refine ⟨xi24Vert trc.mOrd[trc.edX[h]!]!, (mu_mem g1).1, (mu_mem g1).2, ?_⟩
  exact xi24_adj_of_wit (hord _ g1).1 (trAct_lt hv0) g2 g3 g4

theorem far_facts :
    ∀ k < trc.farTree.pts.size,
    MUat (xi24Vert (ap trc.farTree.pts k)) ∧ EDat (xi24Vert (ap trc.farTree.pts k)) := by
  obtain ⟨-, -, -, htree, -⟩ := trFarOK_spec far_ok
  obtain ⟨-, h0, hall⟩ := treeOK_spec' htree
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h0]
      exact ⟨MUat_v0, EDat_v0⟩
    · obtain ⟨hp, hl, he⟩ := (hall k hk).2 hk0
      rw [Array.mem_range] at hl
      have hpk : ap trc.farTree.par k < trc.farTree.pts.size := by omega
      obtain ⟨hmu, hed⟩ := ih _ hp hpk
      have hpm := (hall _ hpk).1
      have e : xi24Vert (ap trc.farTree.pts k) = xiIso (conjPt xiGens[ap trc.farTree.lab k]!)
          (xi24Vert (ap trc.farTree.pts (ap trc.farTree.par k))) := by
        rw [xiIso_apply, xiConj_xi24Vert hl hpm, he]
      rw [e]
      exact ⟨MUat_iso _ (xiConj_root hl) hmu, EDat_iso _ (xiConj_root hl) hed⟩

theorem far_MU_ED
    {v : trOrbit} (h0 : v ≠ xi24Root) (h1 : ¬ xi24.Adj xi24Root v) :
    MUat v ∧ EDat v := by
  obtain ⟨m, hm, hfar, rfl⟩ := far_iff.1 ⟨h0, h1⟩
  obtain ⟨-, -, -, -, hcov⟩ := trFarOK_spec far_ok
  have hin := hcov m hm hfar
  simp only [inTreeB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hin
  obtain ⟨hpos, hpts⟩ := hin
  have := far_facts _ hpos
  rwa [hpts] at this

theorem xi24_MU :
    ∀ v, v ≠ xi24Root → ¬ ((pairModel pair_J).xi trOrbit).Adj xi24Root v →
    (((pairModel pair_J).xi trOrbit).induce
      {x | ((pairModel pair_J).xi trOrbit).Adj xi24Root x ∧
        ((pairModel pair_J).xi trOrbit).Adj x v}).Connected :=
  fun _ h0 h1 => (far_MU_ED h0 h1).1

theorem xi24_D2 :
    ∀ v, v ≠ xi24Root → ¬ ((pairModel pair_J).xi trOrbit).Adj xi24Root v →
    ∃ x, ((pairModel pair_J).xi trOrbit).Adj xi24Root x ∧
      ((pairModel pair_J).xi trOrbit).Adj x v := by
  intro v h0 h1
  have := (far_MU_ED h0 h1).1.nonempty
  obtain ⟨⟨x, hx⟩⟩ := this
  exact ⟨x, hx⟩

theorem xi24_ED :
    ∀ v w, v ≠ xi24Root → ¬ ((pairModel pair_J).xi trOrbit).Adj xi24Root v →
    w ≠ xi24Root → ¬ ((pairModel pair_J).xi trOrbit).Adj xi24Root w →
    ((pairModel pair_J).xi trOrbit).Adj v w →
    ∃ x, ((pairModel pair_J).xi trOrbit).Adj xi24Root x ∧
      ((pairModel pair_J).xi trOrbit).Adj x v ∧ ((pairModel pair_J).xi trOrbit).Adj x w :=
  fun _ w h0 h1 hw0 hw1 hvw => (far_MU_ED h0 h1).2 w hw0 hw1 hvw

end CFSG.Sporadic.Fi23
