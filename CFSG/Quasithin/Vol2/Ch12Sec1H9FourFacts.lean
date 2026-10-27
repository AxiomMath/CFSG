module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9FourModel
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Iso

public section

namespace CFSG.Quasithin.H13.H9Four

open CFSG.Open CFSG.Quasithin.E3

theorem Elt.inv_b (e : Elt) : e.inv.b = e.b := by
  cases h : e.b <;> simp [Elt.inv, h]

@[expose] def modelL4 : Subgroup (MulAut Pt) where
  carrier := {x | ∃ e : Elt, e.valid = true ∧ e.b = false ∧ e.sem = x}
  mul_mem' := fun ⟨e, he, heb, h1⟩ ⟨f, hf, hfb, h2⟩ =>
    ⟨e.mul f, Elt.valid_mul he hf, by
      show xor e.b f.b = false
      rw [heb, hfb]
      rfl, by rw [Elt.sem_mul he hf, h1, h2]⟩
  one_mem' := ⟨Elt.one, Elt.valid_one, rfl, Elt.sem_one⟩
  inv_mem' := fun ⟨e, he, heb, h1⟩ =>
    ⟨e.inv, Elt.valid_inv he, by rw [Elt.inv_b, heb], by rw [Elt.sem_inv he, h1]⟩

theorem modelL4_le : modelL4 ≤ modelM4 := fun _ ⟨e, he, _, h⟩ => ⟨e, he, h⟩

theorem Elt.sem_mem_modelL4_iff {e : Elt} (he : e.valid = true) :
    e.sem ∈ modelL4 ↔ e.b = false := by
  constructor
  · rintro ⟨f, hf, hfb, h⟩
    rw [← Elt.sem_injective hf he h, hfb]
  · intro hb
    exact ⟨e, he, hb, rfl⟩

theorem Elt.sem_ne_one {e : Elt} (he : e.valid = true) (h1 : e ≠ Elt.one) : e.sem ≠ 1 :=
  fun h => h1 (Elt.sem_injective he Elt.valid_one (by rw [h, Elt.sem_one]))

theorem conj_mem_modelL4 {m x : MulAut Pt} (hm : m ∈ modelM4) (hx : x ∈ modelL4) :
    m * x * m⁻¹ ∈ modelL4 := by
  obtain ⟨e, he, rfl⟩ := hm
  obtain ⟨f, hf, hfb, rfl⟩ := hx
  refine ⟨(e.mul f).mul e.inv, Elt.valid_mul (Elt.valid_mul he hf) (Elt.valid_inv he), ?_, ?_⟩
  · show xor (xor e.b f.b) e.inv.b = false
    rw [Elt.inv_b, hfb]
    cases e.b <;> rfl
  · rw [Elt.sem_mul (Elt.valid_mul he hf) (Elt.valid_inv he), Elt.sem_mul he hf, Elt.sem_inv he]

theorem conjAut_le_modelL4 {X : Subgroup (MulAut Pt)} (hX : X ≤ modelL4) {m : MulAut Pt}
    (hm : m ∈ modelM4) : conjAut X m ≤ modelL4 := by
  intro x hx
  have h := conj_mem_modelL4 hm (hX (H9Conj.mem_conjAut.mp hx))
  rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h

@[expose] def ptW₁ : Subgroup Pt where
  carrier := {w | w.2 = 1}
  mul_mem' := fun {a b} (ha : a.2 = 1) (hb : b.2 = 1) =>
    show a.2 * b.2 = 1 by rw [ha, hb, one_mul]
  one_mem' := rfl
  inv_mem' := fun {a} (ha : a.2 = 1) => show a.2⁻¹ = 1 by rw [ha]; exact inv_one

@[expose] def ptW₂ : Subgroup Pt where
  carrier := {w | w.1 = 1}
  mul_mem' := fun {a b} (ha : a.1 = 1) (hb : b.1 = 1) =>
    show a.1 * b.1 = 1 by rw [ha, hb, one_mul]
  one_mem' := rfl
  inv_mem' := fun {a} (ha : a.1 = 1) => show a.1⁻¹ = 1 by rw [ha]; exact inv_one

theorem mem_ptW₁ {w : Pt} : w ∈ ptW₁ ↔ w.2 = 1 := Iff.rfl

theorem mem_ptW₂ {w : Pt} : w ∈ ptW₂ ↔ w.1 = 1 := Iff.rfl

theorem Mat.app_one' (v : Mat) : v.app 1 = 1 := by
  simp [Mat.app]

theorem Elt.act_of_false {e : Elt} (hb : e.b = false) (w : Pt) :
    e.act w = (e.a.app w.1, (Mat.tr e.ai).app w.2) := by
  simp only [Elt.act, hb, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem Elt.act_of_true {e : Elt} (hb : e.b = true) (w : Pt) :
    e.act w = (e.a.app w.2, (Mat.tr e.ai).app w.1) := by
  simp only [Elt.act, hb, ↓reduceIte]
  rfl

theorem Elt.act_W₁ {e : Elt} (hb : e.b = false) {w : Pt} (hw : w ∈ ptW₁) : e.act w ∈ ptW₁ := by
  rw [Elt.act_of_false hb]
  show (Mat.tr e.ai).app w.2 = 1
  rw [mem_ptW₁.mp hw, Mat.app_one']

theorem Elt.act_W₂ {e : Elt} (hb : e.b = false) {w : Pt} (hw : w ∈ ptW₂) : e.act w ∈ ptW₂ := by
  rw [Elt.act_of_false hb]
  show e.a.app w.1 = 1
  rw [mem_ptW₂.mp hw, Mat.app_one']

theorem Elt.act_W₁_swap {e : Elt} (hb : e.b = true) {w : Pt} (hw : w ∈ ptW₁) :
    e.act w ∈ ptW₂ := by
  rw [Elt.act_of_true hb]
  show e.a.app w.2 = 1
  rw [mem_ptW₁.mp hw, Mat.app_one']

theorem Elt.act_W₂_swap {e : Elt} (hb : e.b = true) {w : Pt} (hw : w ∈ ptW₂) :
    e.act w ∈ ptW₁ := by
  rw [Elt.act_of_true hb]
  show (Mat.tr e.ai).app w.1 = 1
  rw [mem_ptW₂.mp hw, Mat.app_one']

theorem map_ptW {e : Elt} (he : e.valid = true) {U U' : Subgroup Pt}
    (h : ∀ w ∈ U, e.act w ∈ U') (h' : ∀ w ∈ U', e.inv.act w ∈ U) :
    U.map e.sem.toMonoidHom = U' := by
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, Elt.sem_apply he]
    exact h w hw
  · intro hu
    refine ⟨e.inv.act u, h' u hu, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, Elt.sem_apply he, Elt.act_act_inv he]

theorem map_ptW_of_mem {m : MulAut Pt} (hm : m ∈ modelM4) :
    (m ∈ modelL4 ∧ ptW₁.map m.toMonoidHom = ptW₁ ∧ ptW₂.map m.toMonoidHom = ptW₂) ∨
      (m ∉ modelL4 ∧ ptW₁.map m.toMonoidHom = ptW₂ ∧ ptW₂.map m.toMonoidHom = ptW₁) := by
  obtain ⟨e, he, rfl⟩ := hm
  have hib := Elt.inv_b e
  cases hb : e.b
  · rw [hb] at hib
    exact Or.inl ⟨(Elt.sem_mem_modelL4_iff he).mpr hb,
      map_ptW he (fun _ => Elt.act_W₁ hb) fun _ => Elt.act_W₁ hib,
      map_ptW he (fun _ => Elt.act_W₂ hb) fun _ => Elt.act_W₂ hib⟩
  · rw [hb] at hib
    exact Or.inr ⟨fun h => by
        rw [(Elt.sem_mem_modelL4_iff he).mp h] at hb
        exact Bool.noConfusion hb,
      map_ptW he (fun _ => Elt.act_W₁_swap hb) fun _ => Elt.act_W₂_swap hib,
      map_ptW he (fun _ => Elt.act_W₂_swap hb) fun _ => Elt.act_W₁_swap hib⟩

theorem modelL4_le_stabV₁ : modelL4 ≤ stabV ptW₁ := by
  rintro _ ⟨e, he, hb, rfl⟩
  have h := (map_ptW_of_mem (Elt.sem_mem he)).resolve_right
    fun h => h.1 ((Elt.sem_mem_modelL4_iff he).mpr hb)
  intro u
  constructor
  · intro hu
    rw [← h.2.1]
    exact Subgroup.mem_map_of_mem _ hu
  · intro hu
    rw [← h.2.1] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    rwa [← e.sem.injective hwu]

theorem card_ptW₁ : Nat.card ptW₁ = 2 ^ 4 := by
  let e : ptW₁ ≃ (Fin 4 → ZMod 2) :=
    { toFun := fun w => Multiplicative.toAdd (w : Pt).1
      invFun := fun x => ⟨(Multiplicative.ofAdd x, 1), rfl⟩
      left_inv := fun w => Subtype.ext (Prod.ext rfl (mem_ptW₁.mp w.2).symm)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem length_elems (gs : List Elt) : (elems gs).length = 2 ^ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [elems_cons, List.length_append, List.length_map, ih, List.length_cons, pow_succ]
    ring

theorem mem_sub_of_mem_elems {gs : List Elt} (h : Good gs) {e : Elt} (he : e ∈ elems gs) :
    e.sem ∈ sub gs :=
  (mem_sub_iff h.1 h.2.1 h.2.2 _).mpr ⟨e, he, rfl⟩

theorem isElemAbelian2_sub {gs : List Elt} (h : Good gs) : IsElemAbelian2 (sub gs) := by
  have hcomm : (semSet gs).Pairwise Commute := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩ -
    exact h.2.2 g hg g' hg'
  have hc : ∀ x ∈ Subgroup.closure (semSet gs), ∀ y ∈ Subgroup.closure (semSet gs),
      x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val ((Subgroup.isMulCommutative_closure hcomm).is_comm.comm
      (⟨x, hx⟩ : Subgroup.closure (semSet gs)) ⟨y, hy⟩)
  refine ⟨hc, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    rw [pow_two]
    exact h.2.1 g hg
  | one => exact one_pow 2
  | mul y z hy hz ihy ihz =>
    rw [(show Commute y z from hc y hy z hz).mul_pow, ihy, ihz, one_mul]
  | inv y _ ih => rw [inv_pow, ih, inv_one]

theorem isPGroup_sub {gs : List Elt} (h : Good gs) : IsPGroup 2 ↥(sub gs) :=
  isPGroup_of_isElemAbelian2 (isElemAbelian2_sub h)

theorem conjAut_bot (m : MulAut Pt) : conjAut ⊥ m = ⊥ := Subgroup.map_bot _

theorem conjAut_eq_isoAut (X : Subgroup (MulAut Pt)) (m : MulAut Pt) :
    conjAut X m = H9Iso.isoAut m X := by
  unfold conjAut H9Iso.isoAut
  congr 1

theorem card_commV_conjAut (X : Subgroup (MulAut Pt)) (m : MulAut Pt) :
    Nat.card (commV (conjAut X m)) = Nat.card (commV X) := by
  rw [conjAut_eq_isoAut]
  exact H9Iso.card_commV_isoAut m X

theorem mem_zpowers_of_sq {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left
    show x ^ (2 * j) = 1
    rw [zpow_mul, h2, one_zpow]
  · right
    show x ^ (2 * j + 1) = x
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem four_le_card {X : Subgroup (MulAut Pt)} (hX : IsElemAbelian2 X) {x y : MulAut Pt}
    (hx : x ∈ X) (hy : y ∈ X) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) : 4 ≤ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hX.2 x hx
  have hlt : Subgroup.zpowers x < X := by
    refine lt_of_le_of_ne ((Subgroup.zpowers_le).mpr hx) fun h => ?_
    rcases mem_zpowers_of_sq hx2 (by rw [h]; exact hy) with h1 | h1
    · exact hy1 h1
    · exact hxy h1.symm
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1,
    card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian2 hX)] at h1
  rw [card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian2 hX)]
  generalize rk ↥X = r at h1 ⊢
  rcases r with _ | _ | r
  · norm_num at h1
  · norm_num at h1
  · have : 2 ^ 2 ≤ 2 ^ (r + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem exists_two_of_card {X : Subgroup (MulAut Pt)} (hX : IsElemAbelian2 X)
    (h : 2 < Nat.card X) : ∃ x ∈ X, ∃ y ∈ X, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  obtain hbot | ⟨x, hx, hx1⟩ := Subgroup.bot_or_exists_ne_one X
  · rw [hbot, Subgroup.card_bot] at h
    omega
  by_contra hne
  have hle : X ≤ Subgroup.zpowers x := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact Subgroup.one_mem _
    · by_cases hxy : x = y
      · rw [← hxy]
        exact Subgroup.mem_zpowers x
      · exact absurd ⟨x, hx, y, hy, hx1, hy1, hxy⟩ hne
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have := orderOf_le_of_pow_eq_one (by norm_num) (hX.2 x hx)
  omega

theorem mQuot_le_of_card {P X : Subgroup (MulAut Pt)} (hP : IsPGroup 2 ↥P) (hXP : X ≤ P)
    {k : ℕ} (h : Nat.card P ≤ 2 ^ k * Nat.card X) : mQuot P X ≤ k := by
  have h1 := card_eq_two_pow_mul hP hXP
  have hpos : 0 < Nat.card X := Nat.card_pos
  rw [h1] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h hpos)

theorem card_le_of_mQuot {P X : Subgroup (MulAut Pt)} (hP : IsPGroup 2 ↥P) (hXP : X ≤ P)
    {k : ℕ} (h : mQuot P X ≤ k) : Nat.card P ≤ 2 ^ k * Nat.card X := by
  rw [card_eq_two_pow_mul hP hXP]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h)

theorem mem_fixPts_single (e : Elt) (w : Pt) :
    w ∈ fixPts [e] ↔ e.act w = w := by
  rw [fixPts, List.mem_filter]
  simp only [List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_allPts w, h⟩⟩

theorem mem_fixPts_pair (e f : Elt) (w : Pt) :
    w ∈ fixPts [e, f] ↔ e.act w = w ∧ f.act w = w := by
  rw [fixPts, List.mem_filter]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_allPts w, h⟩⟩

theorem mem_fixPts₁ {e : Elt} (he : e.valid = true) (w : Pt) :
    w ∈ fixPts₁ [e] ↔ w ∈ fixV (Subgroup.zpowers e.sem) ⊓ ptW₁ := by
  rw [fixPts₁, List.mem_filter, mem_fixPts_single, Subgroup.mem_inf, H.mem_fixV_zpowers_iff,
    Elt.sem_apply he, mem_ptW₁, beq_iff_eq]

theorem mem_fixPts₂ {e : Elt} (he : e.valid = true) (w : Pt) :
    w ∈ fixPts₂ [e] ↔ w ∈ fixV (Subgroup.zpowers e.sem) ⊓ ptW₂ := by
  rw [fixPts₂, List.mem_filter, mem_fixPts_single, Subgroup.mem_inf, H.mem_fixV_zpowers_iff,
    Elt.sem_apply he, mem_ptW₂, beq_iff_eq]

theorem card_fixPts₁ {e : Elt} (he : e.valid = true) :
    Nat.card ↥(fixV (Subgroup.zpowers e.sem) ⊓ ptW₁) = (fixPts₁ [e]).length :=
  card_subgroup_eq_length ((allPts_nodup.filter _).filter _)
    fun w => (mem_fixPts₁ he w).symm

theorem card_fixPts₂ {e : Elt} (he : e.valid = true) :
    Nat.card ↥(fixV (Subgroup.zpowers e.sem) ⊓ ptW₂) = (fixPts₂ [e]).length :=
  card_subgroup_eq_length ((allPts_nodup.filter _).filter _)
    fun w => (mem_fixPts₂ he w).symm

theorem relIndex_mul_fixPts₁ {e : Elt} (he : e.valid = true) :
    (fixV (Subgroup.zpowers e.sem) ⊓ ptW₁).relIndex ptW₁ * (fixPts₁ [e]).length = 2 ^ 4 := by
  have h := Subgroup.relIndex_mul_card (H := fixV (Subgroup.zpowers e.sem) ⊓ ptW₁) (K := ptW₁)
  rw [inf_eq_left.2 inf_le_right, card_fixPts₁ he, card_ptW₁] at h
  exact h

@[expose] def Classifies (R : List (List Elt)) : Prop :=
  (∀ gs ∈ R, Good gs) ∧ ∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A →
    ∃ gs ∈ R, ∃ m ∈ modelM4, A = conjAut (sub gs) m

theorem classifies_of {R : List (List Elt)} (hnil : [] ∈ R) (hgood : ∀ gs ∈ R, Good gs)
    (hcl : RepClosed R) : Classifies R :=
  ⟨hgood, exists_rep_of hnil hgood hcl⟩

theorem card_le_of_classifies {R : List (List Elt)} (hR : Classifies R)
    (h : ∀ gs ∈ R, Nat.card (sub gs) ≤ 2 ^ 4) {A : Subgroup (MulAut Pt)}
    (hAM : A ≤ modelM4) (hA : IsElemAbelian2 A) : Nat.card A ≤ 2 ^ 4 := by
  obtain ⟨gs, hgs, m, -, rfl⟩ := hR.2 A hAM hA
  rw [H9Conj.card_conjAut]
  exact h gs hgs

theorem le_L_of_classifies {R : List (List Elt)} (hR : Classifies R)
    (h : ∀ gs ∈ R, sub gs ≠ ⊥ → Nat.card Pt ≤ Nat.card (sub gs) * Nat.card (fixV (sub gs)) →
      sub gs ≤ modelL4 ∧ Nat.card (sub gs) = 2 ^ 4) {A : Subgroup (MulAut Pt)}
    (hAM : A ≤ modelM4) (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hff : Nat.card Pt ≤ Nat.card A * Nat.card (fixV A)) :
    A ≤ modelL4 ∧ Nat.card A = 2 ^ 4 := by
  obtain ⟨gs, hgs, m, hm, rfl⟩ := hR.2 A hAM hA
  rw [H9Conj.card_conjAut, H9Conj.card_fixV_conjAut] at hff
  obtain ⟨h1, h2⟩ := h gs hgs (fun h0 => hA1 (by rw [h0, conjAut_bot])) hff
  exact ⟨conjAut_le_modelL4 h1 hm, by rw [H9Conj.card_conjAut, h2]⟩

theorem card_le_two_of_commV_of_classifies {R : List (List Elt)} (hR : Classifies R)
    (h : ∀ gs ∈ R, Nat.card (commV (sub gs)) ≤ 2 ^ 2 → Nat.card (sub gs) ≤ 2)
    {X : Subgroup (MulAut Pt)} (hXM : X ≤ modelM4) (hX : IsElemAbelian2 X)
    (hc : Nat.card (commV X) ≤ 2 ^ 2) : Nat.card X ≤ 2 := by
  obtain ⟨gs, hgs, m, -, rfl⟩ := hR.2 X hXM hX
  rw [card_commV_conjAut] at hc
  rw [H9Conj.card_conjAut]
  exact h gs hgs hc

theorem card_le_two_of_fixV_of_classifies {R : List (List Elt)} (hR : Classifies R)
    (h : ∀ gs ∈ R, Nat.card Pt ≤ 2 ^ 2 * Nat.card (fixV (sub gs)) → Nat.card (sub gs) ≤ 2)
    {X : Subgroup (MulAut Pt)} (hXM : X ≤ modelM4) (hX : IsElemAbelian2 X)
    (hc : Nat.card Pt ≤ 2 ^ 2 * Nat.card (fixV X)) : Nat.card X ≤ 2 := by
  obtain ⟨gs, hgs, m, -, rfl⟩ := hR.2 X hXM hX
  rw [H9Conj.card_fixV_conjAut] at hc
  rw [H9Conj.card_conjAut]
  exact h gs hgs hc

theorem closure_commPts_le {gs : List Elt} (h : Good gs) :
    Subgroup.closure {w | w ∈ commPts (elems gs)} ≤ commV (sub gs) := by
  rw [Subgroup.closure_le]
  intro w hw
  simp only [Set.mem_ofPred_eq, commPts, List.mem_flatMap, List.mem_map] at hw
  obtain ⟨e, he, v, -, rfl⟩ := hw
  exact Subgroup.subset_closure ⟨e.sem, mem_sub_of_mem_elems h he, v,
    by rw [Elt.sem_apply (valid_of_mem_elems h.1 e he)]⟩

theorem fixV_zpowers_conj (x m : MulAut Pt) :
    fixV (Subgroup.zpowers (m * x * m⁻¹)) = (fixV (Subgroup.zpowers x)).map m.toMonoidHom :=
  CFSG.Quasithin.fixV_zpowers_conj m x

theorem map_inf_fix (x m : MulAut Pt) (U : Subgroup Pt) :
    fixV (Subgroup.zpowers (m * x * m⁻¹)) ⊓ U.map m.toMonoidHom =
      (fixV (Subgroup.zpowers x) ⊓ U).map m.toMonoidHom := by
  rw [fixV_zpowers_conj, Subgroup.map_inf_eq _ _ _ m.injective]

theorem fixPts₁_eq {e f : Elt} (he : e.valid = true)
    (hf : f.valid = true)
    (h : fixV (Subgroup.zpowers e.sem) ⊓ ptW₁ = fixV (Subgroup.zpowers f.sem) ⊓ ptW₁) :
    fixPts₁ [e] = fixPts₁ [f] := by
  have hP : ∀ g : Elt, g.valid = true → ∀ w : Pt,
      ((w.2 == 1) && ([g].all fun g' => g'.act w == w)) = true ↔
        w ∈ fixV (Subgroup.zpowers g.sem) ⊓ ptW₁ := by
    intro g hg w
    rw [Subgroup.mem_inf, H.mem_fixV_zpowers_iff, Elt.sem_apply hg, mem_ptW₁]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_cons, List.all_nil, Bool.and_true]
    exact And.comm
  unfold fixPts₁ fixPts
  rw [List.filter_filter, List.filter_filter]
  exact List.filter_congr fun w _ => Bool.eq_iff_iff.mpr ((hP e he w).trans
    ((SetLike.ext_iff.mp h w).trans (hP f hf w).symm))

theorem fixPts₂_eq {e f : Elt} (he : e.valid = true)
    (hf : f.valid = true)
    (h : fixV (Subgroup.zpowers e.sem) ⊓ ptW₂ = fixV (Subgroup.zpowers f.sem) ⊓ ptW₂) :
    fixPts₂ [e] = fixPts₂ [f] := by
  have hP : ∀ g : Elt, g.valid = true → ∀ w : Pt,
      ((w.1 == 1) && ([g].all fun g' => g'.act w == w)) = true ↔
        w ∈ fixV (Subgroup.zpowers g.sem) ⊓ ptW₂ := by
    intro g hg w
    rw [Subgroup.mem_inf, H.mem_fixV_zpowers_iff, Elt.sem_apply hg, mem_ptW₂]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_cons, List.all_nil, Bool.and_true]
    exact And.comm
  unfold fixPts₂ fixPts
  rw [List.filter_filter, List.filter_filter]
  exact List.filter_congr fun w _ => Bool.eq_iff_iff.mpr ((hP e he w).trans
    ((SetLike.ext_iff.mp h w).trans (hP f hf w).symm))

@[expose] def ConstFixL (X : Subgroup (MulAut Pt)) : Prop :=
  X ≤ modelL4 ∧ ∀ b ∈ X, ∀ c ∈ X, b ≠ 1 → c ≠ 1 →
    fixV (Subgroup.zpowers b) ⊓ ptW₁ = fixV (Subgroup.zpowers c) ⊓ ptW₁ ∧
      fixV (Subgroup.zpowers b) ⊓ ptW₂ = fixV (Subgroup.zpowers c) ⊓ ptW₂

theorem axes_of_classifies {R : List (List Elt)} (hR : Classifies R)
    (h : ∀ gs ∈ R, ConstFixL (sub gs) → 2 ^ 2 ≤ Nat.card (sub gs) →
      Nat.card (sub gs) = 2 ^ 2 ∧ ∀ b ∈ sub gs, b ≠ 1 →
        Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ ptW₁) = 2 ^ 2 ∧
          Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ ptW₂) = 2 ^ 2)
    {B : Subgroup (MulAut Pt)} (hBL : B ≤ modelL4)
    (hB : IsElemAbelian2 B) (hcard : 2 ^ 2 ≤ Nat.card B)
    (hfix : ∀ b ∈ B, ∀ c ∈ B, b ≠ 1 → c ≠ 1 →
      fixV (Subgroup.zpowers b) ⊓ ptW₁ = fixV (Subgroup.zpowers c) ⊓ ptW₁ ∧
        fixV (Subgroup.zpowers b) ⊓ ptW₂ = fixV (Subgroup.zpowers c) ⊓ ptW₂) :
    Nat.card B = 2 ^ 2 ∧
      ∀ b ∈ B, b ≠ 1 → Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ ptW₁) = 2 ^ 2 := by
  obtain ⟨gs, hgs, m, hm, rfl⟩ := hR.2 B (hBL.trans modelL4_le) hB
  have hsubL : sub gs ≤ modelL4 := by
    have h := conjAut_le_modelL4 hBL (modelM4.inv_mem hm)
    rwa [conjAut_conj_inv'] at h
  rw [H9Conj.card_conjAut] at hcard
  have hfix' : ∀ b ∈ sub gs, ∀ c ∈ sub gs, b ≠ 1 → c ≠ 1 →
      fixV (Subgroup.zpowers b) ⊓ ptW₁ = fixV (Subgroup.zpowers c) ⊓ ptW₁ ∧
        fixV (Subgroup.zpowers b) ⊓ ptW₂ = fixV (Subgroup.zpowers c) ⊓ ptW₂ := by
    intro b hb c hc hb1 hc1
    have hconj : ∀ x ∈ sub gs, m * x * m⁻¹ ∈ conjAut (sub gs) m := fun x hx => by
      rw [H9Conj.mem_conjAut, show m⁻¹ * (m * x * m⁻¹) * m = x by group]
      exact hx
    have hne : ∀ x : MulAut Pt, x ≠ 1 → m * x * m⁻¹ ≠ 1 := fun x hx h => hx (by
      calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
        _ = 1 := by rw [h]; group)
    obtain ⟨h1, h2⟩ := hfix _ (hconj b hb) _ (hconj c hc) (hne b hb1) (hne c hc1)
    rcases map_ptW_of_mem hm with ⟨-, hW₁, hW₂⟩ | ⟨-, hW₁, hW₂⟩
    · rw [← hW₁, map_inf_fix, map_inf_fix] at h1
      rw [← hW₂, map_inf_fix, map_inf_fix] at h2
      exact ⟨Subgroup.map_injective m.injective h1, Subgroup.map_injective m.injective h2⟩
    · rw [← hW₂, map_inf_fix, map_inf_fix] at h1
      rw [← hW₁, map_inf_fix, map_inf_fix] at h2
      exact ⟨Subgroup.map_injective m.injective h2, Subgroup.map_injective m.injective h1⟩
  obtain ⟨hl4, hall⟩ := h gs hgs ⟨hsubL, hfix'⟩ hcard
  refine ⟨by rw [H9Conj.card_conjAut, hl4], fun b hb hb1 => ?_⟩
  have hb' := H9Conj.mem_conjAut.mp hb
  have hbe : b = m * (m⁻¹ * b * m) * m⁻¹ := by group
  have hb1' : m⁻¹ * b * m ≠ 1 := fun h1 => hb1 (by rw [hbe, h1]; group)
  obtain ⟨h₁, h₂⟩ := hall _ hb' hb1'
  rw [hbe]
  rcases map_ptW_of_mem hm with ⟨-, hW₁, -⟩ | ⟨-, -, hW₂⟩
  · rw [← hW₁, map_inf_fix, Subgroup.card_map_of_injective (f := m.toMonoidHom) m.injective, h₁]
  · rw [← hW₂, map_inf_fix, Subgroup.card_map_of_injective (f := m.toMonoidHom) m.injective, h₂]

theorem isElemAbelian2_of_le {X Y : Subgroup (MulAut Pt)} (hXY : X ≤ Y)
    (hY : IsElemAbelian2 Y) : IsElemAbelian2 X :=
  ⟨fun x hx y hy => hY.1 x (hXY hx) y (hXY hy), fun x hx => hY.2 x (hXY hx)⟩

theorem mem_gam2Pts {E : List Elt} {w : Pt} :
    w ∈ gam2Pts E ↔ ∃ a ∈ E, ∃ b ∈ E, a ≠ Elt.one ∧ b ≠ Elt.one ∧ a ≠ b ∧ a.act w = w ∧
      b.act w = w := by
  simp only [gam2Pts, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, b, hb, hw⟩
    split_ifs at hw with hc
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      exact ⟨a, ha, b, hb, hc.1.1, hc.1.2, hc.2, (mem_fixPts_pair a b w).mp hw⟩
    · exact absurd hw List.not_mem_nil
  · rintro ⟨a, ha, b, hb, ha1, hb1, hab, hwa, hwb⟩
    refine ⟨a, ha, b, hb, ?_⟩
    have hc : (a != Elt.one && b != Elt.one && a != b) = true := by simp [ha1, hb1, hab]
    simp only [hc, ↓reduceIte]
    exact (mem_fixPts_pair a b w).mpr ⟨hwa, hwb⟩

theorem mem_gam3Pts {E : List Elt} {w : Pt} :
    w ∈ gam3Pts E ↔ ∃ a ∈ E, a ≠ Elt.one ∧ a.act w = w := by
  simp only [gam3Pts, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, hw⟩
    split_ifs at hw with hc
    · exact ⟨a, ha, by simpa using hc, (mem_fixPts_single a w).mp hw⟩
    · exact absurd hw List.not_mem_nil
  · rintro ⟨a, ha, ha1, hwa⟩
    refine ⟨a, ha, ?_⟩
    have hc : (a != Elt.one) = true := by simpa using ha1
    simp only [hc, ↓reduceIte]
    exact (mem_fixPts_single a w).mpr hwa

theorem closure_gam2_le {gs : List Elt} (hgood : Good gs)
    (h16 : Nat.card (sub gs) = 2 ^ 4) :
    Subgroup.closure {w | w ∈ gam2Pts (elems gs)} ≤ gammaCheck 2 (sub gs) := by
  have hval := valid_of_mem_elems hgood.1
  rw [Subgroup.closure_le]
  intro w hw
  obtain ⟨a, ha, b, hb, ha1, hb1, hab, hwa, hwb⟩ := mem_gam2Pts.mp hw
  have hab' : ∀ g ∈ [a, b], g ∈ elems gs := by
    intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl
    · exact ha
    · exact hb
  have hX : sub [a, b] ≤ sub gs := by
    rw [sub, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact mem_sub_of_mem_elems hgood (hab' g hg)
  have h4 : 4 ≤ Nat.card (sub [a, b]) :=
    four_le_card (isElemAbelian2_of_le hX (isElemAbelian2_sub hgood))
      (Subgroup.subset_closure ⟨a, by simp, rfl⟩) (Subgroup.subset_closure ⟨b, by simp, rfl⟩)
      (Elt.sem_ne_one (hval a ha) ha1) (Elt.sem_ne_one (hval b hb) hb1)
      fun h => hab (Elt.sem_injective (hval a ha) (hval b hb) h)
  have hq : mQuot (sub gs) (sub [a, b]) ≤ 2 :=
    mQuot_le_of_card (isPGroup_sub hgood) hX (by rw [h16]; norm_num; omega)
  refine H9Conj.fixV_le_gammaCheck hX hq ?_
  rw [mem_fixV_sub fun g hg => hval g (hab' g hg)]
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl
  · exact hwa
  · exact hwb

theorem gammaCheck_two_le {gs : List Elt} (hgood : Good gs)
    (h16 : Nat.card (sub gs) = 2 ^ 4) :
    gammaCheck 2 (sub gs) ≤ Subgroup.closure {w | w ∈ gam2Pts (elems gs)} := by
  have hval := valid_of_mem_elems hgood.1
  refine H9Conj.gammaCheck_le fun X hX hXk => ?_
  have hc := card_le_of_mQuot (isPGroup_sub hgood) hX hXk
  rw [h16] at hc
  have h2 : 2 < Nat.card X := by norm_num at hc; omega
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ :=
    exists_two_of_card (isElemAbelian2_of_le hX (isElemAbelian2_sub hgood)) h2
  obtain ⟨a, ha, rfl⟩ := (mem_sub_iff hgood.1 hgood.2.1 hgood.2.2 _).mp (hX hx)
  obtain ⟨b, hb, rfl⟩ := (mem_sub_iff hgood.1 hgood.2.1 hgood.2.2 _).mp (hX hy)
  intro w hw
  refine Subgroup.subset_closure (mem_gam2Pts.mpr ⟨a, ha, b, hb, ?_, ?_, ?_, ?_, ?_⟩)
  · rintro rfl
    exact hx1 Elt.sem_one
  · rintro rfl
    exact hy1 Elt.sem_one
  · rintro rfl
    exact hxy rfl
  · rw [← Elt.sem_apply (hval a ha)]
    exact hw _ hx
  · rw [← Elt.sem_apply (hval b hb)]
    exact hw _ hy

theorem gammaCheck_two_eq {gs : List Elt} (hgood : Good gs)
    (h16 : Nat.card (sub gs) = 2 ^ 4) :
    gammaCheck 2 (sub gs) = Subgroup.closure {w | w ∈ gam2Pts (elems gs)} :=
  le_antisymm (gammaCheck_two_le hgood h16) (closure_gam2_le hgood h16)

theorem closure_gam3_le {gs : List Elt} (hgood : Good gs)
    (h16 : Nat.card (sub gs) = 2 ^ 4) :
    Subgroup.closure {w | w ∈ gam3Pts (elems gs)} ≤ gammaCheck 3 (sub gs) := by
  have hval := valid_of_mem_elems hgood.1
  rw [Subgroup.closure_le]
  intro w hw
  obtain ⟨a, ha, ha1, hwa⟩ := mem_gam3Pts.mp hw
  have hX : sub [a] ≤ sub gs := by
    rw [sub, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [List.mem_singleton.mp hg]
    exact mem_sub_of_mem_elems hgood ha
  have hmem : a.sem ∈ sub [a] := Subgroup.subset_closure ⟨a, List.mem_singleton_self a, rfl⟩
  have h2 : 2 ≤ Nat.card (sub [a]) := by
    have hne : sub [a] ≠ ⊥ := fun h =>
      Elt.sem_ne_one (hval a ha) ha1 (Subgroup.mem_bot.mp (h ▸ hmem))
    have := (Subgroup.one_lt_card_iff_ne_bot (sub [a])).mpr hne
    omega
  have hq : mQuot (sub gs) (sub [a]) ≤ 3 :=
    mQuot_le_of_card (isPGroup_sub hgood) hX (by rw [h16]; norm_num; omega)
  refine H9Conj.fixV_le_gammaCheck hX hq ?_
  rw [mem_fixV_sub fun g hg => by rw [List.mem_singleton.mp hg]; exact hval a ha]
  intro g hg
  rw [List.mem_singleton.mp hg]
  exact hwa

theorem isTransvOn_iff {e : Elt} (he : e.valid = true)
    (hb : e.b = false) : IsTransvOn e.sem ptW₁ ↔ (fixPts₁ [e]).length = 8 := by
  have h := relIndex_mul_fixPts₁ he
  have hst := modelL4_le_stabV₁ ((Elt.sem_mem_modelL4_iff he).mpr hb)
  unfold IsTransvOn
  rw [and_iff_right hst]
  norm_num at h
  constructor
  · intro h2
    rw [h2] at h
    omega
  · intro h8
    rw [h8] at h
    omega

theorem seven_of {gs : List Elt} (hgood : Good gs)
    (h16 : Nat.card (sub gs) = 2 ^ 4)
    (ht : ∃ x ∈ elems gs, x.b = false ∧ (fixPts₁ [x]).length = 8)
    (hn : ∃ x ∈ elems gs, (x.b = false ∧ ¬x = Elt.one) ∧ ¬(fixPts₁ [x]).length = 8)
    (h3 : 128 ≤ (spanList (gam3Pts (elems gs))).length) :
    (∃ b ∈ sub gs ⊓ modelL4, IsTransvOn b ptW₁) ∧
      (∃ b ∈ sub gs ⊓ modelL4, b ≠ 1 ∧ ¬ IsTransvOn b ptW₁) ∧
      2 ^ 7 ≤ Nat.card (gammaCheck 3 (sub gs)) := by
  have hval := valid_of_mem_elems hgood.1
  obtain ⟨x, hx, hxb, hx8⟩ := ht
  obtain ⟨y, hy, ⟨hyb, hy1⟩, hy8⟩ := hn
  refine ⟨⟨x.sem, Subgroup.mem_inf.mpr ⟨mem_sub_of_mem_elems hgood hx,
      (Elt.sem_mem_modelL4_iff (hval x hx)).mpr hxb⟩, (isTransvOn_iff (hval x hx) hxb).mpr hx8⟩,
    ⟨y.sem, Subgroup.mem_inf.mpr ⟨mem_sub_of_mem_elems hgood hy,
      (Elt.sem_mem_modelL4_iff (hval y hy)).mpr hyb⟩, Elt.sem_ne_one (hval y hy) hy1,
      fun h => hy8 ((isTransvOn_iff (hval y hy) hyb).mp h)⟩, ?_⟩
  have h1 := Subgroup.card_le_of_le (closure_gam3_le hgood h16)
  rw [card_closure_eq_spanList] at h1
  calc 2 ^ 7 = 128 := by norm_num
    _ ≤ _ := h3.trans h1

theorem lemH93_of_classifies {R : List (List Elt)} (hR : Classifies R)
    {A₀ A₁ A₂ : Subgroup (MulAut Pt)}
    (hmem : ∀ A ∈ ({A₀, A₁, A₂} : Set (Subgroup (MulAut Pt))),
      A ≤ modelM4 ∧ IsElemAbelian2 A ∧ Nat.card A = 2 ^ 4)
    (h16 : ∀ gs ∈ R, Nat.card (sub gs) = 2 ^ 4 → sub gs = A₀ ∨ sub gs = A₁ ∨ sub gs = A₂)
    (h0 : Nat.card (fixV A₀) = 2 ^ 4 ∧ gammaCheck 2 A₀ = ⊤)
    (h1 : Nat.card (fixV A₁) = 2 ∧ Nat.card (gammaCheck 2 A₁) = 2 ^ 6)
    (h2 : Nat.card (fixV A₂) = 2 ^ 2 ∧ Nat.card (gammaCheck 2 A₂) = 2 ^ 6 ∧
      ∀ a ∈ A₂, (∀ w ∈ gammaCheck 2 A₂, a w = w) → a = 1)
    (h7 : ∀ A ∈ ({A₁, A₂} : Set (Subgroup (MulAut Pt))),
      (∃ b ∈ A ⊓ modelL4, IsTransvOn b ptW₁) ∧
        (∃ b ∈ A ⊓ modelL4, b ≠ 1 ∧ ¬ IsTransvOn b ptW₁) ∧
        2 ^ 7 ≤ Nat.card (gammaCheck 3 A)) :
    ∃ A₀ A₁ A₂ : Subgroup (MulAut Pt),
    (∀ A ∈ ({A₀, A₁, A₂} : Set (Subgroup (MulAut Pt))),
      A ≤ modelM4 ∧ IsElemAbelian2 A ∧ Nat.card A = 2 ^ 4) ∧
    (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → Nat.card A = 2 ^ 4 →
      ∃ m ∈ modelM4, A = conjAut A₀ m ∨ A = conjAut A₁ m ∨ A = conjAut A₂ m) ∧
    (Nat.card (fixV A₀) = 2 ^ 4 ∧ gammaCheck 2 A₀ = ⊤) ∧
    (Nat.card (fixV A₁) = 2 ∧ Nat.card (gammaCheck 2 A₁) = 2 ^ 6) ∧
    (Nat.card (fixV A₂) = 2 ^ 2 ∧ Nat.card (gammaCheck 2 A₂) = 2 ^ 6 ∧
      ∀ a ∈ A₂, (∀ w ∈ gammaCheck 2 A₂, a w = w) → a = 1) ∧
    ∀ A ∈ ({A₁, A₂} : Set (Subgroup (MulAut Pt))),
      (∃ b ∈ A ⊓ modelL4, IsTransvOn b ptW₁) ∧
        (∃ b ∈ A ⊓ modelL4, b ≠ 1 ∧ ¬ IsTransvOn b ptW₁) ∧
        2 ^ 7 ≤ Nat.card (gammaCheck 3 A) := by
  refine ⟨A₀, A₁, A₂, hmem, fun A hAM hA hcard => ?_, h0, h1, h2, h7⟩
  obtain ⟨gs, hgs, m, hm, rfl⟩ := hR.2 A hAM hA
  rw [H9Conj.card_conjAut] at hcard
  rcases h16 gs hgs hcard with h | h | h <;> rw [h]
  · exact ⟨m, hm, Or.inl rfl⟩
  · exact ⟨m, hm, Or.inr (Or.inl rfl)⟩
  · exact ⟨m, hm, Or.inr (Or.inr rfl)⟩

end CFSG.Quasithin.H13.H9Four
