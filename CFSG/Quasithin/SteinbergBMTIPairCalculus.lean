module

public import CFSG.Quasithin.SteinbergBMCenterlessComponentNormal
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

private theorem mem_conjugate_iff_conj {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem isElementaryAbelian_two_of {E : Subgroup G} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ x ∈ E, x * x = 1) : CFSG.IsElementaryAbelian 2 E :=
  CFSG.IsElementaryAbelian.two_of_forall_mul_self hEc hE2

theorem elementaryAbelian_two_facts {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 2 E) :
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1 := by
  refine ⟨fun x hx y hy => congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
    fun x hx => ?_⟩
  rw [← pow_two]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx

theorem twist_mem_commute {E : Subgroup G} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {t : G}
    (ht : t ∈ normalizer (E : Set G)) (ht2 : t * t = 1) {e : G} (he : e ∈ E) :
    e * (t * e * t⁻¹) ∈ E ∧ t * (e * (t * e * t⁻¹)) = e * (t * e * t⁻¹) * t := by
  have hte : t * e * t⁻¹ ∈ E := (mem_normalizer_iff.mp ht e).mp he
  refine ⟨E.mul_mem he hte, ?_⟩
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h1 : t * e = t * e * t⁻¹ * t := by group
  have h2 : t * (t * e * t⁻¹) = e * t := by
    calc t * (t * e * t⁻¹) = t * t * e * t⁻¹ := by group
      _ = e * t := by rw [ht2, one_mul, hinv]
  have hc := hEc _ hte e he
  calc t * (e * (t * e * t⁻¹)) = t * e * (t * e * t⁻¹) := (mul_assoc _ _ _).symm
    _ = t * e * t⁻¹ * t * (t * e * t⁻¹) := by rw [← h1]
    _ = t * e * t⁻¹ * (t * (t * e * t⁻¹)) := mul_assoc _ _ _
    _ = t * e * t⁻¹ * (e * t) := by rw [h2]
    _ = t * e * t⁻¹ * e * t := (mul_assoc _ _ _).symm
    _ = e * (t * e * t⁻¹) * t := by rw [hc]

theorem twist_eq_one_iff {e t : G} (he2 : e * e = 1) :
    e * (t * e * t⁻¹) = 1 ↔ t * e = e * t := by
  rw [mul_eq_one_iff_inv_eq, inv_eq_of_mul_eq_one_right he2, eq_comm, mul_inv_eq_iff_eq_mul]

theorem exists_ne_one_commute {E : Subgroup G} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ x ∈ E, x * x = 1) (hE : E ≠ ⊥) {t : G} (ht : t ∈ normalizer (E : Set G))
    (ht2 : t * t = 1) : ∃ f ∈ E, f ≠ 1 ∧ t * f = f * t := by
  obtain ⟨⟨e, he⟩, he1'⟩ := ne_bot_iff_exists_ne_one.mp hE
  have he1 : e ≠ 1 := fun h => he1' (Subtype.ext h)
  by_cases hte : t * e = e * t
  · exact ⟨e, he, he1, hte⟩
  · obtain ⟨hm, hc⟩ := twist_mem_commute hEc ht ht2 he
    exact ⟨_, hm, fun h => hte ((twist_eq_one_iff (hE2 e he)).mp h), hc⟩

theorem exists_twist_range {E : Subgroup G} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ x ∈ E, x * x = 1) {t : G} (ht : t ∈ normalizer (E : Set G)) (ht2 : t * t = 1) :
    ∃ R : Subgroup G, R ≤ E ⊓ centralizer ({t} : Set G) ∧
      (∀ r ∈ R, ∃ e ∈ E, e * (t * e * t⁻¹) = r) ∧
      Nat.card R * Nat.card (E ⊓ centralizer ({t} : Set G) : Subgroup G) = Nat.card E := by
  have hconj : ∀ e ∈ E, t * e * t⁻¹ ∈ E := fun e he => (mem_normalizer_iff.mp ht e).mp he
  let φ : E →* E := MonoidHom.mk'
    (fun e => ⟨e * (t * e * t⁻¹), (twist_mem_commute hEc ht ht2 e.2).1⟩) fun a b => by
      apply Subtype.ext
      change (a * b : G) * (t * (a * b) * t⁻¹) = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹))
      have hc := hEc b b.2 _ (hconj a a.2)
      calc (a * b : G) * (t * (a * b) * t⁻¹)
          = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
        _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hc]
        _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group
  have hker : φ.ker.map E.subtype = E ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      refine ⟨e.2, ?_⟩
      have h1 : (e : G) * (t * e * t⁻¹) = 1 := congrArg Subtype.val (φ.mem_ker.mp he)
      exact mem_centralizer_singleton_iff.mpr ((twist_eq_one_iff (hE2 e e.2)).mp h1).symm
    · rintro ⟨hxE, hxC⟩
      refine ⟨⟨x, hxE⟩, φ.mem_ker.mpr (Subtype.ext ?_), rfl⟩
      change x * (t * x * t⁻¹) = 1
      have hxC' : x * t = t * x :=
        mem_centralizer_singleton_iff.mp (show x ∈ centralizer ({t} : Set G) from hxC)
      exact (twist_eq_one_iff (hE2 x hxE)).mpr hxC'.symm
  refine ⟨φ.range.map E.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
    obtain ⟨hm, hc⟩ := twist_mem_commute hEc ht ht2 e.2
    exact ⟨hm, mem_centralizer_singleton_iff.mpr hc.symm⟩
  · rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, e.2, rfl⟩
  · rw [card_map_of_injective E.subtype_injective, ← hker,
      card_map_of_injective E.subtype_injective, mul_comm]
    exact card_ker_mul_card_range φ

theorem card_le_card_inf_centralizer_sq [Finite G] {E : Subgroup G}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1) {t : G}
    (ht : t ∈ normalizer (E : Set G)) (ht2 : t * t = 1) :
    Nat.card E ≤ Nat.card (E ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
  obtain ⟨R, hR, -, hcard⟩ := exists_twist_range hEc hE2 ht ht2
  rw [← hcard, pow_two]
  exact Nat.mul_le_mul_right _ (card_le_of_le hR)

theorem mem_normalizer_of_commute_of_TI {D : Subgroup G}
    (hTI : ∀ x : G, D ⊓ CFSG.conjugate D x = ⊥ ∨ CFSG.conjugate D x = D) {d : G} (hd : d ∈ D)
    (hd1 : d ≠ 1) {c : G} (hc : c * d = d * c) : c ∈ normalizer (D : Set G) := by
  have hdc : d ∈ CFSG.conjugate D c := by
    rw [mem_conjugate_iff_conj, hc, mul_inv_cancel_right]
    exact hd
  rcases hTI c with h | h
  · exfalso
    have hmem : d ∈ D ⊓ CFSG.conjugate D c := ⟨hd, hdc⟩
    rw [h, mem_bot] at hmem
    exact hd1 hmem
  · rw [mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff_conj, h]

structure ElementaryTIPair (V A : Subgroup G) : Prop where
  comm_left : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  sq_left : ∀ x ∈ V, x * x = 1
  comm_right : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  sq_right : ∀ x ∈ A, x * x = 1
  disjoint : V ⊓ A = ⊥
  ti_left : ∀ x : G, V ⊓ CFSG.conjugate V x = ⊥ ∨ CFSG.conjugate V x = V
  ti_right : ∀ x : G, A ⊓ CFSG.conjugate A x = ⊥ ∨ CFSG.conjugate A x = A

namespace ElementaryTIPair

variable {V A : Subgroup G}

theorem symm (h : ElementaryTIPair V A) : ElementaryTIPair A V :=
  ⟨h.comm_right, h.sq_right, h.comm_left, h.sq_left, by rw [inf_comm]; exact h.disjoint,
    h.ti_right, h.ti_left⟩

theorem commute (h : ElementaryTIPair V A) {u b : G} (hu : u ∈ V ⊓ normalizer (A : Set G))
    (hb : b ∈ A ⊓ normalizer (V : Set G)) : u * b = b * u := by
  have hV : u * (b * u⁻¹ * b⁻¹) ∈ V :=
    V.mul_mem hu.1 ((mem_normalizer_iff.mp hb.2 _).mp (V.inv_mem hu.1))
  have hA : u * b * u⁻¹ * b⁻¹ ∈ A :=
    A.mul_mem ((mem_normalizer_iff.mp hu.2 b).mp hb.1) (A.inv_mem hb.1)
  have h1 : u * b * u⁻¹ * b⁻¹ = 1 := by
    have hmem : u * b * u⁻¹ * b⁻¹ ∈ V ⊓ A := ⟨by simpa [mul_assoc] using hV, hA⟩
    rw [h.disjoint, mem_bot] at hmem
    exact hmem
  calc u * b = u * b * u⁻¹ * b⁻¹ * (b * u) := by group
    _ = b * u := by rw [h1, one_mul]

theorem le_centralizer (h : ElementaryTIPair V A) :
    A ⊓ normalizer (V : Set G) ≤
      centralizer ((V ⊓ normalizer (A : Set G) : Subgroup G) : Set G) :=
  fun _ hb => mem_centralizer_iff.mpr fun _ hu => h.commute hu hb

theorem inf_eq_bot (h : ElementaryTIPair V A) :
    (V ⊓ normalizer (A : Set G)) ⊓ (A ⊓ normalizer (V : Set G)) = ⊥ :=
  le_bot_iff.mp (h.disjoint ▸ inf_le_inf inf_le_left inf_le_left)

theorem eq_inf_centralizer (h : ElementaryTIPair V A) {u : G}
    (hu : u ∈ V ⊓ normalizer (A : Set G)) (hu1 : u ≠ 1) :
    A ⊓ normalizer (V : Set G) = A ⊓ centralizer ({u} : Set G) := by
  ext a
  refine ⟨fun ha => ⟨ha.1, ?_⟩, fun ha => ⟨ha.1, ?_⟩⟩
  · exact mem_centralizer_singleton_iff.mpr (h.commute hu ha).symm
  · exact mem_normalizer_of_commute_of_TI h.ti_left hu.1 hu1
      (mem_centralizer_singleton_iff.mp ha.2)

theorem ne_bot (h : ElementaryTIPair V A) (hA : A ≠ ⊥) (hU : V ⊓ normalizer (A : Set G) ≠ ⊥) :
    A ⊓ normalizer (V : Set G) ≠ ⊥ := by
  obtain ⟨⟨u, hu⟩, hu1'⟩ := ne_bot_iff_exists_ne_one.mp hU
  have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
  obtain ⟨f, hf, hf1, hfu⟩ :=
    exists_ne_one_commute h.comm_right h.sq_right hA hu.2 (h.sq_left u hu.1)
  rw [h.eq_inf_centralizer hu hu1]
  intro hbot
  have hmem : f ∈ A ⊓ centralizer ({u} : Set G) :=
    ⟨hf, mem_centralizer_singleton_iff.mpr hfu.symm⟩
  rw [hbot, mem_bot] at hmem
  exact hf1 hmem

theorem isElementaryAbelian_sup (h : ElementaryTIPair V A) :
    CFSG.IsElementaryAbelian 2
      ((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) : Subgroup G) := by
  have := isElementaryAbelian_two_of (E := V ⊓ normalizer (A : Set G))
    (fun x hx y hy => h.comm_left x hx.1 y hy.1) fun x hx => h.sq_left x hx.1
  have := isElementaryAbelian_two_of (E := A ⊓ normalizer (V : Set G))
    (fun x hx y hy => h.comm_right x hx.1 y hy.1) fun x hx => h.sq_right x hx.1
  exact CFSG.IsElementaryAbelian.sup_of_le_centralizer h.le_centralizer

theorem coe_sup (h : ElementaryTIPair V A) :
    (((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) : Subgroup G) : Set G) =
      ((V ⊓ normalizer (A : Set G) : Subgroup G) : Set G) *
        ((A ⊓ normalizer (V : Set G) : Subgroup G) : Set G) :=
  coe_mul_of_left_le_normalizer_right _ _
    (h.symm.le_centralizer.trans (centralizer_le_normalizer _))

theorem card_sup (h : ElementaryTIPair V A) :
    Nat.card ((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) : Subgroup G) =
      Nat.card (V ⊓ normalizer (A : Set G) : Subgroup G) *
        Nat.card (A ⊓ normalizer (V : Set G) : Subgroup G) :=
  card_sup_of_commute h.le_centralizer h.inf_eq_bot

theorem le_normalizer_sup (h : ElementaryTIPair V A) :
    A ≤ normalizer
      (((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) : Subgroup G) : Set G) := by
  rw [sup_eq_closure, le_normalizer_closure_iff]
  intro a ha s hs
  rw [← sup_eq_closure]
  rcases hs with hs | hs
  · by_cases hs1 : s = 1
    · rw [hs1, mul_one, mul_inv_cancel]
      exact one_mem _
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.sq_right a ha)
    obtain ⟨hm, hc⟩ := twist_mem_commute h.comm_right hs.2 (h.sq_left s hs.1) ha
    have hB : a * (s * a * s⁻¹) ∈ A ⊓ normalizer (V : Set G) := by
      rw [h.eq_inf_centralizer hs hs1]
      exact ⟨hm, mem_centralizer_singleton_iff.mpr hc.symm⟩
    have he : a * s * a⁻¹ = a * (s * a * s⁻¹) * s := by
      rw [hainv]
      group
    rw [he]
    exact mul_mem (mem_sup_right hB) (mem_sup_left hs)
  · rw [h.comm_right a ha s hs.1, mul_inv_cancel_right]
    exact mem_sup_right hs

theorem sup_inf_centralizer (h : ElementaryTIPair V A) {v : G} (hv : v ∈ V)
    (hvU : v ∉ V ⊓ normalizer (A : Set G)) :
    ((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G))) ⊓
      centralizer ({v} : Set G) = V ⊓ normalizer (A : Set G) := by
  refine le_antisymm (fun y hy => ?_) fun u hu => ⟨mem_sup_left hu, ?_⟩
  · obtain ⟨hyY, hyv⟩ := hy
    have hy' : y ∈ (((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) :
        Subgroup G) : Set G) := hyY
    rw [h.coe_sup] at hy'
    obtain ⟨u, hu, b, hb, rfl⟩ := hy'
    have hyv' : u * b * v = v * (u * b) := mem_centralizer_singleton_iff.mp hyv
    have huv := h.comm_left u hu.1 v hv
    have hbv : b * v = v * b := by
      have : u * (b * v) = u * (v * b) := by
        calc u * (b * v) = u * b * v := (mul_assoc _ _ _).symm
          _ = v * (u * b) := hyv'
          _ = u * (v * b) := by rw [← mul_assoc, ← huv, mul_assoc]
      exact mul_left_cancel this
    by_cases hb1 : b = 1
    · show u * b ∈ V ⊓ normalizer (A : Set G)
      rw [hb1, mul_one]
      exact hu
    · exfalso
      apply hvU
      rw [h.symm.eq_inf_centralizer hb hb1]
      exact ⟨hv, mem_centralizer_singleton_iff.mpr hbv.symm⟩
  · exact mem_centralizer_singleton_iff.mpr (h.comm_left u hu.1 v hv)

theorem card_le_of_not_mem [Finite G] (h : ElementaryTIPair V A) {a : G} (ha : a ∈ A)
    (haB : a ∉ A ⊓ normalizer (V : Set G)) :
    Nat.card (V ⊓ normalizer (A : Set G) : Subgroup G) ≤
      Nat.card (A ⊓ normalizer (V : Set G) : Subgroup G) := by
  obtain ⟨hYc, hY2⟩ := elementaryAbelian_two_facts h.isElementaryAbelian_sup
  have hle := card_le_card_inf_centralizer_sq hYc hY2 (h.le_normalizer_sup ha)
    (h.sq_right a ha)
  rw [sup_comm, h.symm.sup_inf_centralizer ha haB, sup_comm, h.card_sup, pow_two] at hle
  exact Nat.le_of_mul_le_mul_right hle Nat.card_pos

theorem eq_of_eq [Finite G] (h : ElementaryTIPair V A) (hcard : Nat.card V = Nat.card A)
    (hUV : V ⊓ normalizer (A : Set G) = V) : A ⊓ normalizer (V : Set G) = A := by
  by_contra hne
  obtain ⟨a, ha, haB⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne inf_le_left hne)
  have hle := h.card_le_of_not_mem ha haB
  rw [hUV, hcard] at hle
  exact hne (eq_of_le_of_card_ge inf_le_left hle)

theorem lt_of_lt [Finite G] (h : ElementaryTIPair V A) (hcard : Nat.card V = Nat.card A)
    (hUV : V ⊓ normalizer (A : Set G) < V) : A ⊓ normalizer (V : Set G) < A := by
  obtain ⟨v, hv, hvU⟩ := IsConcreteLE.exists_of_lt hUV
  have hle := h.symm.card_le_of_not_mem hv hvU
  refine lt_of_le_of_ne inf_le_left fun hBA => ?_
  have hlt := card_lt_of_lt hUV
  rw [hBA] at hle
  omega

theorem commutator_eq_bot (h : ElementaryTIPair V A) (hU : V ⊓ normalizer (A : Set G) = V)
    (hB : A ⊓ normalizer (V : Set G) = A) : ⁅V, A⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [mem_centralizer_iff]
  intro a ha
  have hv' : v ∈ V ⊓ normalizer (A : Set G) := by rw [hU]; exact hv
  have ha' : a ∈ A ⊓ normalizer (V : Set G) := by rw [hB]; exact ha
  exact (h.commute hv' ha').symm

theorem commutator_zpowers_eq [Finite G] (h : ElementaryTIPair V A)
    (hUB : Nat.card (V ⊓ normalizer (A : Set G) : Subgroup G) =
      Nat.card (A ⊓ normalizer (V : Set G) : Subgroup G)) {v : G} (hv : v ∈ V)
    (hvU : v ∉ V ⊓ normalizer (A : Set G)) :
    ⁅(V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)), zpowers v⁆ =
      V ⊓ normalizer (A : Set G) := by
  obtain ⟨hYc, hY2⟩ := elementaryAbelian_two_facts h.isElementaryAbelian_sup
  have hVN : V ≤ normalizer
      (((V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)) : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact h.symm.le_normalizer_sup
  have hcomm_eq : ∀ y ∈ (V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G)),
      ∀ k : G, ⁅y, k⁆ = y * (k * y * k⁻¹) := by
    intro y hy k
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right (hY2 y hy)]
    group
  refine le_antisymm ?_ ?_
  · rw [commutator_le]
    intro y hy k hk
    have hkV : k ∈ V := (zpowers_le.mpr hv) hk
    by_cases hkU : k ∈ V ⊓ normalizer (A : Set G)
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hYc y hy k (mem_sup_left hkU))]
      exact one_mem _
    · rw [hcomm_eq y hy k, ← h.sup_inf_centralizer hkV hkU]
      obtain ⟨hm, hc⟩ := twist_mem_commute hYc (hVN hkV) (h.sq_left k hkV) hy
      exact ⟨hm, mem_centralizer_singleton_iff.mpr hc.symm⟩
  · obtain ⟨R, hR, hRtw, hRcard⟩ := exists_twist_range hYc hY2 (hVN hv) (h.sq_left v hv)
    rw [h.sup_inf_centralizer hv hvU] at hR hRcard
    have h1 := hRcard.trans h.card_sup
    have hpos : 0 < Nat.card (V ⊓ normalizer (A : Set G) : Subgroup G) := Nat.card_pos
    have h2 : Nat.card R = Nat.card (A ⊓ normalizer (V : Set G) : Subgroup G) := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1, mul_comm]
    have hReq : R = V ⊓ normalizer (A : Set G) :=
      eq_of_le_of_card_ge hR (hUB.trans h2.symm).le
    intro r hr
    rw [← hReq] at hr
    obtain ⟨e, he, rfl⟩ := hRtw r hr
    rw [← hcomm_eq e he v]
    exact commutator_mem_commutator he (mem_zpowers v)

end ElementaryTIPair

theorem equal_rank_elementary_TI_pair_mutual_normalizer_calculus [Finite G]
    {V A : Subgroup G} {n : ℕ} (hVe : CFSG.IsElementaryAbelian 2 V)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hVn : Nat.card V = 2 ^ n) (hAn : Nat.card A = 2 ^ n)
    (hVA : V ⊓ A = ⊥) (hVTI : ∀ x : G, V ⊓ CFSG.conjugate V x = ⊥ ∨ CFSG.conjugate V x = V)
    (hATI : ∀ x : G, A ⊓ CFSG.conjugate A x = ⊥ ∨ CFSG.conjugate A x = A)
    (hU : V ⊓ normalizer (A : Set G) ≠ ⊥) :
    let U := V ⊓ normalizer (A : Set G)
    let B := A ⊓ normalizer (V : Set G)
    let Y := U ⊔ B
    B ≠ ⊥ ∧ (∀ b ∈ B, b ≠ 1 → U = V ⊓ centralizer ({b} : Set G)) ∧
      (∀ u ∈ U, u ≠ 1 → B = A ⊓ centralizer ({u} : Set G)) ∧
      ((Y : Set G) = (U : Set G) * (B : Set G) ∧ U ⊓ B = ⊥ ∧ ⁅U, B⁆ = ⊥) ∧
      CFSG.IsElementaryAbelian 2 Y ∧ Y ≤ V ⊔ A ∧ (Y.subgroupOf (V ⊔ A)).Normal ∧
      (U = V → B = A ∧ ⁅V, A⁆ = ⊥) ∧
      (U < V → B < A ∧ Nat.card U = Nat.card B ∧
        (∀ b ∈ B, (∀ v ∈ V, b * v * b⁻¹ = v) → b = 1) ∧
        (∀ b ∈ B, b ≠ 1 → V ⊓ centralizer ({b} : Set G) = U) ∧
        ∀ v ∈ V, v ∉ U → Y ⊓ centralizer ({v} : Set G) = U ∧ ⁅Y, zpowers v⁆ = U) := by
  intro U B Y
  obtain ⟨hVc, hV2⟩ := elementaryAbelian_two_facts hVe
  obtain ⟨hAc, hA2⟩ := elementaryAbelian_two_facts hAe
  have h : ElementaryTIPair V A := ⟨hVc, hV2, hAc, hA2, hVA, hVTI, hATI⟩
  have hcard : Nat.card V = Nat.card A := hVn.trans hAn.symm
  have hA1 : A ≠ ⊥ := by
    intro hA
    apply hU
    have hV1 : V = ⊥ := by
      rw [← card_eq_one, hcard, hA, card_bot]
    rw [hV1, bot_inf_eq]
  have hYle : Y ≤ V ⊔ A := sup_le_sup inf_le_left inf_le_left
  have hVN : V ≤ normalizer (Y : Set G) := by
    rw [show Y = B ⊔ U from sup_comm _ _]
    exact h.symm.le_normalizer_sup
  refine ⟨h.ne_bot hA1 hU, fun b hb hb1 => h.symm.eq_inf_centralizer hb hb1,
    fun u hu hu1 => h.eq_inf_centralizer hu hu1,
    ⟨h.coe_sup, h.inf_eq_bot, commutator_eq_bot_iff_le_centralizer.mpr h.symm.le_centralizer⟩,
    h.isElementaryAbelian_sup, hYle,
    (normal_subgroupOf_iff_le_normalizer hYle).mpr (sup_le hVN h.le_normalizer_sup),
    fun hUV => ⟨h.eq_of_eq hcard hUV, h.commutator_eq_bot hUV (h.eq_of_eq hcard hUV)⟩,
    fun hUV => ?_⟩
  have hBA := h.lt_of_lt hcard hUV
  obtain ⟨v₀, hv₀, hv₀U⟩ := IsConcreteLE.exists_of_lt hUV
  obtain ⟨a₀, ha₀, ha₀B⟩ := IsConcreteLE.exists_of_lt hBA
  have hUB : Nat.card U = Nat.card B :=
    le_antisymm (h.card_le_of_not_mem ha₀ ha₀B) (h.symm.card_le_of_not_mem hv₀ hv₀U)
  refine ⟨hBA, hUB, fun b hb hbV => ?_,
    fun b hb hb1 => (h.symm.eq_inf_centralizer hb hb1).symm,
    fun v hv hvU => ⟨h.sup_inf_centralizer hv hvU, h.commutator_zpowers_eq hUB hv hvU⟩⟩
  by_contra hb1
  apply hUV.ne
  show V ⊓ normalizer (A : Set G) = V
  rw [h.symm.eq_inf_centralizer hb hb1]
  refine le_antisymm inf_le_left fun v hv => ⟨hv, mem_centralizer_singleton_iff.mpr ?_⟩
  calc v * b = b * v * b⁻¹ * b := by rw [hbV v hv]
    _ = b * v := by group

end CFSG.Quasithin.SteinbergBM
