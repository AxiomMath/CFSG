module

public import CFSG.Monster.GMS.S4Fusion
public import CFSG.Monster.GMS.S342
public import CFSG.Monster.GMS.TwoCentral
public import CFSG.Monster.GMS.S4FamilyIso
public import Certificates.Certificate3024
public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.NotConj
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035

public section

namespace CFSG.Monster.GMS.S4Family

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Assembly

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Basic

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem orderOf_eq_two_of_isConj_a (hG : GMSF1Type d₀ a z₀) {x : G} (hx : IsConj a x) :
    orderOf x = 2 :=
  (orderOf_eq_of_isConj hx).symm.trans hG.1.1

omit [Finite G] in
theorem orderOf_eq_two_of_isConj_z₀ (hG : GMSF1Type d₀ a z₀) {x : G} (hx : IsConj z₀ x) :
    orderOf x = 2 :=
  (orderOf_eq_of_isConj hx).symm.trans hG.2.1

theorem not_isConj_of_isConj (hG : GMSF1Type d₀ a z₀) {x : G} (h1 : IsConj a x)
    (h2 : IsConj z₀ x) : False :=
  hG.not_isConj (h1.trans h2.symm)

omit [Finite G] in
theorem orderOf_mul_eq_two {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hc : x * y = y * x) (hne : x ≠ y) : orderOf (x * y) = 2 := by
  have hxx := mul_self_eq_one_of_orderOf hx
  have hyy := mul_self_eq_one_of_orderOf hy
  refine orderOf_eq_two_of_mul_self ?_ ?_
  · calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = 1 := by rw [← mul_assoc, hxx, one_mul, hyy]
  · intro h1
    apply hne
    rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hyy]

theorem isConj_or_isConj_z₀
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {x t : G}
    (hx : IsConj a x) (ht : t ∈ C[x]) (ht2 : orderOf t = 2) : IsConj a t ∨ IsConj z₀ t :=
  isConj_or_isConj_of_mem_centralizer I.sls I.tableV I.leech hG hx ht ht2

omit [Finite G] in
theorem eq_of_forall_comm_twoB (hG : GMSF1Type d₀ a z₀) {t x : G} (ht : IsConj z₀ t)
    (hx : x ∈ C[t]) (hx1 : x ≠ 1) (hcomm : ∀ y ∈ C[t], y * x = x * y) : x = t := by
  obtain ⟨hz, hQ, -, -, hcon⟩ := hG.2.of_isConj ht
  have hxQ : (⟨x, hx⟩ : ↥C[t]) ∈ pCore 2 ↥C[t] := by
    refine hcon (Subgroup.mem_centralizer_iff.mpr fun q _ => ?_)
    exact Subtype.ext (hcomm q.1 q.2)
  have hmem : x ∈ ((Subgroup.center (pCore 2 ↥C[t])).map (pCore 2 ↥C[t]).subtype).map
      C[t].subtype :=
    ⟨⟨x, hx⟩, ⟨⟨⟨x, hx⟩, hxQ⟩, Subgroup.mem_center_iff.mpr fun q =>
      Subtype.ext (Subtype.ext (hcomm q.1.1 q.1.2)), rfl⟩, rfl⟩
  rw [center_pCore_map_eq_zpowers hz hQ hcon, mem_zpowers_iff_of_orderOf_eq_two hz] at hmem
  exact hmem.resolve_left hx1

end Basic

section Iso

variable {G G' : Type} [Group G] [Group G'] [Finite G'] {d₀ : B} {a' z₀' : G'}

theorem apply_self_twoA
    (I' : GMSInterfaces d₀ G') (hG' : GMSF1Type d₀ a' z₀') {t : G} {t' : G'}
    (ht2 : orderOf t = 2) (ht' : IsConj a' t') {f : G → G'} (hf : IsIsoOn f C[t] C[t']) :
    f t = t' :=
  mulEquiv_centralizer_apply_self I' hG' ht2 ht' (isoEquiv hf)

omit [Finite G'] in
theorem apply_self_twoB (hG' : GMSF1Type d₀ a' z₀') {t : G} {t' : G'} (ht2 : orderOf t = 2)
    (ht' : IsConj z₀' t') {f : G → G'} (hf : IsIsoOn f C[t] C[t']) : f t = t' := by
  have htC : t ∈ C[t] := self_mem_centralizer t
  refine eq_of_forall_comm_twoB hG' ht' (hf.map_mem t htC) ?_ ?_
  · intro h1
    have : f t = f 1 := h1.trans (iso_map_one hf).symm
    exact ne_one_of_orderOf ht2 (hf.injOn htC (Subgroup.one_mem _) this)
  · intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hf.surjOn y hy
    have hc : y₀ * t = t * y₀ := Subgroup.mem_centralizer_singleton_iff.mp hy₀
    rw [← hf.map_mul y₀ hy₀ t htC, ← hf.map_mul t htC y₀ hy₀, hc]

end Iso

section Cubes

variable {G : Type} [Group G]

theorem count_three_cases {z₀ x y t : G} (h : twoBCount z₀ x y t = 3) :
    (¬ IsConj z₀ t ∧ IsConj z₀ (t * x) ∧ IsConj z₀ (t * y) ∧ IsConj z₀ (t * x * y)) ∨
    (IsConj z₀ t ∧ ¬ IsConj z₀ (t * x) ∧ IsConj z₀ (t * y) ∧ IsConj z₀ (t * x * y)) ∨
    (IsConj z₀ t ∧ IsConj z₀ (t * x) ∧ ¬ IsConj z₀ (t * y) ∧ IsConj z₀ (t * x * y)) ∨
    (IsConj z₀ t ∧ IsConj z₀ (t * x) ∧ IsConj z₀ (t * y) ∧ ¬ IsConj z₀ (t * x * y)) := by
  classical
  unfold twoBCount at h
  by_cases h0 : IsConj z₀ t <;> by_cases h1 : IsConj z₀ (t * x) <;>
    by_cases h2 : IsConj z₀ (t * y) <;> by_cases h3 : IsConj z₀ (t * x * y) <;>
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, h0, h1, h2, h3, ↓reduceIte,
      List.length_cons, List.length_nil] at h <;> first | omega | tauto

theorem eight_identities {s a y : G} (hay : a * y = y * a) (haa : a * a = 1)
    (hyy : y * y = 1) :
    s * a * a = s ∧ s * a * a * y = s * y ∧ s * y * y = s ∧ s * y * a = s * a * y ∧
      s * y * a * y = s * a ∧ s * a * y * a = s * y ∧ s * a * y * y = s * a ∧
      s * a * y * a * y = s := by
  have i1 : s * a * a = s := by rw [mul_assoc, haa, mul_one]
  have i3 : s * y * y = s := by rw [mul_assoc, hyy, mul_one]
  have i4 : s * y * a = s * a * y := by rw [mul_assoc, ← hay, ← mul_assoc]
  have i6 : s * a * y * a = s * y := by
    rw [mul_assoc (s * a) y a, ← hay, ← mul_assoc, i1]
  exact ⟨i1, by rw [i1], i3, i4, by rw [i4, mul_assoc, hyy, mul_one], i6,
    by rw [mul_assoc, hyy, mul_one], by rw [i6, i3]⟩

end Cubes

section Conj

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem isConj_a_of_not_isConj_z₀
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {x : G}
    (hx : orderOf x = 2) (h : ¬ IsConj z₀ x) : IsConj a x :=
  (s31_five I.sls I.tableV I.leech hG I.leechInv hx).resolve_right h

theorem exists_eight_data
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hEX : EightGroupExists a z₀) :
    ∃ y p : G, y ∈ C[a] ∧ p ∈ C[a] ∧ p ∈ C[y] ∧ IsConj a y ∧ IsConj a (a * y) ∧ IsConj a p ∧
      IsConj z₀ (p * a) ∧ IsConj z₀ (p * y) ∧ IsConj z₀ (p * a * y) := by
  obtain ⟨y, z, u, hT, hay⟩ := exists_twoClasses_isConj_mul I.sls I.tableV I.leech hG
  have hyA : IsConj a y := hT.isConj_b
  have ha2 : orderOf a = 2 := hG.1.1
  have hy2 : orderOf y = 2 := orderOf_eq_two_of_isConj_a hG hyA
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf ha2
  have hyy : y * y = 1 := mul_self_eq_one_of_orderOf hy2
  have hay2 : orderOf (a * y) = 2 := orderOf_eq_two_of_isConj_a hG hay
  have hcay : a * y = y * a :=
    mul_comm_of_mul_self_eq_one haa hyy (mul_self_eq_one_of_orderOf hay2)
  obtain ⟨s, ⟨hss, hsa, hsy, hs1, hsne_a, hsne_y, hsne_ay⟩, hcount⟩ :=
    hEX a y ⟨IsConj.refl a, hyA, hay⟩ 3 (Or.inr (Or.inl rfl))
  have hs2 : orderOf s = 2 := orderOf_eq_two_of_mul_self hss hs1
  have c_sa : Commute s a := hsa
  have c_sy : Commute s y := hsy
  have c_ay : Commute a y := hcay
  have c_ya : Commute y a := c_ay.symm
  have hsay : s * (a * y) = a * y * s := (c_sa.mul_right c_sy).eq
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := eight_identities hcay haa hyy
  have hyC : y ∈ C[a] := Subgroup.mem_centralizer_singleton_iff.mpr hcay.symm
  rcases count_three_cases hcount with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ |
      ⟨h0, h1, h2, h3⟩
  ·
    exact ⟨y, s, hyC, Subgroup.mem_centralizer_singleton_iff.mpr hsa,
      Subgroup.mem_centralizer_singleton_iff.mpr hsy, hyA, hay,
      isConj_a_of_not_isConj_z₀ I hG hs2 h0, h1, h2, h3⟩
  ·
    have hp2 : orderOf (s * a) = 2 := orderOf_mul_eq_two hs2 ha2 hsa hsne_a
    refine ⟨y, s * a, hyC, Subgroup.mem_centralizer_singleton_iff.mpr
      (c_sa.mul_left (Commute.refl a)).eq, Subgroup.mem_centralizer_singleton_iff.mpr
      (c_sy.mul_left c_ay).eq, hyA, hay, isConj_a_of_not_isConj_z₀ I hG hp2 h1, ?_, h3, ?_⟩
    · rw [i1]; exact h0
    · rw [i2]; exact h2
  ·
    have hp2 : orderOf (s * y) = 2 := orderOf_mul_eq_two hs2 hy2 hsy hsne_y
    refine ⟨y, s * y, hyC, Subgroup.mem_centralizer_singleton_iff.mpr
      (c_sa.mul_left c_ya).eq, Subgroup.mem_centralizer_singleton_iff.mpr
      (c_sy.mul_left (Commute.refl y)).eq, hyA, hay, isConj_a_of_not_isConj_z₀ I hG hp2 h2,
      ?_, ?_, ?_⟩
    · rw [i4]; exact h3
    · rw [i3]; exact h0
    · rw [i5]; exact h1
  ·
    have hp2 : orderOf (s * a * y) = 2 := by
      rw [mul_assoc]
      exact orderOf_mul_eq_two hs2 hay2 hsay hsne_ay
    refine ⟨y, s * a * y, hyC, Subgroup.mem_centralizer_singleton_iff.mpr
      ((c_sa.mul_left (Commute.refl a)).mul_left c_ya).eq,
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((c_sy.mul_left c_ay).mul_left (Commute.refl y)).eq, hyA, hay,
      isConj_a_of_not_isConj_z₀ I hG hp2 h3, ?_, ?_, ?_⟩
    · rw [i6]; exact h2
    · rw [i7]; exact h1
    · rw [i8]; exact h0

end Conj

end CFSG.Monster.GMS.S4Family
