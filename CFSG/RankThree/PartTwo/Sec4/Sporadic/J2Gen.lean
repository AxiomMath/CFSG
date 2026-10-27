
module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Base
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Base
public import CFSG.Foundations.Basic
public import CFSG.Monster.B.Mathieu.SylowSound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  Subgroup
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem pow_two_pow_eq_one [Finite G] {N : ℕ} (hN : ¬ 2 ^ (N + 1) ∣ Nat.card G) {g : G}
    (h : ∃ k, g ^ 2 ^ k = 1) : g ^ 2 ^ N = 1 := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have hdvd : 2 ^ m ∣ Nat.card G := hm ▸ _root_.orderOf_dvd_natCard g
  have hmN : m ≤ N := by
    by_contra hc
    exact hN ((pow_dvd_pow 2 (by omega)).trans hdvd)
  rw [← orderOf_dvd_iff_pow_eq_one, hm]
  exact pow_dvd_pow 2 hmN

theorem two_of_mem {H : Subgroup G} (hH : IsPGroup 2 H) {g : G} (hg : g ∈ H) :
    ∃ k, g ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨g, hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_normalizer_of_map_conj_eq' {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have e : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    rw [← mul_left_cancel (mul_right_cancel e)]
    exact hy

theorem mem_normalizer_zpowers_of_mem [Finite G] {u g : G} (h : g * u * g⁻¹ ∈ zpowers u) :
    g ∈ normalizer ((zpowers u : Subgroup G) : Set G) := by
  have hle : (zpowers u).map (MulAut.conj g).toMonoidHom ≤ zpowers u := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact h
  have heq : (zpowers u).map (MulAut.conj g).toMonoidHom = zpowers u :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact mem_normalizer_of_map_conj_eq' heq

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ v ∈ H, g * v * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact mem_normalizer_of_map_conj_eq' heq

theorem conj_mem_centralizer_of_mem_normalizer {x n c : G}
    (hn : n ∈ normalizer ((zpowers x : Subgroup G) : Set G))
    (hc : c ∈ centralizer ({x} : Set G)) : n * c * n⁻¹ ∈ centralizer ({x} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hc ⊢
  have hy : n⁻¹ * x * n ∈ zpowers x := by
    have := (mem_normalizer_iff.mp (inv_mem hn) x).mp (mem_zpowers x)
    simpa using this
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
  have hcy : c * (n⁻¹ * x * n) = n⁻¹ * x * n * c := by
    rw [← hk]
    exact (Commute.zpow_right (show Commute c x from hc) k).eq
  calc n * c * n⁻¹ * x = n * (c * (n⁻¹ * x * n)) * n⁻¹ := by group
    _ = n * (n⁻¹ * x * n * c) * n⁻¹ := by rw [hcy]
    _ = x * (n * c * n⁻¹) := by group

theorem centralizer_le_normalizer_zpowers' [Finite G] (x : G) :
    centralizer ({x} : Set G) ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_zpowers_of_mem ?_
  rw [mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]
  exact mem_zpowers x

theorem mulAut_mul_conj (φ : MulAut G) (x : G) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  refine MulEquiv.ext fun k => ?_
  simp [MulAut.mul_apply, MulAut.inv_apply]

theorem le_inSubgroup_pCore {H V : Subgroup G} (hVH : V ≤ H) (hVn : (V.subgroupOf H).Normal)
    (hV2 : IsPGroup 2 V) : V ≤ inSubgroup (CFSG.pCore 2) H := by
  have hp : IsPGroup 2 (V.subgroupOf H) := hV2.comap_of_injective _ H.subtype_injective
  have hle : V.subgroupOf H ≤ CFSG.pCore 2 H := le_sSup ⟨hVn, hp⟩
  intro v hv
  exact ⟨⟨v, hVH hv⟩, hle (by rw [mem_subgroupOf]; exact hv), rfl⟩

theorem two_of_mem_inSubgroup_pCore {H : Subgroup G} {w : G}
    (hw : w ∈ inSubgroup (CFSG.pCore 2) H) : w ∈ H ∧ ∃ k, w ^ 2 ^ k = 1 := by
  obtain ⟨w', hw', rfl⟩ := hw
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := H) ⟨w', hw'⟩
  refine ⟨w'.2, k, ?_⟩
  have := congrArg (fun q : CFSG.pCore 2 H => ((q : H) : G)) hk
  simpa using this

theorem conj_mem_inSubgroup_pCore {H : Subgroup G} {w n : G}
    (hw : w ∈ inSubgroup (CFSG.pCore 2) H) (hn : n ∈ H) :
    n * w * n⁻¹ ∈ inSubgroup (CFSG.pCore 2) H := by
  obtain ⟨w', hw', rfl⟩ := hw
  exact ⟨_, (CFSG.pCore_normal (p := 2) (G := H)).conj_mem w' hw' ⟨n, hn⟩, rfl⟩

theorem inSubgroup_pCore_eq {H V : Subgroup G} (hVH : V ≤ H) (hVn : (V.subgroupOf H).Normal)
    (hV2 : IsPGroup 2 V) (hT : ∀ w ∈ inSubgroup (CFSG.pCore 2) H, w ∈ V) :
    inSubgroup (CFSG.pCore 2) H = V :=
  le_antisymm (fun w hw => hT w hw) (le_inSubgroup_pCore hVH hVn hV2)

theorem T_test {H : Subgroup G} {w : G} (hw : w ∈ inSubgroup (CFSG.pCore 2) H) :
    w ∈ H ∧ (∃ k, w ^ 2 ^ k = 1) ∧ ∀ n ∈ H, ∃ k, (w * (n * w * n⁻¹)) ^ 2 ^ k = 1 := by
  obtain ⟨hwH, h2⟩ := two_of_mem_inSubgroup_pCore hw
  refine ⟨hwH, h2, fun n hn => ?_⟩
  exact (two_of_mem_inSubgroup_pCore ((inSubgroup (CFSG.pCore 2) H).mul_mem hw
    (conj_mem_inSubgroup_pCore hw hn))).2

theorem klein_sq {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    a * b * (a * b) = 1 := by
  rw [mul_assoc, ← mul_assoc b, ← hab, mul_assoc, hb, mul_one, ha]

theorem klein_mul_mem {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {x y : G} (hx : x = 1 ∨ x = a ∨ x = b ∨ x = a * b)
    (hy : y = 1 ∨ y = a ∨ y = b ∨ y = a * b) :
    x * y = 1 ∨ x * y = a ∨ x * y = b ∨ x * y = a * b := by
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e3 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
  have e4 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
  have e5 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e6 : a * b * (a * b) = 1 := klein_sq ha hb hab
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, ha, hb, e1, e3, e4, e5, e6, ← hab, true_or, or_true]

@[expose] def kleinSub {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  mul_mem' hx hy := klein_mul_mem ha hb hab hx hy
  one_mem' := Or.inl rfl
  inv_mem' {x} hx := by
    have hx' : x⁻¹ = x := by
      rcases hx with h | h | h | h <;> rw [h]
      · exact inv_one
      · exact inv_eq_of_mul_eq_one_right ha
      · exact inv_eq_of_mul_eq_one_right hb
      · exact inv_eq_of_mul_eq_one_right (klein_sq ha hb hab)
    show x⁻¹ = 1 ∨ x⁻¹ = a ∨ x⁻¹ = b ∨ x⁻¹ = a * b
    rw [hx']
    exact hx

variable {a b : G} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}

theorem mem_kleinSub {x : G} :
    x ∈ kleinSub ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem mul_self_of_mem_kleinSub {x : G} (hx : x ∈ kleinSub ha hb hab) : x * x = 1 := by
  rcases mem_kleinSub.1 hx with h | h | h | h <;> rw [h]
  · exact mul_one 1
  · exact ha
  · exact hb
  · exact klein_sq ha hb hab

theorem isPGroup_kleinSub : IsPGroup 2 (kleinSub ha hb hab) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, pow_one, sq, OneMemClass.coe_one]
  exact mul_self_of_mem_kleinSub g.2

end Generic

theorem okA_spec {t : Array ℕ} (h : okA t = true) : validA 315 t = true ∧ inP t = true := by
  simpa [okA] using h

theorem eq_of_rep {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1) (hu : Rep 315 u h.1)
    (he : eqA 315 t u = true) : g = h :=
  Subtype.ext (eq_of_eqA ht hu he)

theorem rep_mul {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1) (hu : Rep 315 u h.1) :
    Rep 315 (compA 315 t u) (g * h).1 :=
  rep_compA ht hu

theorem rep_pow {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (k : ℕ) :
    Rep 315 (powArr 315 t k) (g ^ k).1 := by
  rw [Subgroup.coe_pow]
  exact rep_powArr ht k

theorem rep_one : Rep 315 (idA 315) (1 : GJ).1 := rep_idA

theorem rep_conj {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1) (hv : validA 315 t = true)
    (hu : Rep 315 u h.1) : Rep 315 (conjA 315 t u) (g * h * g⁻¹).1 := by
  have := rep_conjA hv hu
  rw [(rep_of_validA hv).unique ht] at this
  simpa using this

theorem rep_conjInv {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1) (hv : validA 315 t = true)
    (hu : Rep 315 u h.1) : Rep 315 (conjInvA 315 t u) (g⁻¹ * h * g).1 := by
  have := rep_conjInvA hv hu
  rw [(rep_of_validA hv).unique ht] at this
  simpa using this

theorem commute_of_commA {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1) (hu : Rep 315 u h.1)
    (hc : commA t u = true) : Commute g h := by
  have := eqA_iff (rep_compA ht hu) (rep_compA hu ht)
  exact Subtype.ext ((this.1 hc))

theorem commA_of_commute {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1) (hu : Rep 315 u h.1)
    (hc : Commute g h) : commA t u = true :=
  (eqA_iff (rep_compA ht hu) (rep_compA hu ht)).2 (congrArg Subtype.val hc.eq)

theorem inCert_of_mem {gs : Array (Array ℕ)} {c : CFSG.Monster.B.Fischer.ArrCert}
    (henum : enumOK 315 gs keyPts c = true) {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (hg : g ∈ subOf gs) : inCert c t = true := by
  obtain ⟨i, hi, hr⟩ := exists_rep_subOf (by decide) henum hg
  rw [inCert, List.any_eq_true]
  refine ⟨c.pts[i]!, ?_, (eqA_iff ht hr).2 rfl⟩
  rw [getElem!_pos c.pts i hi]
  exact Array.getElem_mem_toList hi

theorem mem_of_inCert {gs : Array (Array ℕ)} {c : CFSG.Monster.B.Fischer.ArrCert}
    (henum : enumOK 315 gs keyPts c = true) {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (h : inCert c t = true) : g ∈ subOf gs :=
  mem_subOf_of_any (by decide) henum ht h

theorem card_GJ : Nat.card GJ = 604800 := card_P

theorem subOf_eq_closure {gs : Array (Array ℕ)} {S : Set GJ}
    (h : permsA 315 gs = (CFSG.ComponentClassification.J2Cover.P).subtype '' S) :
    subOf gs = closure S := by
  rw [subOf, h, ← MonoidHom.map_closure, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]

@[expose] noncomputable def gElt (gs : Array (Array ℕ))
    (h : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true) (k : ℕ)
    (hk : k < gs.size) : GJ :=
  elA gs[k]! (h k hk)

theorem subOf_eq_closure_gElt (gs : Array (Array ℕ))
    (h : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true) :
    subOf gs = closure {g | ∃ k, ∃ hk : k < gs.size, gElt gs h k hk = g} := by
  apply subOf_eq_closure
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨gElt gs h k hk, ⟨k, hk, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem rep_sqIterA_perm {t : Array ℕ} {g : Equiv.Perm (Fin 315)} (ht : Rep 315 t g) (n : ℕ) :
    Rep 315 (sqIterA n t) (g ^ 2 ^ n) := by
  induction n generalizing t g with
  | zero => simpa [sqIterA] using ht
  | succ n ih =>
    have h2 : Rep 315 (sqA t) (g * g) := rep_compA ht ht
    rw [sqIterA, pow_succ', pow_mul, sq]
    exact ih h2

theorem rep_sqIterA {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (n : ℕ) :
    Rep 315 (sqIterA n t) (g ^ 2 ^ n).1 := by
  rw [Subgroup.coe_pow]
  exact rep_sqIterA_perm ht n

theorem isTwoA_iff {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) :
    isTwoA t = true ↔ g ^ 2 ^ 7 = 1 := by
  rw [isTwoA, eqA_iff (rep_sqIterA ht 7) rep_one]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩

theorem pow128 {g : GJ} (h : ∃ k, g ^ 2 ^ k = 1) : g ^ 2 ^ 7 = 1 :=
  pow_two_pow_eq_one (by rw [card_GJ]; norm_num) h

theorem rep_conj_perm {t u : Array ℕ} {g h : Equiv.Perm (Fin 315)} (ht : Rep 315 t g)
    (hv : validA 315 t = true) (hu : Rep 315 u h) : Rep 315 (conjA 315 t u) (g * h * g⁻¹) := by
  have := rep_conjA hv hu
  rwa [(rep_of_validA hv).unique ht] at this

@[expose] noncomputable def eltOf (t : Array ℕ) (h : okA t = true) : GJ := elA t (okA_spec h)

theorem rep_eltOf {t : Array ℕ} (h : okA t = true) : Rep 315 t (eltOf t h).1 := rep_elA _

theorem rep_gElt (gs : Array (Array ℕ))
    (h : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true) (k : ℕ)
    (hk : k < gs.size) : Rep 315 gs[k]! (gElt gs h k hk).1 :=
  rep_elA _

theorem gElt_mem (gs : Array (Array ℕ))
    (h : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true) (k : ℕ)
    (hk : k < gs.size) : gElt gs h k hk ∈ subOf gs := by
  rw [subOf_eq_closure_gElt gs h]
  exact subset_closure ⟨k, hk, rfl⟩

theorem subOf_le_of (gs : Array (Array ℕ))
    (h : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true) {H : Subgroup GJ}
    (hH : ∀ k (hk : k < gs.size), gElt gs h k hk ∈ H) : subOf gs ≤ H := by
  rw [subOf_eq_closure_gElt gs h, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact hH k hk

theorem permOfArr_gElt (gs : Array (Array ℕ))
    (h : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true) (k : ℕ)
    (hk : k < gs.size) : permOfArr 315 gs[k]! = (gElt gs h k hk).1 :=
  (rep_of_validA (h k hk).1).unique (rep_gElt gs h k hk)

theorem getElem!_push_lt {gs : Array (Array ℕ)} {a : Array ℕ} {k : ℕ} (hk : k < gs.size) :
    (gs.push a)[k]! = gs[k]! := by
  rw [getElem!_pos (gs.push a) k (by rw [Array.size_push]; omega), getElem!_pos gs k hk,
    Array.getElem_push_lt hk]

theorem getElem!_push_size {gs : Array (Array ℕ)} {a : Array ℕ} : (gs.push a)[gs.size]! = a := by
  rw [getElem!_pos (gs.push a) gs.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem spec_push {gs : Array (Array ℕ)} {a : Array ℕ}
    (hgs : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true)
    (ha : validA 315 a = true ∧ inP a = true) :
    ∀ k < (gs.push a).size, validA 315 (gs.push a)[k]! = true ∧ inP (gs.push a)[k]! = true := by
  intro k hk
  rw [Array.size_push] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | rfl
  · rw [getElem!_push_lt hlt]
    exact hgs k hlt
  · rw [getElem!_push_size]
    exact ha

theorem subOf_le_push (gs : Array (Array ℕ)) (a : Array ℕ) : subOf gs ≤ subOf (gs.push a) := by
  intro g hg
  rw [mem_subOf] at hg ⊢
  refine Subgroup.closure_mono ?_ hg
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < gs.size := hk
  exact ⟨k, by show k < (gs.push a).size; rw [Array.size_push]; omega,
    by show permOfArr 315 (gs.push a)[k]! = _; rw [getElem!_push_lt hk']⟩

theorem mem_subOf_push_last {gs : Array (Array ℕ)} {a : Array ℕ} {g : GJ} (ha : Rep 315 a g.1)
    (hv : validA 315 a = true) : g ∈ subOf (gs.push a) := by
  rw [mem_subOf]
  refine Subgroup.subset_closure ⟨gs.size, by show gs.size < (gs.push a).size; simp, ?_⟩
  show permOfArr 315 (gs.push a)[gs.size]! = g.1
  rw [getElem!_push_size]
  exact (rep_of_validA hv).unique ha

theorem subOf_push_le {gs : Array (Array ℕ)} {a : Array ℕ}
    (hgs : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true) {g : GJ}
    (ha : Rep 315 a g.1) (hv : validA 315 a = true) {H : Subgroup GJ} (h1 : subOf gs ≤ H)
    (h2 : g ∈ H) : subOf (gs.push a) ≤ H := by
  intro x hx
  rw [mem_subOf] at hx
  have hle : Subgroup.closure (permsA 315 (gs.push a)) ≤
      H.map (CFSG.ComponentClassification.J2Cover.P).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < gs.size + 1 := by simpa using hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
    · refine ⟨gElt gs hgs k hlt, h1 (gElt_mem gs hgs k hlt), ?_⟩
      show (gElt gs hgs k hlt).1 = permOfArr 315 (gs.push a)[k]!
      rw [getElem!_push_lt hlt]
      exact (permOfArr_gElt gs hgs k hlt).symm
    · refine ⟨g, h2, ?_⟩
      show g.1 = permOfArr 315 (gs.push a)[gs.size]!
      rw [getElem!_push_size]
      exact ((rep_of_validA hv).unique ha).symm
  obtain ⟨x', hx', hxx'⟩ := hle hx
  rw [← Subtype.ext hxx']
  exact hx'

theorem normalizer_zpowers_eq {u hA : GJ} {gs : Array (Array ℕ)} {a : Array ℕ}
    (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (hC : centralizer ({u} : Set GJ) = subOf gs)
    (hgs : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true)
    (ha : Rep 315 a hA.1) (hv : validA 315 a = true) (hconj : hA * u * hA⁻¹ = u ^ 2) :
    normalizer ((zpowers u : Subgroup GJ) : Set GJ) = subOf (gs.push a) := by
  have hle := subOf_le_push gs a
  have hmA : hA ∈ subOf (gs.push a) := mem_subOf_push_last ha hv
  apply le_antisymm
  · intro g hg
    have hmem := (mem_normalizer_iff.mp hg u).mp (mem_zpowers u)
    have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
    have hfin : IsOfFinOrder u := orderOf_pos_iff.1 (by rw [hord]; norm_num)
    obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 (hfin.mem_zpowers_iff_mem_range_orderOf.1 hmem)
    rw [Finset.mem_range, hord] at hk
    interval_cases k
    · exfalso
      rw [pow_zero] at hk'
      apply hu1
      have : g * u * g⁻¹ = g * 1 * g⁻¹ := by rw [mul_one, mul_inv_cancel]; exact hk'.symm
      exact mul_right_cancel (mul_left_cancel this)
    · apply hle
      rw [← hC, mem_centralizer_singleton_iff]
      have h1 : g * u * g⁻¹ = u := by rw [← hk', pow_one]
      calc g * u = g * u * g⁻¹ * g := by group
        _ = u * g := by rw [h1]
    · have hc : hA⁻¹ * g ∈ centralizer ({u} : Set GJ) := by
        rw [mem_centralizer_singleton_iff]
        have h1 : g * u * g⁻¹ = u ^ 2 := hk'.symm
        have h2 : hA⁻¹ * u ^ 2 * hA = u := by rw [← hconj]; group
        calc hA⁻¹ * g * u = hA⁻¹ * (g * u * g⁻¹) * g := by group
          _ = hA⁻¹ * u ^ 2 * hA * (hA⁻¹ * g) := by rw [h1]; group
          _ = u * (hA⁻¹ * g) := by rw [h2]
      have := (subOf (gs.push a)).mul_mem hmA (hle (hC ▸ hc))
      rwa [mul_inv_cancel_left] at this
  · refine subOf_push_le hgs ha hv ?_ (mem_normalizer_zpowers_of_mem ?_)
    · rw [← hC]
      exact centralizer_le_normalizer_zpowers' u
    · rw [hconj]
      exact pow_mem (mem_zpowers u) 2

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
