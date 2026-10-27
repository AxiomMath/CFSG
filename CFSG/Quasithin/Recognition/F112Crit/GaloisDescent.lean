module

public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Abel

public section

namespace CFSG.Quasithin.F112Crit

namespace GaloisDescent

variable {A : Type*} [AddCommGroup A]

@[expose] def subId (x : A ≃+ A) : A →+ A where
  toFun a := x a - a
  map_zero' := by simp
  map_add' a b := by simp only [map_add]; abel

@[expose] def commSub (x : A ≃+ A) : AddSubgroup A := (subId x).range

@[expose] def fixSub (t : A ≃+ A) : AddSubgroup A where
  carrier := {a | t a = a}
  zero_mem' := map_zero t
  add_mem' := fun {a b} (ha : t a = a) (hb : t b = b) => by
    show t (a + b) = a + b
    rw [map_add, ha, hb]
  neg_mem' := fun {a} (ha : t a = a) => by
    show t (-a) = -a
    rw [map_neg, ha]

theorem mem_fixSub {t : A ≃+ A} {a : A} : a ∈ fixSub t ↔ t a = a := Iff.rfl

theorem x_sub_mem_commSub (x : A ≃+ A) (a : A) : x a - a ∈ commSub x := ⟨a, rfl⟩

theorem card_commSub_eq_index (t : A ≃+ A) : Nat.card (commSub t) = (fixSub t).index := by
  have hker : (subId t).ker = fixSub t := by
    ext a
    rw [AddMonoidHom.mem_ker]
    show t a - a = 0 ↔ t a = a
    exact sub_eq_zero
  rw [← hker, AddSubgroup.index_ker]
  rfl

theorem iterate_sub (x : A ≃+ A) (n : ℕ) (a b : A) :
    (⇑x)^[n] (a - b) = (⇑x)^[n] a - (⇑x)^[n] b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_sub, ih]

@[expose] def orbitSum (x : A ≃+ A) (p : ℕ) (a : A) : A := ∑ i ∈ Finset.range p, (⇑x)^[i] a

theorem orbitSum_sub (x : A ≃+ A) (p : ℕ) (a b : A) :
    orbitSum x p (a - b) = orbitSum x p a - orbitSum x p b := by
  simp only [orbitSum, iterate_sub, Finset.sum_sub_distrib]

theorem orbitSum_apply {x : A ≃+ A} {p : ℕ} (hxp : ∀ a, (⇑x)^[p] a = a) (a : A) :
    orbitSum x p (x a) = orbitSum x p a := by
  unfold orbitSum
  have h1 := Finset.sum_range_succ' (fun i => (⇑x)^[i] a) p
  have h2 := Finset.sum_range_succ (fun i => (⇑x)^[i] a) p
  have h3 : ∑ i ∈ Finset.range p, (⇑x)^[i] (x a) = ∑ i ∈ Finset.range p, (⇑x)^[i + 1] a := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.iterate_succ_apply]
  have h4 : (⇑x)^[p] a = (⇑x)^[0] a := by rw [hxp]; rfl
  have h5 := h1.symm.trans h2
  rw [h4] at h5
  rw [h3]
  exact add_right_cancel h5

theorem orbitSum_of_fixed {x : A ≃+ A} {p : ℕ} {a : A} (ha : x a = a) :
    orbitSum x p a = p • a := by
  unfold orbitSum
  simp only [Function.iterate_fixed ha, Finset.sum_const, Finset.card_range]

theorem odd_nsmul_eq (h2 : ∀ a : A, a + a = 0) {p : ℕ} (hp : p % 2 = 1) (a : A) : p • a = a := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have e : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
    rw [e, succ_nsmul, succ_nsmul, ih (by omega), add_assoc, h2, add_zero]

theorem commSub_stable {x t : A ≃+ A} (htx : ∀ a, t (x a) = x.symm (t a)) {w : A}
    (hw : w ∈ commSub x) :
    x w ∈ commSub x ∧ x.symm w ∈ commSub x ∧ t w ∈ commSub x := by
  obtain ⟨a, ha⟩ := hw
  have ha' : x a - a = w := ha
  subst ha'
  refine ⟨⟨x a, ?_⟩, ⟨x.symm a, ?_⟩, ⟨-(x.symm (t a)), ?_⟩⟩
  · show x (x a) - x a = x (x a - a)
    rw [map_sub]
  · show x (x.symm a) - x.symm a = x.symm (x a - a)
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  · show x (-(x.symm (t a))) - -(x.symm (t a)) = t (x a - a)
    rw [map_sub, htx, map_neg, AddEquiv.apply_symm_apply]
    abel

theorem commSub_iff {x t : A ≃+ A} (htx : ∀ a, t (x a) = x.symm (t a)) (a : A) :
    a ∈ commSub x ↔ x a ∈ commSub x := by
  refine ⟨fun h => (commSub_stable htx h).1, fun h => ?_⟩
  have := (commSub_stable htx h).2.1
  rwa [AddEquiv.symm_apply_apply] at this

theorem commSub_fix {x : A ≃+ A} {p : ℕ} (h2 : ∀ a : A, a + a = 0) (hp2 : p % 2 = 1)
    (hxp : ∀ a, (⇑x)^[p] a = a) {w : A} (hw : w ∈ commSub x) (hxw : x w = w) : w = 0 := by
  obtain ⟨a, ha⟩ := hw
  have ha' : x a - a = w := ha
  have h1 : orbitSum x p w = 0 := by
    rw [← ha', orbitSum_sub, orbitSum_apply hxp, sub_self]
  have h3 := orbitSum_of_fixed (p := p) hxw
  rw [h1, odd_nsmul_eq h2 hp2] at h3
  exact h3.symm

theorem fix_of_sq_fix {x : A ≃+ A} {p : ℕ} (hxp : ∀ a, (⇑x)^[p] a = a) (hp2 : p % 2 = 1) {w : A}
    (h : x (x w) = w) : x w = w := by
  obtain ⟨k, hk⟩ : ∃ k, p + 1 = 2 * k := ⟨(p + 1) / 2, by omega⟩
  have h1 : (⇑x)^[2] w = w := by simpa [Function.iterate_succ_apply] using h
  have h2 : (⇑x)^[2 * k] w = w := by
    rw [Function.iterate_mul]; exact Function.iterate_fixed h1 k
  have h3 : (⇑x)^[p + 1] w = x w := by
    rw [Function.iterate_succ_apply', hxp]
  rw [← h3, hk]; exact h2

theorem sub_symm_aux (x : A ≃+ A) (u u' : A) :
    x (u - u') - x.symm (u - u') = (x u - x.symm u) - (x u' - x.symm u') := by
  rw [map_sub, map_sub]; abel

theorem dvd_card_sub_one [Finite A] {x : A ≃+ A} {p : ℕ} (hp : p.Prime)
    (hxp : ∀ a, (⇑x)^[p] a = a) {W : AddSubgroup A} (hWx : ∀ a, a ∈ W ↔ x a ∈ W)
    (hfix : ∀ w ∈ W, x w = w → w = 0) : p ∣ Nat.card W - 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype A := Fintype.ofFinite A
  let σ : Equiv.Perm ↥W := Equiv.Perm.subtypePerm x.toEquiv (fun a => (hWx a).symm)
  have hσn : ∀ (n : ℕ) (w : ↥W), ((σ ^ n) w : A) = (⇑x)^[n] (w : A) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih => intro w; rw [pow_succ, Equiv.Perm.mul_apply, ih]; rfl
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    refine Equiv.ext fun w => Subtype.ext ?_
    rw [hσn, hxp]
    rfl
  have hmod := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) hσ
  have hcard : (Equiv.Perm.support σ)ᶜ.card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨⟨0, W.zero_mem⟩, ?_⟩
    ext w
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro hw
      have h1 : x (w : A) = (w : A) := congrArg Subtype.val hw
      exact Subtype.ext (hfix w w.2 h1)
    · intro hw
      subst hw
      exact Subtype.ext (map_zero x)
  rw [hcard, ← Nat.card_eq_fintype_card] at hmod
  have hpos : 0 < Nat.card W := Nat.card_pos
  exact (Nat.modEq_iff_dvd' (by omega)).mp hmod

section Core

variable {W : AddSubgroup A} {x t : A ≃+ A}

theorem symm_mem_of_stable (hWx : ∀ a, a ∈ W ↔ x a ∈ W) {a : A} (ha : a ∈ W) : x.symm a ∈ W := by
  rw [hWx, AddEquiv.apply_symm_apply]; exact ha

theorem card_eq_sq [Finite A] (htt : ∀ a, t (t a) = a) (htx : ∀ a, t (x a) = x.symm (t a))
    (hWx : ∀ a, a ∈ W ↔ x a ∈ W) (hWt : ∀ a ∈ W, t a ∈ W)
    (hx2 : ∀ w ∈ W, x (x w) = w → w = 0) :
    Nat.card W = Nat.card ↥(W ⊓ fixSub t) ^ 2 := by
  have htxs : ∀ a, t (x.symm a) = x (t a) := fun a => by
    have h := htx (x.symm a)
    rw [AddEquiv.apply_symm_apply] at h
    rw [h, AddEquiv.apply_symm_apply]
  have key : ∀ d ∈ W, x d = x.symm d → d = 0 := by
    intro d hd h
    apply hx2 d hd
    rw [h, AddEquiv.apply_symm_apply]
  let φ : ↥(W ⊓ fixSub t) × ↥(W ⊓ fixSub t) → ↥W := fun k =>
    ⟨(k.1 : A) + x (k.2 : A), W.add_mem k.1.2.1 ((hWx _).mp k.2.2.1)⟩
  have hinj : Function.Injective φ := by
    have aux : ∀ d₁ d₂ : A, d₁ ∈ W ⊓ fixSub t → d₂ ∈ W ⊓ fixSub t → d₁ + x d₂ = 0 →
        d₁ = 0 ∧ d₂ = 0 := by
      intro d₁ d₂ h₁ h₂ h
      have ht₁ : t d₁ = d₁ := h₁.2
      have ht₂ : t d₂ = d₂ := h₂.2
      have h' : d₁ + x.symm d₂ = 0 := by
        have := congrArg t h
        rw [map_add, map_zero, htx, ht₁, ht₂] at this
        exact this
      have hxd : x d₂ = x.symm d₂ := by
        have e1 : x d₂ = -d₁ := eq_neg_of_add_eq_zero_right h
        have e2 : x.symm d₂ = -d₁ := eq_neg_of_add_eq_zero_right h'
        rw [e1, e2]
      have hd₂ : d₂ = 0 := key d₂ h₂.1 hxd
      refine ⟨?_, hd₂⟩
      rw [hd₂, map_zero, add_zero] at h
      exact h
    rintro ⟨k₁, k₂⟩ ⟨k₁', k₂'⟩ h
    have h' : (k₁ : A) + x (k₂ : A) = (k₁' : A) + x (k₂' : A) := congrArg Subtype.val h
    have h'' : ((k₁ : A) - k₁') + x ((k₂ : A) - k₂') = 0 := by
      rw [map_sub]
      calc ((k₁ : A) - k₁') + (x (k₂ : A) - x (k₂' : A))
          = ((k₁ : A) + x (k₂ : A)) - ((k₁' : A) + x (k₂' : A)) := by abel
        _ = 0 := sub_eq_zero.mpr h'
    obtain ⟨e1, e2⟩ := aux _ _ ((W ⊓ fixSub t).sub_mem k₁.2 k₁'.2)
      ((W ⊓ fixSub t).sub_mem k₂.2 k₂'.2) h''
    have e1' : (k₁ : A) = k₁' := sub_eq_zero.mp e1
    have e2' : (k₂ : A) = k₂' := sub_eq_zero.mp e2
    exact Prod.ext (Subtype.ext e1') (Subtype.ext e2')
  have hsurj : Function.Surjective φ := by
    let ψ : ↥W → ↥W := fun u =>
      ⟨x (u : A) - x.symm (u : A),
        W.sub_mem ((hWx _).mp u.2) (symm_mem_of_stable hWx u.2)⟩
    have hψinj : Function.Injective ψ := by
      intro u u' h
      have h1 : x (u : A) - x.symm (u : A) = x (u' : A) - x.symm (u' : A) :=
        congrArg Subtype.val h
      have h2 : x ((u : A) - u') = x.symm ((u : A) - u') := by
        have := sub_symm_aux x (u : A) (u' : A)
        rw [h1, sub_self] at this
        exact sub_eq_zero.mp this
      have h3 := key _ (W.sub_mem u.2 u'.2) h2
      exact Subtype.ext (sub_eq_zero.mp h3)
    have hψsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψinj
    intro w
    obtain ⟨b, hb⟩ := hψsurj ⟨(w : A) - t (w : A), W.sub_mem w.2 (hWt _ w.2)⟩
    have hb' : x (b : A) - x.symm (b : A) = (w : A) - t (w : A) := congrArg Subtype.val hb
    have htb : t (b : A) = b := by
      have h1 : x.symm (t (b : A)) - x (t (b : A)) = t (w : A) - w := by
        have := congrArg t hb'
        rw [map_sub, map_sub, htx, htxs, htt] at this
        exact this
      have h2 : x (t (b : A) - b) = x.symm (t (b : A) - b) := by
        have h5 : x (t (b : A)) - x.symm (t (b : A)) = x (b : A) - x.symm (b : A) := by
          calc x (t (b : A)) - x.symm (t (b : A))
              = -(x.symm (t (b : A)) - x (t (b : A))) := by abel
            _ = -(t (w : A) - w) := by rw [h1]
            _ = (w : A) - t (w : A) := by abel
            _ = x (b : A) - x.symm (b : A) := hb'.symm
        have := sub_symm_aux x (t (b : A)) (b : A)
        rw [h5, sub_self] at this
        exact sub_eq_zero.mp this
      have h6 := key _ (W.sub_mem (hWt _ b.2) b.2) h2
      exact sub_eq_zero.mp h6
    have hbK : (b : A) ∈ W ⊓ fixSub t := ⟨b.2, htb⟩
    have haK : (w : A) - x (b : A) ∈ W ⊓ fixSub t := by
      refine ⟨W.sub_mem w.2 ((hWx _).mp b.2), ?_⟩
      show t ((w : A) - x (b : A)) = (w : A) - x (b : A)
      rw [map_sub, htx, htb]
      have h0 : t (w : A) - x.symm (b : A) - ((w : A) - x (b : A)) = 0 := by
        calc t (w : A) - x.symm (b : A) - ((w : A) - x (b : A))
            = (x (b : A) - x.symm (b : A)) - ((w : A) - t (w : A)) := by abel
          _ = 0 := sub_eq_zero.mpr hb'
      exact sub_eq_zero.mp h0
    refine ⟨(⟨(w : A) - x (b : A), haK⟩, ⟨(b : A), hbK⟩), Subtype.ext ?_⟩
    show ((w : A) - x (b : A)) + x (b : A) = w
    abel
  have := Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at this
  rw [← this, sq]

end Core

section Main

variable {x t : A ≃+ A} {p : ℕ}

theorem card_commSub_eq_sq [Finite A] (h2 : ∀ a : A, a + a = 0) (hp2 : p % 2 = 1)
    (hxp : ∀ a, (⇑x)^[p] a = a) (htt : ∀ a, t (t a) = a) (htx : ∀ a, t (x a) = x.symm (t a)) :
    Nat.card (commSub x) = Nat.card ↥(commSub x ⊓ fixSub t) ^ 2 :=
  card_eq_sq htt htx (commSub_iff htx) (fun _ hw => (commSub_stable htx hw).2.2)
    (fun w hw h => commSub_fix h2 hp2 hxp hw (fix_of_sq_fix hxp hp2 h))

theorem dvd_card_commSub_sub_one [Finite A] (h2 : ∀ a : A, a + a = 0) (hp : p.Prime)
    (hp2 : p % 2 = 1) (hxp : ∀ a, (⇑x)^[p] a = a) (htx : ∀ a, t (x a) = x.symm (t a)) :
    p ∣ Nat.card (commSub x) - 1 :=
  dvd_card_sub_one hp hxp (commSub_iff htx) (fun _ hw => commSub_fix h2 hp2 hxp hw)

theorem relIndex_le_index [Finite A] (W : AddSubgroup A) (t : A ≃+ A) :
    (W ⊓ fixSub t).relIndex W ≤ (fixSub t).index := by
  rw [inf_comm, AddSubgroup.inf_relIndex_right]
  calc (fixSub t).relIndex W ≤ (fixSub t).relIndex ⊤ :=
        AddSubgroup.relIndex_le_of_le_right le_top
          (by rw [AddSubgroup.relIndex_top_right]; exact AddSubgroup.index_ne_zero_of_finite)
    _ = (fixSub t).index := AddSubgroup.relIndex_top_right _

theorem relIndex_eq_card [Finite A] (h2 : ∀ a : A, a + a = 0) (hp2 : p % 2 = 1)
    (hxp : ∀ a, (⇑x)^[p] a = a) (htt : ∀ a, t (t a) = a) (htx : ∀ a, t (x a) = x.symm (t a)) :
    (commSub x ⊓ fixSub t).relIndex (commSub x) = Nat.card ↥(commSub x ⊓ fixSub t) := by
  have h1 := AddSubgroup.relIndex_mul_card (commSub x ⊓ fixSub t) (commSub x)
  rw [inf_eq_left.mpr (inf_le_left : commSub x ⊓ fixSub t ≤ commSub x)] at h1
  have h2' := card_commSub_eq_sq h2 hp2 hxp htt htx
  have hpos : 0 < Nat.card ↥(commSub x ⊓ fixSub t) := Nat.card_pos
  rw [h2', sq] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem eq_three_of_index_le_two [Finite A] (h2 : ∀ a : A, a + a = 0) (hp : p.Prime)
    (hp2 : p % 2 = 1) (hxp : ∀ a, (⇑x)^[p] a = a) (htt : ∀ a, t (t a) = a)
    (htx : ∀ a, t (x a) = x.symm (t a)) (hW : commSub x ≠ ⊥) (hidx : (fixSub t).index ≤ 2) :
    p = 3 ∧ Nat.card (commSub x) = 4 ∧ Nat.card ↥(commSub x ⊓ fixSub t) = 2 := by
  have hsq := card_commSub_eq_sq h2 hp2 hxp htt htx
  have hrel := relIndex_eq_card h2 hp2 hxp htt htx
  have hle := relIndex_le_index (commSub x) t
  have hK2 : Nat.card ↥(commSub x ⊓ fixSub t) ≤ 2 := by
    rw [← hrel]; exact hle.trans hidx
  have hKpos : 0 < Nat.card ↥(commSub x ⊓ fixSub t) := Nat.card_pos
  have hne : Nat.card (commSub x) ≠ 1 := fun h => hW (AddSubgroup.card_eq_one.mp h)
  have hK : Nat.card ↥(commSub x ⊓ fixSub t) = 2 := by
    by_contra hK
    have : Nat.card ↥(commSub x ⊓ fixSub t) = 1 := by omega
    apply hne
    rw [hsq, this]; norm_num
  have hW4 : Nat.card (commSub x) = 4 := by rw [hsq, hK]; norm_num
  refine ⟨?_, hW4, hK⟩
  have hdvd := dvd_card_commSub_sub_one h2 hp hp2 hxp htx
  rw [hW4] at hdvd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd

theorem card_le_card_fix [Finite A] (h2 : ∀ a : A, a + a = 0) (hp2 : p % 2 = 1)
    (hxp : ∀ a, (⇑x)^[p] a = a) (htx : ∀ a, t (x a) = x.symm (t a)) (Z : AddSubgroup A)
    (hZt : ∀ a ∈ Z, t a = a) (hZx : ∀ a ∈ Z, x a = a → a = 0) :
    Nat.card Z ≤ Nat.card ↥(commSub x ⊓ fixSub t) := by
  have htxs : ∀ a, t (x.symm a) = x (t a) := fun a => by
    have h := htx (x.symm a)
    rw [AddEquiv.apply_symm_apply] at h
    rw [h, AddEquiv.apply_symm_apply]
  have hθ : ∀ a ∈ Z, x a - x.symm a ∈ commSub x ⊓ fixSub t := by
    intro a ha
    refine ⟨?_, ?_⟩
    ·
      have h1 : x a - x.symm a = (x a - a) + (x (x.symm a) - x.symm a) := by
        rw [AddEquiv.apply_symm_apply]; abel
      rw [h1]
      exact (commSub x).add_mem (x_sub_mem_commSub x a) (x_sub_mem_commSub x (x.symm a))
    · show t (x a - x.symm a) = x a - x.symm a
      rw [map_sub, htx, htxs, hZt a ha]
      have hc : (x a - x.symm a) + (x a - x.symm a) = 0 := h2 _
      have h4 : x.symm a - x a = -(x a - x.symm a) := by abel
      rw [h4]
      exact neg_eq_of_add_eq_zero_right hc
  let f : ↥Z → ↥(commSub x ⊓ fixSub t) := fun a => ⟨x (a : A) - x.symm (a : A), hθ a a.2⟩
  have hf : Function.Injective f := by
    intro a a' h
    have h1 : x (a : A) - x.symm (a : A) = x (a' : A) - x.symm (a' : A) := congrArg Subtype.val h
    have h2' : x ((a : A) - a') = x.symm ((a : A) - a') := by
      have := sub_symm_aux x (a : A) (a' : A)
      rw [h1, sub_self] at this
      exact sub_eq_zero.mp this
    have h3 : x (x ((a : A) - a')) = (a : A) - a' := by
      rw [h2', AddEquiv.apply_symm_apply]
    have h4 := fix_of_sq_fix hxp hp2 h3
    have h5 := hZx _ (Z.sub_mem a.2 a'.2) h4
    exact Subtype.ext (sub_eq_zero.mp h5)
  exact Nat.card_le_card_of_injective f hf

end Main

end GaloisDescent

end CFSG.Quasithin.F112Crit
