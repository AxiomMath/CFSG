module

public import CFSG.Timmesfeld.Bridge.OddTranspSecondKind

public section

namespace CFSG.Timmesfeld.Bridge.OddTransp

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {D : Set G}

theorem odd_two_pow_iff {k : ℕ} : Odd (2 ^ k) ↔ k = 0 := by
  cases k with
  | zero => simp
  | succ k => simp [pow_succ, Nat.odd_mul]

theorem eq_of_inv_mul_mem_center (hS : Setup G D) {e e' : G} (he : e ∈ D) (he' : e' ∈ D)
    (h : e⁻¹ * e' ∈ Subgroup.center G) : e = e' := by
  by_contra hne
  have hz := Subgroup.mem_center_iff.mp h
  have hcomm : Commute e e' := by
    have e1 : e' = e * (e⁻¹ * e') := by group
    rw [e1]
    exact (Commute.refl e).mul_right (hz e)
  have hall : ∀ f ∈ D, Commute f e := by
    intro f hf
    have hfz : Commute f (e * e') := by
      rw [show e * e' = e⁻¹ * e' by rw [hS.oddT.inv_eq he]]
      exact hz f
    exact ((hS.oddT.commute_mul_iff he he' hf hne hcomm).mp hfz).1
  have hec : e ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.closure D := hS.gen ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact (hall x hx).eq
    | one => simp
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx => exact (Commute.inv_left (show Commute x e from hx)).eq
  obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj he he')
  apply hne
  rw [← hc, Subgroup.mem_center_iff.mp hec c, mul_inv_cancel_right]

section Local

variable (hD : IsOddTransp D) (hN : IsNormalSet D) {Q : Subgroup G} [hQn : Q.Normal]
  (hQ : IsPGroup 2 Q)
include hD hN hQ

omit hN in
theorem commute_of_mul_inv_mem {c d : G} (hc : c ∈ D) (hd : d ∈ D) (hcd : c * d⁻¹ ∈ Q) :
    Commute c d := by
  refine commute_of_inv_mul_mem_two hD hQ hc hd ?_
  have := hQn.conj_mem _ (Q.inv_mem hcd) c⁻¹
  simpa [mul_assoc] using this

theorem commute_conj_of_mem {a : G} (ha : a ∈ D) {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) :
    Commute (q * a * q⁻¹) (q' * a * q'⁻¹) := by
  refine commute_of_mul_inv_mem hD hQ (hN q a ha) (hN q' a ha) ?_
  have e : q * a * q⁻¹ * (q' * a * q'⁻¹)⁻¹ = q * (a * (q⁻¹ * q') * a⁻¹) * q'⁻¹ := by group
  rw [e]
  exact Q.mul_mem (Q.mul_mem hq (hQn.conj_mem _ (Q.mul_mem (Q.inv_mem hq) hq') a)) (Q.inv_mem hq')

theorem commute_of_mem_commutator {a f : G} (ha : a ∈ D) (hf : f ∈ D) (hfa : Commute f a) {y : G}
    (hy : y ∈ ⁅Q, Subgroup.zpowers a⁆) : Commute f y := by
  have hle : ⁅Q, Subgroup.zpowers a⁆ ≤ Subgroup.centralizer {f} := by
    rw [Subgroup.commutator_le]
    intro q hq t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases (mem_zpowers_of_mul_self (hD.mul_self_eq_one ha)).mp ht with rfl | rfl
    · simp
    ·
      have hP : IsPGroup 2 (Subgroup.closure ({t, f} : Set G) ⊔ Q : Subgroup G) := by
        refine IsPGroup.to_sup_of_normal_right ?_ hQ
        exact isPGroup_two_closure_pair (hD.mul_self_eq_one ha) (hD.mul_self_eq_one hf) (k := 1)
          (by rw [pow_one, ← (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one ha)
            (hD.mul_self_eq_one hf))]; exact hfa.symm)
      have htP : t ∈ (Subgroup.closure ({t, f} : Set G) ⊔ Q : Subgroup G) :=
        Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      have hfP : f ∈ (Subgroup.closure ({t, f} : Set G) ⊔ Q : Subgroup G) :=
        Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      have hqP : q ∈ (Subgroup.closure ({t, f} : Set G) ⊔ Q : Subgroup G) :=
        Subgroup.mem_sup_right hq
      have hc := hD.commute_of_isPGroup hP hf (hN q t ha) hfP
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hqP htP) (Subgroup.inv_mem _ hqP))
      rw [commutatorElement_def]
      exact (hc.mul_right hfa.inv_right).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem commute_of_mem_commutator_self {a : G} (ha : a ∈ D) {y y' : G}
    (hy : y ∈ ⁅Q, Subgroup.zpowers a⁆) (hy' : y' ∈ ⁅Q, Subgroup.zpowers a⁆) : Commute y y' := by
  rw [Subgroup.commutator_def] at hy hy'
  refine Asc72.commute_of_mem_closure ?_ hy hy'
  rintro _ ⟨q, hq, t, ht, rfl⟩ _ ⟨q', hq', t', ht', rfl⟩
  have ha2 := hD.mul_self_eq_one ha
  rcases (mem_zpowers_of_mul_self ha2).mp ht with h | h
  · rw [h, commutatorElement_one_right]
    exact Commute.one_left _
  rcases (mem_zpowers_of_mul_self ha2).mp ht' with h' | h'
  · rw [h', commutatorElement_one_right]
    exact Commute.one_right _
  rw [h, h']
  have h1 := commute_conj_of_mem hD hN hQ ha hq hq'
  have h2 : Commute (q * a * q⁻¹) a := by simpa using commute_conj_of_mem hD hN hQ ha hq Q.one_mem
  have h3 : Commute (q' * a * q'⁻¹) a := by
    simpa using commute_conj_of_mem hD hN hQ ha hq' Q.one_mem
  simp only [commutatorElement_def]
  exact (h1.mul_left h3.symm.inv_left).mul_right (h2.inv_right.mul_left (Commute.refl a⁻¹))

omit hD hN hQn in
theorem exists_orderOf_eq_two_pow {x : G} (hx : x ∈ Q) : ∃ k : ℕ, orderOf x = 2 ^ k := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  exact ⟨i, hi⟩

theorem commute_iff_of_mem {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : ¬ Commute a b) {y : G}
    (hy : y ∈ Q) : Commute y (a * b) ↔ Commute y a ∧ Commute y b := by
  constructor
  · intro hyab
    have ha2 := hD.mul_self_eq_one ha
    have hb2 := hD.mul_self_eq_one hb
    have hai : a⁻¹ = a := hD.inv_eq ha
    have hya : Commute y a := by
      have hyba : Commute y (b * a) := by
        have : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, hai, hD.inv_eq hb]
        rw [← this]
        exact hyab.inv_right
      have h1 : Commute (a * y * a) (a * b) := by
        show a * y * a * (a * b) = a * b * (a * y * a)
        calc a * y * a * (a * b) = a * y * (a * a) * b := by group
          _ = a * y * b * (a * a) := by rw [ha2, mul_one, mul_one]
          _ = a * (y * (b * a)) * a := by group
          _ = a * ((b * a) * y) * a := by rw [hyba.eq]
          _ = a * b * (a * y * a) := by group
      set u := y⁻¹ * (a * y * a) with hu
      have huQ : u ∈ Q := Q.mul_mem (Q.inv_mem hy) (by
        have := hQn.conj_mem y hy a
        rwa [hai] at this)
      have huab : Commute u (a * b) := hyab.inv_left.mul_left h1
      have hprod : y⁻¹ * a * y * b = u * (a * b) := by
        rw [hu]
        calc y⁻¹ * a * y * b = y⁻¹ * a * y * (a * a) * b := by rw [ha2, mul_one]
          _ = y⁻¹ * (a * y * a) * (a * b) := by group
      obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hQ huQ
      have hoddab : Odd (orderOf (a * b)) := hD.odd_of_not_commute ha hb hab
      have hab1 : orderOf (a * b) ≠ 1 := by
        intro h1
        rw [orderOf_eq_one_iff] at h1
        exact hab (hD.eq_of_mul_eq_one ha h1 ▸ Commute.refl a)
      have hcop : Nat.Coprime (orderOf u) (orderOf (a * b)) := by
        rw [hk]
        exact (Nat.coprime_two_left.mpr hoddab).pow_left k
      have hord : orderOf (y⁻¹ * a * y * b) = 2 ^ k * orderOf (a * b) := by
        rw [hprod, huab.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hk]
      have hk0 : k = 0 := by
        by_contra hk0
        have hD' : y⁻¹ * a * y ∈ D := by
          have := hN y⁻¹ a ha
          simpa using this
        have hpos := hoddab.pos
        rcases hD.2 _ hD' _ hb with h | h <;> rw [hord] at h
        · have hle := Nat.le_of_dvd (by norm_num) h
          have h2k : 2 ≤ 2 ^ k := Nat.le_self_pow hk0 2
          have : 3 ≤ orderOf (a * b) := by
            obtain ⟨m, hm⟩ := hoddab
            omega
          nlinarith
        · rw [Nat.odd_mul, odd_two_pow_iff] at h
          exact hk0 h.1
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      have : a * y * a = y := by
        rw [hu] at hk
        exact (eq_of_inv_mul_eq_one hk).symm
      show y * a = a * y
      calc y * a = a * y * a * a := by rw [this]
        _ = a * y := by rw [mul_assoc, ha2, mul_one]
    refine ⟨hya, ?_⟩
    have e : b = a * (a * b) := by rw [← mul_assoc, hD.mul_self_eq_one ha, one_mul]
    rw [e]
    exact hya.mul_right hyab
  · rintro ⟨h1, h2⟩
    exact h1.mul_right h2

theorem exists_conj_of_mul_inv_mem [Finite G] {a b c : G} (ha : a ∈ D) (hb : b ∈ D)
    (hab : ¬ Commute a b) (hc : c ∈ D) (hca : c * a⁻¹ ∈ Q) (hcb : ¬ Commute c b) :
    ∃ x ∈ ⁅Q, Subgroup.zpowers b⁆, x * a * x⁻¹ = c := by
  by_cases hac : a = c
  · exact ⟨1, Subgroup.one_mem _, by rw [hac]; group⟩
  have hcomm : Commute a c := (commute_of_mul_inv_mem hD hQ hc ha hca).symm
  have htri : IsTriangle D a b c := ⟨ha, hc, hb, hac, hcomm, hab, hcb⟩
  have hacQ : a * c ∈ Q := by
    have h1 := hQn.conj_mem _ hca a⁻¹
    have e : a⁻¹ * (c * a⁻¹) * a⁻¹⁻¹ = a * c := by
      calc a⁻¹ * (c * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * c * (a⁻¹ * a) := by group
        _ = a * c := by rw [inv_mul_cancel, mul_one, hD.inv_eq ha]
    rwa [e] at h1
  have hpow : ∀ x : G, x * x = 1 → ∃ k : ℕ, orderOf (a * c * x) = 2 ^ k := by
    intro x hx
    have hsq : (a * c * x) ^ 2 ∈ Q := by
      have e : (a * c * x) ^ 2 = a * c * (x * (a * c) * x⁻¹) := by
        rw [pow_two, inv_eq_of_mul_eq_one_right hx]
        group
      rw [e]
      exact Q.mul_mem hacQ (hQn.conj_mem _ hacQ x)
    obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hQ hsq
    have h1 : (a * c * x) ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul, ← hk, pow_orderOf_eq_one]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨i, hi⟩
  have hnot3 : ∀ x : G, x * x = 1 → ¬ IsThirdKind a x c := by
    rintro x hx ⟨n, hn, hn1, hord⟩
    obtain ⟨k, hk⟩ := hpow x hx
    have hdvd : n ∣ 2 ^ k := ⟨2, by rw [← hk, hord]; ring⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hi, odd_two_pow_iff] at hn
    have hi0 : i = 0 := hn
    rw [hi, hi0, pow_zero] at hn1
    exact lt_irrefl 1 hn1
  have h4 : orderOf (a * c * b) = 4 := by
    rcases htri.orderOf_cases hD hN with ⟨hodd, h1⟩ | h4 | h3
    · obtain ⟨k, hk⟩ := hpow b (hD.mul_self_eq_one hb)
      rw [hk, odd_two_pow_iff] at hodd
      rw [hk, hodd, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h4
    · exact absurd h3 (hnot3 b (hD.mul_self_eq_one hb))
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure {a, b} → IsTriangle D a x c →
      ¬ IsThirdKind a x c := fun x hx _ _ => hnot3 x (hD.mul_self_eq_one hx)
  obtain ⟨x, hx, hxe⟩ := (secondKind_structure hD hN htri h4 hno).conj
  refine ⟨x, ?_, hxe⟩
  have hQ'Q : conjClosure (Subgroup.closure ({a, b} : Set G)) (a * c) ≤ Q := by
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, -, rfl⟩
    exact hQn.conj_mem _ hacQ g
  exact Subgroup.commutator_mono_left hQ'Q hx

omit hN in
theorem commute_of_mul_inv_mem_of_commute {a c f : G} (ha : a ∈ D) (hc : c ∈ D) (hf : f ∈ D)
    (hca : c * a⁻¹ ∈ Q) (hfa : Commute f a) : Commute f c := by
  have hP : IsPGroup 2 (Subgroup.closure ({a, f} : Set G) ⊔ Q : Subgroup G) := by
    refine IsPGroup.to_sup_of_normal_right ?_ hQ
    exact isPGroup_two_closure_pair (hD.mul_self_eq_one ha) (hD.mul_self_eq_one hf) (k := 1)
      (by rw [pow_one, ← (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one ha)
        (hD.mul_self_eq_one hf))]; exact hfa.symm)
  have haP : a ∈ (Subgroup.closure ({a, f} : Set G) ⊔ Q : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hfP : f ∈ (Subgroup.closure ({a, f} : Set G) ⊔ Q : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hcP : c ∈ (Subgroup.closure ({a, f} : Set G) ⊔ Q : Subgroup G) := by
    have := Subgroup.mul_mem _ (Subgroup.mem_sup_right hca) haP
    simpa using this
  exact hD.commute_of_isPGroup hP hf hc hfP hcP

theorem conj_mul_conj_eq {a b x₁ x₂ : G} (ha : a ∈ D) (hx₁ : x₁ ∈ ⁅Q, Subgroup.zpowers b⁆)
    (hx₂ : x₂ ∈ ⁅Q, Subgroup.zpowers b⁆) :
    ⁅⁅x₂, a⁆⁻¹, x₁⁆ ∈ ⁅Q, Subgroup.zpowers a⁆ ⊓ ⁅Q, Subgroup.zpowers b⁆ ∧
      x₁ * x₂ * a * (x₁ * x₂)⁻¹ =
        ⁅⁅x₂, a⁆⁻¹, x₁⁆ * (a * (x₁ * a * x₁⁻¹) * (x₂ * a * x₂⁻¹)) := by
  have ha2 := hD.mul_self_eq_one ha
  have hQbQ : ⁅Q, Subgroup.zpowers b⁆ ≤ Q := Subgroup.commutator_le_left Q _
  have hQaQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := Subgroup.commutator_le_left Q _
  have hx₁Q : x₁ ∈ Q := hQbQ hx₁
  have hx₂Q : x₂ ∈ Q := hQbQ hx₂
  have hφ : ∀ x : G, x * a * x⁻¹ = ⁅x, a⁆ * a := fun x => by rw [commutatorElement_def]; group
  have hφQa : ∀ x ∈ Q, ⁅x, a⁆ ∈ ⁅Q, Subgroup.zpowers a⁆ := fun x hx =>
    Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers a)
  have hu : ⁅x₂, a⁆⁻¹ ∈ ⁅Q, Subgroup.zpowers a⁆ := Subgroup.inv_mem _ (hφQa x₂ hx₂Q)
  have hz : ⁅⁅x₂, a⁆⁻¹, x₁⁆ ∈ ⁅Q, Subgroup.zpowers a⁆ ⊓ ⁅Q, Subgroup.zpowers b⁆ := by
    constructor
    · have hn := Subgroup.normalizer_commutator_ge_left (H₁ := Q) (H₂ := Subgroup.zpowers a)
        hx₁Q
      have h1 := (Subgroup.mem_normalizer_iff.mp hn _).mp (Subgroup.inv_mem _ hu)
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact Subgroup.mul_mem _ hu (by simpa [mul_assoc] using h1)
    · have hn := Subgroup.normalizer_commutator_ge_left (H₁ := Q) (H₂ := Subgroup.zpowers b)
        (hQaQ hu)
      have h1 := (Subgroup.mem_normalizer_iff.mp hn _).mp hx₁
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hx₁)
  refine ⟨hz, ?_⟩
  have hacd : a * (x₁ * a * x₁⁻¹) * (x₂ * a * x₂⁻¹) = ⁅x₁, a⁆ * ⁅x₂, a⁆ * a := by
    rw [hφ x₁, hφ x₂]
    have hcomm1 : Commute a ⁅x₁, a⁆ :=
      commute_of_mem_commutator hD hN hQ ha ha (Commute.refl a) (hφQa x₁ hx₁Q)
    calc a * (⁅x₁, a⁆ * a) * (⁅x₂, a⁆ * a) = a * ⁅x₁, a⁆ * a * ⁅x₂, a⁆ * a := by group
      _ = ⁅x₁, a⁆ * ⁅x₂, a⁆ * a := by rw [hcomm1.eq, mul_assoc ⁅x₁, a⁆, ha2, mul_one]
  rw [hacd, hφ (x₁ * x₂), commutatorElement_mul_left_eq_conj_mul]
  have e1 : x₁ * ⁅x₂, a⁆ * x₁⁻¹ = ⁅x₂, a⁆ * ⁅⁅x₂, a⁆⁻¹, x₁⁆ := by
    rw [commutatorElement_def ⁅x₂, a⁆⁻¹ x₁]
    group
  have hφφ : Commute ⁅x₂, a⁆ ⁅x₁, a⁆ :=
    commute_of_mem_commutator_self hD hN hQ ha (hφQa x₂ hx₂Q) (hφQa x₁ hx₁Q)
  have hzφ : Commute ⁅x₂, a⁆ ⁅⁅x₂, a⁆⁻¹, x₁⁆ :=
    commute_of_mem_commutator_self hD hN hQ ha (hφQa x₂ hx₂Q) hz.1
  rw [e1]
  calc ⁅x₂, a⁆ * ⁅⁅x₂, a⁆⁻¹, x₁⁆ * ⁅x₁, a⁆ * a =
      ⁅⁅x₂, a⁆⁻¹, x₁⁆ * ⁅x₂, a⁆ * ⁅x₁, a⁆ * a := by rw [hzφ.eq]
    _ = ⁅⁅x₂, a⁆⁻¹, x₁⁆ * (⁅x₁, a⁆ * ⁅x₂, a⁆ * a) := by
      rw [mul_assoc ⁅⁅x₂, a⁆⁻¹, x₁⁆ ⁅x₂, a⁆, hφφ.eq]
      group

theorem localQ_three [Finite G] (hS : Setup G D) {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (hab : ¬ Commute a b) (hgen : Subgroup.closure (insert b {f | f ∈ D ∧ Commute f a}) = ⊤) :
    ⁅Q, Subgroup.zpowers a⁆ ⊓ ⁅Q, Subgroup.zpowers b⁆ ≤ Subgroup.center G ∧
      (∀ y ∈ Q, ∃ y₁ ∈ Q, Commute y₁ a ∧ ∃ y₂ ∈ ⁅Q, Subgroup.zpowers b⁆, y = y₁ * y₂) ∧
      ∀ c ∈ D, c * a⁻¹ ∈ Q → ∀ d ∈ D, d * a⁻¹ ∈ Q →
        ∃! e, e ∈ D ∧ (a * c * d)⁻¹ * e ∈ Subgroup.center G := by
  have ha2 := hD.mul_self_eq_one ha
  have hQbQ : ⁅Q, Subgroup.zpowers b⁆ ≤ Q := Subgroup.commutator_le_left Q _
  have hQaQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := Subgroup.commutator_le_left Q _
  have hcent : ∀ y : G, Commute b y → (∀ f ∈ D, Commute f a → Commute f y) →
      y ∈ Subgroup.center G := by
    intro y hby hfy
    have hle : Subgroup.closure (insert b {f | f ∈ D ∧ Commute f a}) ≤
        Subgroup.centralizer {y} := by
      rw [Subgroup.closure_le]
      rintro t (rfl | ⟨hf, hfa⟩)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hby
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hfy t hf hfa)
    rw [hgen] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  have hcenter : ⁅Q, Subgroup.zpowers a⁆ ⊓ ⁅Q, Subgroup.zpowers b⁆ ≤ Subgroup.center G :=
    fun y ⟨hya, hyb⟩ => hcent y (commute_of_mem_commutator hD hN hQ hb hb (Commute.refl b) hyb)
      (fun f hf hfa => commute_of_mem_commutator hD hN hQ ha hf hfa hya)
  have hncomm : ∀ c ∈ D, c * a⁻¹ ∈ Q → ¬ Commute c b := by
    intro c hc hca hcb
    have hcz : c ∈ Subgroup.center G := hcent c hcb.symm
      (fun f hf hfa => commute_of_mul_inv_mem_of_commute hD hQ ha hc hf hca hfa)
    obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj hc ha)
    rw [Subgroup.mem_center_iff.mp hcz g, mul_inv_cancel_right] at hg
    exact hab (hg ▸ hcb)
  refine ⟨hcenter, ?_, ?_⟩
  ·
    intro y hy
    have hc : y * a * y⁻¹ ∈ D := hN y a ha
    have hca : y * a * y⁻¹ * a⁻¹ ∈ Q := by
      have h1 := hQn.conj_mem _ (Q.inv_mem hy) a
      have e : y * a * y⁻¹ * a⁻¹ = y * (a * y⁻¹ * a⁻¹) := by group
      rw [e]
      exact Q.mul_mem hy h1
    obtain ⟨x, hx, hxe⟩ := exists_conj_of_mul_inv_mem hD hN hQ ha hb hab hc hca
      (hncomm _ hc hca)
    have hxQ : x ∈ Q := hQbQ hx
    refine ⟨x⁻¹ * y, Q.mul_mem (Q.inv_mem hxQ) hy, ?_, y⁻¹ * x * y, ?_, by group⟩
    · show x⁻¹ * y * a = a * (x⁻¹ * y)
      have h1 : x⁻¹ * (y * a * y⁻¹) * x = a := by rw [← hxe]; group
      calc x⁻¹ * y * a = x⁻¹ * (y * a * y⁻¹) * x * (x⁻¹ * y) := by group
        _ = a * (x⁻¹ * y) := by rw [h1]
    · have hnorm := Subgroup.normalizer_commutator_ge_left (H₁ := Q) (H₂ := Subgroup.zpowers b)
        (Q.inv_mem hy)
      have h1 := (Subgroup.mem_normalizer_iff.mp hnorm x).mp hx
      simpa using h1
  ·
    intro c hc hca d hd hda
    obtain ⟨x₁, hx₁, rfl⟩ := exists_conj_of_mul_inv_mem hD hN hQ ha hb hab hc hca
      (hncomm c hc hca)
    obtain ⟨x₂, hx₂, rfl⟩ := exists_conj_of_mul_inv_mem hD hN hQ ha hb hab hd hda
      (hncomm d hd hda)
    obtain ⟨hz, he_eq⟩ := conj_mul_conj_eq hD hN hQ ha hx₁ hx₂
    have hzc := hcenter hz
    have hzφ := Subgroup.mem_center_iff.mp hzc
    refine ⟨x₁ * x₂ * a * (x₁ * x₂)⁻¹, ⟨hN _ a ha, ?_⟩, ?_⟩
    · rw [he_eq, ← hzφ, inv_mul_cancel_left]
      exact hzc
    · rintro e' ⟨he'D, he'⟩
      have h1 : (a * (x₁ * a * x₁⁻¹) * (x₂ * a * x₂⁻¹))⁻¹ * (x₁ * x₂ * a * (x₁ * x₂)⁻¹) ∈
          Subgroup.center G := by
        rw [he_eq, ← hzφ, inv_mul_cancel_left]
        exact hzc
      refine (eq_of_inv_mul_mem_center hS (hN _ a ha) he'D ?_).symm
      have h2 := (Subgroup.center G).mul_mem ((Subgroup.center G).inv_mem h1) he'
      simpa [mul_assoc] using h2

end Local

end CFSG.Timmesfeld.Bridge.OddTransp
