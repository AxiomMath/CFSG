module

public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.SubgroupLists

open scoped commutatorElement

variable {R : Type*} [Group R]

section ClassTwo

variable (hclass : commutator R ≤ Subgroup.center R)
include hclass

theorem commutatorElement_mem_center (a b : R) : ⁅a, b⁆ ∈ Subgroup.center R :=
  hclass (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))

theorem commutatorElement_mul_right (a b c : R) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hz := Subgroup.mem_center_iff.mp (commutatorElement_mem_center hclass a c)
  have key : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [key, hz b, mul_inv_cancel_right]

theorem commutatorElement_mul_left (a b c : R) : ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have hw := Subgroup.mem_center_iff.mp (commutatorElement_mem_center hclass b c)
  have key : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
    simp only [commutatorElement_def]
    group
  rw [key, hw a, mul_inv_cancel_right]
  exact (hw _).symm

theorem commutatorElement_pow_left (a c : R) (k : ℕ) : ⁅a ^ k, c⁆ = ⁅a, c⁆ ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, commutatorElement_mul_left hclass, ih, pow_succ]

theorem commutatorElement_pow_right (a c : R) (k : ℕ) : ⁅a, c ^ k⁆ = ⁅a, c⁆ ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, commutatorElement_mul_right hclass, ih, pow_succ]

theorem mul_pow_eq_class_two (x y : R) (k : ℕ) :
    (x * y) ^ k = x ^ k * y ^ k * ⁅y, x⁆ ^ (∑ i ∈ Finset.range k, i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    set c := ⁅y, x⁆ with hcdef
    have hcen : ∀ m : ℕ, ∀ g : R, g * c ^ m = c ^ m * g := fun m =>
      Subgroup.mem_center_iff.mp
        (Subgroup.pow_mem _ (commutatorElement_mem_center hclass y x) m)
    have hyx : y ^ k * x = c ^ k * (x * y ^ k) := by
      rw [hcdef, ← commutatorElement_pow_left hclass, commutatorElement_def]
      group
    rw [pow_succ (x * y), ih, Finset.sum_range_succ, pow_add c]
    set T := ∑ i ∈ Finset.range k, i
    calc x ^ k * y ^ k * c ^ T * (x * y) = x ^ k * (y ^ k * x) * y * c ^ T := by
          rw [mul_assoc (x ^ k * y ^ k), ← hcen T (x * y)]
          group
      _ = x ^ k * (c ^ k * (x * y ^ k)) * y * c ^ T := by rw [hyx]
      _ = (x ^ k * c ^ k) * x * y ^ k * y * c ^ T := by group
      _ = (c ^ k * x ^ k) * x * y ^ k * y * c ^ T := by rw [hcen k (x ^ k)]
      _ = c ^ k * (x ^ (k + 1) * y ^ (k + 1) * c ^ T) := by group
      _ = x ^ (k + 1) * y ^ (k + 1) * c ^ T * c ^ k := by rw [← hcen k]
      _ = x ^ (k + 1) * y ^ (k + 1) * (c ^ T * c ^ k) := by rw [mul_assoc]

end ClassTwo

section Core

variable [Finite R] {n : ℕ} [hn : Fact n.Prime]

omit [Finite R] in
theorem mul_pow_prime_eq (hn2 : n ≠ 2) (hclass : commutator R ≤ Subgroup.center R)
    (hpow : ∀ x : R, x ^ n ∈ Subgroup.center R) (x y : R) : (x * y) ^ n = x ^ n * y ^ n := by
  rw [mul_pow_eq_class_two hclass, Finset.sum_range_id]
  have hodd : Odd n := hn.out.odd_of_ne_two hn2
  obtain ⟨m, hm⟩ := hodd
  have hsum : n * (n - 1) / 2 = n * m := by
    rw [hm]
    have : (2 * m + 1) * (2 * m + 1 - 1) = 2 * ((2 * m + 1) * m) := by
      rw [Nat.add_sub_cancel]
      ring
    rw [this, Nat.mul_div_cancel_left _ two_pos]
  have hc : ⁅y, x⁆ ^ n = 1 := by
    rw [← commutatorElement_pow_left hclass, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hpow y) x |>.symm
  rw [hsum, pow_mul, hc, one_pow, mul_one]

omit [Finite R] in
@[expose] noncomputable def powHom (hn2 : n ≠ 2) (hclass : commutator R ≤ Subgroup.center R)
    (hpow : ∀ x : R, x ^ n ∈ Subgroup.center R) : R →* R where
  toFun x := x ^ n
  map_one' := one_pow n
  map_mul' := mul_pow_prime_eq hn2 hclass hpow

theorem card_le_of_pow_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (hC : ∀ c : C, c ^ n = 1) : Nat.card C ≤ n := by
  have := Fintype.ofFinite C
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hn.out.pos (Monoid.exponent_dvd_of_forall_pow_eq_one hC)

omit [Finite R] in
theorem card_eq_card_map_mul_card_inf_ker {G : Type*} [Group G] (φ : R →* G) (H : Subgroup R) :
    Nat.card H = Nat.card (H.map φ) * Nat.card (H ⊓ φ.ker : Subgroup R) := by
  let ψ : H →* G := φ.comp H.subtype
  have hrange : ψ.range = H.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ψ.ker = Nat.card (H ⊓ φ.ker : Subgroup R) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : H) : R), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker]

theorem exists_extraspecial_omega (hn2 : n ≠ 2) (hR : IsPGroup n R)
    (hnc : ¬ IsMulCommutative R) (B : Subgroup R) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    [hBn : B.Normal] (hBi : B.index = n) (hBcent : ∀ x : R, (∀ b ∈ B, x * b = b * x) → x ∈ B)
    (hclass : commutator R ≤ Subgroup.center R) (hZ : IsCyclic (Subgroup.center R))
    (hΩ : ∀ H : Subgroup R, (∀ x, x ∈ H ↔ x ^ n = 1) → (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) →
      IsCyclic H) :
    ∃ H : Subgroup R, (∀ x, x ∈ H ↔ x ^ n = 1) ∧ Nat.card H = n ^ 3 ∧
      IsExtraspecialPGroup n H := by
  classical
  have hn1 : 1 < n := hn.out.one_lt
  set Z := Subgroup.center R with hZdef
  have hZB : Z ≤ B := fun z hz => hBcent z fun b _ => Subgroup.mem_center_iff.mp hz b |>.symm
  have hBtop : B ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hBi
    omega
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ B := by
    by_contra h
    push Not at h
    exact hBtop (eq_top_iff.mpr fun x _ => h x)
  have hsup : B ⊔ Subgroup.zpowers x₀ = ⊤ := by
    have hdvd : (B ⊔ Subgroup.zpowers x₀).index ∣ n :=
      hBi ▸ Subgroup.index_dvd_of_le le_sup_left
    rcases (Nat.dvd_prime hn.out).mp hdvd with h1 | hn'
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have h := Subgroup.relIndex_mul_index (le_sup_left : B ≤ B ⊔ Subgroup.zpowers x₀)
      rw [hn', hBi] at h
      have h1 : B.relIndex (B ⊔ Subgroup.zpowers x₀) = 1 := by
        have := Nat.eq_of_mul_eq_mul_right hn.out.pos (h.trans (one_mul n).symm)
        exact this
      have hle := Subgroup.relIndex_eq_one.mp h1
      exact hx₀ (hle (le_sup_right (a := B) (Subgroup.mem_zpowers x₀)))
  have hcentral : ∀ b ∈ B, x₀ * b = b * x₀ → b ∈ Z := by
    intro b hb hbx
    have hle : B ⊔ Subgroup.zpowers x₀ ≤ Subgroup.centralizer {b} := by
      refine sup_le (fun a ha => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hBc b hb a ha).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hbx
    rw [hsup] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    have := hle (Subgroup.mem_top g)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hx₀n : x₀ ^ n ∈ B := hBi ▸ Subgroup.pow_index_mem B x₀
  let f : B →* Z :=
    { toFun := fun b => ⟨⁅x₀, (b : R)⁆, commutatorElement_mem_center hclass _ _⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact commutatorElement_mul_right hclass _ _ _) }
  have hfker : ∀ b : B, f b = 1 ↔ (b : R) ∈ Z := by
    intro b
    constructor
    · intro h
      have h' : ⁅x₀, (b : R)⁆ = 1 := congrArg Subtype.val h
      rw [commutatorElement_eq_one_iff_mul_comm] at h'
      exact hcentral b b.2 h'
    · intro h
      apply Subtype.ext
      show ⁅x₀, (b : R)⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp h x₀)
  have hfpow : ∀ b : B, f b ^ n = 1 := by
    intro b
    apply Subtype.ext
    show ⁅x₀, (b : R)⁆ ^ n = 1
    rw [← commutatorElement_pow_left hclass, commutatorElement_eq_one_iff_mul_comm]
    exact hBc _ hx₀n _ b.2
  have hrange : Nat.card f.range ≤ n := by
    have : IsCyclic f.range := Subgroup.isCyclic _
    refine card_le_of_pow_eq_one_of_isCyclic fun c => ?_
    obtain ⟨_, b, rfl⟩ := c
    exact Subtype.ext (hfpow b)
  have hkerf : f.ker = Z.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, hfker, Subgroup.mem_subgroupOf]
  have hBZ : Nat.card B = Nat.card f.range * Nat.card (Z.subgroupOf B) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hkerf]
  have hrel : Z.relIndex B = n := by
    have hidx := Subgroup.card_mul_index (Z.subgroupOf B)
    rw [hBZ] at hidx
    have hpos : 0 < Nat.card (Z.subgroupOf B) := Nat.card_pos
    have hrel' : Z.relIndex B = Nat.card f.range := by
      rw [Subgroup.relIndex]
      nlinarith [hidx]
    rw [hrel']
    have hfp : IsPGroup n f.range := by
      rintro ⟨_, b, rfl⟩
      obtain ⟨k, hk⟩ := hR.to_subgroup B b
      exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_pow, ← map_pow, hk, map_one,
        OneMemClass.coe_one])⟩
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hfp
    have hj1 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      apply hBtop
      have hall : ∀ b : B, f b = 1 := fun b => by
        have hsub : Subsingleton f.range := (Nat.card_eq_one_iff_unique.mp hj).1
        exact congrArg Subtype.val (Subsingleton.elim (⟨f b, b, rfl⟩ : f.range) 1)
      refine eq_top_iff.mpr fun x _ => hBcent x fun b hb => ?_
      exact Subgroup.mem_center_iff.mp ((hfker ⟨b, hb⟩).mp (hall ⟨b, hb⟩)) x
    have hjn : n ^ j ≤ n := hj ▸ hrange
    have : j = 1 := by
      rcases Nat.lt_or_ge j 2 with h | h
      · omega
      · exfalso
        have := Nat.pow_le_pow_right hn.out.pos h
        nlinarith
    rw [hj, this, pow_one]
  have hZidx : Z.index = n * n := by
    rw [← Subgroup.relIndex_mul_index hZB, hrel, hBi]
  have hQcard : Nat.card (R ⧸ Z) = n ^ 2 := by
    rw [← Subgroup.index_eq_card, hZidx, sq]
  have hQnc : ¬ IsCyclic (R ⧸ Z) := by
    intro hcyc
    exact hnc ((QuotientGroup.mk' Z).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk']))
  have hpow : ∀ x : R, x ^ n ∈ Z := by
    intro x
    have hdvd : orderOf (x : R ⧸ Z) ∣ n ^ 2 := hQcard ▸ orderOf_dvd_natCard _
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hn.out).mp hdvd
    have hi1 : i ≤ 1 := by
      by_contra h
      have hi2 : i = 2 := by omega
      exact hQnc (isCyclic_of_orderOf_eq_card (x : R ⧸ Z) (by rw [hio, hi2, hQcard]))
    have : (x : R ⧸ Z) ^ n = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hio]
      exact Nat.pow_dvd_of_le_of_pow_dvd hi1 (dvd_refl _) |>.trans (by rw [pow_one])
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
  let P := powHom hn2 hclass hpow
  have hP : ∀ x, P x = x ^ n := fun _ => rfl
  set H := P.ker with hHdef
  have hHmem : ∀ x, x ∈ H ↔ x ^ n = 1 := fun x => by rw [MonoidHom.mem_ker, hP]
  have hRcard : Nat.card R = n ^ 2 * Nat.card Z := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hQcard]
  have hRPcard : Nat.card R = Nat.card P.range * Nat.card H := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange P).toEquiv]
  have hPZ : Nat.card P.range ≤ Nat.card Z := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, rfl⟩
    exact hpow x
  have : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hnc ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have hHZcard : Nat.card (H ⊓ Z : Subgroup R) = n := by
    apply le_antisymm
    · have hle : H ⊓ Z ≤ Z := inf_le_right
      have e := Subgroup.subgroupOfEquivOfLe hle
      have : IsCyclic ((H ⊓ Z).subgroupOf Z) := Subgroup.isCyclic _
      have : IsCyclic (H ⊓ Z : Subgroup R) := isCyclic_of_surjective e.toMonoidHom e.surjective
      exact card_le_of_pow_eq_one_of_isCyclic fun w =>
        Subtype.ext (by rw [SubgroupClass.coe_pow, (hHmem _).mp w.2.1, OneMemClass.coe_one])
    · have hZnt : Nontrivial Z := hR.center_nontrivial
      have hZp : IsPGroup n Z := hR.to_subgroup Z
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hk
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) n
        (by rw [hk]; exact dvd_pow_self n hk0)
      have hzH : (z : R) ∈ H ⊓ Z := ⟨(hHmem _).mpr (by
        rw [← SubgroupClass.coe_pow, ← hz, pow_orderOf_eq_one, OneMemClass.coe_one]), z.2⟩
      have hzo : orderOf (⟨z, hzH⟩ : (H ⊓ Z : Subgroup R)) = n := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hz]
      calc n = orderOf (⟨z, hzH⟩ : (H ⊓ Z : Subgroup R)) := hzo.symm
        _ ≤ Nat.card (H ⊓ Z : Subgroup R) := orderOf_le_card
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hHq : H.map (QuotientGroup.mk' Z) = ⊤ := by
    by_contra hne
    have hcardHq : Nat.card (H.map (QuotientGroup.mk' Z)) ∣ n ^ 2 :=
      hQcard ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hn.out).mp hcardHq
    have hi1 : i ≤ 1 := by
      by_contra h
      have hi2 : i = 2 := by omega
      apply hne
      rw [← Subgroup.card_eq_iff_eq_top, hio, hi2, hQcard]
    have hcyc : IsCyclic (H.map (QuotientGroup.mk' Z)) := by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [pow_zero] at hio
        have : Subsingleton (H.map (QuotientGroup.mk' Z)) :=
          (Nat.card_eq_one_iff_unique.mp hio).1
        exact isCyclic_of_subsingleton
      · rw [pow_one] at hio
        exact isCyclic_of_prime_card hio
    have hHab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
      have hcomm :=
        ((QuotientGroup.mk' Z).subgroupMap H).isMulCommutative_of_isCyclic_of_ker_le_center
        (by
          intro x hx
          have hxZ : (x : R) ∈ Z := by
            have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
            simpa [QuotientGroup.eq_one_iff] using this
          rw [Subgroup.mem_center_iff]
          intro y
          exact Subtype.ext (Subgroup.mem_center_iff.mp hxZ y))
      intro a ha b hb
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hHcyc := hΩ H hHmem hHab
    have hHle : Nat.card H ≤ n := card_le_of_pow_eq_one_of_isCyclic fun h =>
      Subtype.ext (by rw [SubgroupClass.coe_pow, (hHmem _).mp h.2, OneMemClass.coe_one])
    have hle : n ^ 2 * Nat.card Z ≤ n * Nat.card Z := by
      rw [← hRcard, hRPcard, mul_comm n]
      exact Nat.mul_le_mul hPZ hHle
    have hle' : n * n ≤ n * 1 := by
      have := Nat.le_of_mul_le_mul_right hle hZpos
      rw [sq] at this
      omega
    have := Nat.le_of_mul_le_mul_left hle' hn.out.pos
    omega
  have hHcard : Nat.card H = n ^ 3 := by
    rw [card_eq_card_map_mul_card_inf_ker (QuotientGroup.mk' Z) H, hHq, Subgroup.card_top,
      QuotientGroup.ker_mk', hHZcard, hQcard]
    ring
  have hHnc : ¬ IsMulCommutative H := by
    intro hHc
    apply hnc
    have hdecomp : ∀ a : R, ∃ h ∈ H, h⁻¹ * a ∈ Z := by
      intro a
      have : (a : R ⧸ Z) ∈ H.map (QuotientGroup.mk' Z) := hHq ▸ Subgroup.mem_top _
      obtain ⟨h, hh, hha⟩ := this
      exact ⟨h, hh, QuotientGroup.eq.mp hha⟩
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨h₁, hh₁, hz₁⟩ := hdecomp a
    obtain ⟨h₂, hh₂, hz₂⟩ := hdecomp b
    have hc := hHc.is_comm.comm ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩
    have hc' : h₁ * h₂ = h₂ * h₁ := congrArg Subtype.val hc
    have ha : a = h₁ * (h₁⁻¹ * a) := by group
    have hb : b = h₂ * (h₂⁻¹ * b) := by group
    set z₁ := h₁⁻¹ * a
    set z₂ := h₂⁻¹ * b
    have e1 := Subgroup.mem_center_iff.mp hz₁
    have e2 := Subgroup.mem_center_iff.mp hz₂
    rw [ha, hb]
    calc h₁ * z₁ * (h₂ * z₂) = h₁ * (z₁ * h₂) * z₂ := by group
      _ = h₁ * (h₂ * z₁) * z₂ := by rw [e1 h₂]
      _ = (h₁ * h₂) * (z₁ * z₂) := by group
      _ = (h₂ * h₁) * (z₂ * z₁) := by rw [hc', e2 z₁]
      _ = h₂ * (h₁ * z₂) * z₁ := by group
      _ = h₂ * (z₂ * h₁) * z₁ := by rw [e2 h₁]
      _ = h₂ * z₂ * (h₁ * z₁) := by group
  refine ⟨H, hHmem, hHcard, ?_⟩
  exact CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three (hR.to_subgroup H)
    (fun x => Subtype.ext (by rw [SubgroupClass.coe_pow, (hHmem _).mp x.2, OneMemClass.coe_one]))
    hHcard hHnc

end Core

end CFSG.RankThree.SubgroupLists
