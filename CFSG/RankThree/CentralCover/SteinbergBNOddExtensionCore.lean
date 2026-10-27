module

public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.CentralCover

open scoped commutatorElement

section CentralCommutators

variable {P : Type*} [Group P] {A : Subgroup P}

theorem mul_comm_of_mem_le_center (hA : A ≤ Subgroup.center P) {a : P} (ha : a ∈ A) (g : P) :
    a * g = g * a :=
  (Subgroup.mem_center_iff.1 (hA ha) g).symm

theorem commutatorElement_mul_central_left (hA : A ≤ Subgroup.center P) {a : P} (ha : a ∈ A)
    (x y : P) : ⁅x * a, y⁆ = ⁅x, y⁆ := by
  have h1 := mul_comm_of_mem_le_center hA ha
  calc ⁅x * a, y⁆ = x * (a * y) * a⁻¹ * x⁻¹ * y⁻¹ := by simp only [commutatorElement_def]; group
    _ = x * (y * a) * a⁻¹ * x⁻¹ * y⁻¹ := by rw [h1 y]
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

theorem commutatorElement_mul_central_right (hA : A ≤ Subgroup.center P) {c : P} (hc : c ∈ A)
    (x y : P) : ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have h1 := mul_comm_of_mem_le_center hA hc
  calc ⁅x, y * c⁆ = x * y * (c * x⁻¹) * c⁻¹ * y⁻¹ := by simp only [commutatorElement_def]; group
    _ = x * y * (x⁻¹ * c) * c⁻¹ * y⁻¹ := by rw [h1 x⁻¹]
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

variable (hA : A ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A)
include hA hcomm

theorem commutatorElement_mul_left_of_central (x y z : P) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hc := mul_comm_of_mem_le_center hA (hcomm y z)
  calc ⁅x * y, z⁆ = x * ⁅y, z⁆ * (z * x⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
    _ = ⁅y, z⁆ * x * (z * x⁻¹ * z⁻¹) := by rw [hc x]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅x, z⁆ * ⁅y, z⁆ := hc _

theorem commutatorElement_mul_right_of_central (x y z : P) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hc := mul_comm_of_mem_le_center hA (hcomm x z)
  calc ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ * (⁅x, z⁆ * y * y⁻¹) := by rw [hc y]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by group

omit hcomm in
theorem commutatorElement_central_left' {a : P} (ha : a ∈ A) (y : P) : ⁅a, y⁆ = 1 := by
  rw [← one_mul a, commutatorElement_mul_central_left hA ha, commutatorElement_one_left]

@[expose] def commRightHom (x : P) : P →* P where
  toFun y := ⁅x, y⁆
  map_one' := commutatorElement_one_right x
  map_mul' y z := commutatorElement_mul_right_of_central hA hcomm x y z

@[expose] def commLeftHom (y : P) : P →* P where
  toFun x := ⁅x, y⁆
  map_one' := commutatorElement_one_left y
  map_mul' x z := commutatorElement_mul_left_of_central hA hcomm x z y

theorem commRightHom_apply (x y : P) : commRightHom hA hcomm x y = ⁅x, y⁆ := rfl

theorem commLeftHom_apply (x y : P) : commLeftHom hA hcomm y x = ⁅x, y⁆ := rfl

theorem mul_pow_of_central (x y : P) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ n.choose 2 := by
  have hcen : ∀ k : ℕ, ∀ g : P, ⁅y, x⁆ ^ k * g = g * ⁅y, x⁆ ^ k := fun k g =>
    (Commute.pow_left (show Commute ⁅y, x⁆ g from
      mul_comm_of_mem_le_center hA (hcomm y x) g) k).eq
  have hyx : ∀ k : ℕ, y ^ k * x = ⁅y, x⁆ ^ k * x * y ^ k := fun k => by
    have h : ⁅y ^ k, x⁆ = ⁅y, x⁆ ^ k := map_pow (commLeftHom hA hcomm x) y k
    rw [← h, commutatorElement_def]
    group
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    calc x ^ n * y ^ n * ⁅y, x⁆ ^ n.choose 2 * (x * y)
        = x ^ n * (y ^ n * x) * y * ⁅y, x⁆ ^ n.choose 2 := by
          rw [mul_assoc (x ^ n * y ^ n), hcen (n.choose 2) (x * y)]
          group
      _ = x ^ n * (⁅y, x⁆ ^ n * x * y ^ n) * y * ⁅y, x⁆ ^ n.choose 2 := by rw [hyx n]
      _ = x ^ n * ⁅y, x⁆ ^ n * (x * y ^ n * y) * ⁅y, x⁆ ^ n.choose 2 := by group
      _ = ⁅y, x⁆ ^ n * x ^ n * (x * y ^ n * y) * ⁅y, x⁆ ^ n.choose 2 := by rw [hcen n (x ^ n)]
      _ = ⁅y, x⁆ ^ n * (x ^ n * x * y ^ n * y) * ⁅y, x⁆ ^ n.choose 2 := by group
      _ = x ^ (n + 1) * y ^ (n + 1) * ⁅y, x⁆ ^ (n + 1).choose 2 := by
          rw [CFSG.RankThree.choose_two_succ, pow_add ⁅y, x⁆ n (n.choose 2), hcen n]
          simp only [pow_succ]
          group

variable {p : ℕ} (hpow : ∀ x : P, x ^ p ∈ A)
include hpow

theorem commutatorElement_pow_eq_one (x y : P) : ⁅x, y⁆ ^ p = 1 := by
  have h : ⁅x ^ p, y⁆ = ⁅x, y⁆ ^ p := map_pow (commLeftHom hA hcomm y) x p
  rw [← h]
  exact commutatorElement_central_left' hA (hpow x) y

theorem mul_pow_prime_of_central (hp : p.Prime) (hp2 : p ≠ 2) (x y : P) :
    (x * y) ^ p = x ^ p * y ^ p := by
  rw [mul_pow_of_central hA hcomm]
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (k := 2) (by norm_num)
    (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
  rw [hk, pow_mul, commutatorElement_pow_eq_one hA hcomm hpow, one_pow, mul_one]

@[expose] def centralPowHom (hp : p.Prime) (hp2 : p ≠ 2) : P →* P where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow_prime_of_central hA hcomm hpow hp hp2 x y

theorem centralPowHom_apply (hp : p.Prime) (hp2 : p ≠ 2) (x : P) :
    centralPowHom hA hcomm hpow hp hp2 x = x ^ p := rfl

end CentralCommutators

section AbelianPower

variable {P : Type*} [Group P] {A : Subgroup P} (hA : A ≤ Subgroup.center P)
include hA

theorem card_eq_card_pow_range_mul (p : ℕ) :
    Nat.card A = Nat.card (Set.range fun a : A => (a : P) ^ p) *
      Nat.card {a : P // a ∈ A ∧ a ^ p = 1} := by
  have hc : ∀ a b : A, a * b = b * a := fun a b =>
    Subtype.ext (mul_comm_of_mem_le_center hA a.2 b)
  let f : A →* A :=
    { toFun := fun a => a ^ p
      map_one' := one_pow p
      map_mul' := fun a b => (Commute.mul_pow (hc a b) p) }
  have h := Subgroup.card_ker_mul_card_range f
  have e1 : Nat.card f.ker = Nat.card {a : P // a ∈ A ∧ a ^ p = 1} :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, MonoidHom.mem_ker.2 (Subtype.ext a.2.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have e2 : Nat.card f.range = Nat.card (Set.range fun a : A => (a : P) ^ p) :=
    Nat.card_congr
      { toFun := fun y => ⟨y.1.1, by
          obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 y.2
          exact ⟨a, congrArg Subtype.val ha⟩⟩
        invFun := fun z => ⟨⟨z.1, by
          obtain ⟨a, ha⟩ := z.2
          rw [← ha]
          exact A.pow_mem a.2 p⟩, by
          obtain ⟨a, ha⟩ := z.2
          exact MonoidHom.mem_range.2 ⟨a, Subtype.ext ha⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← h, e1, e2, mul_comm]

end AbelianPower


theorem card_inf_ker_mul_card_map {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (H : Subgroup G) : Nat.card (H ⊓ f.ker : Subgroup G) * Nat.card (H.map f) = Nat.card H := by
  have h := Subgroup.card_ker_mul_card_range (f.domRestrict H)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range,
    ← Subgroup.inf_subgroupOf_left] at h
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ f.ker ≤ H)).toEquiv]
  exact h

section RankFormula

variable {P : Type*} [Group P] {A : Subgroup P} [A.Normal] {p : ℕ}

variable (A p) in
@[expose] def IsIsotropicPowKer (U : Subgroup (P ⧸ A)) : Prop :=
  (∀ x : P, (x : P ⧸ A) ∈ U → ∃ a ∈ A, x ^ p = a ^ p) ∧
    ∀ x y : P, (x : P ⧸ A) ∈ U → (y : P ⧸ A) ∈ U → ⁅x, y⁆ = 1

variable (hA : A ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A)
  (hpow : ∀ x : P, x ^ p ∈ A) (hp : p.Prime) (hp2 : p ≠ 2)
include hA hcomm hpow hp hp2

theorem exists_lift_of_isIsotropicPowKer {U : Subgroup (P ⧸ A)} (hU : IsIsotropicPowKer A p U) :
    ∃ E : Subgroup P, IsElementaryAbelian p E ∧ (∀ x : P, x ∈ E ∧ x ∈ A ↔ x ∈ A ∧ x ^ p = 1) ∧
      E.map (QuotientGroup.mk' A) = U ∧
      Nat.card E = Nat.card {a : P // a ∈ A ∧ a ^ p = 1} * Nat.card U := by
  set π := centralPowHom hA hcomm hpow hp hp2
  set E := U.comap (QuotientGroup.mk' A) ⊓ π.ker with hE
  have hEmem : ∀ x : P, x ∈ E ↔ (x : P ⧸ A) ∈ U ∧ x ^ p = 1 := fun x => by
    rw [hE, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker, QuotientGroup.mk'_apply,
      centralPowHom_apply]
  have hinter : ∀ x : P, x ∈ E ∧ x ∈ A ↔ x ∈ A ∧ x ^ p = 1 := fun x => by
    rw [hEmem]
    constructor
    · rintro ⟨⟨-, h⟩, hx⟩
      exact ⟨hx, h⟩
    · rintro ⟨hx, h⟩
      refine ⟨⟨?_, h⟩, hx⟩
      rw [(QuotientGroup.eq_one_iff x).2 hx]
      exact U.one_mem
  have hmap : E.map (QuotientGroup.mk' A) = U := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ((hEmem x).1 hx).1
    · intro hw
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      obtain ⟨a, ha, hxa⟩ := hU.1 x hw
      have hxa' : ((x * a⁻¹ : P) : P ⧸ A) = x := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a⁻¹).2 (inv_mem ha), mul_one]
      refine ⟨x * a⁻¹, (hEmem _).2 ⟨by rw [hxa']; exact hw, ?_⟩, hxa'⟩
      rw [mul_pow_prime_of_central hA hcomm hpow hp hp2, inv_pow, hxa, mul_inv_cancel]
  refine ⟨E, ?_, hinter, hmap, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext ?_⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
               Subtype.ext (by rw [Subgroup.coe_pow, ((hEmem x).1 x.2).2, Subgroup.coe_one]) }
    exact commutatorElement_eq_one_iff_mul_comm.1
      (hU.2 a b ((hEmem a).1 a.2).1 ((hEmem b).1 b.2).1)
  · have h := card_inf_ker_mul_card_map (QuotientGroup.mk' A) E
    rw [QuotientGroup.ker_mk', hmap] at h
    rw [← h]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [Subgroup.mem_inf]
      exact hinter x)

theorem exists_isIsotropicPowKer_of_isElementaryAbelian [Finite P] {E : Subgroup P}
    (hE : IsElementaryAbelian p E) :
    ∃ U : Subgroup (P ⧸ A), IsIsotropicPowKer A p U ∧
      Nat.card E ≤ Nat.card {a : P // a ∈ A ∧ a ^ p = 1} * Nat.card U := by
  set π := centralPowHom hA hcomm hpow hp hp2
  set Ω := A ⊓ π.ker with hΩ
  have hΩmem : ∀ x : P, x ∈ Ω ↔ x ∈ A ∧ x ^ p = 1 := fun x => by
    rw [hΩ, Subgroup.mem_inf, MonoidHom.mem_ker, centralPowHom_apply]
  have : Ω.Normal := ⟨fun n hn g => by
    rw [← mul_comm_of_mem_le_center hA ((hΩmem n).1 hn).1 g, mul_inv_cancel_right]
    exact hn⟩
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hEp : ∀ a ∈ E, a ^ p = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  set E' := E ⊔ Ω with hE'
  have hE'mem : ∀ x : P, x ∈ E' ↔ ∃ e ∈ E, ∃ ω ∈ Ω, e * ω = x := fun x =>
    Subgroup.mem_sup_of_normal_right
  have hE'c : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    obtain ⟨e₁, he₁, ω₁, hω₁, rfl⟩ := (hE'mem x).1 hx
    obtain ⟨e₂, he₂, ω₂, hω₂, rfl⟩ := (hE'mem y).1 hy
    have c1 := mul_comm_of_mem_le_center hA ((hΩmem ω₁).1 hω₁).1
    have c2 := mul_comm_of_mem_le_center hA ((hΩmem ω₂).1 hω₂).1
    calc e₁ * ω₁ * (e₂ * ω₂) = e₁ * e₂ * (ω₁ * ω₂) := by
          rw [show e₁ * ω₁ * (e₂ * ω₂) = e₁ * (ω₁ * e₂) * ω₂ by group, c1 e₂]; group
      _ = e₂ * e₁ * (ω₂ * ω₁) := by rw [hEc e₁ he₁ e₂ he₂, c1 ω₂]
      _ = e₂ * ω₂ * (e₁ * ω₁) := by
          rw [show e₂ * ω₂ * (e₁ * ω₁) = e₂ * (ω₂ * e₁) * ω₁ by group, c2 e₁]; group
  have hE'p : ∀ x ∈ E', x ^ p = 1 := by
    intro x hx
    obtain ⟨e, he, ω, hω, rfl⟩ := (hE'mem x).1 hx
    rw [mul_pow_prime_of_central hA hcomm hpow hp hp2, hEp e he, ((hΩmem ω).1 hω).2, mul_one]
  set U := E'.map (QuotientGroup.mk' A)
  have hlift : ∀ x : P, (x : P ⧸ A) ∈ U → ∃ y ∈ E', ∃ c ∈ A, x = y * c := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    exact ⟨y, hy, y⁻¹ * x, hyx, by rw [mul_inv_cancel_left]⟩
  refine ⟨U, ⟨fun x hx => ?_, fun x y hx hy => ?_⟩, ?_⟩
  · obtain ⟨y, hy, c, hc, rfl⟩ := hlift x hx
    exact ⟨c, hc, by rw [mul_pow_prime_of_central hA hcomm hpow hp hp2, hE'p y hy, one_mul]⟩
  · obtain ⟨x', hx', c, hc, rfl⟩ := hlift x hx
    obtain ⟨y', hy', c', hc', rfl⟩ := hlift y hy
    rw [commutatorElement_mul_central_left hA hc, commutatorElement_mul_central_right hA hc',
      commutatorElement_eq_one_iff_mul_comm]
    exact hE'c x' hx' y' hy'
  · have h := card_inf_ker_mul_card_map (QuotientGroup.mk' A) E'
    rw [QuotientGroup.ker_mk'] at h
    have h1 : Nat.card E ≤ Nat.card E' := Subgroup.card_le_of_le le_sup_left
    have h2 : Nat.card (E' ⊓ A : Subgroup P) ≤ Nat.card {a : P // a ∈ A ∧ a ^ p = 1} :=
      Nat.card_le_card_of_injective
        (fun x => ⟨x.1, (Subgroup.mem_inf.1 x.2).2, hE'p x.1 (Subgroup.mem_inf.1 x.2).1⟩)
        (fun x y hxy => Subtype.ext (Subtype.mk.inj hxy))
    calc Nat.card E ≤ Nat.card E' := h1
      _ = Nat.card (E' ⊓ A : Subgroup P) * Nat.card U := h.symm
      _ ≤ Nat.card {a : P // a ∈ A ∧ a ^ p = 1} * Nat.card U := Nat.mul_le_mul_right _ h2

theorem pRank_eq_add_of_isIsotropicPowKer [Finite P] (hP : IsPGroup p P) {d : ℕ}
    (hd : Nat.card {a : P // a ∈ A ∧ a ^ p = 1} = p ^ d) :
    ∃ r : ℕ, IsGreatest {k | ∃ U : Subgroup (P ⧸ A), IsIsotropicPowKer A p U ∧
      Nat.card U = p ^ k} r ∧ CFSG.pRank p P = d + r := by
  have : Fact p.Prime := ⟨hp⟩
  set S := {k | ∃ U : Subgroup (P ⧸ A), IsIsotropicPowKer A p U ∧ Nat.card U = p ^ k}
  have hS0 : 0 ∈ S := by
    refine ⟨⊥, ⟨fun x hx => ?_, fun x y hx hy => ?_⟩, by rw [Subgroup.card_bot, pow_zero]⟩
    · exact ⟨x, (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 hx), rfl⟩
    · exact commutatorElement_central_left' hA
        ((QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 hx)) y
  have hSb : BddAbove S := by
    refine ⟨Nat.card (P ⧸ A), fun k hk => ?_⟩
    obtain ⟨U, -, hU⟩ := hk
    have h1 := Subgroup.card_le_card_group U
    have h2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
    rw [hU] at h1
    exact (h2.trans_le h1).le
  set r := sSup S
  have hr : r ∈ S := Nat.sSup_mem ⟨0, hS0⟩ hSb
  refine ⟨r, ⟨hr, fun k hk => le_csSup hSb hk⟩, ?_⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  apply le_antisymm
  · obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup P)
    rw [← CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian] at hE
    obtain ⟨U, hU, hcard⟩ := exists_isIsotropicPowKer_of_isElementaryAbelian hA hcomm hpow hp hp2 hE
    obtain ⟨k, hk⟩ := ((hP.to_quotient A).to_subgroup U).exists_card_eq
    have hkr : k ≤ r := le_csSup hSb ⟨U, hU, hk⟩
    rw [hEcard, hd, hk, ← pow_add] at hcard
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
    omega
  · obtain ⟨U, hU, hUcard⟩ := hr
    obtain ⟨E, hE, -, -, hEcard⟩ := exists_lift_of_isIsotropicPowKer hA hcomm hpow hp hp2 hU
    rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian] at hE
    exact CFSG.SectionRank.le_pRank hp.one_lt le_top hE (by rw [hEcard, hd, hUcard, pow_add])

end RankFormula


section QuotientCounting

variable {W : Type*} [Group W] [Finite W] {p : ℕ} (hp : p.Prime)
  (hWc : ∀ u v : W, u * v = v * u) (hWp : ∀ u : W, u ^ p = 1)
include hp hWc hWp

theorem card_sup_zpowers_of_not_mem {U : Subgroup W} {g : W} (hg : g ∉ U) :
    Nat.card (U ⊔ Subgroup.zpowers g : Subgroup W) = p * Nat.card U := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hU : U.Normal := ⟨fun n hn x => by rw [hWc x n, mul_inv_cancel_right]; exact hn⟩
  have hg1 : g ≠ 1 := fun h => hg (h ▸ U.one_mem)
  have hgo : orderOf g = p := orderOf_eq_prime (hWp g) hg1
  set H := U ⊔ Subgroup.zpowers g
  have hle : Nat.card H ≤ Nat.card U * p := by
    have hsurj : Function.Surjective
        (fun x : U × Fin p => (⟨x.1 * g ^ (x.2 : ℕ), Subgroup.mul_mem _
          (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right
            (Subgroup.npow_mem_zpowers g _))⟩ : H)) := by
      rintro ⟨x, hx⟩
      obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      have hz' := (mem_zpowers_iff_mem_range_orderOf (x := g) (y := z)).1 hz
      rw [hgo] at hz'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz'
      exact ⟨(⟨u, hu⟩, ⟨k, Finset.mem_range.1 hk⟩), rfl⟩
    have h := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_prod, Nat.card_fin] at h
  have hW : IsPGroup p W := fun x => ⟨1, by rw [pow_one]; exact hWp x⟩
  obtain ⟨a, ha⟩ := (hW.to_subgroup H).exists_card_eq
  obtain ⟨b, hb⟩ := (hW.to_subgroup U).exists_card_eq
  have hne : Nat.card H ≠ Nat.card U := fun h => hg (by
    rw [Subgroup.eq_of_le_of_card_ge (le_sup_left : U ≤ H) h.le]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hba : b ≤ a := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1
    (by rw [← ha, ← hb]; exact Subgroup.card_dvd_of_le le_sup_left)
  have hba' : b + 1 ≤ a := lt_of_le_of_ne hba (fun h => hne (by rw [ha, hb, h]))
  have h1 : p ^ (b + 1) ≤ p ^ a := Nat.pow_le_pow_right hp.pos hba'
  rw [ha, hb] at hle ⊢
  rw [pow_succ] at h1
  rw [mul_comm]
  exact le_antisymm hle h1

end QuotientCounting

section Orthogonal

variable {P : Type*} [Group P] {A : Subgroup P} [A.Normal] (hA : A ≤ Subgroup.center P)
  (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A) (M : Subgroup P) [M.Normal]

@[expose] noncomputable def pairModHom (x : P) : P ⧸ A →* P ⧸ M :=
  QuotientGroup.lift A ((QuotientGroup.mk' M).comp (commRightHom hA hcomm x)) (fun a ha => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, commRightHom_apply,
      commutatorElement_eq_one_iff_mul_comm.2 (mul_comm_of_mem_le_center hA ha x).symm,
      map_one])

theorem pairModHom_mk (x y : P) :
    pairModHom hA hcomm M x (y : P ⧸ A) = ((⁅x, y⁆ : P) : P ⧸ M) :=
  QuotientGroup.lift_mk _ _ _

theorem mk_mem_ker_pairModHom (x y : P) :
    (y : P ⧸ A) ∈ (pairModHom hA hcomm M x).ker ↔ ⁅x, y⁆ ∈ M := by
  rw [MonoidHom.mem_ker, pairModHom_mk, QuotientGroup.eq_one_iff]

@[expose] noncomputable def orthMod (U : Subgroup (P ⧸ A)) : Subgroup (P ⧸ A) :=
  ⨅ (x : P) (_ : (x : P ⧸ A) ∈ U), (pairModHom hA hcomm M x).ker

theorem mk_mem_orthMod {U : Subgroup (P ⧸ A)} {y : P} :
    (y : P ⧸ A) ∈ orthMod hA hcomm M U ↔ ∀ x : P, (x : P ⧸ A) ∈ U → ⁅x, y⁆ ∈ M := by
  simp only [orthMod, Subgroup.mem_iInf, mk_mem_ker_pairModHom]

omit [M.Normal] in
theorem commutatorElement_mem_swap {x y : P} : ⁅x, y⁆ ∈ M ↔ ⁅y, x⁆ ∈ M := by
  rw [← commutatorElement_inv, inv_mem_iff]

theorem le_orthMod_iff {U V : Subgroup (P ⧸ A)} :
    U ≤ orthMod hA hcomm M V ↔ ∀ x y : P, (x : P ⧸ A) ∈ V → (y : P ⧸ A) ∈ U → ⁅x, y⁆ ∈ M := by
  constructor
  · intro h x y hx hy
    exact (mk_mem_orthMod hA hcomm M).1 (h hy) x hx
  · intro h w hw
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    exact (mk_mem_orthMod hA hcomm M).2 fun x hx => h x y hx hw

theorem le_orthMod_comm {U V : Subgroup (P ⧸ A)} :
    U ≤ orthMod hA hcomm M V ↔ V ≤ orthMod hA hcomm M U := by
  rw [le_orthMod_iff, le_orthMod_iff]
  exact ⟨fun h x y hx hy => (commutatorElement_mem_swap M).1 (h y x hy hx),
    fun h x y hx hy => (commutatorElement_mem_swap M).1 (h y x hy hx)⟩

theorem mk_mem_orthMod_iff_le_ker {U : Subgroup (P ⧸ A)} {y : P} :
    (y : P ⧸ A) ∈ orthMod hA hcomm M U ↔ U ≤ (pairModHom hA hcomm M y).ker := by
  rw [mk_mem_orthMod]
  constructor
  · intro h w hw
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    exact (mk_mem_ker_pairModHom hA hcomm M y x).2 ((commutatorElement_mem_swap M).1 (h x hw))
  · intro h x hx
    exact (commutatorElement_mem_swap M).1 ((mk_mem_ker_pairModHom hA hcomm M y x).1 (h hx))

theorem orthMod_sup (U V : Subgroup (P ⧸ A)) :
    orthMod hA hcomm M (U ⊔ V) = orthMod hA hcomm M U ⊓ orthMod hA hcomm M V := by
  ext w
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  rw [Subgroup.mem_inf, mk_mem_orthMod_iff_le_ker, mk_mem_orthMod_iff_le_ker,
    mk_mem_orthMod_iff_le_ker, sup_le_iff]

theorem orthMod_anti {U U' : Subgroup (P ⧸ A)} (h : U ≤ U') :
    orthMod hA hcomm M U' ≤ orthMod hA hcomm M U := by
  intro w hw
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  rw [mk_mem_orthMod_iff_le_ker] at hw ⊢
  exact h.trans hw

theorem mk_mem_orthMod_zpowers {x y : P} :
    (y : P ⧸ A) ∈ orthMod hA hcomm M (Subgroup.zpowers (x : P ⧸ A)) ↔ ⁅x, y⁆ ∈ M := by
  rw [mk_mem_orthMod_iff_le_ker, Subgroup.zpowers_le, mk_mem_ker_pairModHom,
    commutatorElement_mem_swap]

theorem mk_mem_orthMod_zpowers_self (x : P) :
    (x : P ⧸ A) ∈ orthMod hA hcomm M (Subgroup.zpowers (x : P ⧸ A)) := by
  rw [mk_mem_orthMod_zpowers, commutatorElement_self]
  exact M.one_mem

theorem sup_zpowers_le_orthMod {U : Subgroup (P ⧸ A)} (hU : U ≤ orthMod hA hcomm M U)
    {g : P ⧸ A} (hg : g ∈ orthMod hA hcomm M U) :
    U ⊔ Subgroup.zpowers g ≤ orthMod hA hcomm M (U ⊔ Subgroup.zpowers g) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  have hg' : U ≤ orthMod hA hcomm M (Subgroup.zpowers (x : P ⧸ A)) :=
    (le_orthMod_comm hA hcomm M).1 (Subgroup.zpowers_le.2 hg)
  rw [orthMod_sup, sup_le_iff, le_inf_iff, le_inf_iff]
  exact ⟨⟨hU, hg'⟩, Subgroup.zpowers_le.2 hg,
    Subgroup.zpowers_le.2 (mk_mem_orthMod_zpowers_self hA hcomm M x)⟩

theorem zpowers_le_orthMod (g : P ⧸ A) :
    Subgroup.zpowers g ≤ orthMod hA hcomm M (Subgroup.zpowers g) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  exact Subgroup.zpowers_le.2 (mk_mem_orthMod_zpowers_self hA hcomm M x)

theorem card_le_card_inf_orthMod_mul [Finite P] {T : Subgroup P} {x : P}
    {V : Subgroup (P ⧸ A)} (hT : ∀ y : P, (y : P ⧸ A) ∈ V → ⁅x, y⁆ ∈ T) :
    Nat.card V ≤ Nat.card (V ⊓ orthMod hA hcomm M (Subgroup.zpowers (x : P ⧸ A)) :
      Subgroup (P ⧸ A)) * Nat.card (T.map (QuotientGroup.mk' M)) := by
  have h := card_inf_ker_mul_card_map (pairModHom hA hcomm M x) V
  have hker : (pairModHom hA hcomm M x).ker =
      orthMod hA hcomm M (Subgroup.zpowers (x : P ⧸ A)) := by
    ext w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    rw [mk_mem_ker_pairModHom, mk_mem_orthMod_zpowers]
  rw [hker] at h
  have hmap : V.map (pairModHom hA hcomm M x) ≤ T.map (QuotientGroup.mk' M) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨_, hT y hw, by rw [pairModHom_mk, QuotientGroup.mk'_apply]⟩
  rw [← h]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hmap)

end Orthogonal


end CFSG.RankThree.CentralCover
