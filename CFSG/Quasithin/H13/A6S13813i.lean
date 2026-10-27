module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace A6Four

variable {M : Type*} [Group M]

theorem exists_fix_mul_inv {P : Subgroup M} (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {p : ℕ}
    (hp : Odd p) (hexp : ∀ x ∈ P, x ^ p = 1) {a : M} (ha : a * a = 1)
    (haP : ∀ x ∈ P, a * x * a⁻¹ ∈ P) {x : M} (hx : x ∈ P) :
    ∃ c ∈ P, ∃ i ∈ P, a * c * a⁻¹ = c ∧ a * i * a⁻¹ = i⁻¹ ∧ x = c * i := by
  obtain ⟨k, hk⟩ := hp
  have hainv : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha).symm
  have hax : a * x * a⁻¹ ∈ P := haP x hx
  set y := a * x * a⁻¹ with hy
  have hay : a * y * a⁻¹ = x := by rw [hy, hainv]; simp only [← mul_assoc]; rw [ha, one_mul,
    mul_assoc, ha, mul_one]
  have hconj : ∀ n : ℕ, a * (x * y) ^ n * a⁻¹ = (y * x) ^ n := by
    intro n
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
    congr 1
    calc a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      _ = y * x := by rw [hay]
  have hconj' : ∀ n : ℕ, a * (x * y⁻¹) ^ n * a⁻¹ = (y * x⁻¹) ^ n := by
    intro n
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
    congr 1
    calc a * (x * y⁻¹) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹)⁻¹ := by group
      _ = y * x⁻¹ := by rw [hay]
  have hxy : x * y = y * x := hP x hx y hax
  refine ⟨(x * y) ^ (k + 1), P.pow_mem (P.mul_mem hx hax) _, (x * y⁻¹) ^ (k + 1),
    P.pow_mem (P.mul_mem hx (P.inv_mem hax)) _, ?_, ?_, ?_⟩
  · rw [hconj, hxy]
  · rw [hconj', ← inv_pow]
    congr 1
    rw [mul_inv_rev, inv_inv]
  · have hc : (x * y) ^ (k + 1) * (x * y⁻¹) ^ (k + 1) = (x * y * (x * y⁻¹)) ^ (k + 1) := by
      rw [(Commute.mul_pow (hP _ (P.mul_mem hx hax) _ (P.mul_mem hx (P.inv_mem hax))))]
    have hxx : x * y * (x * y⁻¹) = x * x := by
      rw [show x * y * (x * y⁻¹) = x * (y * x) * y⁻¹ by group, ← hxy]
      group
    rw [hc, hxx, ← pow_two, ← pow_mul]
    have h2 : 2 * (k + 1) = p + 1 := by omega
    rw [h2, pow_succ, hexp x hx, one_mul]

theorem mem_fixSub {P : Subgroup M} {a x : M} :
    x ∈ P ⊓ Subgroup.centralizer ({a} : Set M) ↔ x ∈ P ∧ a * x * a⁻¹ = x := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by rw [← h, mul_inv_cancel_right]⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    calc x * a = a * x * a⁻¹ * a := by rw [h]
      _ = a * x := by group

theorem fix_or_inv_of_card_prime {P : Subgroup M} {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hcard : Nat.card P = p) {a : M} (ha : a * a = 1) (haP : ∀ x ∈ P, a * x * a⁻¹ ∈ P) :
    (∀ x ∈ P, a * x * a⁻¹ = x) ∨ (∀ x ∈ P, a * x * a⁻¹ = x⁻¹) := by
  have hcyc : IsCyclic ↥P := isCyclic_of_prime_card hcard
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy => by
    have := hcyc.commGroup.mul_comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hexp : ∀ x ∈ P, x ^ p = 1 := fun x hx => by
    have : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.out.ne_zero)
    have := pow_card_eq_one' (x := (⟨x, hx⟩ : ↥P))
    rw [hcard] at this
    exact congrArg Subtype.val this
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.out.ne_zero)
  set C := P ⊓ Subgroup.centralizer ({a} : Set M) with hC
  have hdvd : Nat.card C ∣ p := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | hp'
  · right
    intro x hx
    obtain ⟨c, hc, i, -, hac, hai, rfl⟩ := exists_fix_mul_inv hcomm hodd hexp ha haP hx
    have hcC : c ∈ C := mem_fixSub.2 ⟨hc, hac⟩
    have hc1 : c = 1 := by
      have := Subgroup.card_eq_one.1 h1
      rw [this] at hcC
      exact (Subgroup.mem_bot).1 hcC
    rw [hc1, one_mul, hai]
  · left
    have hCP : C = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hcard])
    intro x hx
    have : x ∈ C := hCP ▸ hx
    exact (mem_fixSub.1 this).2

@[expose] def invSub (P : Subgroup M) (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (a : M) :
    Subgroup M where
  carrier := {x | x ∈ P ∧ a * x * a⁻¹ = x⁻¹}
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨P.mul_mem hx hy, ?_⟩
    rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group, hx', hy',
      mul_inv_rev, hP _ (P.inv_mem hy) _ (P.inv_mem hx)]
  one_mem' := ⟨P.one_mem, by group⟩
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨P.inv_mem hx, ?_⟩
    rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group, hx']

theorem mem_invSub {P : Subgroup M} {hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x} {a x : M} :
    x ∈ invSub P hP a ↔ x ∈ P ∧ a * x * a⁻¹ = x⁻¹ := Iff.rfl

theorem eq_one_of_sq_of_pow_odd {x : M} {p : ℕ} (hp : Odd p) (hxp : x ^ p = 1)
    (hx2 : x * x = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hp
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  have : x ^ p = x := by
    rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← this, hxp]

theorem card_fix_mul_card_inv [Finite M] {P : Subgroup M} (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    {p : ℕ} (hp : Odd p) (hexp : ∀ x ∈ P, x ^ p = 1) {a : M} (ha : a * a = 1)
    (haP : ∀ x ∈ P, a * x * a⁻¹ ∈ P) :
    Nat.card ↥(P ⊓ Subgroup.centralizer ({a} : Set M)) * Nat.card ↥(invSub P hP a) =
      Nat.card P := by
  set C := P ⊓ Subgroup.centralizer ({a} : Set M) with hC
  set I := invSub P hP a with hI
  have hCP : C ≤ P := inf_le_left
  have hIP : I ≤ P := fun x hx => hx.1
  have hdisj : Disjoint (C.subgroupOf P) (I.subgroupOf P) := by
    rw [Subgroup.disjoint_def]
    intro x hxC hxI
    have h1 := (mem_fixSub.1 (Subgroup.mem_subgroupOf.1 hxC)).2
    have h2 := (mem_invSub.1 (Subgroup.mem_subgroupOf.1 hxI)).2
    rw [h1] at h2
    refine Subtype.ext (eq_one_of_sq_of_pow_odd hp (hexp _ x.2) ?_)
    nth_rewrite 2 [h2]
    exact mul_inv_cancel _
  have hmul : ((C.subgroupOf P : Set ↥P) * (I.subgroupOf P : Set ↥P)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨c, hc, i, hi, hac, hai, hx⟩ := exists_fix_mul_inv hP hp hexp ha haP x.2
    refine ⟨⟨c, hc⟩, Subgroup.mem_subgroupOf.2 (mem_fixSub.2 ⟨hc, hac⟩), ⟨i, hi⟩,
      Subgroup.mem_subgroupOf.2 ⟨hi, hai⟩, Subtype.ext hx.symm⟩
  have hcomp := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have h1 := hcomp.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIP).toEquiv] at h1
  exact h1

theorem exists_inv_of_rank_two [Finite M] {P : Subgroup M}
    (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : Nat.card P = p ^ 2) {a b : M} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a)
    (haP : ∀ x ∈ P, a * x * a⁻¹ ∈ P) (hbP : ∀ x ∈ P, b * x * b⁻¹ ∈ P)
    (hna : ¬ ∀ x ∈ P, a * x * a⁻¹ = x) (hnb : ¬ ∀ x ∈ P, b * x * b⁻¹ = x)
    (hnab : ¬ ∀ x ∈ P, a * b * x * (a * b)⁻¹ = x) :
    ∃ z, (z = a ∨ z = b ∨ z = a * b) ∧ ∀ x ∈ P, z * x * z⁻¹ = x⁻¹ := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  set C := P ⊓ Subgroup.centralizer ({a} : Set M) with hCdef
  set I := invSub P hP a with hIdef
  have hcardCI := card_fix_mul_card_inv hP hodd hexp ha haP
  rw [← hCdef, ← hIdef, hcard] at hcardCI
  have hCP : C ≤ P := inf_le_left
  have hIP : I ≤ P := fun x hx => hx.1
  have hCdvd : Nat.card C ∣ p ^ 2 := ⟨_, hcardCI.symm⟩
  obtain ⟨m, hm2, hmC⟩ := (Nat.dvd_prime_pow hp.out).1 hCdvd
  have hpos : 0 < p := hp.out.pos
  by_cases hC1 : m = 0
  ·
    refine ⟨a, Or.inl rfl, fun x hx => ?_⟩
    obtain ⟨c, hc, i, -, hac, hai, rfl⟩ := exists_fix_mul_inv hP hodd hexp ha haP hx
    have hcC : c ∈ C := mem_fixSub.2 ⟨hc, hac⟩
    have hC' : C = ⊥ := Subgroup.card_eq_one.1 (by rw [hmC, hC1, pow_zero])
    rw [hC'] at hcC
    rw [(Subgroup.mem_bot).1 hcC, one_mul, hai]
  by_cases hC2 : m = 2
  · exfalso
    apply hna
    have hCeq : C = P := Subgroup.eq_of_le_of_card_ge hCP (by rw [hmC, hC2, hcard])
    intro x hx
    have : x ∈ C := hCeq ▸ hx
    exact (mem_fixSub.1 this).2
  have hm1 : m = 1 := by omega
  have hCp : Nat.card C = p := by rw [hmC, hm1, pow_one]
  have hIp : Nat.card I = p := by
    rw [hCp, pow_two] at hcardCI
    exact Nat.eq_of_mul_eq_mul_left hpos hcardCI
  have hainv : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha).symm
  have hbinv : b⁻¹ = b := (eq_inv_of_mul_eq_one_left hb).symm
  have hbC : ∀ x ∈ C, b * x * b⁻¹ ∈ C := by
    intro x hx
    obtain ⟨hxP, hxa⟩ := mem_fixSub.1 hx
    refine mem_fixSub.2 ⟨hbP x hxP, ?_⟩
    calc a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by
          rw [hainv, hbinv]
          calc a * (b * x * b) * a = (a * b) * x * (b * a) := by group
            _ = (b * a) * x * (a * b) := by rw [hab]
            _ = b * (a * x * a) * b := by group
      _ = b * x * b⁻¹ := by rw [hxa]
  have hbI : ∀ x ∈ I, b * x * b⁻¹ ∈ I := by
    intro x hx
    obtain ⟨hxP, hxa⟩ := mem_invSub.1 hx
    refine mem_invSub.2 ⟨hbP x hxP, ?_⟩
    calc a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by
          rw [hainv, hbinv]
          calc a * (b * x * b) * a = (a * b) * x * (b * a) := by group
            _ = (b * a) * x * (a * b) := by rw [hab]
            _ = b * (a * x * a) * b := by group
      _ = (b * x * b⁻¹)⁻¹ := by rw [hxa]; group
  have hC := fix_or_inv_of_card_prime hp2 hCp hb hbC
  have hI := fix_or_inv_of_card_prime hp2 hIp hb hbI
  have hdec : ∀ x ∈ P, ∃ c ∈ C, ∃ i ∈ I, x = c * i := fun x hx => by
    obtain ⟨c, hc, i, hi, hac, hai, rfl⟩ := exists_fix_mul_inv hP hodd hexp ha haP hx
    exact ⟨c, mem_fixSub.2 ⟨hc, hac⟩, i, ⟨hi, hai⟩, rfl⟩
  rcases hC with hCf | hCi <;> rcases hI with hIf | hIi
  · exfalso
    apply hnb
    intro x hx
    obtain ⟨c, hc, i, hi, rfl⟩ := hdec x hx
    rw [show b * (c * i) * b⁻¹ = (b * c * b⁻¹) * (b * i * b⁻¹) by group, hCf c hc, hIf i hi]
  · exfalso
    apply hnab
    intro x hx
    obtain ⟨c, hc, i, hi, rfl⟩ := hdec x hx
    rw [show a * b * (c * i) * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ * (a * (b * i * b⁻¹) * a⁻¹)
      by group, hCf c hc, hIi i hi, (mem_fixSub.1 hc).2,
      show a * i⁻¹ * a⁻¹ = (a * i * a⁻¹)⁻¹ by group, (mem_invSub.1 hi).2, inv_inv]
  · refine ⟨a * b, Or.inr (Or.inr rfl), fun x hx => ?_⟩
    obtain ⟨c, hc, i, hi, rfl⟩ := hdec x hx
    rw [show a * b * (c * i) * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ * (a * (b * i * b⁻¹) * a⁻¹)
      by group, hCi c hc, hIf i hi, show a * c⁻¹ * a⁻¹ = (a * c * a⁻¹)⁻¹ by group,
      (mem_fixSub.1 hc).2, (mem_invSub.1 hi).2, mul_inv_rev,
      hP _ (P.inv_mem (hIP hi)) _ (P.inv_mem (hCP hc))]
  · refine ⟨b, Or.inr (Or.inl rfl), fun x hx => ?_⟩
    obtain ⟨c, hc, i, hi, rfl⟩ := hdec x hx
    rw [show b * (c * i) * b⁻¹ = (b * c * b⁻¹) * (b * i * b⁻¹) by group, hCi c hc, hIi i hi,
      mul_inv_rev, hP _ (P.inv_mem (hIP hi)) _ (P.inv_mem (hCP hc))]

section Extraspecial

variable {P Z : Subgroup M} {p : ℕ} (hp : Odd p) (hZP : Z ≤ P)
  (hZcent : ∀ z ∈ Z, ∀ y ∈ P, z * y = y * z) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z)
  (hexp : ∀ x ∈ P, x ^ p = 1)
include hp hZP hexp

theorem eq_of_mem_coset {e : M} (he : e * e = 1) (heZ : ∀ z ∈ Z, e * z * e⁻¹ = z) {x : M}
    (hxz : e * x * e⁻¹ * x⁻¹ ∈ Z) :
    e * x * e⁻¹ = x := by
  set z := e * x * e⁻¹ * x⁻¹ with hz
  have hzx : e * x * e⁻¹ = z * x := by rw [hz]; group
  have heinv : e⁻¹ = e := (eq_inv_of_mul_eq_one_left he).symm
  have h1 : x = e * (e * x * e⁻¹) * e⁻¹ := by
    rw [heinv]
    calc x = (e * e) * x * (e * e) := by rw [he, one_mul, mul_one]
      _ = e * (e * x * e) * e := by group
  have h2 : e * (z * x) * e⁻¹ = z * (z * x) := by
    rw [show e * (z * x) * e⁻¹ = (e * z * e⁻¹) * (e * x * e⁻¹) by group, heZ z hxz, hzx]
  rw [hzx, h2] at h1
  have hz2 : z * z = 1 := by
    have := congrArg (· * x⁻¹) h1
    simp only [mul_inv_cancel] at this
    rw [this]
    group
  have hz1 : z = 1 := eq_one_of_sq_of_pow_odd hp (hexp z (hZP hxz)) hz2
  rw [hzx, hz1, one_mul]

include hZcent hcomm in
theorem mem_of_fix
    (hcent : ∀ x ∈ P, x ∉ Z → ∀ y ∈ P, x * y = y * x → ∃ n : ℤ, ∃ z ∈ Z, y = x ^ n * z)
    {e : M} (he : e * e = 1) (heP : ∀ x ∈ P, e * x * e⁻¹ ∈ P)
    (heZ : ∀ z ∈ Z, e * z * e⁻¹ = z) (hne : ¬ ∀ x ∈ P, e * x * e⁻¹ = x) {x : M} (hx : x ∈ P)
    (hfix : e * x * e⁻¹ = x) : x ∈ Z := by
  by_contra hxZ
  apply hne
  intro y hy
  by_contra hyne
  have hee : ∀ w : M, e * (e * w * e⁻¹) * e⁻¹ = w := fun w => by
    calc e * (e * w * e⁻¹) * e⁻¹ = (e * e) * w * (e * e)⁻¹ := by group
      _ = w := by rw [he]; group
  set y' := y * (e * y * e⁻¹)⁻¹ with hy'
  have hy'P : y' ∈ P := P.mul_mem hy (P.inv_mem (heP y hy))
  have hey' : e * y' * e⁻¹ = y'⁻¹ := by
    rw [hy']
    calc e * (y * (e * y * e⁻¹)⁻¹) * e⁻¹ = (e * y * e⁻¹) * (e * (e * y * e⁻¹) * e⁻¹)⁻¹ := by
          group
      _ = (y * (e * y * e⁻¹)⁻¹)⁻¹ := by rw [hee]; group
  set c := x * y' * x⁻¹ * y'⁻¹ with hc
  have hcZ : c ∈ Z := hcomm x hx y' hy'P
  have hec : e * c * e⁻¹ = c⁻¹ := by
    have h1 : e * c * e⁻¹ = (e * x * e⁻¹) * (e * y' * e⁻¹) * (e * x * e⁻¹)⁻¹ *
        (e * y' * e⁻¹)⁻¹ := by rw [hc]; group
    rw [h1, hfix, hey', inv_inv]
    have h2 : x * y'⁻¹ * x⁻¹ * y' = y'⁻¹ * c⁻¹ * y' := by rw [hc]; group
    rw [h2, ← hZcent _ (Z.inv_mem hcZ) _ (P.inv_mem hy'P)]
    group
  have hc1 : c = 1 := by
    have h1 := heZ c hcZ
    rw [hec] at h1
    refine eq_one_of_sq_of_pow_odd hp (hexp c (hZP hcZ)) ?_
    nth_rewrite 2 [← h1]
    exact mul_inv_cancel c
  have hxy : x * y' = y' * x := by
    have : x * y' * x⁻¹ * y'⁻¹ = 1 := hc1
    calc x * y' = (x * y' * x⁻¹ * y'⁻¹) * (y' * x) := by group
      _ = y' * x := by rw [this, one_mul]
  obtain ⟨n, z, hz, hyz⟩ := hcent x hx hxZ y' hy'P hxy
  have h3 : e * y' * e⁻¹ = y' := by
    rw [hyz, show e * (x ^ n * z) * e⁻¹ = (e * x * e⁻¹) ^ n * (e * z * e⁻¹) by
      rw [← MulAut.conj_apply, map_mul, map_zpow, MulAut.conj_apply, MulAut.conj_apply],
      hfix, heZ z hz]
  rw [hey'] at h3
  have hy1 : y' = 1 := by
    refine eq_one_of_sq_of_pow_odd hp (hexp y' hy'P) ?_
    nth_rewrite 2 [← h3]
    exact mul_inv_cancel y'
  apply hyne
  have : y * (e * y * e⁻¹)⁻¹ = 1 := hy1
  calc e * y * e⁻¹ = (y * (e * y * e⁻¹)⁻¹)⁻¹ * y := by group
    _ = y := by rw [this, inv_one, one_mul]

include hcomm in
theorem inv_mod_of_fix_le {e : M} (he : e * e = 1) (heP : ∀ x ∈ P, e * x * e⁻¹ ∈ P)
    (heZ : ∀ z ∈ Z, e * z * e⁻¹ = z) (hfix : ∀ x ∈ P, e * x * e⁻¹ = x → x ∈ Z) {x : M}
    (hx : x ∈ P) : e * x * e⁻¹ * x ∈ Z := by
  have hee : ∀ w : M, e * (e * w * e⁻¹) * e⁻¹ = w := fun w => by
    calc e * (e * w * e⁻¹) * e⁻¹ = (e * e) * w * (e * e)⁻¹ := by group
      _ = w := by rw [he]; group
  set w := e * x * e⁻¹ * x with hw
  have hwP : w ∈ P := P.mul_mem (heP x hx) hx
  have hew : e * w * e⁻¹ = x * (e * x * e⁻¹) := by
    rw [hw]
    calc e * (e * x * e⁻¹ * x) * e⁻¹ = (e * (e * x * e⁻¹) * e⁻¹) * (e * x * e⁻¹) := by group
      _ = x * (e * x * e⁻¹) := by rw [hee]
  apply hfix w hwP
  apply eq_of_mem_coset hp hZP hexp he heZ
  rw [hew, hw]
  have := hcomm x hx (e * x * e⁻¹) (heP x hx)
  convert this using 1
  group

include hZcent hcomm in
theorem false_of_extraspecial
    (hcent : ∀ x ∈ P, x ∉ Z → ∀ y ∈ P, x * y = y * x → ∃ n : ℤ, ∃ z ∈ Z, y = x ^ n * z)
    {a b : M} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (haP : ∀ x ∈ P, a * x * a⁻¹ ∈ P) (hbP : ∀ x ∈ P, b * x * b⁻¹ ∈ P)
    (haZ : ∀ z ∈ Z, a * z * a⁻¹ = z) (hbZ : ∀ z ∈ Z, b * z * b⁻¹ = z)
    (hna : ¬ ∀ x ∈ P, a * x * a⁻¹ = x) (hnb : ¬ ∀ x ∈ P, b * x * b⁻¹ = x)
    (hnab : ¬ ∀ x ∈ P, a * b * x * (a * b)⁻¹ = x) : False := by
  have hia : ∀ x ∈ P, a * x * a⁻¹ * x ∈ Z := fun x hx =>
    inv_mod_of_fix_le hp hZP hcomm hexp ha haP haZ
      (fun x hx h => mem_of_fix hp hZP hZcent hcomm hexp hcent ha haP haZ hna hx h) hx
  have hib : ∀ x ∈ P, b * x * b⁻¹ * x ∈ Z := fun x hx =>
    inv_mod_of_fix_le hp hZP hcomm hexp hb hbP hbZ
      (fun x hx h => mem_of_fix hp hZP hZcent hcomm hexp hcent hb hbP hbZ hnb hx h) hx
  have habab : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  have habP : ∀ x ∈ P, a * b * x * (a * b)⁻¹ ∈ P := fun x hx => by
    rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group]
    exact haP _ (hbP x hx)
  have habZ : ∀ z ∈ Z, a * b * z * (a * b)⁻¹ = z := fun z hz => by
    rw [show a * b * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ by group, hbZ z hz, haZ z hz]
  apply hnab
  intro x hx
  apply eq_of_mem_coset hp hZP hexp habab habZ
  have h1 := hib x hx
  have h2 := hia x hx
  set z₁ := b * x * b⁻¹ * x with hz₁
  set z₂ := a * x * a⁻¹ * x with hz₂
  have hbx : b * x * b⁻¹ = z₁ * x⁻¹ := by rw [hz₁]; group
  have hax : a * x * a⁻¹ = z₂ * x⁻¹ := by rw [hz₂]; group
  have e1 : a * b * x * (a * b)⁻¹ * x⁻¹ = (a * z₁ * a⁻¹) * (a * x * a⁻¹)⁻¹ * x⁻¹ := by
    rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group, hbx]
    group
  rw [e1, haZ z₁ h1, hax, mul_inv_rev, inv_inv, ← mul_assoc, mul_assoc z₁ x,
    ← hZcent _ (Z.inv_mem h2) x hx]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  exact Z.mul_mem h1 (Z.inv_mem h2)

end Extraspecial

theorem extraspecial_data [Finite M] {P : Subgroup M} {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPOnePlusTwo p ↥P) :
    let Z := (Subgroup.center ↥P).map P.subtype
    Z ≤ P ∧ Nat.card Z = p ∧ (∀ z ∈ Z, ∀ y ∈ P, z * y = y * z) ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧ (∀ x ∈ P, x ^ p = 1) ∧
      ∀ x ∈ P, x ∉ Z → ∀ y ∈ P, x * y = y * x → ∃ n : ℤ, ∃ z ∈ Z, y = x ^ n * z := by
  intro Z
  obtain ⟨hext, hcard3, hexp⟩ := hP
  have hZP : Z ≤ P := Subgroup.map_subtype_le _
  have hZcard : Nat.card Z = p := by
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hext.center_order_p
  have hmemZ : ∀ x (hx : x ∈ P), x ∈ Z ↔ ∀ y ∈ P, x * y = y * x := by
    intro x hx
    constructor
    · rintro ⟨z, hz, rfl⟩ y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩).symm
    · intro h
      refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (h y y.2).symm, rfl⟩
  have hZcent : ∀ z ∈ Z, ∀ y ∈ P, z * y = y * z := fun z hz y hy =>
    (hmemZ z (hZP hz)).1 hz y hy
  have hexp' : ∀ x ∈ P, x ^ p = 1 := fun x hx => congrArg Subtype.val (hexp ⟨x, hx⟩)
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    intro x hx y hy
    have hab := hext.quotient_elementary_abelian
    have hc := hab.toIsMulCommutative.is_comm.comm
      (QuotientGroup.mk (⟨x⁻¹, P.inv_mem hx⟩ : ↥P)) (QuotientGroup.mk ⟨y⁻¹, P.inv_mem hy⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
    refine ⟨_, (Subgroup.center ↥P).inv_mem hc, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    group
  refine ⟨hZP, hZcard, hZcent, hcomm, hexp', fun x hx hxZ y hy hxy => ?_⟩
  set K := Subgroup.zpowers x ⊔ Z with hK
  set C := P ⊓ Subgroup.centralizer ({x} : Set M) with hC
  have hKC : K ≤ C := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    · intro z hz
      exact ⟨hZP hz, Subgroup.mem_centralizer_singleton_iff.2 (hZcent z hz x hx)⟩
  have hCP : C ≤ P := inf_le_left
  have hPcard : Nat.card P = p ^ 3 := hcard3
  have hCne : C ≠ P := by
    intro h
    apply hxZ
    refine (hmemZ x hx).2 fun y hy => ?_
    have : y ∈ C := h ▸ hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 this.2).symm
  have hCdvd : Nat.card C ∣ p ^ 3 := hPcard ▸ Subgroup.card_dvd_of_le hCP
  obtain ⟨c, hc3, hCc⟩ := (Nat.dvd_prime_pow hp.out).1 hCdvd
  have hc2 : c ≤ 2 := by
    by_contra h
    exact hCne (Subgroup.eq_of_le_of_card_ge hCP (by rw [hCc, hPcard, show c = 3 by omega]))
  have hKdvd : Nat.card K ∣ p ^ 3 := hPcard ▸ Subgroup.card_dvd_of_le (hKC.trans hCP)
  obtain ⟨k, hk3, hKk⟩ := (Nat.dvd_prime_pow hp.out).1 hKdvd
  have hZK : Z < K := lt_of_le_of_ne le_sup_right fun h => hxZ (h ▸ Subgroup.mem_sup_left
    (Subgroup.mem_zpowers x))
  have hk2 : 2 ≤ k := by
    have h1 := Subgroup.card_lt_of_lt hZK
    rw [hZcard, hKk] at h1
    by_contra h
    have : k ≤ 1 := by omega
    have : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos this
    rw [pow_one] at this
    omega
  have hKCeq : K = C := Subgroup.eq_of_le_of_card_ge hKC (by
    rw [hKk, hCc]; exact Nat.pow_le_pow_right hp.out.pos (by omega))
  have hyC : y ∈ C := ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 hxy.symm⟩
  rw [← hKCeq] at hyC
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Z : Set M) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [← hZcent z hz x hx, mul_inv_cancel_right]
      exact hz
    · intro hz
      have h1 : x * z * x⁻¹ ∈ P := by
        have hzP : z ∈ P := by
          have := P.mul_mem (P.mul_mem (P.inv_mem hx) (hZP hz)) hx
          simpa [mul_assoc] using this
        exact P.mul_mem (P.mul_mem hx hzP) (P.inv_mem hx)
      have h2 : z = x⁻¹ * (x * z * x⁻¹) * x := by group
      rw [h2, ← hZcent _ hz x⁻¹ (P.inv_mem hx)]
      simpa [mul_assoc] using hz
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hxN
  have hy' : y ∈ ((Subgroup.zpowers x : Set M) * (Z : Set M)) := by
    rw [← hset]
    exact hyC
  obtain ⟨w, hw, z, hz, rfl⟩ := hy'
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  exact ⟨n, z, hz, rfl⟩

section PrimeCases

variable {V : Type} [CommGroup V] [Finite V]

theorem prime_cases (hV : ∀ v : V, v ^ 2 = 1) {X U P : Subgroup (MulAut V)} (hU : U ∈ Qset X)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hPp : IsPGroup p P) (hPexp : ∀ x ∈ P, x ^ p = 1)
    (hUP : ∀ u ∈ U, ∀ x ∈ P, u * x * u⁻¹ ∈ P)
    (hfaith : ∀ u ∈ U, (∀ x ∈ P, u * x = x * u) → u = 1) :
    (p = 3 ∨ p = 5) ∧ (p = 5 → ∃ t ∈ U, t ≠ 1 ∧ t ^ 2 = 1 ∧
      rk (commV (Subgroup.zpowers t)) = 2 ∧
      Nat.card (⁅P, Subgroup.zpowers t⁆ : Subgroup (MulAut V)) = 5 ∧
      IsDirectSum ⊤ (commV ⁅P, Subgroup.zpowers t⁆)
        (fixV (⁅P, Subgroup.zpowers t⁆ ⊔ Subgroup.zpowers t)) ∧
      rk (commV ⁅P, Subgroup.zpowers t⁆) = 4) := by
  obtain ⟨⟨hUA2, hUr⟩, hUk⟩ := hU
  have hUel := hUA2.isElemAbelian2
  have hu2 : ∀ u ∈ U, u * u = 1 := fun u hu => by rw [← pow_two]; exact hUel.2 u hu
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  set X₀ := U ⊔ P with hX₀
  have hUN : U ≤ Subgroup.normalizer (P : Set (MulAut V)) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hUP u hu x hx, fun hx => ?_⟩
    have h1 := hUP u⁻¹ (U.inv_mem hu) _ hx
    simpa [mul_assoc] using h1
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUN
  have hmem : ∀ g ∈ X₀, ∃ u ∈ U, ∃ x ∈ P, g = u * x := by
    intro g hg
    have : g ∈ ((U : Set (MulAut V)) * (P : Set (MulAut V))) := by rw [← hset]; exact hg
    obtain ⟨u, hu, x, hx, rfl⟩ := this
    exact ⟨u, hu, x, hx, rfl⟩
  have hPX₀ : P ≤ X₀ := le_sup_right
  have hPnorm : ∀ g ∈ X₀, ∀ y ∈ P, g * y * g⁻¹ ∈ P := by
    intro g hg y hy
    obtain ⟨u, hu, x, hx, rfl⟩ := hmem g hg
    rw [show u * x * y * (u * x)⁻¹ = u * (x * y * x⁻¹) * u⁻¹ by group]
    exact hUP u hu _ (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx))
  have hPle : P ≤ pCoreOf p X₀ := by
    have hN : (P.subgroupOf X₀).Normal :=
      ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (hPnorm g g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
    exact le_pCoreOf p hPX₀ hN hPp
  have hcore : pCoreOf p X₀ = P := by
    refine le_antisymm (fun g hg => ?_) hPle
    obtain ⟨u, hu, x, hx, rfl⟩ := hmem g (pCoreOf_le p X₀ hg)
    have hu' : u ∈ pCoreOf p X₀ := by
      have := (pCoreOf p X₀).mul_mem hg ((pCoreOf p X₀).inv_mem (hPle hx))
      simpa using this
    have hup : IsPGroup p (pCoreOf p X₀) := pCoreOf_isPGroup p X₀
    obtain ⟨k, hk⟩ := hup ⟨u, hu'⟩
    have hk' : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hu1 : u = 1 := by
      have h2 : u ^ 2 = 1 := by rw [pow_two]; exact hu2 u hu
      have hcop : Nat.Coprime (p ^ k) 2 := Nat.Coprime.pow_left k
        ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
      rw [← orderOf_eq_one_iff]
      exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
        (orderOf_dvd_of_pow_eq_one h2)
    rw [hu1, one_mul]
    exact hx
  have hUX₀ : IsA2 X₀ U := ⟨le_sup_left, hUA2.ne_bot, hUel⟩
  have hq : qOf X₀ ≤ ((2 : ℚ) : WithTop ℚ) := kq_le_iff.2 ⟨U, hUX₀, hUk, hUr⟩
  have hqh := (qhatOf_le_qOf X₀).trans hq
  obtain ⟨r, hr⟩ : ∃ r : ℚ, qhatOf X₀ = (r : WithTop ℚ) := by
    have hne : qhatOf X₀ ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hqh
    exact WithTop.ne_top_iff_exists.1 hne |>.imp fun r h => h.symm
  have hr2 : r ≤ 2 := by rw [hr] at hqh; exact_mod_cast hqh
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr hr2
  obtain ⟨r', hr', -, ⟨⟨hA2, hAr⟩, -⟩, -⟩ := QhatStar_spec hA
  have hcentP : ∀ g ∈ X₀, g ^ 2 = 1 → (∀ y ∈ P, g * y = y * g) → g = 1 := by
    intro g hg hg2 hgc
    obtain ⟨u, hu, x, hx, rfl⟩ := hmem g hg
    have hgc' : ∀ y ∈ P, u * x * y * (u * x)⁻¹ = y := fun y hy => by
      rw [hgc y hy, mul_inv_cancel_right]
    have hux : ∀ y ∈ P, u * y * u⁻¹ = x⁻¹ * y * x := by
      intro y hy
      have h1 := hgc' (x⁻¹ * y * x) (P.mul_mem (P.mul_mem (P.inv_mem hx) hy) hx)
      calc u * y * u⁻¹ = u * x * (x⁻¹ * y * x) * (u * x)⁻¹ := by group
        _ = x⁻¹ * y * x := h1
    have hx2 : ∀ y ∈ P, x * x * y = y * (x * x) := by
      intro y hy
      have h1 : u * (u * y * u⁻¹) * u⁻¹ = x⁻¹ * (x⁻¹ * y * x) * x := by
        rw [hux y hy, hux _ (P.mul_mem (P.mul_mem (P.inv_mem hx) hy) hx)]
      have h2 : u * (u * y * u⁻¹) * u⁻¹ = y := by
        calc u * (u * y * u⁻¹) * u⁻¹ = (u * u) * y * (u * u)⁻¹ := by group
          _ = y := by rw [hu2 u hu]; group
      rw [h2] at h1
      calc x * x * y = x * x * (x⁻¹ * (x⁻¹ * y * x) * x) := by rw [← h1]
        _ = y * (x * x) := by group
    have hxc : ∀ y ∈ P, x * y = y * x := by
      obtain ⟨k, hk⟩ := hodd
      have hxk : x = (x * x) ^ (k + 1) := by
        rw [← pow_two, ← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hPexp x hx,
          one_mul]
      intro y hy
      rw [hxk]
      exact ((Commute.pow_left (hx2 y hy) (k + 1))).eq
    have hu1 : u = 1 := by
      refine hfaith u hu fun y hy => ?_
      have h1 := hux y hy
      rw [show x⁻¹ * y * x = y by rw [mul_assoc, ← hxc y hy]; group] at h1
      calc u * y = u * y * u⁻¹ * u := by group
        _ = y * u := by rw [h1]
    rw [hu1, one_mul] at hg2 ⊢
    refine eq_one_of_sq_of_pow_odd hodd (hPexp x hx) ?_
    rw [← pow_two]
    exact hg2
  have hAP : ⁅pCoreOf p X₀, A⁆ ≠ ⊥ := by
    rw [hcore]
    intro hbot
    apply hA2.ne_bot
    rw [eq_bot_iff]
    intro a ha
    refine (Subgroup.mem_bot).2 (hcentP a (hA2.le ha) (hA2.isElemAbelian2.2 a ha) fun y hy => ?_)
    have h1 : ⁅y, a⁆ ∈ ⁅P, A⁆ := Subgroup.commutator_mem_commutator hy ha
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  obtain ⟨h35, h5, -, -, -⟩ := D2_13 hV hr hA hp2 rfl hAP
  refine ⟨h35, fun hp5 => ?_⟩
  obtain ⟨hr2', hrkA, -, -, -, -⟩ := h5 hp5
  have hAcard : Nat.card A = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [card_eq_two_pow_of_isPGroup hA2.isElemAbelian2.isPGroup, hrkA, pow_one]
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A)).mp hA2.ne_bot
  have ha1' : (a : MulAut V) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hAa : Subgroup.zpowers (a : MulAut V) = A := zpowers_eq_of_prime_card hAcard a.2 ha1'
  obtain ⟨u, hu, x, hx, hax⟩ := hmem a (hA2.le a.2)
  have ha2 : (a : MulAut V) * a = 1 := by rw [← pow_two]; exact hA2.isElemAbelian2.2 a a.2
  have huinv : u⁻¹ = u := (eq_inv_of_mul_eq_one_left (hu2 u hu)).symm
  have hinvx : u * x * u⁻¹ = x⁻¹ := by
    have h1 : u * x * (u * x) = 1 := hax ▸ ha2
    rw [huinv]
    calc u * x * u = (u * x * (u * x)) * x⁻¹ := by group
      _ = x⁻¹ := by rw [h1, one_mul]
  obtain ⟨k, hk⟩ := hodd
  set y := x ^ (k + 1) with hy
  have hyP : y ∈ P := P.pow_mem hx _
  have hyy : y * y = x := by
    rw [hy, ← pow_two, ← pow_mul, show (k + 1) * 2 = p + 1 by omega, pow_succ, hPexp x hx,
      one_mul]
  have hinvy : u * y * u⁻¹ = y⁻¹ := by
    rw [hy, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinvx, inv_pow]
  have hconj : y⁻¹ * u * y = (a : MulAut V) := by
    rw [hax]
    calc y⁻¹ * u * y = y⁻¹ * (u * y * u⁻¹) * u := by group
      _ = y⁻¹ * y⁻¹ * u := by rw [hinvy]
      _ = (y * y)⁻¹ * u := by group
      _ = u * (y * y) := by rw [hyy, ← hinvx]; group
      _ = u * x := by rw [hyy]
  have hpow : ∀ n : ℤ, (y⁻¹ * u * y) ^ n = y⁻¹ * u ^ n * y := fun n => by
    rw [show y⁻¹ * u * y = y⁻¹ * u * y⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
  have hUu : Subgroup.zpowers u = conjBy y A := by
    rw [← hAa, ← hconj]
    ext z
    rw [mem_conjBy_iff]
    constructor
    · intro hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact Subgroup.mem_zpowers_iff.2 ⟨n, hpow n⟩
    · intro hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
      refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
      rw [hpow] at hn
      calc u ^ n = y * (y⁻¹ * u ^ n * y) * y⁻¹ := by group
        _ = z := by rw [hn]; group
  have hUq : Subgroup.zpowers u ∈ QhatStar X₀ := hUu ▸ conjBy_mem_QhatStar hA (hPX₀ hyP)
  have hu1 : u ≠ 1 := by
    intro h1
    apply ha1'
    rw [hax, h1, one_mul]
    refine eq_one_of_sq_of_pow_odd ⟨k, hk⟩ (hPexp x hx) ?_
    have hax' : (a : MulAut V) = x := by rw [hax, h1, one_mul]
    rw [← hax']
    exact ha2
  have hUP' : ⁅pCoreOf p X₀, Subgroup.zpowers u⁆ ≠ ⊥ := by
    rw [hcore]
    intro hbot
    apply hu1
    refine hfaith u hu fun z hz => ?_
    have h1 : ⁅z, u⁆ ∈ ⁅P, Subgroup.zpowers u⁆ :=
      Subgroup.commutator_mem_commutator hz (Subgroup.mem_zpowers u)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  obtain ⟨-, h5', -, -, -⟩ := D2_13 hV hr hUq hp2 rfl hUP'
  obtain ⟨-, -, hD5, -, hdec, hrk4⟩ := h5' hp5
  rw [hcore] at hD5 hdec hrk4
  obtain ⟨r'', hr'', -, ⟨⟨-, hur⟩, -⟩, -⟩ := QhatStar_spec hUq
  have hrr : r'' = r := WithTop.coe_injective (hr''.symm.trans hr)
  have hu2' : u ^ 2 = 1 := by rw [pow_two]; exact hu2 u hu
  have hord : orderOf u = 2 := orderOf_eq_prime hu2' hu1
  have hrk1 : rk (Subgroup.zpowers u) = 1 := by
    unfold rk
    rw [Nat.card_zpowers, hord]
    simp
  have hrk2 : rk (commV (Subgroup.zpowers u)) = 2 := by
    rw [rAV, hrk1, rkIdx_fixV_zpowers, hrr, hr2'] at hur
    exact_mod_cast (by simpa using hur : (rk (commV (Subgroup.zpowers u)) : ℚ) = 2)
  exact ⟨u, hu, hu1, hu2', hrk2, hD5, hdec, hrk4⟩

end PrimeCases

end A6Four

end CFSG.Quasithin.H13.A6
