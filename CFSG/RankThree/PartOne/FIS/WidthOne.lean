module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.RankThree.PartOne.FIS

universe u

namespace WidthOne

theorem eq_one_of_pow_eq_one_of_pow_eq_one {Y : Type*} [Group Y] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {c : Y} {k j : ℕ} (h1 : c ^ p ^ k = 1) (h2 : c ^ q ^ j = 1) :
    c = 1 := by
  have hcop : Nat.Coprime (p ^ k) (q ^ j) := ((Nat.coprime_primes hp hq).2 hpq).pow k j
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one] at h
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h)

theorem exists_pow_eq_one_of_mem {Y : Type*} [Group Y] {p : ℕ} {M : Subgroup Y}
    (hM : IsPGroup p M) {c : Y} (hc : c ∈ M) : ∃ k : ℕ, c ^ p ^ k = 1 := by
  obtain ⟨k, hk⟩ := hM ⟨c, hc⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem eq_of_comm_of_cube {Y : Type*} [Group Y] {a b : Y} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (h3 : (a * b) ^ 3 = 1) : a = b := by
  have h2 : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = a * b * (a * b) := sq _
      _ = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, one_mul]
  have h1 : a * b = 1 := by
    calc a * b = (a * b) ^ 3 * ((a * b) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  exact (eq_inv_of_mul_eq_one_left h1).trans (inv_eq_of_mul_eq_one_right hb)

structure Conditions {X : Type*} [Group X] (E : Set X) : Prop where
  conj : ∀ e ∈ E, ∀ g : X, g * e * g⁻¹ ∈ E
  gen : Subgroup.closure E = ⊤
  mul_self : ∀ e ∈ E, e * e = 1
  ne_one : ∀ e ∈ E, e ≠ 1
  noncomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a → a = b
  cube : ∀ a ∈ E, ∀ b ∈ E, (a * b) ^ 3 = 1

theorem Conditions.map_quotient {X : Type*} [Group X] {E : Set X} (hE : Conditions E)
    (M : Subgroup X) [M.Normal] (hM : Odd (Nat.card M)) :
    Conditions ((QuotientGroup.mk' M) '' E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩ g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨g * e * g⁻¹, hE.conj e he g, by simp⟩
  · rw [← MonoidHom.map_closure, hE.gen, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
  · rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hE.mul_self e he, map_one]
  · rintro _ ⟨e, he, rfl⟩ h1
    have heM : e ∈ M := (QuotientGroup.eq_one_iff e).1 h1
    have hord : orderOf e = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hE.mul_self e he) (hE.ne_one e he)
    have hdvd := Subgroup.orderOf_dvd_natCard M heM
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.2 hM) (even_iff_two_dvd.2 hdvd)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    refine eq_of_comm_of_cube ?_ ?_ hab ?_
    · rw [← map_mul, hE.mul_self a ha, map_one]
    · rw [← map_mul, hE.mul_self b hb, map_one]
    · rw [← map_mul, ← map_pow, hE.cube a ha b hb, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_pow, hE.cube a ha b hb, map_one]

theorem map_pairClosure {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (E : Set X) :
    (Subgroup.closure {x | ∃ a ∈ E, ∃ b ∈ E, x = a * b}).map f =
      Subgroup.closure {y | ∃ a ∈ f '' E, ∃ b ∈ f '' E, y = a * b} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, map_mul f a b⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, map_mul f a b⟩

theorem pairClosure_normal {X : Type*} [Group X] {E : Set X}
    (hconj : ∀ e ∈ E, ∀ g : X, g * e * g⁻¹ ∈ E) :
    (Subgroup.closure {x | ∃ a ∈ E, ∃ b ∈ E, x = a * b}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨g * a * g⁻¹, hconj a ha g, g * b * g⁻¹, hconj b hb g, ?_⟩
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem exists_odd_normal {X : Type u} [Group X] [Finite X] (t : X) (ht1 : t ≠ 1)
    (ht2 : t * t = 1)
    (hiso : ∀ g : X, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t) :
    ∃ N : Subgroup X, N.Normal ∧ Odd (Nat.card N) ∧ ∀ g : X, g * t * g⁻¹ * t⁻¹ ∈ N := by
  let e : Shrink.{0} X ≃* X := Shrink.mulEquiv
  have : Finite (Shrink.{0} X) := Finite.of_equiv X e.toEquiv.symm
  let := Fintype.ofFinite (Shrink.{0} X)
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar (Shrink.{0} X) (e.symm t)
    (fun h => ht1 (by simpa using congrArg e h))
    (by rw [← map_mul, ht2, map_one])
    (fun g hg => by
      apply e.injective
      simpa using hiso (e g) (by simpa using congrArg e hg))
  refine ⟨N.map e.toMonoidHom, hNn.map e.toMonoidHom e.surjective, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hNodd
  · intro g
    exact ⟨e.symm g * e.symm t * (e.symm g)⁻¹ * (e.symm t)⁻¹, hN (e.symm g), by simp⟩

theorem isPGroup_three_aux (n : ℕ) : ∀ {X : Type u} [Group X] [Finite X] (E : Set X),
    Nat.card X = n → Conditions E →
      IsPGroup 3 (Subgroup.closure {x | ∃ a ∈ E, ∃ b ∈ E, x = a * b}) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ E hn hE
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup X,
      P = Subgroup.closure {x | ∃ a ∈ E, ∃ b ∈ E, x = a * b} := ⟨_, rfl⟩
  rw [← hPdef]
  have hPn : P.Normal := hPdef ▸ pairClosure_normal hE.conj
  have hPmem : ∀ a ∈ E, ∀ b ∈ E, a * b ∈ P := fun a ha b hb =>
    hPdef ▸ Subgroup.subset_closure ⟨a, ha, b, hb, rfl⟩
  have hPle : ∀ K : Subgroup X, (∀ a ∈ E, ∀ b ∈ E, a * b ∈ K) → P ≤ K := fun K hK => by
    rw [hPdef, Subgroup.closure_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hK a ha b hb
  by_cases hP : P = ⊥
  · rw [hP]
    exact IsPGroup.of_bot
  obtain ⟨a0, ha0⟩ : E.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hP
    rw [hPdef, h]
    simp
  have hiso : ∀ g : X, (g * a0 * g⁻¹) * a0 = a0 * (g * a0 * g⁻¹) → g * a0 * g⁻¹ = a0 :=
    fun g hg => hE.noncomm _ (hE.conj a0 ha0 g) a0 ha0 hg
  obtain ⟨N, hNn, hNodd, hN⟩ :=
    exists_odd_normal a0 (hE.ne_one a0 ha0) (hE.mul_self a0 ha0) hiso
  have hEN : ∀ e ∈ E, e * a0⁻¹ ∈ N := by
    intro e he
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hE.mul_self e he)
    have hai : a0⁻¹ = a0 := inv_eq_of_mul_eq_one_right (hE.mul_self a0 ha0)
    have key : a0 * e * a0 * e * a0 = e := by
      calc a0 * e * a0 * e * a0 = a0 * e * a0 * e * a0 * (e * e) := by
            rw [hE.mul_self e he, mul_one]
        _ = (a0 * e) ^ 3 * e := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = e := by rw [hE.cube a0 ha0 e he, one_mul]
    have hconj : a0 * e * a0 * (a0 * e)⁻¹ = e := by
      rw [mul_inv_rev, hei, hai]
      calc a0 * e * a0 * (e * a0) = a0 * e * a0 * e * a0 := by simp only [mul_assoc]
        _ = e := key
    have := hN (a0 * e)
    rwa [hconj] at this
  have hPN : P ≤ N := by
    refine hPle N fun a ha b hb => ?_
    have h1 := N.mul_mem (hEN a ha) (N.inv_mem (hEN b hb))
    rwa [show a * a0⁻¹ * (b * a0⁻¹)⁻¹ = a * b by
      rw [mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_right (hE.mul_self b hb)]; group] at h1
  have hPodd : Odd (Nat.card P) := Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hPN)
  have hPsolv : Group.IsSolvable P := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hPodd
  obtain ⟨M, hMn, hMP, hMne, hMmin⟩ := CFSG.exists_minimal_normal_le P hPn hP
  have : M.Normal := hMn
  have : CFSG.IsMinimalNormal M := ⟨fun K _ hKle => by
    by_cases hK : K = ⊥
    · exact Or.inl hK
    · exact Or.inr (hMmin K inferInstance hKle hK)⟩
  have : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hMP) (Subgroup.inclusion_injective hMP)
  obtain ⟨p, hp, hpM⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian M
  have hMp : IsPGroup p M := CFSG.IsElementaryAbelian.isPGroup p M
  have hModd : Odd (Nat.card M) := Odd.of_dvd_nat hPodd (Subgroup.card_dvd_of_le hMP)
  have hlt : Nat.card (X ⧸ M) < n := by
    have h1 : 1 < Nat.card M := (Subgroup.one_lt_card_iff_ne_bot M).2 hMne
    have h2 : 0 < Nat.card (X ⧸ M) := Nat.card_pos
    rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup M]
    nlinarith
  have hQ : IsPGroup 3 (P.map (QuotientGroup.mk' M)) := by
    have := ih _ hlt ((QuotientGroup.mk' M) '' E) rfl (hE.map_quotient M hModd)
    rwa [← map_pairClosure, ← hPdef] at this
  by_cases hp3 : p = 3
  · subst hp3
    have hker : IsPGroup 3 (QuotientGroup.mk' M).ker := by
      rw [QuotientGroup.ker_mk']
      exact hMp
    exact (hQ.comap_of_ker_isPGroup (QuotientGroup.mk' M) hker).to_le
      (Subgroup.le_comap_map _ _)
  exfalso
  have hMc : ∀ m ∈ M, ∀ x : X, x * m = m * x := by
    intro m hm
    have hE' : ∀ e ∈ E, m * e = e * m := by
      intro e he
      have hb : m * e * m⁻¹ ∈ E := hE.conj e he m
      have hc3 : (e * (m * e * m⁻¹)) ^ 3 = 1 := hE.cube e he _ hb
      have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hE.mul_self e he)
      have hcM : e * (m * e * m⁻¹) ∈ M := by
        have h1 := M.mul_mem (hMn.conj_mem m hm e) (M.inv_mem hm)
        rw [hei] at h1
        simpa [mul_assoc] using h1
      obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem hMp hcM
      have hc1 : e * (m * e * m⁻¹) = 1 := eq_one_of_pow_eq_one_of_pow_eq_one hp Nat.prime_three
        hp3 hk (j := 1) (by rw [pow_one]; exact hc3)
      have h2 : m * e * m⁻¹ = e := (eq_inv_of_mul_eq_one_right hc1).trans hei
      calc m * e = (m * e * m⁻¹) * m := by group
        _ = e * m := by rw [h2]
    intro x
    have hx : x ∈ Subgroup.centralizer {m} := by
      have : Subgroup.closure E ≤ Subgroup.centralizer {m} := by
        rw [Subgroup.closure_le]
        intro e he
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hE' e he
      exact this (hE.gen ▸ Subgroup.mem_top x)
    exact (Subgroup.mem_centralizer_iff.1 hx m rfl).symm
  have hQnil : Group.IsNilpotent (P.map (QuotientGroup.mk' M)) := hQ.isNilpotent
  have hker : ((QuotientGroup.mk' M).subgroupMap P).ker ≤ Subgroup.center P := by
    intro x hx
    have hx1 : QuotientGroup.mk' M (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hxM : (x : X) ∈ M := (QuotientGroup.eq_one_iff _).1 hx1
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hMc _ hxM y)
  have hPnil : Group.IsNilpotent P := by
    have := hQnil
    exact Subgroup.isNilpotent_of_ker_le_center ((QuotientGroup.mk' M).subgroupMap P) hker
  let S : Sylow 3 P := default
  have hS : ∀ y : P, y ^ 3 = 1 → y ∈ S := by
    intro y hy
    have hz : IsPGroup 3 (Subgroup.zpowers y) := IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hy)
    obtain ⟨Q, hQle⟩ := hz.exists_le_sylow
    exact (Q.isPGroup'.le_sylow_of_normal S) (hQle (Subgroup.mem_zpowers y))
  have hPT : P ≤ (S : Subgroup P).map P.subtype := by
    refine hPle _ fun a ha b hb => ?_
    exact ⟨⟨a * b, hPmem a ha b hb⟩, hS _ (Subtype.ext (by simpa using hE.cube a ha b hb)), rfl⟩
  have hT3 : IsPGroup 3 ((S : Subgroup P).map P.subtype) := S.isPGroup'.map P.subtype
  obtain ⟨m, hm, hm1⟩ : ∃ m ∈ M, m ≠ 1 := by
    by_contra h
    apply hMne
    rw [Subgroup.eq_bot_iff_forall]
    intro m hm
    by_contra hm1
    exact h ⟨m, hm, hm1⟩
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem hMp hm
  obtain ⟨j, hj⟩ := exists_pow_eq_one_of_mem hT3 (hPT (hMP hm))
  exact hm1 (eq_one_of_pow_eq_one_of_pow_eq_one hp Nat.prime_three hp3 hk hj)

end WidthOne

theorem isPGroup_three_closure_mul {X : Type*} [Group X] [Finite X] (E : Set X)
    (hconj : ∀ e ∈ E, ∀ g : X, g * e * g⁻¹ ∈ E) (hgen : Subgroup.closure E = ⊤)
    (hsq : ∀ e ∈ E, e * e = 1) (hne : ∀ e ∈ E, e ≠ 1)
    (hnc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a → a = b)
    (h3 : ∀ a ∈ E, ∀ b ∈ E, (a * b) ^ 3 = 1) :
    IsPGroup 3 (Subgroup.closure {x | ∃ a ∈ E, ∃ b ∈ E, x = a * b}) :=
  WidthOne.isPGroup_three_aux (Nat.card X) E rfl ⟨hconj, hgen, hsq, hne, hnc, h3⟩

end CFSG.RankThree.PartOne.FIS
