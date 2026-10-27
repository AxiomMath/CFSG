module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open scoped commutatorElement

variable {F : Type*} [Group F]

@[expose] def powOneClosure (P : Subgroup F) (q : ℕ) : Subgroup F :=
  closure {x | x ∈ P ∧ x ^ q = 1}

theorem map_mem_sup_of_map_mem {X Y : Subgroup F} (f : F →* F) (hX : ∀ x ∈ X, f x ∈ X)
    (hY : ∀ y ∈ Y, f y ∈ Y) {m : F} (hm : m ∈ X ⊔ Y) : f m ∈ X ⊔ Y := by
  have h : (X ⊔ Y).map f ≤ X ⊔ Y := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (map_le_iff_le_comap.mpr hX) (map_le_iff_le_comap.mpr hY)
  exact h (mem_map_of_mem f hm)

variable {A : Type*} [Group A] (φ : A →* MulAut F)

theorem apply_mem_of_characteristic {P : Subgroup F} [P.Characteristic] (σ : MulAut F) {x : F}
    (hx : x ∈ P) : σ x ∈ P := by
  have h := characteristic_iff_map_eq.mp ‹P.Characteristic› σ
  rw [← h]
  exact mem_map_of_mem _ hx

theorem apply_mem_powOneClosure {P : Subgroup F} {q : ℕ} (σ : MulAut F)
    (hσ : ∀ x ∈ P, σ x ∈ P) {d : F} (hd : d ∈ powOneClosure P q) : σ d ∈ powOneClosure P q := by
  induction hd using closure_induction with
  | mem x hx => exact subset_closure ⟨hσ x hx.1, by rw [← map_pow, hx.2, map_one]⟩
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

variable [Finite F]

theorem mem_of_forall_primary_pow_mem (K : Subgroup F) (x : F)
    (hx : ∀ y ∈ zpowers x, (∃ q k : ℕ, q.Prime ∧ orderOf y = q ^ k) → y ∈ K) : x ∈ K := by
  induction hn : orderOf x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases h1 : n = 1
    · rw [h1, orderOf_eq_one_iff] at hn
      rw [hn]
      exact one_mem K
    have hn0 : n ≠ 0 := hn ▸ (orderOf_pos x).ne'
    obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨k, m, hqm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 q hq.ne_one
    have hcop : Nat.Coprime (q ^ k) m :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqm)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hnm
      exact hn0 hnm
    have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hnm
      exact hqm (hnm ▸ hqn)
    have hy : orderOf (x ^ m) = q ^ k := by
      rw [orderOf_pow_of_dvd hm0 (by rw [hn, hnm]; exact dvd_mul_left m (q ^ k)), hn, hnm,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    have hz : orderOf (x ^ (q ^ k)) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero k hq.ne_zero)
        (by rw [hn, hnm]; exact dvd_mul_right (q ^ k) m), hn, hnm,
        Nat.mul_div_cancel_left _ (pow_pos hq.pos k)]
    have hmn : m < n := by
      rw [hnm]
      calc m = 1 * m := (one_mul m).symm
        _ < q ^ k * m :=
          Nat.mul_lt_mul_of_pos_right (Nat.one_lt_pow hk hq.one_lt) (Nat.pos_of_ne_zero hm0)
    have hyK : x ^ m ∈ K := hx _ (pow_mem (mem_zpowers x) m) ⟨q, k, hq, hy⟩
    have hzK : x ^ (q ^ k) ∈ K := ih m hmn (x ^ (q ^ k))
      (fun y hy' hy'' => hx y (zpowers_le.mpr (pow_mem (mem_zpowers x) _) hy') hy'') hz
    have hb := Nat.gcd_eq_gcd_ab (q ^ k) m
    rw [hcop.gcd_eq_one, Nat.cast_one] at hb
    have e : x = (x ^ (q ^ k)) ^ (Nat.gcdA (q ^ k) m) * (x ^ m) ^ (Nat.gcdB (q ^ k) m) := by
      conv_lhs => rw [← zpow_one x, hb]
      rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [e]
    exact mul_mem (zpow_mem hzK _) (zpow_mem hyK _)

theorem inf_eq_bot_of_abelian_sylow {q : ℕ} [Fact q.Prime] {P : Subgroup F} [P.Characteristic]
    (hPq : IsPGroup q P) (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hirr : ∀ M : Subgroup F,
      (frattini (powOneClosure P q)).map (powOneClosure P q).subtype ≤ M →
      M ≤ powOneClosure P q → (∀ a : A, ∀ m ∈ M, φ a m ∈ M) →
      M = (frattini (powOneClosure P q)).map (powOneClosure P q).subtype ∨
        M = powOneClosure P q)
    {J : Subgroup F} (hJ : ∀ a : A, ∀ j ∈ J, φ a j ∈ J) (hDJ : ¬ powOneClosure P q ≤ J) :
    J ⊓ P = ⊥ := by
  set D := powOneClosure P q with hD
  have hDP : D ≤ P := (closure_le P).mpr fun x hx => hx.1
  have hDexp : ∀ d ∈ D, d ^ q = 1 := by
    intro d hd
    induction hd using closure_induction with
    | mem x hx => exact hx.2
    | one => exact one_pow q
    | mul x y hx hy ihx ihy =>
      rw [Commute.mul_pow (hPab x (hDP hx) y (hDP hy)) q, ihx, ihy, one_mul]
    | inv x _ ih => rw [inv_pow, ih, inv_one]
  have : IsElementaryAbelian q D :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hPab a (hDP a.2) b (hDP b.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun d => Subtype.ext (by
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        exact hDexp d d.2) }
  have : Fact (IsPGroup q D) := ⟨hPq.to_le hDP⟩
  have hΦ : (frattini D).map D.subtype = ⊥ := by
    rw [CFSG.frattini_eq_bot_of_isElementaryAbelian (p := q), Subgroup.map_bot]
  by_contra hne
  have hdvd : q ∣ Nat.card (J ⊓ P : Subgroup F) := by
    obtain ⟨k, hk⟩ := (hPq.to_le inf_le_right : IsPGroup q (J ⊓ P : Subgroup F)).exists_card_eq
    rcases k with _ | k
    · exact absurd ((card_eq_one).mp (hk.trans (pow_zero q))) hne
    · rw [hk]
      exact dvd_pow_self q k.succ_ne_zero
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have hz' : orderOf (z : F) = q := by rw [Subgroup.orderOf_coe, hz]
  have hz1 : (z : F) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz'
    exact (Fact.out : q.Prime).one_lt.ne hz'
  have hzD : (z : F) ∈ D :=
    subset_closure ⟨(mem_inf.mp z.2).2, by rw [← hz']; exact pow_orderOf_eq_one _⟩
  rcases hirr (J ⊓ D) (by rw [hΦ]; exact bot_le) inf_le_right
      (fun a m hm => mem_inf.mpr ⟨hJ a m (mem_inf.mp hm).1,
        apply_mem_powOneClosure (φ a) (fun x hx => apply_mem_of_characteristic (φ a) hx)
          (mem_inf.mp hm).2⟩) with hM | hM
  · rw [hΦ] at hM
    have h1 : (z : F) ∈ J ⊓ D := mem_inf.mpr ⟨(mem_inf.mp z.2).1, hzD⟩
    rw [hM, mem_bot] at h1
    exact hz1 h1
  · exact hDJ (inf_eq_right.mp hM)

theorem inf_le_commutator_of_cube_sylow {q : ℕ} [Fact q.Prime] {P : Subgroup F} [P.Characteristic]
    (hnc : ∃ a b : P, a * b ≠ b * a) (hcard : Nat.card P = q ^ 3) (hexp : ∀ x ∈ P, x ^ q = 1)
    (hirr : ∀ M : Subgroup F,
      (frattini (powOneClosure P q)).map (powOneClosure P q).subtype ≤ M →
      M ≤ powOneClosure P q → (∀ a : A, ∀ m ∈ M, φ a m ∈ M) →
      M = (frattini (powOneClosure P q)).map (powOneClosure P q).subtype ∨
        M = powOneClosure P q)
    {J : Subgroup F} (hJ : ∀ a : A, ∀ j ∈ J, φ a j ∈ J) (hDJ : ¬ powOneClosure P q ≤ J) :
    J ⊓ P ≤ ⁅P, P⁆ := by
  have hD : powOneClosure P q = P := by
    unfold powOneClosure
    rw [show {x : F | x ∈ P ∧ x ^ q = 1} = (P : Set F) from
      Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, hexp x h⟩⟩, closure_eq]
  rw [hD] at hirr hDJ
  obtain ⟨hcomm, -, hQab, hQpow, -⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure hcard hnc
  have hΦZ : frattini P ≤ center P := by
    have : IsElementaryAbelian q (P ⧸ center P) :=
      { toIsMulCommutative := ⟨⟨hQab⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hQpow }
    have : Fact (IsPGroup q (P ⧸ center P)) :=
      ⟨(IsPGroup.of_card hcard).of_surjective _ (QuotientGroup.mk'_surjective (center P))⟩
    have h1 := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective (center P))
    rwa [CFSG.frattini_eq_bot_of_isElementaryAbelian (R := P ⧸ center P) (p := q),
      MonoidHom.comap_bot,
      QuotientGroup.ker_mk'] at h1
  have hΦA : ∀ a : A, ∀ m ∈ (frattini P).map P.subtype, φ a m ∈ (frattini P).map P.subtype := by
    rintro a _ ⟨f, hf, rfl⟩
    exact ⟨MulAut.characteristic P (φ a) f,
      apply_mem_of_characteristic (MulAut.characteristic P (φ a)) hf, rfl⟩
  have hJPA : ∀ a : A, ∀ m ∈ J ⊓ P, φ a m ∈ J ⊓ P := fun a m hm =>
    mem_inf.mpr ⟨hJ a m (mem_inf.mp hm).1, apply_mem_of_characteristic (φ a) (mem_inf.mp hm).2⟩
  rcases hirr ((J ⊓ P) ⊔ (frattini P).map P.subtype) le_sup_right
      (sup_le inf_le_right (map_subtype_le _))
      (fun a m hm => map_mem_sup_of_map_mem (φ a).toMonoidHom (hJPA a) (hΦA a) hm) with hM | hM
  · calc J ⊓ P ≤ (J ⊓ P) ⊔ (frattini P).map P.subtype := le_sup_left
      _ = (frattini P).map P.subtype := hM
      _ ≤ (center P).map P.subtype := map_mono hΦZ
      _ = ⁅P, P⁆ := by rw [← hcomm, map_subtype_commutator]
  · exfalso
    apply hDJ
    have h1 : J.subgroupOf P ⊔ frattini P = ⊤ := by
      apply map_injective (subtype_injective P)
      rw [Subgroup.map_sup, subgroupOf_map_subtype, hM, ← MonoidHom.range_eq_map,
        range_subtype]
    have h2 := frattini_nongenerating h1
    intro x hx
    have h3 : (⟨x, hx⟩ : P) ∈ J.subgroupOf P := h2 ▸ mem_top _
    exact mem_subgroupOf.mp h3

end CFSG.Quasithin.SteinbergCC
