module

public import CFSG.Walter.J1Props.Facts

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1Recog CFSG.Open Word

theorem exists_zpowers_sup_eq {L : Type*} [Group L] (P : Subgroup L) (h : IsCyclic (normQuot P)) :
    ∃ g ∈ Subgroup.normalizer (P : Set L),
      Subgroup.zpowers g ⊔ Subgroup.centralizer (P : Set L) = Subgroup.normalizer (P : Set L) := by
  obtain ⟨q, hq⟩ := h.exists_generator
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, g.2, le_antisymm (sup_le (Subgroup.zpowers_le.mpr g.2)
    (Subgroup.centralizer_le_normalizer _)) ?_⟩
  intro n hn
  obtain ⟨k, hk⟩ := hq (QuotientGroup.mk ⟨n, hn⟩)
  have hk' : ((g ^ k)⁻¹ * ⟨n, hn⟩ : Subgroup.normalizer (P : Set L)) ∈
      (Subgroup.centralizer (P : Set L)).subgroupOf (Subgroup.normalizer (P : Set L)) := by
    rw [← QuotientGroup.eq]
    rw [← hk, QuotientGroup.mk_zpow]
  rw [Subgroup.mem_subgroupOf] at hk'
  have : n = (g : L) ^ k * (((g ^ k)⁻¹ * ⟨n, hn⟩ : Subgroup.normalizer (P : Set L)) : L) := by
    simp
  rw [this]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) hk'

theorem card_sylow_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (P : Sylow p walterJ1) :
    Nat.card (P : Subgroup walterJ1) = 1 ∨ Nat.card (P : Subgroup walterJ1) = p := by
  by_cases hd : p ∣ 175560
  · right
    have hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
      rcases prime_dvd_card (Fact.out : p.Prime) hd with h | h
      · exact absurd h hp2
      · exact h
    obtain ⟨g, hg⟩ := exists_eq_zpowers_conj hp P
    rw [hg, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_yJ hp]
  · left
    rw [sylow_eq_bot_of_not_dvd hd P, Subgroup.card_bot]

theorem arith_centralizer :
    ∀ pe ∈ [(7, 6), (11, 10), (19, 6)], ∀ a ∈ Nat.divisors 1463, ∀ k ∈ Nat.divisors 120,
      pe.1 ∣ a → pe.2 ∣ k → a ∣ 175560 / (a * k) - 1 → 175560 / (a * k) ≠ 1 → a = pe.1 := by
  decide +kernel

theorem card_normalizer_eq_mul {L : Type*} [Group L] (Q : Subgroup L) :
    Nat.card (Subgroup.normalizer (Q : Set L)) =
      Nat.card (normQuot Q) * Nat.card (Subgroup.centralizer (Q : Set L)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.centralizer (Q : Set L)).subgroupOf (Subgroup.normalizer (Q : Set L))),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (Q : Set L))).toEquiv]

theorem normalizer_le_normalizer_centralizer {L : Type*} [Group L] (H : Subgroup L) :
    Subgroup.normalizer (H : Set L) ≤
      Subgroup.normalizer ((Subgroup.centralizer (H : Set L) : Subgroup L) : Set L) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro y
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hy h hh
    have hh' : g⁻¹ * h * g ∈ H := (hg _).mpr (by
      rw [show g * (g⁻¹ * h * g) * g⁻¹ = h by group]
      exact hh)
    calc h * (g * y * g⁻¹) = g * ((g⁻¹ * h * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * h * g)) * g⁻¹ := by rw [hy _ hh']
      _ = g * y * g⁻¹ * h := by group
  · intro hy h hh
    have := hy _ ((hg h).mp hh)
    have h2 : g * (h * y) * g⁻¹ = g * (y * h) * g⁻¹ := by
      calc g * (h * y) * g⁻¹ = g * h * g⁻¹ * (g * y * g⁻¹) := by group
        _ = g * y * g⁻¹ * (g * h * g⁻¹) := this
        _ = g * (y * h) * g⁻¹ := by group
    simpa using h2

theorem centralizer_zpowers_eq {L : Type*} [Group L] (x : L) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup L) : Set L) =
      Subgroup.centralizer ({x} : Set L) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem centralizer_sylow_eq
    {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 11 ∨ p = 19)
    (P : Sylow p walterJ1) :
    Subgroup.centralizer ((P : Subgroup walterJ1) : Set walterJ1) = P := by
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
    rcases hp with rfl | rfl | rfl <;> simp
  obtain ⟨g, hg⟩ := exists_eq_zpowers_conj hp' P
  set x := g * yJ p * g⁻¹ with hx
  set t := g * iJ p * g⁻¹ with ht
  have hxo : orderOf x = p := by
    rw [hx, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_yJ hp']
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxo
    exact (Fact.out : p.Prime).one_lt.ne hxo
  have hx30 : Nat.Coprime (orderOf x) 30 := by
    rw [hxo]
    rcases hp with rfl | rfl | rfl <;> norm_num
  obtain ⟨hi, hiy⟩ := iJ_inv hp'
  have hto : orderOf t = 2 := by rw [ht, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hi]
  have htx : t * x * t⁻¹ = x⁻¹ := by
    rw [ht, hx, show g * iJ p * g⁻¹ * (g * yJ p * g⁻¹) * (g * iJ p * g⁻¹)⁻¹ =
      g * (iJ p * yJ p * (iJ p)⁻¹) * g⁻¹ by group, hiy]
    group
  set A := Subgroup.centralizer ({x} : Set walterJ1) with hA
  have hCP : Subgroup.centralizer ((P : Subgroup walterJ1) : Set walterJ1) = A := by
    rw [hg, centralizer_zpowers_eq]
  rw [hCP]
  have hPA : (P : Subgroup walterJ1) ≤ A := by
    rw [hg, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  set N := Subgroup.normalizer ((A : Subgroup walterJ1) : Set walterJ1)
  have hk := jankoHyp.card_normalizer_eq hx1 hx30 hto htx
  have hmod := jankoHyp.dvd_index_sub_one hx1 hx30 hto htx
  have hA30 := jankoHyp.coprime_card_centralizer hx1 hx30
  set k := Nat.card (N ⊓ Subgroup.centralizer ({t} : Set walterJ1) : Subgroup walterJ1)
  have hk120 : k ∣ 120 := by
    rw [← card_centralizer_of_orderOf_eq_two hto]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hpA : p ∣ Nat.card A := by
    rw [← hxo]
    exact Subgroup.orderOf_dvd_natCard A (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hA1463 : Nat.card A ∣ 1463 := by
    have h1 : Nat.card A ∣ 120 * 1463 := by
      rw [show 120 * 1463 = 175560 by norm_num, ← card_walterJ1]
      exact Subgroup.card_subgroup_dvd_card A
    exact (Nat.Coprime.dvd_of_dvd_mul_left (J1.JankoHyp.coprime_of_coprime_thirty hA30) h1)
  set e := Nat.card (normQuot (P : Subgroup walterJ1))
  have he : e ∣ k := by
    have hNP : Subgroup.normalizer ((P : Subgroup walterJ1) : Set walterJ1) ≤ N := by
      rw [hg]
      exact normalizer_le_normalizer_centralizer _ |>.trans (by rw [centralizer_zpowers_eq])
    have h1 := Subgroup.card_dvd_of_le hNP
    rw [card_normalizer_eq_mul, hk, hCP] at h1
    have hpos : 0 < Nat.card A := Nat.card_pos
    rw [mul_comm] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hpos h1
  have hidx : N.index = 175560 / (Nat.card A * k) := by
    have := N.card_mul_index
    rw [hk, card_walterJ1] at this
    have hpos : 0 < Nat.card A * k := Nat.mul_pos Nat.card_pos Nat.card_pos
    rw [← this, Nat.mul_div_cancel_left _ hpos]
  have hne1 : N.index ≠ 1 := by
    intro h1
    have hN : N = ⊤ := Subgroup.index_eq_one.mp h1
    have : A.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact hN
    rcases isSimpleGroup_walterJ1.eq_bot_or_eq_top_of_normal A with h0 | h0
    · have : x ∈ A := Subgroup.mem_centralizer_singleton_iff.mpr rfl
      rw [h0, Subgroup.mem_bot] at this
      exact hx1 this
    · rw [h0, Subgroup.card_top, card_walterJ1] at hA1463
      norm_num at hA1463
  have he' : e = if p = 11 then 10 else 6 := by
    rcases hp with rfl | rfl | rfl
    · exact (J2_seven P).2
    · exact (J2_eleven P).2
    · exact (J2_nineteen P).2
  have hcard : Nat.card A = p := by
    have harith := arith_centralizer
    rw [hidx] at hmod hne1
    have hAd : Nat.card A ∈ Nat.divisors 1463 := Nat.mem_divisors.mpr ⟨hA1463, by norm_num⟩
    have hkd : k ∈ Nat.divisors 120 := Nat.mem_divisors.mpr ⟨hk120, by norm_num⟩
    rcases hp with rfl | rfl | rfl
    · exact harith (7, 6) (by simp) _ hAd k hkd hpA (by rw [he'] at he; simpa using he) hmod hne1
    · exact harith (11, 10) (by simp) _ hAd k hkd hpA (by rw [he'] at he; simpa using he) hmod hne1
    · exact harith (19, 6) (by simp) _ hAd k hkd hpA (by rw [he'] at he; simpa using he) hmod hne1
  refine (Subgroup.eq_of_le_of_card_ge hPA ?_).symm
  rw [hcard, hg, Nat.card_zpowers, hxo]

theorem isSolvable_of_abelian_index_two {G : Type*} [Group G] {H A : Subgroup G} [Finite H]
    (hAH : A ≤ H) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hidx : Nat.card A * 2 = Nat.card H) :
    Group.IsSolvable H := by
  have : Finite A := Finite.of_injective _ (Subgroup.inclusion_injective hAH)
  set A' := A.subgroupOf H
  have hA'idx : A'.index = 2 := by
    have h := A'.card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv] at h
    have hpos : 0 < Nat.card A := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h.trans hidx.symm)
  have hn : A'.Normal := Subgroup.normal_of_index_eq_two hA'idx
  have h1 : Group.IsSolvable A' := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext (hA _ a.2 _ b.2))
  have h2 : Group.IsSolvable (H ⧸ A') := by
    have hcyc : IsCyclic (H ⧸ A') := isCyclic_of_prime_card (p := 2) (hp := ⟨Nat.prime_two⟩)
      (by rw [← Subgroup.index_eq_card, hA'idx])
    exact Group.isSolvable_of_comm fun a b => mul_comm' a b
  exact Group.isSolvable_of_ker_le_range A'.subtype (QuotientGroup.mk' A')
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_centralizer
    {x : walterJ1} (hx1 : x ≠ 1) (hodd : Odd (orderOf x)) :
    Group.IsSolvable (Subgroup.centralizer ({x} : Set walterJ1)) := by
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h))
  have : Fact p.Prime := ⟨hp⟩
  set y := x ^ (orderOf x / p) with hy
  have hyo : orderOf y = p := orderOf_pow_orderOf_div (orderOf_pos x).ne' hpx
  have hle : Subgroup.centralizer ({x} : Set walterJ1) ≤
      Subgroup.centralizer ({y} : Set walterJ1) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    exact (Commute.pow_left (hz : Commute z x).symm _).symm
  suffices hs : Group.IsSolvable (Subgroup.centralizer ({y} : Set walterJ1)) from
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpx)
  have hpd : p ∣ 175560 := by
    rw [← hyo, ← card_walterJ1]
    exact orderOf_dvd_natCard y
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  have hX : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyo]
  rcases prime_dvd_card hp hpd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  all_goals first
    | (obtain ⟨u, hu, hXu⟩ := jankoHyp.exists_involution_of_card (Or.inl rfl) hX
       obtain ⟨-, A, -, -, -, hAC, -, -, hA2, -, habel, -⟩ :=
         jankoHyp.bender_4_1_of_centralizer (Or.inl rfl) hX hu hXu
       rw [centralizer_zpowers_eq] at hAC hA2
       exact isSolvable_of_abelian_index_two hAC habel hA2)
    | (obtain ⟨u, hu, hXu⟩ := jankoHyp.exists_involution_of_card (Or.inr rfl) hX
       obtain ⟨-, A, -, -, -, hAC, -, -, hA2, -, habel, -⟩ :=
         jankoHyp.bender_4_1_of_centralizer (Or.inr rfl) hX hu hXu
       rw [centralizer_zpowers_eq] at hAC hA2
       exact isSolvable_of_abelian_index_two hAC habel hA2)
    | (have hy30 : Nat.Coprime (orderOf y) 30 := by rw [hyo]; norm_num
       have hS : IsPGroup _ (Subgroup.zpowers y) := IsPGroup.of_card (n := 1) (by rw [hX, pow_one])
       obtain ⟨t, ht, hty⟩ := J2_inverted hp2 (hS.toSylow (not_dvd_index_of_card (by simp) hX))
       have htyy : t * y * t⁻¹ = y⁻¹ := hty y (Subgroup.mem_zpowers y)
       exact Group.isSolvable_of_comm fun a b => Subtype.ext
         (jankoHyp.commute_of_mem_centralizer hy1 hy30 ht htyy a.2 b.2))

end CFSG.Walter.J1Props
