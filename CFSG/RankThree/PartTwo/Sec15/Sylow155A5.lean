module

public import CFSG.GroupTheory.AlternatingFive.SylowTwo

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155A5

open scoped Pointwise

open Equiv CFSG.GroupTheory.AlternatingFive

local notation "A₅" => alternatingGroup (Fin 5)

theorem mem_alternatingGroup_of_pow_three {n : ℕ} {z : Perm (Fin n)} (hz : z ^ 3 = 1) :
    z ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h := congrArg Equiv.Perm.sign hz
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign z) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem eq_zpowers_of_isPGroup_three {P : Subgroup (Perm (Fin 5))} (hP : IsPGroup 3 P)
    {t : Perm (Fin 5)} (ht : t ∈ P) (ht1 : t ≠ 1) :
    P = Subgroup.zpowers t ∧ orderOf t = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : Nat.card P ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card P
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · exfalso
        apply ht1
        have hP1 : P = ⊥ := Subgroup.eq_bot_of_card_eq P (by simpa using hk)
        have : t ∈ (⊥ : Subgroup (Perm (Fin 5))) := hP1 ▸ ht
        simpa using this
      · rfl
    · exfalso
      have h9 : 9 ∣ Nat.card P := by
        rw [hk]
        exact (pow_dvd_pow 3 hk2)
      have := h9.trans hdvd
      omega
  subst hk1
  have hcard : Nat.card P = 3 := by simpa using hk
  have hord : orderOf t = 3 := by
    have h1 : orderOf t ∣ 3 := hcard ▸ Subgroup.orderOf_dvd_natCard P ht
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  refine ⟨?_, hord⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ht)
  rw [Nat.card_zpowers, hord, hcard]

private lemma zpowers_eq_of_orderOf_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hlt : Nat.card G < p ^ 2) {a b : G} (ha : orderOf a = p) (hb : orderOf b = p) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  have hdvd : p ∣ Nat.card G := ha ▸ orderOf_dvd_natCard a
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hp2 : 2 ≤ p := hp.out.two_le
  have hP : ∀ P : Sylow p G, Nat.card P = p := by
    intro P
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hpk : p ∣ Nat.card P := P.dvd_card_of_dvd_card hdvd
    have hPG : Nat.card P ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · exfalso
          rw [hk, pow_zero] at hpk
          exact hp.out.not_dvd_one hpk
        · rfl
      · exfalso
        have h2 : p ^ 2 ∣ Nat.card G := (hk ▸ pow_dvd_pow p hk2).trans hPG
        exact absurd (Nat.le_of_dvd hpos h2) (by omega)
    rw [hk, hk1, pow_one]
  have hsub : Subsingleton (Sylow p G) := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
    have h1 : P.index * p = Nat.card G := by
      have h := (P : Subgroup G).index_mul_card
      rwa [hP P] at h
    have h2 : P.index < p := by
      rw [pow_two] at hlt
      exact Nat.lt_of_mul_lt_mul_right (h1 ▸ hlt)
    have h3 : Nat.card (Sylow p G) ∣ P.index := P.card_dvd_index
    have hidx : 0 < P.index := by
      rcases Nat.eq_zero_or_pos P.index with h | h
      · rw [h] at h1
        omega
      · exact h
    have h5 : Nat.card (Sylow p G) ≤ P.index := Nat.le_of_dvd hidx h3
    have h4 : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
    have h6 : Nat.card (Sylow p G) = 1 := by
      unfold Nat.ModEq at h4
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h4
      exact h4
    exact (Nat.card_eq_one_iff_unique.mp h6).1
  have hcyc : ∀ {c : G}, orderOf c = p → IsPGroup p (Subgroup.zpowers c) := fun {c} hc =>
    IsPGroup.of_card (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨Pa, hPa⟩ := IsPGroup.exists_le_sylow (hcyc ha)
  obtain ⟨Pb, hPb⟩ := IsPGroup.exists_le_sylow (hcyc hb)
  obtain rfl : Pa = Pb := Subsingleton.elim _ _
  rw [Subgroup.eq_of_le_of_card_ge hPa (by rw [hP Pa, Nat.card_zpowers, ha]),
    Subgroup.eq_of_le_of_card_ge hPb (by rw [hP Pa, Nat.card_zpowers, hb])]

private lemma no_normalize :
    ∀ x z : A₅, x ^ 3 = 1 → x ≠ 1 → z ≠ 1 → (z ^ 2 = 1 ∨ z ^ 5 = 1) →
      ∀ j : Fin 5, x * z * x⁻¹ ≠ z ^ (j : ℕ) := by
  decide +kernel

private lemma card_A5 : Nat.card A₅ = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private lemma not_mem_zpowers {x z : A₅} (hx : orderOf x = 3)
    (hz : orderOf z = 2 ∨ orderOf z = 5) : x * z * x⁻¹ ∉ Subgroup.zpowers z := by
  intro h
  rw [mem_zpowers_iff_mem_range_orderOf] at h
  obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp h
  have hj5 : j < 5 := by
    rw [Finset.mem_range] at hj
    rcases hz with h | h <;> omega
  have hx3 : x ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one x
    rwa [hx] at h1
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hz' : z ^ 2 = 1 ∨ z ^ 5 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rcases hz with h | h <;> rw [h] at h1
    · exact Or.inl h1
    · exact Or.inr h1
  exact no_normalize x z hx3 hx1 hz1 hz' ⟨j, hj5⟩ hjz.symm

private lemma false_of_prime_dvd {x : A₅} (hx : orderOf x = 3) {W : Subgroup A₅}
    (hN : x ∈ Subgroup.normalizer (W : Set A₅)) {p : ℕ} [hp : Fact p.Prime]
    (hp25 : p = 2 ∨ p = 5) (hdvd : p ∣ Nat.card W) (hlt : Nat.card W < p ^ 2) : False := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := W) p hdvd
  have hxz : x * (z : A₅) * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hN _).mp z.2
  have hz' : orderOf (z : A₅) = p := by rw [Subgroup.orderOf_coe]; exact hz
  have hord : orderOf (⟨x * (z : A₅) * x⁻¹, hxz⟩ : W) = p := by
    rw [Subgroup.orderOf_mk, ← hz']
    exact (SemiconjBy.orderOf_eq x (x := (z : A₅)) (y := x * (z : A₅) * x⁻¹)
      (by simp [SemiconjBy, mul_assoc])).symm
  have hmem : (⟨x * (z : A₅) * x⁻¹, hxz⟩ : W) ∈ Subgroup.zpowers z :=
    (zpowers_eq_of_orderOf_eq hlt hord hz) ▸ Subgroup.mem_zpowers _
  have hmem' : x * (z : A₅) * x⁻¹ ∈ Subgroup.zpowers (z : A₅) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  exact not_mem_zpowers hx (by rcases hp25 with rfl | rfl <;> simp [hz']) hmem'

private lemma eq_bot_or_exists_sylow {x : A₅} (hx : orderOf x = 3) {W : Subgroup A₅}
    (hW3 : ¬ 3 ∣ Nat.card W) (hN : x ∈ Subgroup.normalizer (W : Set A₅)) :
    W = ⊥ ∨ ∃ P : Sylow 2 A₅, (P : Subgroup A₅) = W ∧ x • P = P := by
  have hdvd : Nat.card W ∣ 60 := by
    rw [← card_A5]
    exact Subgroup.card_subgroup_dvd_card W
  have hle : Nat.card W ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : Nat.card W = 1 ∨ Nat.card W = 2 ∨ Nat.card W = 4 ∨ Nat.card W = 5 ∨
      Nat.card W = 10 ∨ Nat.card W = 20 := by
    generalize Nat.card W = n at hdvd hle hW3 ⊢
    interval_cases n <;> omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases hcases with h | h | h | h | h | h
  · exact Or.inl (Subgroup.eq_bot_of_card_eq W h)
  · exact (false_of_prime_dvd hx hN (p := 2) (Or.inl rfl) (by rw [h]) (by rw [h]; norm_num)).elim
  · right
    have hP : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [h]; norm_num)
    obtain ⟨P, hPle⟩ := hP.exists_le_sylow
    have hPW : (P : Subgroup A₅) = W :=
      (Subgroup.eq_of_le_of_card_ge hPle (by rw [card_sylow_two_eq P, h])).symm
    refine ⟨P, hPW, ?_⟩
    rw [Sylow.smul_eq_iff_mem_normalizer]
    change x ∈ Subgroup.normalizer ((P : Subgroup A₅) : Set A₅)
    rw [hPW]
    exact hN
  · exact (false_of_prime_dvd hx hN (p := 5) (Or.inr rfl) (by rw [h]) (by rw [h]; norm_num)).elim
  · exact (false_of_prime_dvd hx hN (p := 5) (Or.inr rfl) (by rw [h]; norm_num)
      (by rw [h]; norm_num)).elim
  · exact (false_of_prime_dvd hx hN (p := 5) (Or.inr rfl) (by rw [h]; norm_num)
      (by rw [h]; norm_num)).elim

private lemma exists_swap_A5 {x : A₅} (hx : orderOf x = 3) {R V : Subgroup A₅}
    (hR3 : ¬ 3 ∣ Nat.card R) (hV3 : ¬ 3 ∣ Nat.card V)
    (hR : x ∈ Subgroup.normalizer (R : Set A₅)) (hV : x ∈ Subgroup.normalizer (V : Set A₅)) :
    ∃ u : A₅, u * x * u⁻¹ ∈ Subgroup.zpowers x ∧ (R = ⊥ ∨ ∀ v ∈ V, u * v * u⁻¹ ∈ R) := by
  have hx1 : (1 : A₅) * x * (1 : A₅)⁻¹ ∈ Subgroup.zpowers x := by
    simpa using Subgroup.mem_zpowers x
  rcases eq_bot_or_exists_sylow hx hR3 hR with hR0 | ⟨PR, hPR, hxPR⟩
  · exact ⟨1, hx1, Or.inl hR0⟩
  rcases eq_bot_or_exists_sylow hx hV3 hV with hV0 | ⟨PV, hPV, hxPV⟩
  · refine ⟨1, hx1, Or.inr fun v hv => ?_⟩
    rw [hV0, Subgroup.mem_bot] at hv
    subst hv
    simp
  by_cases hPVR : PV = PR
  · refine ⟨1, hx1, Or.inr fun v hv => ?_⟩
    rw [one_mul, inv_one, mul_one, ← hPR, ← hPVR, hPV]
    exact hv
  · obtain ⟨u, -, -, hux, hu⟩ := exists_swap_of_orderOf_eq_three hx hxPV hxPR hPVR
    refine ⟨u, hux, Or.inr fun v hv => ?_⟩
    have h1 : MulAut.conj u • v ∈ MulAut.conj u • (PV : Subgroup A₅) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (by rw [hPV]; exact hv)
    rw [← Sylow.coe_subgroup_smul, hu, hPR] at h1
    simpa [MulAut.smul_def] using h1

theorem exists_swap {t : Perm (Fin 5)} (ht : t ∈ alternatingGroup (Fin 5)) (ht3 : orderOf t = 3)
    {R V : Subgroup (Perm (Fin 5))} (hRA : R ≤ alternatingGroup (Fin 5))
    (hVA : V ≤ alternatingGroup (Fin 5)) (hR3 : ¬ 3 ∣ Nat.card R) (hV3 : ¬ 3 ∣ Nat.card V)
    (hR : t ∈ Subgroup.normalizer (R : Set (Perm (Fin 5))))
    (hV : t ∈ Subgroup.normalizer (V : Set (Perm (Fin 5)))) :
    ∃ n ∈ alternatingGroup (Fin 5), n * t * n⁻¹ ∈ Subgroup.zpowers t ∧
      V.map (MulAut.conj n).toMonoidHom ≤ Subgroup.normalizer (R : Set (Perm (Fin 5))) := by
  let x : A₅ := ⟨t, ht⟩
  have hx : orderOf x = 3 := by
    rw [show x = ⟨t, ht⟩ from rfl, Subgroup.orderOf_mk, ht3]
  have hnorm : ∀ {W : Subgroup (Perm (Fin 5))},
      t ∈ Subgroup.normalizer (W : Set (Perm (Fin 5))) →
      x ∈ Subgroup.normalizer
        ((W.subgroupOf (alternatingGroup (Fin 5)) : Subgroup A₅) : Set A₅) := by
    intro W hW
    rw [Subgroup.mem_normalizer_iff] at hW ⊢
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hW (h : Perm (Fin 5))
  have hcard : ∀ {W : Subgroup (Perm (Fin 5))}, W ≤ alternatingGroup (Fin 5) →
      Nat.card (W.subgroupOf (alternatingGroup (Fin 5))) = Nat.card W := fun hW =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW).toEquiv
  obtain ⟨u, hux, hu⟩ := exists_swap_A5 hx (by rwa [hcard hRA]) (by rwa [hcard hVA])
    (hnorm hR) (hnorm hV)
  refine ⟨(u : Perm (Fin 5)), u.2, ?_, ?_⟩
  · have h := Subgroup.mem_map_of_mem (alternatingGroup (Fin 5)).subtype hux
    rw [MonoidHom.map_zpowers] at h
    exact h
  · rcases hu with hR0 | hu
    · have hR1 : Nat.card R = 1 := by
        rw [← hcard hRA, hR0, Subgroup.card_bot]
      rw [Subgroup.eq_bot_of_card_eq R hR1, Subgroup.normalizer_eq_top]
      exact le_top
    · intro y hy
      obtain ⟨a, haV, rfl⟩ := Subgroup.mem_map.mp hy
      have h := hu ⟨a, hVA haV⟩ (by rwa [Subgroup.mem_subgroupOf])
      rw [Subgroup.mem_subgroupOf] at h
      exact Subgroup.le_normalizer (by simpa using h)

end CFSG.RankThree.PartTwo.Sec15.Sylow155A5
