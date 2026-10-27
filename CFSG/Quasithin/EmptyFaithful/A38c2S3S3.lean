module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin

open Equiv Equiv.Perm

theorem no_even_order_six_fixed {m : Perm (Fin 7)} (hm : m.sign = 1) (h6 : orderOf m = 6)
    (f : Fin 7) (hf : m f = f) : False := by
  have hlcm : m.cycleType.lcm = 6 := by rw [Equiv.Perm.lcm_cycleType, h6]
  have hsum : m.cycleType.sum = m.support.card := Equiv.Perm.sum_cycleType m
  have hsupp : m.support.card ≤ 6 := by
    have h1 : m.support ⊆ Finset.univ.erase f := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ x⟩
      rintro rfl
      exact (Equiv.Perm.mem_support.mp hx) hf
    simpa using Finset.card_le_card h1
  have hsign := Equiv.Perm.sign_of_cycleType m
  rw [hm] at hsign
  have heven : Even (m.cycleType.sum + Multiset.card m.cycleType) := by
    rw [← neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)]
    exact hsign.symm
  have h2 : ∀ n ∈ m.cycleType, 2 ≤ n := fun n hn => Equiv.Perm.two_le_of_mem_cycleType hn
  generalize m.cycleType = s at *
  have hs6 : s.sum ≤ 6 := hsum ▸ hsupp
  have hcard : Multiset.card s ≤ 3 := by
    have := Multiset.card_nsmul_le_sum h2
    simp only [smul_eq_mul] at this
    omega
  interval_cases hc : Multiset.card s
  · have : s = 0 := Multiset.card_eq_zero.mp hc
    subst this
    simp at hlcm
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hc
    simp at hlcm heven hs6
    subst hlcm
    exact absurd heven (by decide)
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc
    have ha := h2 a (by simp)
    have hb := h2 b (by simp)
    simp at hlcm heven hs6
    have ha6 : a ≤ 4 := by omega
    have hb6 : b ≤ 4 := by omega
    clear hsign hsum h2 hc
    interval_cases a <;> interval_cases b <;>
      first | (exfalso; revert hlcm; decide) | (exfalso; revert heven; decide)
  · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hc
    have ha := h2 a (by simp)
    have hb := h2 b (by simp)
    have hc' := h2 c (by simp)
    simp at hlcm heven hs6
    have ha6 : a = 2 := by omega
    have hb6 : b = 2 := by omega
    have hc6 : c = 2 := by omega
    subst ha6 hb6 hc6
    simp at hlcm

theorem exists_unique_fixed_point_of_card_nine {P : Subgroup (Perm (Fin 7))} (hP : Nat.card P = 9) :
    ∃ f : Fin 7, ∀ x, (∀ p ∈ P, p x = x) ↔ x = f := by
  classical
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  let F : Set (Fin 7) := {x | ∀ p ∈ P, p x = x}
  have hF : MulAction.fixedPoints P (Fin 7) = F := by
    ext x
    simp [MulAction.mem_fixedPoints, F]
  have hmod := hP3.card_modEq_card_fixedPoints (α := Fin 7)
  rw [hF, Nat.card_fin] at hmod
  have hF7 : Nat.card F ≤ 7 := by
    have := Nat.card_le_card_of_injective (Subtype.val : F → Fin 7) Subtype.val_injective
    simpa using this
  have hbound : 9 ≤ (7 - Nat.card F).factorial := by
    let e := Equiv.Perm.subtypeEquivSubtypePerm (fun a : Fin 7 => a ∉ F)
    have hcard : Nat.card {f : Perm (Fin 7) // ∀ a, ¬ (a ∉ F) → f a = a} =
        (Nat.card {a : Fin 7 // a ∉ F}).factorial := by
      rw [← Nat.card_perm, Nat.card_congr e.symm]
    have hsub : Nat.card {a : Fin 7 // a ∉ F} = 7 - Nat.card F := by
      have h1 : Nat.card ↥Fᶜ = Fᶜ.ncard := Nat.card_coe_set_eq _
      have h2 : Nat.card ↥F = F.ncard := Nat.card_coe_set_eq _
      have h3 := Set.ncard_compl F
      rw [Nat.card_fin] at h3
      rw [h2, ← h3, ← h1]
      rfl
    have hinj : Function.Injective (fun p : P => (⟨(p : Perm (Fin 7)), fun a ha => by
        have : a ∈ F := not_not.mp ha
        exact this p p.2⟩ : {f : Perm (Fin 7) // ∀ a, ¬ (a ∉ F) → f a = a})) := by
      intro p q h
      exact Subtype.ext (Subtype.mk.inj h)
    calc 9 = Nat.card P := hP.symm
      _ ≤ Nat.card {f : Perm (Fin 7) // ∀ a, ¬ (a ∉ F) → f a = a} :=
          Nat.card_le_card_of_injective _ hinj
      _ = (7 - Nat.card F).factorial := by rw [hcard, hsub]
  have h1 : Nat.card F = 1 := by
    generalize Nat.card ↥F = n at hmod hF7 hbound
    interval_cases n <;> first | rfl | (exfalso; revert hmod; decide) | (exfalso; revert hbound; decide)
  obtain ⟨hsub, hne⟩ := Nat.card_eq_one_iff_unique.mp h1
  obtain ⟨f⟩ := hne
  refine ⟨f.1, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : F) f)
  · rw [hx]; exact f.2

abbrev altThreeProd : Subgroup (Perm (Fin 3) × Perm (Fin 3)) :=
  (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))

theorem card_altThreeProd : Nat.card altThreeProd = 9 := by
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  have : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  rw [this]

set_option maxRecDepth 10000 in
theorem s3s3_pow_three_of_pow_nine : ∀ x : Perm (Fin 3) × Perm (Fin 3), x ^ 9 = 1 → x ^ 3 = 1 := by
  decide

set_option maxRecDepth 10000 in
theorem mem_altThreeProd_of_pow_three :
    ∀ x : Perm (Fin 3) × Perm (Fin 3), x ^ 3 = 1 → x ∈ altThreeProd := by
  simp only [Subgroup.mem_prod, Equiv.Perm.mem_alternatingGroup]
  decide

theorem card_symThree_prod : Nat.card (Perm (Fin 3) × Perm (Fin 3)) = 36 := by
  rw [Nat.card_prod, Nat.card_perm, Nat.card_fin]; rfl

theorem orderOf_cycle_swap_s3s3 : orderOf (((c[0, 1, 2] : Perm (Fin 3)), (swap 0 1 : Perm (Fin 3))) :
    Perm (Fin 3) × Perm (Fin 3)) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> revert hm0 <;> decide

theorem a7_no_s3s3_quotient (X : Subgroup (alternatingGroup (Fin 7)))
    (ψ : ↥X →* Perm (Fin 3) × Perm (Fin 3)) (hψ : Function.Surjective ψ) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX36 : Nat.card ψ.ker * 36 = Nat.card X := by
    have := Subgroup.card_ker_mul_card_of_surjective hψ
    rwa [card_symThree_prod] at this
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hdvd : Nat.card X ∣ 2520 := hA7 ▸ Subgroup.card_subgroup_dvd_card X
  have h27 : ¬ 27 ∣ Nat.card X := fun h => by
    have := h.trans hdvd
    omega
  have h3ker : ¬ 3 ∣ Nat.card ψ.ker := by
    rintro ⟨k, hk⟩
    exact h27 ⟨k * 4, by omega⟩
  obtain ⟨P, hP9⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥X) 3 (n := 2)
    ⟨Nat.card ψ.ker * 4, by omega⟩
  have hP9' : Nat.card P = 9 := by rw [hP9]; norm_num
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) hP9
  have hidx : ¬ 3 ∣ P.index := by
    intro h
    have h1 := P.card_mul_index
    rw [hP9'] at h1
    obtain ⟨k, hk⟩ := h
    exact h27 ⟨k, by omega⟩
  let Psyl : Sylow 3 ↥X := hP3.toSylow hidx
  have hPinj : Function.Injective (ψ.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hpk : (p : ↥X) ∈ ψ.ker := hp
    have h1 : orderOf (p : ↥X) ∣ Nat.card ψ.ker := by
      have := Subgroup.orderOf_dvd_natCard ψ.ker hpk
      simpa using this
    have h2 : orderOf (p : ↥X) ∣ 9 := by
      have := orderOf_dvd_natCard p
      rw [hP9'] at this
      simpa using this
    have hcop : Nat.Coprime 9 (Nat.card ψ.ker) := by
      have : Nat.Coprime 3 (Nat.card ψ.ker) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3ker
      simpa using Nat.Coprime.pow_left 2 this
    have h3 : orderOf (p : ↥X) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    have : (p : ↥X) = 1 := orderOf_eq_one_iff.mp h3
    exact Subtype.ext this
  let B : Subgroup (Perm (Fin 3) × Perm (Fin 3)) := (ψ.comp P.subtype).range
  have hBle : B ≤ altThreeProd := by
    rintro _ ⟨p, rfl⟩
    apply mem_altThreeProd_of_pow_three
    apply s3s3_pow_three_of_pow_nine
    have h9 : p ^ 9 = 1 := by
      rw [← hP9']
      exact pow_card_eq_one'
    have : (ψ.comp P.subtype) p ^ 9 = 1 := by rw [← map_pow, h9, map_one]
    exact this
  have hBcard : Nat.card B = 9 := by
    rw [← hP9']
    exact (Nat.card_congr (MonoidHom.ofInjective hPinj).toEquiv).symm
  have hBeq : B = altThreeProd :=
    Subgroup.eq_of_le_of_card_ge hBle (by rw [hBcard, card_altThreeProd])
  let N : Subgroup ↥X := altThreeProd.comap ψ
  have hNn : N.Normal := Subgroup.Normal.comap inferInstance ψ
  have hPN : (Psyl : Subgroup ↥X) ≤ N := fun p hp => by
    have : ψ p ∈ B := ⟨⟨p, hp⟩, rfl⟩
    show ψ p ∈ altThreeProd
    rw [← hBeq]
    exact this
  have hfr : Subgroup.normalizer (P : Set ↥X) ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top' Psyl hPN
  have hsurjM : ∀ q : Perm (Fin 3) × Perm (Fin 3), ∃ m ∈ Subgroup.normalizer (P : Set ↥X), ψ m = q := by
    intro q
    obtain ⟨x, rfl⟩ := hψ q
    have hx : x ∈ Subgroup.normalizer (P : Set ↥X) ⊔ N := by rw [hfr]; trivial
    obtain ⟨m, hm, n, hn, hmn⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have hnB : ψ n ∈ B := hBeq ▸ hn
    obtain ⟨p, hp⟩ := hnB
    refine ⟨m * p, Subgroup.mul_mem _ hm (Subgroup.le_normalizer p.2), ?_⟩
    rw [map_mul, show ψ (p : ↥X) = ψ n from hp, ← map_mul, hmn]
  obtain ⟨m, hmN, hm⟩ := hsurjM (c[0, 1, 2], swap 0 1)
  have h6 : 6 ∣ orderOf m := by
    have := orderOf_map_dvd ψ m
    rwa [hm, orderOf_cycle_swap_s3s3] at this
  obtain ⟨k, hk⟩ := h6
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := orderOf_pos m
    omega
  have hm'ord : orderOf (m ^ k) = 6 := by
    rw [orderOf_pow_of_dvd hk0 ⟨6, by rw [hk]; ring⟩, hk]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)
  have hm'N : m ^ k ∈ Subgroup.normalizer (P : Set ↥X) := Subgroup.pow_mem _ hmN k
  let ι : ↥X →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp X.subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hP'9 : Nat.card (P.map ι) = 9 := by
    rw [Subgroup.card_map_of_injective hι, hP9']
  obtain ⟨f, hf⟩ := exists_unique_fixed_point_of_card_nine hP'9
  have hμf : ι (m ^ k) f = f := by
    have hmem : ∀ p ∈ P.map ι, p (ι (m ^ k) f) = ι (m ^ k) f := by
      rintro _ ⟨p₀, hp₀, rfl⟩
      have h1 : (m ^ k)⁻¹ * p₀ * (m ^ k)⁻¹⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (inv_mem hm'N) p₀).mp hp₀
      have h2 : ∀ x ∈ P.map ι, x f = f := fun x hx => (hf f).mpr rfl x hx
      have h3 := h2 (ι ((m ^ k)⁻¹ * p₀ * (m ^ k)⁻¹⁻¹)) ⟨_, h1, rfl⟩
      simp only [map_mul, map_inv, inv_inv, Perm.mul_apply] at h3
      have h4 := congrArg (ι (m ^ k)) h3
      simpa using h4
    exact (hf _).mp hmem
  have hsign : (ι (m ^ k)).sign = 1 := Equiv.Perm.mem_alternatingGroup.mp (m ^ k).1.2
  have hord : orderOf (ι (m ^ k)) = 6 := by
    rw [orderOf_injective ι hι, hm'ord]
  exact no_even_order_six_fixed hsign hord f hμf

end CFSG.Quasithin
