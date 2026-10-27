module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.WielandtProductFinal
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
import CFSG.Walter.J1Props.Facts
import CFSG.Walter.Models
import CFSG.Adapters.Certificate43Check
import TauCeti.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped Pointwise

private theorem uc22s216_not_dvd_of_permutes_J1 {X : Type} [Group X] [Finite X]
    (f : X ≃* CFSG.Open.walterJ1) {S B : Subgroup X} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤)
    (hBn : Group.IsNilpotent ↥B) (hBo : Odd (Nat.card ↥B))
    (hBS : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X)) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hsq : ¬ q ^ 2 ∣ 175560) (h8 : ∀ n : ℕ, n ∣ 8 → n % q = 1 → n = 1) :
    ¬ q ∣ Nat.card ↥B := by
  intro hqB
  haveI := CFSG.Adapters.certificate43_holds
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hX : Nat.card X = 175560 := by
    rw [Nat.card_congr f.toEquiv, CFSG.Walter.J1Props.card_walterJ1]
  have hS2 : IsPGroup 2 ↥S := hS.2.1
  have hS8 : Nat.card ↥S = 8 := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    have hidx : ¬ 2 ∣ S.index := by
      have h := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h
    have hmul := Subgroup.card_mul_index S
    rw [hk, hX] at hmul
    have hk3 : k ≤ 3 := by
      by_contra hk
      have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have h : 2 ^ k ∣ 175560 := ⟨S.index, hmul.symm⟩
      have := h16.trans h
      norm_num at this
    rw [hk]
    interval_cases k <;> omega
  have hcoe : ((B ⊔ S : Subgroup X) : Set X) = (B : Set X) * (S : Set X) :=
    CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hBS
  have hBY : B ≤ B ⊔ S := le_sup_left
  have hSY : S ≤ B ⊔ S := le_sup_right
  have hsolv : Group.IsSolvable ↥(B ⊔ S) := by
    have eB : ↥(B.subgroupOf (B ⊔ S)) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBY
    have eS : ↥(S.subgroupOf (B ⊔ S)) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSY
    haveI := hBn
    refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product (B.subgroupOf (B ⊔ S))
      (S.subgroupOf (B ⊔ S)) (Group.nilpotent_of_mulEquiv eB.symm)
      ((hS2.of_equiv eS.symm).isNilpotent) ?_ ?_
    · rw [Nat.card_congr eB.toEquiv, Nat.card_congr eS.toEquiv, hS8,
        show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact (Nat.coprime_two_right.2 hBo).pow_right 3
    · intro g
      have hg : (g : X) ∈ ((B ⊔ S : Subgroup X) : Set X) := g.2
      rw [hcoe] at hg
      obtain ⟨b, hb, s, hs, hbs⟩ := hg
      exact ⟨⟨b, hBY hb⟩, hb, ⟨s, hSY hs⟩, hs, Subtype.ext hbs.symm⟩
  let π : Set Nat.Primes := {p | p.val = 2 ∨ p.val = q}
  have hU : CFSG.IsPiSubgroup π (S.subgroupOf (B ⊔ S)) := by
    intro p hp
    have hp' : p.val ∣ 2 ^ 3 := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv, hS8,
        show (8 : ℕ) = 2 ^ 3 by norm_num] at hp
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq p.prop Nat.prime_two).1 (p.prop.dvd_of_dvd_pow hp'))
  obtain ⟨H, hH, hSH⟩ := CFSG.SolvableHall.solvable_hall_containment hsolv π _ hU
  have hHX : Nat.card ↥H ∣ 175560 := by
    rw [← hX]
    exact (Subgroup.card_subgroup_dvd_card H).trans (Subgroup.card_subgroup_dvd_card (B ⊔ S))
  have hqH : q ∣ Nat.card ↥H := by
    have hqY : q ∣ Nat.card ↥H * H.index :=
      (Subgroup.card_mul_index H) ▸ hqB.trans (Subgroup.card_dvd_of_le hBY)
    rcases (Nat.Prime.dvd_mul hq).1 hqY with h | h
    · exact h
    · exact absurd (Or.inr rfl) (hH.p_in_pi_of_p_dvd_index ⟨q, hq⟩ h)
  obtain ⟨Q⟩ : Nonempty (Sylow q ↥H) := inferInstance
  have hsqH : ¬ q ^ 2 ∣ Nat.card ↥H := fun h => hsq (h.trans hHX)
  have hQ : Nat.card ↥(Q : Subgroup ↥H) = q := Sylow.card_eq_of_dvd_of_not_sq_dvd Q hqH hsqH
  have hidx8 : (Q : Subgroup ↥H).index ∣ 8 := by
    have hmul := Subgroup.card_mul_index (Q : Subgroup ↥H)
    rw [hQ] at hmul
    have hdvd : (Q : Subgroup ↥H).index ∣ 8 * 21945 := by
      rw [show 8 * 21945 = 175560 by norm_num]
      exact (Dvd.intro_left _ hmul).trans hHX
    refine (Nat.Coprime.dvd_of_dvd_mul_right ?_ hdvd)
    refine Nat.coprime_of_dvd fun p hp hpi hp21945 => ?_
    have hpH : p ∣ Nat.card ↥H := hpi.trans (Dvd.intro_left _ hmul)
    rcases hH.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hpH with h | h
    · have h2 : p = 2 := h
      rw [h2] at hp21945
      norm_num at hp21945
    · have hpq : p = q := h
      exact Q.not_dvd_index (hpq ▸ hpi)
  have hn1 : Nat.card (Sylow q ↥H) = 1 := by
    refine h8 _ ((Sylow.card_dvd_index Q).trans hidx8) ?_
    have h := card_sylow_modEq_one q ↥H
    rw [Nat.ModEq, Nat.mod_eq_of_lt hq.one_lt] at h
    exact h
  haveI : Subsingleton (Sylow q ↥H) := (Nat.card_eq_one_iff_unique.mp hn1).1
  have hQn : (Q : Subgroup ↥H).Normal := Q.normal_of_subsingleton
  let ι : ↥H →* X := (B ⊔ S).subtype.comp H.subtype
  have hι : Function.Injective ι := (B ⊔ S).subtype_injective.comp H.subtype_injective
  set P : Subgroup X := (Q : Subgroup ↥H).map ι with hPdef
  have hP : Nat.card ↥P = q := by rw [Subgroup.card_map_of_injective hι, hQ]
  have hSN : S ≤ Subgroup.normalizer (P : Set X) := by
    intro s hs
    let s' : ↥H :=
      ⟨⟨s, hSY hs⟩, hSH (show (⟨s, hSY hs⟩ : ↥(B ⊔ S)) ∈ S.subgroupOf (B ⊔ S) from hs)⟩
    have hιs : ι s' = s := rfl
    rw [Subgroup.mem_normalizer_iff, hPdef]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨s' * y * s'⁻¹, hQn.conj_mem y hy s', ?_⟩
      rw [map_mul, map_mul, map_inv, hιs]
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hy' := hQn.conj_mem y hy s'⁻¹
      rw [inv_inv] at hy'
      refine ⟨s'⁻¹ * y * s', hy', ?_⟩
      rw [map_mul, map_mul, map_inv, hιs, hyx]
      group
  have h8N : 8 ∣ Nat.card (Subgroup.normalizer (P : Set X)) := hS8 ▸ Subgroup.card_dvd_of_le hSN
  have hPf : Nat.card ↥(P.map f.toMonoidHom) = q := by
    rw [Subgroup.card_map_of_injective f.injective, hP]
  have hNf : (Subgroup.normalizer (P : Set X)).map f.toMonoidHom =
      Subgroup.normalizer ((P.map f.toMonoidHom : Subgroup CFSG.Open.walterJ1) :
        Set CFSG.Open.walterJ1) :=
    Subgroup.map_equiv_normalizer_eq P f
  have h8f : 8 ∣ Nat.card (Subgroup.normalizer
      ((P.map f.toMonoidHom : Subgroup CFSG.Open.walterJ1) : Set CFSG.Open.walterJ1)) := by
    rw [← hNf, Subgroup.card_map_of_injective f.injective]
    exact h8N
  exact CFSG.Walter.J1Props.not_eight_dvd_card_normalizer hq2 hPf h8f

theorem uc22s216_prime_eq_three_or_seven_of_permutes_J1 {X : Type} [Group X] [Finite X]
    (hX : IsJ1 X) {S B : Subgroup X} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤)
    (hBn : Group.IsNilpotent ↥B) (hBo : Odd (Nat.card ↥B))
    (hBS : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X)) {q : ℕ} (hq : q.Prime)
    (hqB : q ∣ Nat.card ↥B) : q = 3 ∨ q = 7 := by
  obtain ⟨eJ⟩ := hX
  let f : X ≃* CFSG.Open.walterJ1 := eJ.trans CFSG.Walter.walterJ1EquivNative.symm
  have hXc : Nat.card X = 175560 := by
    rw [Nat.card_congr f.toEquiv, CFSG.Walter.J1Props.card_walterJ1]
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hBo) (even_iff_two_dvd.2 hqB)
  have hqX : q ∣ 175560 := hXc ▸ hqB.trans (Subgroup.card_subgroup_dvd_card B)
  have key := fun (hsq : ¬ q ^ 2 ∣ 175560) (h8 : ∀ n : ℕ, n ∣ 8 → n % q = 1 → n = 1) =>
    uc22s216_not_dvd_of_permutes_J1 f hS hBn hBo hBS hq hq2 hsq h8 hqB
  rcases CFSG.Walter.J1Props.prime_dvd_card hq hqX with h | h | h | h | h | h
  · exact absurd h hq2
  · exact Or.inl h
  · subst h
    exact (key (by norm_num) (fun n hn h1 => by
      have := Nat.le_of_dvd (by norm_num) hn
      interval_cases n <;> omega)).elim
  · exact Or.inr h
  · subst h
    exact (key (by norm_num) (fun n hn h1 => by
      have := Nat.le_of_dvd (by norm_num) hn
      interval_cases n <;> omega)).elim
  · subst h
    exact (key (by norm_num) (fun n hn h1 => by
      have := Nat.le_of_dvd (by norm_num) hn
      interval_cases n <;> omega)).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
