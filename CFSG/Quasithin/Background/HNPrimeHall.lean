module

public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.HSL3PairNPrime

public section

namespace CFSG.Quasithin.H.NPrimeHall

open CFSG.Quasithin.E3
open scoped Pointwise

theorem three_pow_mod_eight (j : ℕ) : 3 ^ j % 8 = 1 ∨ 3 ^ j % 8 = 3 := by
  induction j with
  | zero => left; rfl
  | succ j ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem exists_prime_dvd_ne_three {c : ℕ} (hc : 3 ≤ c) : ∃ p, p.Prime ∧ p ≠ 3 ∧ p ∣ 2 ^ c - 1 := by
  by_contra h
  push Not at h
  have h8 : 8 ∣ 2 ^ c := by
    rw [show c = 3 + (c - 3) by omega, pow_add]
    exact Dvd.intro _ rfl
  have hpos : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  have hne : 2 ^ c - 1 ≠ 0 := by omega
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hne fun {d} hd hdn => by
    by_contra hd3
    exact h d hd hd3 hdn
  have hmod : (2 ^ c - 1) % 8 = 7 := by omega
  rw [heq] at hmod
  rcases three_pow_mod_eight (2 ^ c - 1).primeFactorsList.length with h' | h' <;> omega

variable {M : Type*} [Group M]

@[expose] def IndexThree (X : Subgroup M) : Prop :=
  ∀ S H : Subgroup M, IsSylowIn 2 S X → S ≤ H → H ≤ X →
    Nat.card H = Nat.card S ∨ 3 * Nat.card S ∣ Nat.card H

variable [Finite M]

theorem nPrime_set_nonempty (X : Subgroup M) :
    {c : ℕ | ∃ Y B S : Subgroup M, Y ≤ B ∧ B ≤ X ∧ IsCyclic Y ∧ Nat.card Y = 2 ^ c - 1 ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Odd (Nat.card B) ∧ IsSylowIn 2 S X ∧
      (B : Set M) * (S : Set M) = (S : Set M) * (B : Set M)}.Nonempty := by
  obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two X
  refine ⟨1, ⊥, ⊥, S, bot_le, bot_le, inferInstance, by simp, fun x hx y hy => ?_, by simp, hS,
    by simp⟩
  rw [Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy]

theorem nPrime_le_two {X : Subgroup M} (hX : IndexThree X) : nPrime X ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold nPrime
  refine csSup_le (nPrime_set_nonempty X) ?_
  rintro c ⟨Y, B, S, hYB, hBX, -, hYc, hBab, hBodd, hS, hBS⟩
  by_contra hc
  obtain ⟨p, hp, hp3, hpd⟩ := exists_prime_dvd_ne_three (by omega : 3 ≤ c)
  have hpB : p ∣ Nat.card B := (hYc ▸ hpd).trans (Subgroup.card_dvd_of_le hYB)
  obtain ⟨a, ha⟩ := hS.isPGroup.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card S) := by
    rw [ha]
    exact Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hBodd)
  have hinf : B ⊓ S = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hHcard : Nat.card ↥(B ⊔ S) = Nat.card B * Nat.card S := Tri.card_sup_eq_mul hBS hinf
  have hsolv := Tri.isSolvable_sup_of_permute hBab hBodd hS.isPGroup hBS
  set π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨p, hp⟩} with hπ
  have hU : IsPiSubgroup π (S.subgroupOf (B ⊔ S)) := by
    intro q hq
    have hq' : q.val ∣ Nat.card S := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at hq
    rw [ha] at hq'
    have hq2 : q.val = 2 := (Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp
      (q.2.dvd_of_dvd_pow hq')
    left
    exact Subtype.ext hq2
  obtain ⟨H₀', hH₀', hSH₀'⟩ := CFSG.SolvableHall.solvable_hall_containment hsolv π _ hU
  set H₀ := H₀'.map (B ⊔ S).subtype with hH₀
  have hH₀card : Nat.card H₀ = Nat.card H₀' :=
    Subgroup.card_map_of_injective (B ⊔ S).subtype_injective
  have hSH₀ : S ≤ H₀ := fun s hs => ⟨⟨s, le_sup_right (a := B) hs⟩, hSH₀' hs, rfl⟩
  have hH₀X : H₀ ≤ X := (Subgroup.map_subtype_le H₀').trans (sup_le hBX hS.le)
  obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hSH₀
  have hidx := H₀'.card_mul_index
  rw [← hH₀card, hr, hHcard, mul_assoc, mul_comm (Nat.card B)] at hidx
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hrB : r * H₀'.index = Nat.card B := Nat.eq_of_mul_eq_mul_left hSpos hidx
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hrB
    exact (Nat.card_pos (α := B)).ne' hrB.symm
  have hrodd : Odd r := Odd.of_dvd_nat hBodd (Dvd.intro _ hrB)
  have hrp : r = p ^ r.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hr0 fun {d} hd hdr => ?_
    have hdH : d ∣ Nat.card H₀' := by
      rw [← hH₀card, hr]
      exact Dvd.dvd.mul_left hdr _
    rcases hH₀'.p_in_pi_of_p_dvd_card ⟨d, hd⟩ hdH with h | h
    · have : d = 2 := congrArg Subtype.val h
      subst this
      exact absurd (even_iff_two_dvd.mpr hdr) (Nat.not_even_iff_odd.mpr hrodd)
    · exact congrArg Subtype.val h
  have hpr : p ∣ r := by
    have hpi : ¬ p ∣ H₀'.index := fun h =>
      hH₀'.p_in_pi_of_p_dvd_index ⟨p, hp⟩ h (Or.inr rfl)
    rw [← hrB] at hpB
    exact (hp.dvd_mul.mp hpB).resolve_right hpi
  rcases hX S H₀ hS hSH₀ hH₀X with h | h
  · rw [hr] at h
    have h1 : r = 1 := by
      have := Nat.eq_of_mul_eq_mul_left hSpos (h.trans (mul_one _).symm)
      exact this
    rw [h1] at hpr
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpr)
  · rw [hr, mul_comm 3] at h
    have h3 : 3 ∣ r := Nat.dvd_of_mul_dvd_mul_left hSpos h
    rw [hrp] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm

omit [Finite M] in
theorem indexThree_map {M' : Type*} [Group M'] [Finite M'] {f : M →* M'}
    (hf : Function.Injective f) {X : Subgroup M} (h : IndexThree X) : IndexThree (X.map f) := by
  intro S H hS hSH hHX
  have hSr : S ≤ f.range := hS.le.trans (Subgroup.map_le_range f X)
  have hHr : H ≤ f.range := hHX.trans (Subgroup.map_le_range f X)
  have hS' : S = (S.comap f).map f := (Subgroup.map_comap_eq_self hSr).symm
  have hH' : H = (H.comap f).map f := (Subgroup.map_comap_eq_self hHr).symm
  have hSyl : IsSylowIn 2 (S.comap f) X := by
    rw [← E1.isSylowIn_map_of_injective hf, ← hS']
    exact hS
  have hSH' : S.comap f ≤ H.comap f := Subgroup.comap_mono hSH
  have hHX' : H.comap f ≤ X := by
    rw [← Subgroup.map_le_map_iff_of_injective hf, ← hH']
    exact hHX
  have hcS : Nat.card S = Nat.card (S.comap f) := by
    conv_lhs => rw [hS']
    exact Subgroup.card_map_of_injective hf
  have hcH : Nat.card H = Nat.card (H.comap f) := by
    conv_lhs => rw [hH']
    exact Subgroup.card_map_of_injective hf
  rw [hcS, hcH]
  exact h _ _ hSyl hSH' hHX'

theorem indexThree_of_surjective {G Γ : Type*} [Group G] [Finite G] [Group Γ] [Finite Γ]
    {π : G →* Γ} (hπ : Function.Surjective π) (hker : Nat.card π.ker = 3)
    (h : IndexThree (⊤ : Subgroup Γ)) : IndexThree (⊤ : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro S H hS hSH -
  obtain ⟨a, ha⟩ := hS.isPGroup.exists_card_eq
  have hcard : ∀ K : Subgroup G, Nat.card K = Nat.card (K.map π) * Nat.card ↥(K ⊓ π.ker) := by
    intro K
    have h1 := Subgroup.card_ker_mul_card_range (π.comp K.subtype)
    have h2 : (π.comp K.subtype).range = K.map π := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have h3 : Nat.card (π.comp K.subtype).ker = Nat.card ↥(K ⊓ π.ker) :=
      Nat.card_congr ⟨fun x => ⟨x.1, x.1.2, x.2⟩, fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun _ => rfl,
        fun _ => rfl⟩
    rw [h2, h3] at h1
    rw [← h1, mul_comm]
  have hdvd : ∀ K : Subgroup G, Nat.card ↥(K ⊓ π.ker) ∣ 3 := fun K => by
    rw [← hker]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hSk : Nat.card ↥(S ⊓ π.ker) = 1 := by
    have h1 : Nat.card ↥(S ⊓ π.ker) ∣ 2 ^ a := ha ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 := hdvd S
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right a (by norm_num)) h2 h1
  have hSmap : Nat.card (S.map π) = Nat.card S := by
    rw [hcard S, hSk, mul_one]
  have hSyl : IsSylowIn 2 (S.map π) ⊤ := by
    refine ⟨le_top, hS.isPGroup.map π, ?_⟩
    rw [Subgroup.relIndex_top_right]
    intro h2
    apply hS.not_dvd_relIndex
    rw [Subgroup.relIndex_top_right]
    have hG := hcard ⊤
    rw [inf_of_le_right le_top, hker, Subgroup.map_top_of_surjective π hπ] at hG
    simp only [Subgroup.card_top] at hG
    have hi1 := (S.map π).card_mul_index
    have hi2 := S.card_mul_index
    rw [hSmap] at hi1
    have hpos : 0 < Nat.card S := Nat.card_pos
    have he : S.index = (S.map π).index * 3 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [hi2, hG, ← hi1, mul_assoc]
    rw [he]
    exact Dvd.dvd.mul_right h2 3
  rcases h _ _ hSyl (Subgroup.map_mono hSH) le_top with h1 | h1
  · rw [hSmap] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp (hdvd H) with h3 | h3
    · left
      rw [hcard H, h1, h3, mul_one]
    · right
      rw [hcard H, h1, h3, mul_comm]
  · right
    rw [hSmap] at h1
    rw [hcard H]
    exact h1.trans (Dvd.intro _ rfl)

theorem nPrime_le_of_normal {L X : Subgroup M} (hLX : L ≤ X)
    (hN : X ≤ Subgroup.normalizer (L : Set M)) (h2 : ∀ x ∈ X, x ^ 2 ∈ L) :
    nPrime X ≤ nPrime L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine csSup_le (nPrime_set_nonempty X) ?_
  rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
  have hBL : B ≤ L := by
    intro b hb
    have hodd : Odd (orderOf b) :=
      Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb)
    obtain ⟨m, hm⟩ := hodd
    have hb' : b = (b ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf b + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [hb']
    exact L.pow_mem (h2 b (hBX hb)) _
  have hLnX : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hN
  have hSL := hS.inf_normal hLX hLnX
  have hperm : (B : Set M) * ((S ⊓ L : Subgroup M) : Set M) =
      ((S ⊓ L : Subgroup M) : Set M) * B := by
    apply SL3Pair.mul_comm_of_subset
    rintro _ ⟨s, hs, b, hb, rfl⟩
    have hsb : s * b ∈ (S : Set M) * B := Set.mul_mem_mul hs.1 hb
    rw [← hBS] at hsb
    obtain ⟨b', hb', s', hs', he⟩ := hsb
    have he' : b' * s' = s * b := he
    have hs'L : s' ∈ L := by
      have e : s' = b'⁻¹ * (s * b) := by rw [← he']; group
      rw [e]
      exact L.mul_mem (L.inv_mem (hBL hb')) (L.mul_mem hs.2 (hBL hb))
    exact ⟨b', hb', s', ⟨hs', hs'L⟩, he⟩
  exact le_nPrime hYB hBL hY hYc hBab hBodd hSL hperm

theorem sq_mem_of_relIndex_le_two {L X : Subgroup M} (hLX : L ≤ X)
    (hN : X ≤ Subgroup.normalizer (L : Set M)) (hi : L.relIndex X ≤ 2) :
    ∀ x ∈ X, x ^ 2 ∈ L := by
  intro x hx
  have hLnX : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hN
  have hcard : Nat.card (↥X ⧸ L.subgroupOf X) ≤ 2 := by
    rw [← Subgroup.index_eq_card]
    exact hi
  have h := Subgroup.index_dvd_card (H := L.subgroupOf X)
  set q : ↥X ⧸ L.subgroupOf X := QuotientGroup.mk ⟨x, hx⟩ with hq
  have hq2 : q ^ 2 = 1 := by
    have : orderOf q ∣ 2 := by
      have h1 := orderOf_dvd_natCard q
      interval_cases h' : Nat.card (↥X ⧸ L.subgroupOf X)
      · exact absurd h' Nat.card_pos.ne'
      · rw [orderOf_eq_one_iff.mpr (Subsingleton.elim (h := Finite.card_le_one_iff_subsingleton.mp
            h'.le) q 1)]
        exact one_dvd 2
      · exact h1
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hmem : (⟨x, hx⟩ : ↥X) ^ 2 ∈ L.subgroupOf X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hq2
  exact hmem

theorem two_le_nPrime_of_three {X S H : Subgroup M} (hS : IsSylowIn 2 S X) (hSH : S ≤ H)
    (hHX : H ≤ X) (hH : Nat.card H = 3 * Nat.card S) : 2 ≤ nPrime X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 (Dvd.intro _ hH.symm)
  set B := Subgroup.zpowers (y : M) with hBdef
  have hBcard : Nat.card B = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy]
  have hBH : B ≤ H := (Subgroup.zpowers_le).mpr y.2
  obtain ⟨a, ha⟩ := hS.isPGroup.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card S) := by
    rw [hBcard, ha]
    exact Nat.Coprime.pow_right a (by norm_num)
  have hBS' : (B.subgroupOf H).IsComplement' (S.subgroupOf H) := by
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv, hBcard, hH]
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv]
  have hmulH : ∀ {K L : Subgroup M}, K ≤ H → L ≤ H →
      (K.subgroupOf H).IsComplement' (L.subgroupOf H) → (K : Set M) * L = H := by
    intro K L hK hL hKL
    refine Set.Subset.antisymm ?_ fun h hh => ?_
    · rintro _ ⟨k, hk, l, hl, rfl⟩
      exact H.mul_mem (hK hk) (hL hl)
    · obtain ⟨⟨k, l⟩, hkl⟩ := hKL.2 ⟨h, hh⟩
      exact ⟨k.1, k.2, l.1, l.2, congrArg Subtype.val hkl⟩
  have h1 := hmulH hBH hSH hBS'
  have h2 := hmulH hSH hBH hBS'.symm
  refine le_nPrime le_rfl (hBH.trans hHX) inferInstance (by rw [hBcard]; norm_num)
    (fun a ha b hb => ?_) (by rw [hBcard]; decide) hS (h1.trans h2.symm)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_add, ← zpow_add, add_comm]

theorem two_le_nPrime_of_normal {X Z : Subgroup M} (hZX : Z ≤ X)
    (hN : X ≤ Subgroup.normalizer (Z : Set M)) (hZ : Nat.card Z = 3) : 2 ≤ nPrime X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two X
  have hperm : (Z : Set M) * S = S * Z := by
    apply SL3Pair.mul_comm_of_subset
    rintro _ ⟨s, hs, z, hz, rfl⟩
    refine ⟨s * z * s⁻¹, ?_, s, hs, by group⟩
    exact (Subgroup.mem_normalizer_iff.mp (hN (hS.le hs)) z).mp hz
  have hcyc : IsCyclic Z := isCyclic_of_prime_card hZ
  refine le_nPrime le_rfl hZX hcyc (by rw [hZ]; norm_num) (fun a ha b hb => ?_)
    (by rw [hZ]; decide) hS hperm
  have h := hcyc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val h

end CFSG.Quasithin.H.NPrimeHall
