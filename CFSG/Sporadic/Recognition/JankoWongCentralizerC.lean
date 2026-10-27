module

public import CFSG.Sporadic.Recognition.JankoWongOddCore
public import CFSG.Sporadic.Recognition.JankoWongThreeSylow

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem card_centralizer_subtype {G : Type*} [Group G] {C : Subgroup G} (u : C) :
    Nat.card (centralizer ({u} : Set C)) =
      Nat.card (C ⊓ centralizer ({(u : G)} : Set G) : Subgroup G) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun k => ⟨(k.1 : G), k.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp k.2))⟩
      invFun := fun m => ⟨⟨m.1, m.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.2.2))⟩
      left_inv := fun k => rfl
      right_inv := fun m => rfl }

theorem card_inf_centralizer_conj {G : Type*} [Group G] (g x v : G) :
    Nat.card (centralizer ({g * x * g⁻¹} : Set G) ⊓ centralizer ({g * v * g⁻¹} : Set G) :
      Subgroup G) =
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun k => ⟨g⁻¹ * k.1 * g, by
        obtain ⟨k, h1, h2⟩ := k
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp h1
        have h2 := Subgroup.mem_centralizer_singleton_iff.mp h2
        refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
          Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        · calc g⁻¹ * k * g * x = g⁻¹ * (k * (g * x * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * x * g⁻¹) * k) * g := by rw [h1]
            _ = x * (g⁻¹ * k * g) := by group
        · calc g⁻¹ * k * g * v = g⁻¹ * (k * (g * v * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * v * g⁻¹) * k) * g := by rw [h2]
            _ = v * (g⁻¹ * k * g) := by group⟩
      invFun := fun m => ⟨g * m.1 * g⁻¹, by
        obtain ⟨m, h1, h2⟩ := m
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp h1
        have h2 := Subgroup.mem_centralizer_singleton_iff.mp h2
        refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
          Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        · calc g * m * g⁻¹ * (g * x * g⁻¹) = g * (m * x) * g⁻¹ := by group
            _ = g * (x * m) * g⁻¹ := by rw [h1]
            _ = (g * x * g⁻¹) * (g * m * g⁻¹) := by group
        · calc g * m * g⁻¹ * (g * v * g⁻¹) = g * (m * v) * g⁻¹ := by group
            _ = g * (v * m) * g⁻¹ := by rw [h2]
            _ = (g * v * g⁻¹) * (g * m * g⁻¹) := by group⟩
      left_inv := fun m => by
        apply Subtype.ext
        show g * (g⁻¹ * m.1 * g) * g⁻¹ = m.1
        group
      right_inv := fun m => by
        apply Subtype.ext
        show g⁻¹ * (g * m.1 * g⁻¹) * g = m.1
        group }

namespace Setup

variable {G : Type} [Group G] [Finite G]

theorem card_inf_centralizer_involution (S : Setup G) {x : S.H} (hx3 : x ^ 3 = 1)
    (hxt : (S.ρ x).cycleType = {3, 3}) {v : G} (hv : v ^ 2 = 1) (hv1 : v ≠ 1)
    (hvx : v * (x : G) = (x : G) * v) :
    Nat.card (centralizer ({(x : G)} : Set G) ⊓ centralizer ({v} : Set G) : Subgroup G) = 36 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (S.oneClass v S.z (orderOf_eq_prime hv hv1) S.order_z)
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hz2 : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z
  have hz1 : S.z ≠ 1 := fun e => S.cover.ne_one (Subtype.ext e)
  have hs'z : g * (x : G) * g⁻¹ ∈ S.H := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    calc g * (x : G) * g⁻¹ * (g * v * g⁻¹) = g * ((x : G) * v) * g⁻¹ := by group
      _ = g * (v * (x : G)) * g⁻¹ := by rw [hvx]
      _ = g * v * g⁻¹ * (g * (x : G) * g⁻¹) := by group
  set y : S.H := ⟨g * (x : G) * g⁻¹, hs'z⟩ with hy
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    show (g * (x : G) * g⁻¹) ^ 3 = 1
    have : (g * (x : G) * g⁻¹) ^ 3 = g * (x : G) ^ 3 * g⁻¹ := by simp [pow_succ, mul_assoc]
    rw [this, hxG3]; simp
  have hx1 : x ≠ 1 := fun e => by
    rw [e, map_one, cycleType_one] at hxt
    simp at hxt
  have hy1 : y ≠ 1 := fun e => hx1 (by
    have h1 : g * (x : G) * g⁻¹ = 1 := congrArg Subtype.val e
    have h2 : (x : G) = 1 := by
      calc (x : G) = g⁻¹ * (g * (x : G) * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    exact Subtype.ext h2)
  have hyz : y ≠ zIn S.z := fun e => by
    have : y ^ 3 = zIn S.z := by
      rw [e, pow_succ, S.zIn_sq, one_mul]
    rw [hy3] at this
    exact S.cover.ne_one this.symm
  have hρy : S.ρ y ≠ 1 := fun e => by
    rcases S.cover.mem_ker_iff.mp e with e1 | e1
    · exact hy1 e1
    · exact hyz e1
  have hρy3 : (S.ρ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hyt : (S.ρ y).cycleType = {3, 3} := by
    rcases cycleType_of_cube_eq_one_ne_one hρy3 hρy with h | h
    · exfalso
      refine S.not_isConj_type3_type33 hy3 hx3 h hxt ?_
      exact (isConj_iff.mpr ⟨g, rfl⟩ : IsConj (x : G) (g * (x : G) * g⁻¹)).symm
    · exact h
  have h36 := S.cover.card_centralizer_type33 hy3 hyt
  calc Nat.card (centralizer ({(x : G)} : Set G) ⊓ centralizer ({v} : Set G) : Subgroup G)
      = Nat.card (centralizer ({g * (x : G) * g⁻¹} : Set G) ⊓
          centralizer ({g * v * g⁻¹} : Set G) : Subgroup G) :=
        (card_inf_centralizer_conj g (x : G) v).symm
    _ = Nat.card (S.H ⊓ centralizer ({g * (x : G) * g⁻¹} : Set G) : Subgroup G) := by
        rw [hg, inf_comm]
    _ = Nat.card (centralizer ({y} : Set S.H)) := (card_centralizer_subtype y).symm
    _ = 36 := h36

theorem isPGroup_three_of_odd_normal (S : Setup G) {x t : S.H} (hx3 : x ^ 3 = 1)
    (hxt : (S.ρ x).cycleType = {3, 3}) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htz : t ≠ zIn S.z)
    (htx : t * x = x * t) {X : Subgroup ↥(centralizer ({(x : G)} : Set G))} [X.Normal]
    (hX : Odd (Nat.card X)) : IsPGroup 3 X := by
  have hz2 : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z
  have hz1 : S.z ≠ 1 := fun e => S.cover.ne_one (Subtype.ext e)
  have htG2 : (t : G) ^ 2 = 1 := by
    have := congrArg Subtype.val ht2
    simpa using this
  have htG1 : (t : G) ≠ 1 := fun e => ht1 (Subtype.ext e)
  have htz' : (t : G) ≠ S.z := fun e => htz (Subtype.ext e)
  have hzt : (t : G) * S.z = S.z * (t : G) := Subgroup.mem_centralizer_singleton_iff.mp t.2
  have hzx : S.z * (x : G) = (x : G) * S.z := (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm
  have htxG : (t : G) * (x : G) = (x : G) * (t : G) := congrArg Subtype.val htx
  have hztG2 : (S.z * (t : G)) ^ 2 = 1 := by
    rw [pow_two]
    calc S.z * (t : G) * (S.z * (t : G)) = S.z * ((t : G) * S.z) * (t : G) := by group
      _ = S.z * (S.z * (t : G)) * (t : G) := by rw [hzt]
      _ = (S.z * S.z) * ((t : G) * (t : G)) := by simp only [mul_assoc]
      _ = 1 := by rw [← pow_two, ← pow_two, hz2, htG2, one_mul]
  have hztG1 : S.z * (t : G) ≠ 1 := fun e => htz' (by
    have hinv : S.z⁻¹ = S.z := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    calc (t : G) = S.z⁻¹ * (S.z * (t : G)) := by group
      _ = S.z := by rw [e, mul_one, hinv])
  have hztx : S.z * (t : G) * (x : G) = (x : G) * (S.z * (t : G)) := by
    calc S.z * (t : G) * (x : G) = S.z * ((t : G) * (x : G)) := by group
      _ = S.z * ((x : G) * (t : G)) := by rw [htxG]
      _ = (S.z * (x : G)) * (t : G) := by group
      _ = ((x : G) * S.z) * (t : G) := by rw [hzx]
      _ = (x : G) * (S.z * (t : G)) := by group
  let u₁ : centralizer ({(x : G)} : Set G) :=
    ⟨S.z, Subgroup.mem_centralizer_singleton_iff.mpr hzx⟩
  let u₂ : centralizer ({(x : G)} : Set G) :=
    ⟨(t : G), Subgroup.mem_centralizer_singleton_iff.mpr htxG⟩
  have hu₁ : u₁ ^ 2 = 1 := Subtype.ext (by simpa using hz2)
  have hu₂ : u₂ ^ 2 = 1 := Subtype.ext (by simpa using htG2)
  have hc : u₁ * u₂ = u₂ * u₁ := Subtype.ext hzt.symm
  have c₁ : Nat.card (centralizer ({u₁} : Set (centralizer ({(x : G)} : Set G)))) = 36 := by
    rw [card_centralizer_subtype u₁]
    exact S.card_inf_centralizer_involution hx3 hxt (v := S.z) hz2 hz1 hzx
  have c₂ : Nat.card (centralizer ({u₂} : Set (centralizer ({(x : G)} : Set G)))) = 36 := by
    rw [card_centralizer_subtype u₂]
    exact S.card_inf_centralizer_involution hx3 hxt (v := (t : G)) htG2 htG1 htxG
  have c₁₂ : Nat.card (centralizer ({u₁ * u₂} : Set (centralizer ({(x : G)} : Set G)))) = 36 := by
    rw [card_centralizer_subtype (u₁ * u₂)]
    exact S.card_inf_centralizer_involution hx3 hxt (v := S.z * (t : G)) hztG2 hztG1 hztx
  have key : ∀ p : ℕ, p.Prime → p ∣ Nat.card X → p = 3 := by
    intro p hp hpX
    by_contra hp3
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hX) (even_iff_two_dvd.mpr hpX)
    have hnd : ¬ p ∣ 36 := by
      intro hd
      have h36' : (36 : ℕ) = 2 ^ 2 * 3 ^ 2 := by norm_num
      rw [h36'] at hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
    exact not_dvd_card_of_klein hX hu₁ hu₂ hc hp (by rw [c₁]; exact hnd) (by rw [c₂]; exact hnd)
      (by rw [c₁₂]; exact hnd) hpX
  have hne : Nat.card X ≠ 0 := Nat.card_pos.ne'
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hne
    (fun {d} hd hdX => key d hd hdX))

theorem isPGroup_three_of_odd_normal_G (S : Setup G) {x t : S.H} (hx3 : x ^ 3 = 1)
    (hxt : (S.ρ x).cycleType = {3, 3}) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htz : t ≠ zIn S.z)
    (htx : t * x = x * t) {X : Subgroup G} (hXC : X ≤ centralizer ({(x : G)} : Set G))
    (hXn : ∀ g ∈ centralizer ({(x : G)} : Set G), ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hX : Odd (Nat.card X)) : IsPGroup 3 X := by
  have hnorm : (X.subgroupOf (centralizer ({(x : G)} : Set G))).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (hXn g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hodd : Odd (Nat.card (X.subgroupOf (centralizer ({(x : G)} : Set G)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv]
    exact hX
  exact (S.isPGroup_three_of_odd_normal hx3 hxt ht2 ht1 htz htx hodd).of_equiv
    (Subgroup.subgroupOfEquivOfLe hXC)

theorem false_of_hasNormalPComplement (S : Setup G) (h27 : ¬ 27 ∣ Nat.card G) {x t : S.H}
    (hx3 : x ^ 3 = 1) (hxt : (S.ρ x).cycleType = {3, 3}) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htz : t ≠ zIn S.z) (htx : t * x = x * t)
    (hN : CFSG.HasNormalPComplement 2 ↥(centralizer ({(x : G)} : Set G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hXn, hXcop, hXq⟩ := hN
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp hXcop
  have hX3 : IsPGroup 3 X := S.isPGroup_three_of_odd_normal hx3 hxt ht2 ht1 htz htx hXodd
  have hX9 : Nat.card X ≤ 9 := by
    have hmap : IsPGroup 3 ↥(X.map (centralizer ({(x : G)} : Set G)).subtype) :=
      hX3.map (centralizer ({(x : G)} : Set G)).subtype
    have := card_le_nine_of_not_dvd h27 hmap
    rwa [Subgroup.card_map_of_injective (centralizer ({(x : G)} : Set G)).subtype_injective] at this
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXq
  have hCcard : Nat.card ↥(centralizer ({(x : G)} : Set G)) = 2 ^ k * Nat.card X := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup X, hk]
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(centralizer ({(x : G)} : Set G))) := inferInstance
  have hT4 := S.card_sylow_centralizer_type33 hx3 hxt T
  rw [T.card_eq_multiplicity] at hT4
  have hfact : (Nat.card ↥(centralizer ({(x : G)} : Set G))).factorization 2 = k := by
    rw [hCcard, Nat.factorization_mul (by positivity) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    have h2 : (Nat.card X).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h =>
        (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr h))
    simp [h2]
  rw [hfact] at hT4
  have hk2 : k = 2 := by
    have : (2 : ℕ) ^ k = 2 ^ 2 := by rw [hT4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  have hC36 : Nat.card ↥(centralizer ({(x : G)} : Set G)) ≤ 36 := by rw [hCcard, hk2]; omega
  have hz2 : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z
  have hz1 : S.z ≠ 1 := fun e => S.cover.ne_one (Subtype.ext e)
  have hzx : S.z * (x : G) = (x : G) * S.z := (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm
  have hCH : Nat.card (centralizer ({(x : G)} : Set G) ⊓ centralizer ({S.z} : Set G) :
      Subgroup G) = 36 :=
    S.card_inf_centralizer_involution hx3 hxt hz2 hz1 hzx
  have hle : centralizer ({(x : G)} : Set G) ⊓ S.H ≤ centralizer ({(x : G)} : Set G) :=
    inf_le_left
  have heq : centralizer ({(x : G)} : Set G) ⊓ S.H = centralizer ({(x : G)} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hCH]; exact hC36)
  exact S.not_centralizer_le_H hx3 hxt (by rw [← heq]; exact inf_le_right)

end Setup

end CFSG.Sporadic.Recognition.JankoWong
