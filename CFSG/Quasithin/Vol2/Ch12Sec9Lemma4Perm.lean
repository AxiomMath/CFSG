module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13

namespace L1294J

open Equiv MulAction

theorem exists_isSwap_mem {n : ℕ} (hn : 2 ≤ n) {S : Subgroup (Perm (Fin n))}
    (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.index) : ∃ g ∈ S, g.IsSwap := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t : Perm (Fin n) := swap ⟨0, by omega⟩ ⟨1, by omega⟩ with ht
  have htswap : t.IsSwap := ⟨_, _, by simp [Fin.ext_iff], rfl⟩
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htswap.orderOf, pow_one])
  obtain ⟨P₀, hP₀⟩ := ht2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin n)) P₀ (hS.toSylow hidx)
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · have hmem : g * t * g⁻¹ ∈ ((g • P₀ : Sylow 2 (Perm (Fin n))) : Subgroup (Perm (Fin n))) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have : t ∈ (P₀ : Subgroup (Perm (Fin n))) := hP₀ (Subgroup.mem_zpowers t)
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
    rw [hg] at hmem
    simpa using hmem
  · obtain ⟨x, y, hxy, hxyt⟩ := htswap
    refine ⟨g x, g y, fun h => hxy (g.injective h), ?_⟩
    rw [hxyt, ← swap_apply_apply]

theorem isPGroup_zpowers {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {c : G} (hc : c ^ p = 1) :
    IsPGroup p (Subgroup.zpowers c) := by
  have hdvd : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hc
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

variable {n : ℕ}

theorem mem_fixedPoints_zpowers {c : Perm (Fin n)} {a : Fin n} :
    a ∈ fixedPoints (Subgroup.zpowers c) (Fin n) ↔ c a = a := by
  constructor
  · intro h
    exact h ⟨c, Subgroup.mem_zpowers c⟩
  · rintro h ⟨z, k, rfl⟩
    exact Perm.zpow_apply_eq_self_of_apply_eq_self h k

theorem card_fixedPoints_modEq {c : Perm (Fin n)} (hc : c ^ 7 = 1) :
    n ≡ Nat.card (fixedPoints (Subgroup.zpowers c) (Fin n)) [MOD 7] := by
  have h7 : Nat.Prime 7 := by decide
  have : Fact (Nat.Prime 7) := ⟨h7⟩
  have := (isPGroup_zpowers h7 hc).card_modEq_card_fixedPoints (Fin n)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem eq_one_of_card_fixedPoints {c : Perm (Fin n)}
    (h : n ≤ Nat.card (fixedPoints (Subgroup.zpowers c) (Fin n))) : c = 1 := by
  have huniv : fixedPoints (Subgroup.zpowers c) (Fin n) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq]
    exact h
  exact Perm.ext fun a => mem_fixedPoints_zpowers.1 (huniv ▸ Set.mem_univ a)

theorem card_fixedPoints_le (c : Perm (Fin n)) :
    Nat.card (fixedPoints (Subgroup.zpowers c) (Fin n)) ≤ n := by
  calc _ ≤ Nat.card (Fin n) := Finite.card_subtype_le _
    _ = n := by simp

theorem card_orbit_eq_seven (hn : n < 49) {c : Perm (Fin n)} (hc : c ^ 7 = 1) {a : Fin n}
    (ha : c a ≠ a) : Nat.card (orbit (Subgroup.zpowers c) a) = 7 := by
  have h7 : Nat.Prime 7 := by decide
  have : Fact (Nat.Prime 7) := ⟨h7⟩
  obtain ⟨k, hk⟩ := (isPGroup_zpowers h7 hc).card_orbit a
  have hle : Nat.card (orbit (Subgroup.zpowers c) a) ≤ n := by
    calc _ ≤ Nat.card (Fin n) := Finite.card_subtype_le _
      _ = n := by simp
  rcases k with _ | _ | k
  · exfalso
    rw [pow_zero] at hk
    have hsub : Subsingleton (orbit (Subgroup.zpowers c) a) :=
      (Nat.card_eq_one_iff_unique.1 hk).1
    have hc' : c • a ∈ orbit (Subgroup.zpowers c) a := ⟨⟨c, Subgroup.mem_zpowers c⟩, rfl⟩
    exact ha (congrArg Subtype.val (Subsingleton.elim (⟨c • a, hc'⟩ :
      orbit (Subgroup.zpowers c) a) ⟨a, mem_orbit_self a⟩))
  · simpa using hk
  · have h49 : 49 ≤ 7 ^ (k + 1 + 1) := by
      calc 49 = 7 ^ 2 := by norm_num
        _ ≤ 7 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem exists_of_mem_orbit {H : Subgroup (Perm (Fin n))} {c : Perm (Fin n)} (hcH : c ∈ H)
    {a b : Fin n} (hb : b ∈ orbit (Subgroup.zpowers c) a) : ∃ h ∈ H, h a = b := by
  obtain ⟨⟨z, hz⟩, hzab⟩ := hb
  exact ⟨z, (Subgroup.zpowers_le.2 hcH) hz, hzab⟩

theorem eq_top_seven {H S : Subgroup (Perm (Fin 7))} (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.index)
    (hSH : S ≤ H) {c : Perm (Fin 7)} (hcH : c ∈ H) (hc : c ^ 7 = 1) (hc1 : c ≠ 1) : H = ⊤ := by
  classical
  obtain ⟨t, htS, ht⟩ := exists_isSwap_mem (by norm_num) hS hidx
  have hfix : ∀ a : Fin 7, c a ≠ a := by
    intro a ha
    have hmod := card_fixedPoints_modEq hc
    have hle := card_fixedPoints_le c
    have hpos : 1 ≤ Nat.card (fixedPoints (Subgroup.zpowers c) (Fin 7)) :=
      Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨⟨a, mem_fixedPoints_zpowers.2 ha⟩⟩,
        Set.toFinite _⟩)
    unfold Nat.ModEq at hmod
    exact hc1 (eq_one_of_card_fixedPoints (by omega))
  have htrans : IsPretransitive H (Fin 7) := by
    refine ⟨fun a b => ?_⟩
    have horb : orbit (Subgroup.zpowers c) a = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [Set.ncard_univ, ← Nat.card_coe_set_eq, card_orbit_eq_seven (by norm_num) hc (hfix a)]
      simp
    obtain ⟨h, hh, hab⟩ := exists_of_mem_orbit hcH (horb ▸ Set.mem_univ b : b ∈ _)
    exact ⟨⟨h, hh⟩, hab⟩
  have hprim : IsPreprimitive H (Fin 7) :=
    IsPreprimitive.of_prime_card (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
  exact Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hprim t ht (hSH htS)

theorem exists_moved_eight {S : Subgroup (Perm (Fin 8))} (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ S.index) (p : Fin 8) : ∃ s ∈ S, s p ≠ p := by
  classical
  by_contra hall
  push Not at hall
  have hSst : S ≤ stabilizer (Perm (Fin 8)) p := fun s hs => hall s hs
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hmul := S.card_mul_index
  rw [hk, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hmul
  have h128 : 2 ^ 7 ∣ 2 ^ k := by
    have h2 : 2 ^ 7 ∣ 2 ^ k * S.index :=
      Dvd.intro 315 (by rw [hmul]; norm_num [Nat.factorial])
    have hcop : Nat.Coprime (2 ^ 7) S.index :=
      Nat.Coprime.pow_left 7 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hidx)
    exact hcop.dvd_of_dvd_mul_right h2
  have horb : orbit (Perm (Fin 8)) p = Set.univ :=
    Set.eq_univ_of_forall fun q => ⟨swap p q, swap_apply_left p q⟩
  have hidx8 : (stabilizer (Perm (Fin 8)) p).index = 8 := by
    rw [index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hst := (stabilizer (Perm (Fin 8)) p).card_mul_index
  rw [hidx8, Nat.card_perm, Nat.card_fin] at hst
  have hstc : Nat.card (stabilizer (Perm (Fin 8)) p) = 5040 := by
    rw [show Nat.factorial 8 = 40320 from rfl] at hst
    omega
  have hdvd := Subgroup.card_dvd_of_le hSst
  rw [hk, hstc] at hdvd
  have := h128.trans hdvd
  norm_num at this

theorem eq_top_eight {H S : Subgroup (Perm (Fin 8))} (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.index)
    (hSH : S ≤ H) {c : Perm (Fin 8)} (hcH : c ∈ H) (hc : c ^ 7 = 1) (hc1 : c ≠ 1) : H = ⊤ := by
  classical
  obtain ⟨t, htS, ht⟩ := exists_isSwap_mem (by norm_num) hS hidx
  have hmod := card_fixedPoints_modEq hc
  have hle := card_fixedPoints_le c
  have hf1 : Nat.card (fixedPoints (Subgroup.zpowers c) (Fin 8)) = 1 := by
    unfold Nat.ModEq at hmod
    have hne : Nat.card (fixedPoints (Subgroup.zpowers c) (Fin 8)) ≠ 8 := fun h8 =>
      hc1 (eq_one_of_card_fixedPoints (by omega))
    omega
  obtain ⟨⟨p, hp⟩, hpu⟩ := Nat.card_eq_one_iff_exists.1 hf1
  have hcp : c p = p := mem_fixedPoints_zpowers.1 hp
  have honly : ∀ x, c x = x → x = p := fun x hx =>
    congrArg Subtype.val (hpu ⟨x, mem_fixedPoints_zpowers.2 hx⟩)
  have hcomp : ∀ x y, x ≠ p → y ≠ p → ∃ k : ℤ, (c ^ k) x = y := by
    intro x y hx hy
    have hxc : c x ≠ x := fun h => hx (honly x h)
    have hsub : orbit (Subgroup.zpowers c) x ⊆ {p}ᶜ := by
      rintro _ ⟨⟨z, k, rfl⟩, rfl⟩ hzp
      apply hx
      have h1 : (c ^ k) x = p := hzp
      have h2 : (c ^ k) p = p := Perm.zpow_apply_eq_self_of_apply_eq_self hcp k
      exact (c ^ k).injective (h1.trans h2.symm)
    have heq : orbit (Subgroup.zpowers c) x = {p}ᶜ := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_
      rw [Set.ncard_compl, Set.ncard_singleton, ← Nat.card_coe_set_eq,
        card_orbit_eq_seven (by norm_num) hc hxc]
      simp
    obtain ⟨⟨z, k, rfl⟩, hzk⟩ := (heq ▸ (hy : y ∈ ({p}ᶜ : Set (Fin 8))) :
      y ∈ orbit (Subgroup.zpowers c) x)
    exact ⟨k, hzk⟩
  obtain ⟨s, hsS, hsp⟩ := exists_moved_eight hS hidx p
  have hto : ∀ x, ∃ h ∈ H, h x = p := by
    intro x
    by_cases hx : x = p
    · exact ⟨1, H.one_mem, by rw [hx]; rfl⟩
    · obtain ⟨k, hk⟩ := hcomp x (s p) hx hsp
      refine ⟨s⁻¹ * c ^ k, H.mul_mem (H.inv_mem (hSH hsS)) (H.zpow_mem hcH k), ?_⟩
      rw [Perm.mul_apply, hk]
      exact s.symm_apply_apply p
  have h2 : IsMultiplyPretransitive H (Fin 8) 2 := by
    rw [is_two_pretransitive_iff]
    intro a b a' b' hab hab'
    obtain ⟨h₁, hh₁, h₁a⟩ := hto a
    obtain ⟨h₂, hh₂, h₂a⟩ := hto a'
    have hb1 : h₁ b ≠ p := fun h => hab (h₁.injective (h₁a.trans h.symm))
    have hb2 : h₂ b' ≠ p := fun h => hab' (h₂.injective (h₂a.trans h.symm))
    obtain ⟨k, hk⟩ := hcomp _ _ hb1 hb2
    refine ⟨⟨h₂⁻¹ * c ^ k * h₁, H.mul_mem (H.mul_mem (H.inv_mem hh₂) (H.zpow_mem hcH k)) hh₁⟩,
      ?_, ?_⟩
    · show (h₂⁻¹ * c ^ k * h₁) a = a'
      rw [Perm.mul_apply, Perm.mul_apply, h₁a, Perm.zpow_apply_eq_self_of_apply_eq_self hcp k,
        ← h₂a]
      exact h₂.symm_apply_apply a'
    · show (h₂⁻¹ * c ^ k * h₁) b = b'
      rw [Perm.mul_apply, Perm.mul_apply, hk]
      exact h₂.symm_apply_apply b'
  exact Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (isPreprimitive_of_is_two_pretransitive h2) t ht (hSH htS)

theorem alternatingGroup_le_of_normal (hn : 5 ≤ n) {L : Subgroup (Perm (Fin n))} [L.Normal]
    (hL : ¬ Nat.card L ∣ 2) : alternatingGroup (Fin n) ≤ L := by
  classical
  have hs : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn)
  have hLn : (L.subgroupOf (alternatingGroup (Fin n))).Normal :=
    Subgroup.Normal.subgroupOf inferInstance _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf (alternatingGroup (Fin n))) with
    h | h
  · exfalso
    apply hL
    have hinj : Function.Injective (Perm.sign.comp L.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hxA : (x : Perm (Fin n)) ∈ alternatingGroup (Fin n) := hx
      have : (⟨x, hxA⟩ : alternatingGroup (Fin n)) ∈ L.subgroupOf (alternatingGroup (Fin n)) :=
        Subgroup.mem_subgroupOf.2 x.2
      rw [h, Subgroup.mem_bot] at this
      have hx1 : (x : Perm (Fin n)) = 1 := congrArg Subtype.val this
      exact (Subgroup.mem_bot).2 (Subtype.ext hx1)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at hle
    have hpos : 0 < Nat.card L := Nat.card_pos
    interval_cases h' : Nat.card L <;> norm_num
  · intro x hx
    have : (⟨x, hx⟩ : alternatingGroup (Fin n)) ∈ L.subgroupOf (alternatingGroup (Fin n)) := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

theorem false_of_perm (hn : n = 7 ∨ n = 8) {L S : Subgroup (Perm (Fin n))} (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ S.index) (hSL : S ≤ Subgroup.normalizer (L : Set (Perm (Fin n)))) {k : ℕ}
    (hL : Nat.card L = 2 ^ k * 21) : False := by
  classical
  have h7 : Nat.Prime 7 := by decide
  have : Fact (Nat.Prime 7) := ⟨h7⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := L) 7
    (by rw [hL]; exact Dvd.dvd.mul_left (by norm_num) _)
  have hc7 : (c : Perm (Fin n)) ^ 7 = 1 := by
    rw [← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one]
  have hc1 : (c : Perm (Fin n)) ≠ 1 := by
    intro h
    have : c = 1 := Subtype.ext h
    rw [this, orderOf_one] at hc
    norm_num at hc
  have htop : L ⊔ S = ⊤ := by
    rcases hn with rfl | rfl
    · exact eq_top_seven hS hidx le_sup_right (Subgroup.mem_sup_left c.2) hc7 hc1
    · exact eq_top_eight hS hidx le_sup_right (Subgroup.mem_sup_left c.2) hc7 hc1
  have hnorm : L.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer hSL
  have hA : alternatingGroup (Fin n) ≤ L := by
    refine alternatingGroup_le_of_normal (by rcases hn with rfl | rfl <;> norm_num) ?_
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    rw [hL] at this
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have : Nontrivial (Fin n) := by
    rcases hn with rfl | rfl <;> infer_instance
  have hdvd := Subgroup.card_dvd_of_le hA
  rw [hL, nat_card_alternatingGroup, Nat.card_fin] at hdvd
  have h5 : 5 ∣ 2 ^ k * 21 := by
    refine Nat.dvd_trans ?_ hdvd
    rcases hn with rfl | rfl <;> decide
  have h5' : ¬ 5 ∣ 2 ^ k * 21 := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h with h | h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h) (by norm_num)
    · norm_num at h
  exact h5' h5

end L1294J

end CFSG.Quasithin.H13
