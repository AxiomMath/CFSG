module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrS5
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

@[expose] def pairSub {G : Type*} [Group G] (a : G) (ha : a * a = 1) : Subgroup G where
  carrier := {g | g = 1 ∨ g = a}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> simp [ha]
  inv_mem' := by
    rintro x (rfl | rfl)
    · simp
    · exact Or.inr (inv_eq_of_mul_eq_one_right ha)

theorem relIndex_eq_two_of_cover {G : Type*} [Group G] {B A : Subgroup G} {x : G} (hxA : x ∈ A)
    (hxB : x ∉ B) (hcov : ∀ g ∈ A, g ∈ B ∨ g * x ∈ B) : B.relIndex A = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨x, hxA, fun b hb => ?_⟩
  rcases hcov b hb with h | h
  · exact Or.inr ⟨h, fun h' => hxB (by simpa using B.mul_mem (B.inv_mem h) h')⟩
  · exact Or.inl ⟨h, fun h' => hxB (by simpa using B.mul_mem (B.inv_mem h') h)⟩

theorem S4_le_of_D8_lt {K : Subgroup (Perm (Fin 5))} (hK : D8 ≤ K) (hne : K ≠ D8) : S4 ≤ K := by
  by_cases h4 : ∀ x ∈ K, x 4 = 4
  · have hKS : K ≤ S4 := fun x hx => h4 x hx
    obtain ⟨k, hk⟩ : 8 ∣ Nat.card K := card_D8 ▸ Subgroup.card_dvd_of_le hK
    have h24 : Nat.card K ∣ 24 := card_S4 ▸ Subgroup.card_dvd_of_le hKS
    have hk3 : k ∣ 3 := by
      rw [hk, show (24 : ℕ) = 8 * 3 by norm_num] at h24
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h24
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
    · exact absurd (Subgroup.eq_of_le_of_card_ge hK (by rw [hk, card_D8])).symm hne
    · rw [Subgroup.eq_of_le_of_card_ge hKS (by rw [hk, card_S4])]
  · push Not at h4
    obtain ⟨x, hxK, hx4⟩ := h4
    have hto4 : ∀ a : Fin 5, ∃ g ∈ K, g a = 4 := by
      intro a
      by_cases ha : a = 4
      · exact ⟨1, K.one_mem, by rw [ha]; rfl⟩
      · obtain ⟨σ, hσ, hσa⟩ := exists_D8_apply a (x 4) ha hx4
        refine ⟨x⁻¹ * σ, K.mul_mem (K.inv_mem hxK) (hK hσ), ?_⟩
        rw [Perm.mul_apply, hσa, Perm.inv_def, Equiv.symm_apply_apply]
    have : MulAction.IsPretransitive K (Fin 5) := by
      rw [MulAction.isPretransitive_iff]
      intro a b
      obtain ⟨g, hg, hga⟩ := hto4 a
      obtain ⟨h, hh, hhb⟩ := hto4 b
      refine ⟨⟨h⁻¹ * g, K.mul_mem (K.inv_mem hh) hg⟩, ?_⟩
      change (h⁻¹ * g) a = b
      rw [Perm.mul_apply, hga, ← hhb, Perm.inv_def, Equiv.symm_apply_apply]
    have hprim := MulAction.IsPreprimitive.of_prime_card (G := K) (X := Fin 5)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    rw [Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hprim (swap 0 2)
      ⟨0, 2, by decide, rfl⟩ (hK (by decide))]
    exact le_top

theorem card_perm_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem not_two_dvd_index {H : Subgroup (Perm (Fin 5))} (hH : Nat.card H = 8) : ¬ 2 ∣ H.index := by
  have h := H.card_mul_index
  rw [hH, card_perm_five] at h
  have h15 : H.index = 15 := by omega
  rw [h15]
  norm_num

theorem card_le_four {D : Subgroup (Perm (Fin 5))} (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (h2 : ∀ a ∈ D, a * a = 1) : Nat.card D ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : IsPGroup 2 D := fun g => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (h2 g g.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hD
  have hdvd : 2 ^ k ∣ 120 := hk ▸ card_perm_five ▸ Subgroup.card_subgroup_dvd_card D
  have hk3 : k ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 120 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h16
  rcases (by omega : k ≤ 2 ∨ k = 3) with hk2 | rfl
  · rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  · exfalso
    have hD8 : IsPGroup 2 D8 := IsPGroup.of_card (n := 3) (by rw [card_D8]; norm_num)
    let P0 := hD8.toSylow (not_two_dvd_index card_D8)
    let P1 := hD.toSylow (not_two_dvd_index (by rw [hk]; norm_num))
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) P0 P1
    obtain ⟨a, ha, b, hb, hab⟩ := D8_not_comm
    have hmem : ∀ y ∈ D8, MulAut.conj g y ∈ D := by
      intro y hy
      have h1 : ((g • P0 : Sylow 2 (Perm (Fin 5))) : Subgroup (Perm (Fin 5))) = D := by
        rw [hg]
        rfl
      rw [← h1, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ (D8 : Subgroup (Perm (Fin 5))) hy
    apply hab
    apply (MulAut.conj g).injective
    rw [map_mul, map_mul]
    exact hc _ (hmem a ha) _ (hmem b hb)

theorem elem_cases {D : Subgroup (Perm (Fin 5))} (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (h2 : ∀ a ∈ D, a * a = 1) :
    D = ⊥ ∨ (∃ a ∈ D, a ≠ 1 ∧ ∀ d ∈ D, d = 1 ∨ d = a) ∨
      ∃ a ∈ D, ∃ b ∈ D, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
        ∀ d ∈ D, d = 1 ∨ d = a ∨ d = b ∨ d = a * b := by
  by_cases hD : D = ⊥
  · exact Or.inl hD
  right
  obtain ⟨⟨a, ha⟩, ha1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hD
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  by_cases hb : ∃ b ∈ D, b ≠ 1 ∧ b ≠ a
  · obtain ⟨b, hbD, hb1, hba⟩ := hb
    right
    refine ⟨a, ha, b, hbD, ha1, hb1, fun h => hba h.symm, fun d hd => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨hd1, hda, hdb, hdab⟩ := hne
    have haa := h2 a ha
    have hbb := h2 b hbD
    have hab1 : a * b ≠ 1 := fun h =>
      hba (by rw [← one_mul b, ← haa, mul_assoc, h, mul_one])
    have haba : a * b ≠ a := fun h => hb1 (by
      rw [← one_mul b, ← haa, mul_assoc, h, haa])
    have habb : a * b ≠ b := fun h => ha1 (by
      rw [← mul_one a, ← hbb, ← mul_assoc, h, hbb])
    let f : Fin 5 → D := ![1, ⟨a, ha⟩, ⟨b, hbD⟩, ⟨a * b, D.mul_mem ha hbD⟩, ⟨d, hd⟩]
    have hs : 1 ≠ a ∧ 1 ≠ b ∧ b ≠ a ∧ 1 ≠ a * b ∧ a ≠ a * b ∧ b ≠ a * b ∧ 1 ≠ d ∧ a ≠ d ∧
        b ≠ d ∧ a * b ≠ d :=
      ⟨Ne.symm ha1, Ne.symm hb1, hba, Ne.symm hab1, Ne.symm haba, Ne.symm habb, Ne.symm hd1,
        Ne.symm hda, Ne.symm hdb, Ne.symm hdab⟩
    have hf : Function.Injective f := by
      intro i j hij
      have hij' := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | (exfalso; simp [f] at hij'; tauto)
    have h5 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at h5
    have h4 := card_le_four hc h2
    omega
  · push Not at hb
    left
    exact ⟨a, ha, ha1, fun d hd => by
      by_cases h1 : d = 1
      · exact Or.inl h1
      · exact Or.inr (hb d hd h1)⟩

theorem exists_hyperplane_fix {D : Subgroup (Perm (Fin 5))}
    (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (h2 : ∀ a ∈ D, a * a = 1) (hD : D ≠ ⊥) :
    ∃ D' : Subgroup (Perm (Fin 5)), D' ≤ D ∧ (∃ x ∈ D, x ∉ D' ∧ ∀ d ∈ D, d ∈ D' ∨ d * x ∈ D') ∧
      ∃ u, IsO u ∧ (∀ d ∈ D', pv d u = u) ∧ ∃ d ∈ D, pv d u ≠ u := by
  rcases elem_cases hc h2 with h | ⟨a, ha, ha1, hD1⟩ | ⟨a, ha, b, hb, ha1, hb1, hab, hD4⟩
  · exact absurd h hD
  · obtain ⟨u, hu, hau⟩ := exists_not_fix_one a (h2 a ha) ha1
    refine ⟨⊥, bot_le, ⟨a, ha, by rwa [Subgroup.mem_bot], fun d hd => ?_⟩, u, hu,
      fun d hd => ?_, a, ha, hau⟩
    · rcases hD1 d hd with rfl | rfl
      · exact Or.inl (Subgroup.one_mem _)
      · exact Or.inr (by rw [h2 _ ha]; exact Subgroup.one_mem _)
    · rw [Subgroup.mem_bot] at hd
      rw [hd]
      rfl
  · have haa := h2 a ha
    have hbb := h2 b hb
    rcases exists_fix_not_fix_two a b haa hbb (hc a ha b hb) hab ha1 hb1 with
      ⟨u, hu, hau, hbu⟩ | ⟨u, hu, hbu, hau⟩
    · refine ⟨pairSub a haa, ?_, ⟨b, hb, ?_, fun d hd => ?_⟩, u, hu, fun d hd => ?_, b, hb, hbu⟩
      · rintro g (rfl | rfl)
        · exact D.one_mem
        · exact ha
      · rintro (h | h)
        · exact hb1 h
        · exact hab h.symm
      · rcases hD4 d hd with rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr (Or.inl hbb)
        · exact Or.inr (Or.inr (by rw [mul_assoc, hbb, mul_one]))
      · rcases hd with rfl | rfl
        · rfl
        · exact hau
    · refine ⟨pairSub b hbb, ?_, ⟨a, ha, ?_, fun d hd => ?_⟩, u, hu, fun d hd => ?_, a, ha, hau⟩
      · rintro g (rfl | rfl)
        · exact D.one_mem
        · exact hb
      · rintro (h | h)
        · exact ha1 h
        · exact hab h
      · rcases hD4 d hd with rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr (Or.inl haa)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr (Or.inr (by rw [mul_assoc, ← hc a ha b hb, ← mul_assoc, haa, one_mul]))
      · rcases hd with rfl | rfl
        · rfl
        · exact hbu

theorem exists_fix_ne_zero {D : Subgroup (Perm (Fin 5))}
    (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (h2 : ∀ a ∈ D, a * a = 1) :
    ∃ u, IsO u ∧ u ≠ 0 ∧ ∀ d ∈ D, pv d u = u := by
  rcases elem_cases hc h2 with h | ⟨a, ha, -, hD1⟩ | ⟨a, ha, b, hb, -, -, -, hD4⟩
  · obtain ⟨u, hu, hu0, -, -⟩ := exists_fix_ne_zero_two 1 1 (by simp) (by simp) rfl
    refine ⟨u, hu, hu0, fun d hd => ?_⟩
    rw [h, Subgroup.mem_bot] at hd
    rw [hd]
    rfl
  · obtain ⟨u, hu, hu0, hau, -⟩ := exists_fix_ne_zero_two a a (h2 a ha) (h2 a ha) rfl
    refine ⟨u, hu, hu0, fun d hd => ?_⟩
    rcases hD1 d hd with rfl | rfl
    · rfl
    · exact hau
  · obtain ⟨u, hu, hu0, hau, hbu⟩ :=
      exists_fix_ne_zero_two a b (h2 a ha) (h2 b hb) (hc a ha b hb)
    refine ⟨u, hu, hu0, fun d hd => ?_⟩
    rcases hD4 d hd with rfl | rfl | rfl | rfl
    · rfl
    · exact hau
    · exact hbu
    · rw [pv_mul, hbu, hau]

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
