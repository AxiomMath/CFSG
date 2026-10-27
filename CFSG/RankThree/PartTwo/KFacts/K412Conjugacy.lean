module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating10

public section

namespace CFSG.RankThree.PartTwo.KFacts.K412

open Equiv Subgroup CFSG.RankThree.PartTwo.KFacts.KP2
open scoped Pointwise

theorem exists_conj_le_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E : Subgroup G} (hE : IsPGroup p E) (P : Sylow p G) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ P := by
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 : MulAut.conj g • y ∈ MulAut.conj g • (Q : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (Q : Subgroup G) (hQ hy)
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact h1

theorem map_conj_comm {G : Type*} [Group G] {E : Subgroup G} (g : G)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, ∀ y ∈ E.map (MulAut.conj g).toMonoidHom,
      x * y = y * x := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, hab x hx y hy]

theorem card_map_conj {G : Type*} [Group G] (E : Subgroup G) (g : G) :
    Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_perm_seven : Nat.card (Perm (Fin 7)) = 5040 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem not_three_dvd_index_of_card_nine {E : Subgroup (Perm (Fin 7))} (h9 : Nat.card E = 9) :
    ¬ 3 ∣ E.index := by
  have h := E.card_mul_index
  rw [h9, card_perm_seven] at h
  omega

theorem exists_conj_eq_eNine {E : Subgroup (Perm (Fin 7))} (h9 : Nat.card E = 9) :
    ∃ g : Perm (Fin 7), E.map (MulAut.conj g).toMonoidHom = eNine := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  have hE0 : IsPGroup 3 eNine := IsPGroup.of_card (n := 2) (by rw [card_eNine]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hE (hE0.toSylow
    (not_three_dvd_index_of_card_nine card_eNine))
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [card_map_conj, h9, card_eNine]

@[expose] def sylTenF (i j k l : Fin 3) : Perm (Fin 10) := eTwentySevenF i j k * wCycle ^ (l : ℕ)

theorem wCycle_pow_three : wCycle ^ 3 = 1 := by
  decide +kernel

theorem wCycle_mem_normTen : wCycle ∈ normTen := (mem_inf.1 wCycle_mem_normAlt).1

theorem exists_pow_mul_eq (l i j k : Fin 3) : ∃ i' j' k' : Fin 3,
    wCycle ^ (l : ℕ) * eTwentySevenF i j k = eTwentySevenF i' j' k' * wCycle ^ (l : ℕ) := by
  obtain ⟨i', j', k', h⟩ := (mem_normalizer_iff.1 (pow_mem wCycle_mem_normTen (l : ℕ))
    (eTwentySevenF i j k)).1 ⟨i, j, k, rfl⟩
  exact ⟨i', j', k', by rw [← h]; group⟩

theorem wCycle_pow_mod (n : ℕ) : wCycle ^ n = wCycle ^ ((⟨n % 3, Nat.mod_lt _ (by norm_num)⟩ :
    Fin 3) : ℕ) :=
  pow_eq_pow_mod n wCycle_pow_three

@[expose] def sylTen : Subgroup (Perm (Fin 10)) where
  carrier := {x | ∃ i j k l, x = sylTenF i j k l}
  mul_mem' := by
    rintro _ _ ⟨i, j, k, l, rfl⟩ ⟨i', j', k', l', rfl⟩
    obtain ⟨a, b, c, h1⟩ := exists_pow_mul_eq l i' j' k'
    obtain ⟨a', b', c', h2⟩ := eTwentySevenF_mul i j k a b c
    refine ⟨a', b', c', ⟨((l : ℕ) + l') % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    rw [sylTenF, sylTenF, sylTenF, ← wCycle_pow_mod, pow_add,
      show eTwentySevenF i j k * wCycle ^ (l : ℕ) * (eTwentySevenF i' j' k' * wCycle ^ (l' : ℕ)) =
        eTwentySevenF i j k * (wCycle ^ (l : ℕ) * eTwentySevenF i' j' k') * wCycle ^ (l' : ℕ) by
        group, h1, ← h2]
    group
  one_mem' := ⟨0, 0, 0, 0, by rw [sylTenF, eTwentySevenF_zero]; simp⟩
  inv_mem' := by
    rintro _ ⟨i, j, k, l, rfl⟩
    obtain ⟨a, b, c, h1⟩ := eTwentySevenF_inv i j k
    obtain ⟨a', b', c', h2⟩ := exists_pow_mul_eq ⟨(2 * (l : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩
      a b c
    refine ⟨a', b', c', ⟨(2 * (l : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    have hinv : (wCycle ^ (l : ℕ))⁻¹ = wCycle ^ ((2 * (l : ℕ)) % 3) := by
      rw [← pow_eq_pow_mod _ wCycle_pow_three]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show (l : ℕ) + 2 * l = 3 * l by ring, pow_mul, wCycle_pow_three, one_pow]
    rw [sylTenF, sylTenF, mul_inv_rev, hinv, h1]
    exact h2

@[expose] def blockOf (x : Fin 10) : ℕ := if x.val < 3 then 0 else if x.val < 6 then 1 else 2

theorem blockOf_sylTenF : ∀ i j k l : Fin 3, blockOf (sylTenF i j k l 0) = l.val := by
  decide +kernel

theorem eTwentySevenF_injective : ∀ p q : Fin 3 × Fin 3 × Fin 3,
    eTwentySevenF p.1 p.2.1 p.2.2 = eTwentySevenF q.1 q.2.1 q.2.2 → p = q := by
  decide +kernel

theorem sylTenF_injective : Function.Injective
    (fun q : Fin 3 × Fin 3 × Fin 3 × Fin 3 => sylTenF q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  rintro ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩ h
  simp only at h
  have hl : l = l' := by
    have h0 := congrArg (fun σ : Perm (Fin 10) => blockOf (σ 0)) h
    simp only [blockOf_sylTenF] at h0
    exact Fin.ext h0
  subst hl
  have h' : eTwentySevenF i j k = eTwentySevenF i' j' k' := mul_right_cancel h
  have := eTwentySevenF_injective (i, j, k) (i', j', k') h'
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

theorem card_sylTen : Nat.card sylTen = 81 := by
  have : (sylTen : Set (Perm (Fin 10))) =
      Set.range (fun q : Fin 3 × Fin 3 × Fin 3 × Fin 3 => sylTenF q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    ext x
    exact ⟨fun ⟨i, j, k, l, h⟩ => ⟨(i, j, k, l), h.symm⟩,
      fun ⟨q, h⟩ => ⟨q.1, q.2.1, q.2.2.1, q.2.2.2, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, this, Nat.card_range_of_injective sylTenF_injective]
  simp

theorem card_eTwentySeven : Nat.card eTwentySeven = 27 := by
  have : (eTwentySeven : Set (Perm (Fin 10))) =
      Set.range (fun q : Fin 3 × Fin 3 × Fin 3 => eTwentySevenF q.1 q.2.1 q.2.2) := by
    ext x
    exact ⟨fun ⟨i, j, k, h⟩ => ⟨(i, j, k), h.symm⟩, fun ⟨q, h⟩ => ⟨q.1, q.2.1, q.2.2, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, this,
    Nat.card_range_of_injective (fun p q h => eTwentySevenF_injective p q h)]
  simp

theorem card_perm_ten : Nat.card (Perm (Fin 10)) = 3628800 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem eTwentySeven_le_sylTen : eTwentySeven ≤ sylTen := by
  rintro _ ⟨i, j, k, rfl⟩
  exact ⟨i, j, k, 0, by simp [sylTenF]⟩

theorem commute_sylTenF : ∀ a b c l : Fin 3, l ≠ 0 → ∀ i j k : Fin 3,
    eTwentySevenF i j k * sylTenF a b c l = sylTenF a b c l * eTwentySevenF i j k →
      i = j ∧ j = k := by
  decide +kernel

theorem diag_pow : ∀ i : Fin 3, eTwentySevenF i i i = eTwentySevenF 1 1 1 ^ (i : ℕ) := by
  decide +kernel

theorem diag_spec : eTwentySevenF 1 1 1 ^ 3 = 1 ∧ eTwentySevenF 1 1 1 ≠ 1 := by
  decide +kernel

theorem eq_eTwentySeven_of_le_sylTen {E : Subgroup (Perm (Fin 10))} (hE : E ≤ sylTen)
    (h27 : Nat.card E = 27) (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : E = eTwentySeven := by
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [h27, card_eTwentySeven])
  obtain ⟨a, b, c, l, rfl⟩ := hE hx
  by_cases hl : l = 0
  · subst hl
    exact ⟨a, b, c, by simp [sylTenF]⟩
  exfalso
  have hle : E ⊓ eTwentySeven ≤ zpowers (eTwentySevenF 1 1 1) := by
    rintro y ⟨hyE, i, j, k, rfl⟩
    obtain ⟨rfl, rfl⟩ := commute_sylTenF a b c l hl i j k (hab _ hyE _ hx)
    rw [diag_pow i]
    exact pow_mem (mem_zpowers (eTwentySevenF 1 1 1)) _
  have hcard3 : Nat.card (E ⊓ eTwentySeven : Subgroup (Perm (Fin 10))) ≤ 3 := by
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, orderOf_eq_prime diag_spec.1 diag_spec.2] at this
  have hidx : ∀ H : Subgroup (Perm (Fin 10)), Nat.card H = 27 → H ≤ sylTen →
      H.relIndex sylTen = 3 := by
    intro H hH hHS
    have h1 := relIndex_mul_index hHS
    have h2 := H.card_mul_index
    have h3 := sylTen.card_mul_index
    rw [hH, card_perm_ten] at h2
    rw [card_sylTen, card_perm_ten] at h3
    have h4 : sylTen.index = 44800 := by omega
    have h5 : H.index = 134400 := by omega
    rw [h4, h5] at h1
    omega
  have hinf : (E ⊓ eTwentySeven).relIndex sylTen ≤
      E.relIndex sylTen * eTwentySeven.relIndex sylTen := Subgroup.relIndex_inf_le
  rw [hidx E h27 hE, hidx _ card_eTwentySeven eTwentySeven_le_sylTen] at hinf
  have h1 := relIndex_mul_index (inf_le_left.trans hE : E ⊓ eTwentySeven ≤ sylTen)
  have h2 := (E ⊓ eTwentySeven).card_mul_index
  have h3 := sylTen.card_mul_index
  rw [card_sylTen, card_perm_ten] at h3
  rw [card_perm_ten] at h2
  have h4 : sylTen.index = 44800 := by omega
  rw [h4] at h1
  have h5 : (E ⊓ eTwentySeven).index ≤ 9 * 44800 := by
    rw [← h1]
    exact Nat.mul_le_mul_right _ hinf
  have h6 : Nat.card (E ⊓ eTwentySeven : Subgroup (Perm (Fin 10))) *
      (E ⊓ eTwentySeven).index ≤ 3 * (9 * 44800) := Nat.mul_le_mul hcard3 h5
  omega

theorem not_three_dvd_index_sylTen : ¬ 3 ∣ sylTen.index := by
  have h := sylTen.card_mul_index
  rw [card_sylTen, card_perm_ten] at h
  omega

theorem exists_conj_eq_eTwentySeven {E : Subgroup (Perm (Fin 10))} (h27 : Nat.card E = 27)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ g : Perm (Fin 10), E.map (MulAut.conj g).toMonoidHom = eTwentySeven := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [h27]; norm_num)
  have hS : IsPGroup 3 sylTen := IsPGroup.of_card (n := 4) (by rw [card_sylTen]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hE (hS.toSylow not_three_dvd_index_sylTen)
  exact ⟨g, eq_eTwentySeven_of_le_sylTen hg (by rw [card_map_conj, h27]) (map_conj_comm g hab)⟩

end CFSG.RankThree.PartTwo.KFacts.K412
