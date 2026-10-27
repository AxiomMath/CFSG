module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckA6

open CFSG.RankThree.PartTwo.Sec4 (IsTripleCover)

private theorem isSolvable_of_card_dvd_180 {Q : Type*} [Group Q] [Finite Q]
    (hd : Nat.card Q ∣ 180) (hle : Nat.card Q ≤ 30) : Group.IsSolvable Q := by
  have key : Nat.card Q ∣ 2 ^ 2 * 3 ^ 2 ∨ Nat.card Q ∣ 2 ^ 2 * 5 ^ 1 ∨
      Nat.card Q ∣ 3 ^ 1 * 5 ^ 1 ∨ Nat.card Q = 30 := by
    generalize Nat.card Q = m at hd hle
    interval_cases m <;> first | (exfalso; revert hd; decide) | decide
  rcases key with h | h | h | h
  · exact TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three h
  · exact TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_five h
  · exact TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_three Nat.prime_five h
  · have hsq : Squarefree (Nat.card Q) := by
      have h30 : (30 : ℕ) = 2 * 3 * 5 := by norm_num
      rw [h, h30, Nat.squarefree_mul (by norm_num), Nat.squarefree_mul (by norm_num)]
      exact ⟨⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩, Nat.prime_five.squarefree⟩
    haveI : IsZGroup Q := IsZGroup.of_squarefree hsq
    infer_instance

private theorem eq_bot_of_isPerfect_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {F : Subgroup G} (hF : Group.IsPerfect ↥F) (hp : IsPGroup p F) : F = ⊥ := by
  by_contra hne
  haveI : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).2 hne
  haveI := hF
  haveI : Group.IsNilpotent F := hp.isNilpotent
  exact Group.IsPerfect.not_isNilpotent F inferInstance

private theorem le_of_isPerfect_of_isSolvable_quotient {G : Type*} [Group G] {F U N : Subgroup G}
    [(U.subgroupOf N).Normal] (hF : Group.IsPerfect ↥F) (hFN : F ≤ N)
    (hQ : Group.IsSolvable (↥N ⧸ U.subgroupOf N)) : F ≤ U := by
  haveI := hF
  let φ : ↥F →* ↥N ⧸ U.subgroupOf N :=
    (QuotientGroup.mk' (U.subgroupOf N)).comp (Subgroup.inclusion hFN)
  haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hbot : φ.range = ⊥ := by
    by_contra hne
    haveI : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  intro x hx
  have h1 : φ ⟨x, hx⟩ = 1 := by
    have hmem : φ ⟨x, hx⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  exact (QuotientGroup.eq_one_iff (N := U.subgroupOf N) (⟨x, hFN hx⟩ : N)).1 h1

private theorem six_le_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 360) {H : Subgroup G} (hH : H ≠ ⊤) : 6 ≤ H.index := by
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_perm, ← Subgroup.index_eq_card, hG] at h1
  by_contra hlt
  have h5 : H.index.factorial ≤ (5 : ℕ).factorial := Nat.factorial_le (by omega)
  have h120 : (5 : ℕ).factorial = 120 := by decide
  omega

private theorem isSolvable_normalizer_quotient {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 360) {U : Subgroup G} (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) :
    Group.IsSolvable (↥(Subgroup.normalizer (U : Set G)) ⧸
      U.subgroupOf (Subgroup.normalizer (U : Set G))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUcard : 1 < Nat.card U := (Subgroup.one_lt_card_iff_ne_bot U).2 hU1
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 hU
  have ha0 : a ≠ 0 := by
    rintro rfl
    omega
  have h2U : 2 ∣ Nat.card U := ha ▸ dvd_pow_self 2 ha0
  have hNtop : Subgroup.normalizer (U : Set G) ≠ ⊤ := by
    intro h
    haveI : U.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h' | h'
    · exact hU1 h'
    · rw [h', Subgroup.card_top, hG] at ha
      have h3 : 3 ∣ 2 ^ a := ha ▸ (by norm_num : 3 ∣ 360)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hN60 : Nat.card (Subgroup.normalizer (U : Set G)) ≤ 60 := by
    have h6 := six_le_index hG hNtop
    have hmul := Subgroup.card_mul_index (Subgroup.normalizer (U : Set G))
    rw [hG] at hmul
    nlinarith
  have hN360 : Nat.card (Subgroup.normalizer (U : Set G)) ∣ 360 :=
    hG ▸ Subgroup.card_subgroup_dvd_card _
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (U.subgroupOf (Subgroup.normalizer (U : Set G)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv] at hQ
  refine isSolvable_of_card_dvd_180 ?_ ?_
  · rw [hQ] at hN360
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 2)
      (((Nat.mul_dvd_mul_left _ h2U).trans hN360).trans (by norm_num))
  · rw [hQ] at hN60
    nlinarith

theorem eq_bot_of_isPerfect_le_normalizer_A6 {F U : Subgroup (alternatingGroup (Fin 6))}
    (hF : Group.IsPerfect ↥F) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hFU : F ≤ Subgroup.normalizer (U : Set (alternatingGroup (Fin 6)))) : F = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hG : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  exact eq_bot_of_isPerfect_of_isPGroup hF (hU.to_le (le_of_isPerfect_of_isSolvable_quotient hF hFU
    (isSolvable_normalizer_quotient hG hU hU1)))

theorem eq_bot_of_isPerfect_le_normalizer_of_hom_A6 {X : Type*} [Group X] [Finite X]
    (π : X →* alternatingGroup (Fin 6)) (hker : IsPGroup 3 π.ker) {F U : Subgroup X}
    (hF : Group.IsPerfect ↥F) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hFU : F ≤ Subgroup.normalizer (U : Set X)) : F = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hF
  have hUbar : U.map π ≠ ⊥ := by
    intro h
    exact hU1 ((IsPGroup.disjoint_of_ne 2 3 (by norm_num) U π.ker hU hker).eq_bot_of_le
      ((Subgroup.map_eq_bot_iff U).1 h))
  have hFbar : F.map π = ⊥ :=
    eq_bot_of_isPerfect_le_normalizer_A6 (Group.IsPerfect.map π) (hU.map π) hUbar
      ((Subgroup.map_mono hFU).trans (Subgroup.le_normalizer_map π))
  exact eq_bot_of_isPerfect_of_isPGroup hF (hker.to_le ((Subgroup.map_eq_bot_iff F).1 hFbar))

theorem eq_bot_of_isPerfect_le_normalizer_tripleA6 {X : Type*} [Group X] [Finite X]
    (h : IsTripleCover X (alternatingGroup (Fin 6))) {F U : Subgroup X}
    (hF : Group.IsPerfect ↥F) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hFU : F ≤ Subgroup.normalizer (U : Set X)) : F = ⊥ := by
  obtain ⟨hZ, ⟨e⟩⟩ := h
  let π : X →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hker : π.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' (Subgroup.center X) x) = 1 ↔ x ∈ Subgroup.center X
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  refine eq_bot_of_isPerfect_le_normalizer_of_hom_A6 π ?_ hF hU hU1 hFU
  rw [hker]
  exact IsPGroup.of_card (p := 3) (n := 1) (by rw [hZ]; norm_num)

end CFSG.RankThree.PartTwo.Sec15.LiebeckA6
