module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowA1112
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowAlt
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1E9

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open Equiv Equiv.Perm

section Sylow

open scoped Pointwise

variable {S : Type} [Group S] [Finite S]

theorem e9Move_of_sylow (h3 : (Nat.card S).factorization 3 = 2) {E₀ : Subgroup S}
    (hE₀ : Nat.card E₀ = 9)
    (hmv : ∀ s ∈ E₀, s ≠ 1 → ∃ n ∈ Subgroup.normalizer (E₀ : Set S),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S)) : E9Move S := by
  intro E _ hE9 s hs hs1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Sylow 3 S := Sylow.ofCard E₀ (by rw [hE₀, h3]; norm_num)
  let P : Sylow 3 S := Sylow.ofCard E (by rw [hE9, h3]; norm_num)
  haveI : Finite (Sylow 3 S) := Sylow.finite_of_finiteIndex Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q P
  have hPg : E = MulAut.conj g • E₀ := by
    have h := congrArg (fun R : Sylow 3 S => (R : Subgroup S)) hg
    simp only [Sylow.coe_subgroup_smul] at h
    exact h.symm
  have hmap : E = E₀.map (MulAut.conj g).toMonoidHom := by
    rw [hPg]
    rfl
  rw [hmap] at hs ⊢
  obtain ⟨s', hs', rfl⟩ := hs
  have hs'1 : s' ≠ 1 := by
    rintro rfl
    exact hs1 (map_one _)
  obtain ⟨n, hn, hns⟩ := hmv s' hs' hs'1
  refine ⟨(MulAut.conj g) n, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨n, hn, rfl⟩
  · intro hn'
    apply hns
    have hZ : (Subgroup.zpowers s').map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers ((MulAut.conj g).toMonoidHom s') := MonoidHom.map_zpowers _ s'
    rw [← hZ, ← Subgroup.map_equiv_normalizer_eq] at hn'
    obtain ⟨m, hm, hmn⟩ := hn'
    rwa [(MulAut.conj g).injective hmn] at hm

end Sylow

section A8

@[expose] def a8a : alternatingGroup (Fin 8) :=
  ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a8b : alternatingGroup (Fin 8) :=
  ⟨swap 3 4 * swap 4 5, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a8n1 : alternatingGroup (Fin 8) :=
  ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 6 7, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a8n2 : alternatingGroup (Fin 8) :=
  ⟨swap 0 1 * swap 6 7, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a8E : Subgroup (alternatingGroup (Fin 8)) :=
  Subgroup.zpowers a8a ⊔ Subgroup.zpowers a8b

theorem a8_facts : a8a ^ 3 = 1 ∧ a8b ^ 3 = 1 ∧ a8a * a8b = a8b * a8a ∧ a8a ≠ 1 ∧ a8b ≠ 1 ∧
    a8b ≠ a8a ∧ a8b ≠ a8a⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem a8_e9 : CFSG.Assembly.IsElemAbelian 3 a8E ∧ Nat.card a8E = 9 := by
  obtain ⟨ha3, hb3, hab, ha1, hb1, hba, hbai⟩ := a8_facts
  exact e9_of_commute ha3 ha1 hb3 hab (not_mem_zpowers_of_ne ha3 hb1 hba hbai)

theorem mem_a8E {x : alternatingGroup (Fin 8)} (hx : x ∈ a8E) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ x = a8a ^ i * a8b ^ j := by
  obtain ⟨ha3, hb3, hab, -, -, -, -⟩ := a8_facts
  have hc : ∀ u ∈ Subgroup.zpowers a8a, ∀ v ∈ Subgroup.zpowers a8b, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute a8a a8b from hab).zpow_zpow i j).eq
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).2
  have hx' : x ∈ ((Subgroup.zpowers a8a ⊔ Subgroup.zpowers a8b : Subgroup _) : Set _) := hx
  rw [hset] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx'
  have hpow : ∀ (c : alternatingGroup (Fin 8)), c ^ 3 = 1 → ∀ w ∈ Subgroup.zpowers c,
      ∃ k : ℕ, k < 3 ∧ w = c ^ k := by
    intro c hc3 w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨(k % 3).toNat, by omega, ?_⟩
    have h1 : c ^ k = c ^ (k % 3) := zpow_eq_zpow_emod' k hc3
    rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
  obtain ⟨i, hi, rfl⟩ := hpow a8a ha3 u hu
  obtain ⟨j, hj, rfl⟩ := hpow a8b hb3 v hv
  exact ⟨i, j, hi, hj, rfl⟩

theorem a8n_mem_normalizer : a8n1 ∈ Subgroup.normalizer (a8E : Set (alternatingGroup (Fin 8))) ∧
    a8n2 ∈ Subgroup.normalizer (a8E : Set (alternatingGroup (Fin 8))) := by
  have h1 : a8n1 * a8a * a8n1⁻¹ = a8b ∧ a8n1 * a8b * a8n1⁻¹ = a8a ∧
      a8n2 * a8a * a8n2⁻¹ = a8a ^ 2 ∧ a8n2 * a8b * a8n2⁻¹ = a8b := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  refine ⟨mem_normalizer_of_map_le ?_, mem_normalizer_of_map_le ?_⟩
  · rw [a8E, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      show a8n1 * a8a * a8n1⁻¹ ∈ _
      rw [h1.1]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · rw [Subgroup.zpowers_le]
      show a8n1 * a8b * a8n1⁻¹ ∈ _
      rw [h1.2.1]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · rw [a8E, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      show a8n2 * a8a * a8n2⁻¹ ∈ _
      rw [h1.2.2.1]
      exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2)
    · rw [Subgroup.zpowers_le]
      show a8n2 * a8b * a8n2⁻¹ ∈ _
      rw [h1.2.2.2]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem not_mem_normalizer_of_conj {G : Type*} [Group G] {n s : G}
    (h : n * s * n⁻¹ ∉ Subgroup.zpowers s) :
    n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set G) := fun hn =>
  h ((Subgroup.mem_normalizer_iff.mp hn s).mp (Subgroup.mem_zpowers s))

theorem a8_move (s : alternatingGroup (Fin 8)) (hs : s ∈ a8E) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (a8E : Set (alternatingGroup (Fin 8))),
      n ∉ Subgroup.normalizer
        ((Subgroup.zpowers s : Subgroup (alternatingGroup (Fin 8))) :
          Set (alternatingGroup (Fin 8))) := by
  obtain ⟨i, j, hi, hj, rfl⟩ := mem_a8E hs
  have key : ∀ n : alternatingGroup (Fin 8), ∀ t : alternatingGroup (Fin 8), t ^ 3 = 1 →
      n * t * n⁻¹ ≠ 1 → n * t * n⁻¹ ≠ t → n * t * n⁻¹ ≠ t⁻¹ →
      n ∉ Subgroup.normalizer
        ((Subgroup.zpowers t : Subgroup (alternatingGroup (Fin 8))) :
          Set (alternatingGroup (Fin 8))) := fun n t ht h1 h2 h3 =>
    not_mem_normalizer_of_conj (not_mem_zpowers_of_ne ht h1 h2 h3)
  interval_cases i <;> interval_cases j
  · exact absurd (by decide) hs1
  · exact ⟨a8n1, a8n_mem_normalizer.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a8n1, a8n_mem_normalizer.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a8n1, a8n_mem_normalizer.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a8n2, a8n_mem_normalizer.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a8n2, a8n_mem_normalizer.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a8n1, a8n_mem_normalizer.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a8n2, a8n_mem_normalizer.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a8n2, a8n_mem_normalizer.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩

theorem card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem e9Move_alt8 : E9Move (alternatingGroup (Fin 8)) := by
  have h3 : (Nat.card (alternatingGroup (Fin 8))).factorization 3 = 2 := by
    rw [card_alt8]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num) (by norm_num)
  exact e9Move_of_sylow h3 a8_e9.2 a8_move

theorem rankTwo_alt8 : RankTwoData (alternatingGroup (Fin 8)) := by
  refine ⟨cubeInner_of_not_three_dvd_card_outer (not_three_dvd_outer_alternatingGroup
    (by norm_num)), fun E hE => ?_, ⟨a8E, a8_e9⟩⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 _ g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hd : 3 ^ k ∣ 20160 := hk ▸ card_alt8 ▸ Subgroup.card_subgroup_dvd_card E
  rw [hk]
  have : k ≤ 2 := by
    by_contra h
    push Not at h
    have : 3 ^ 3 ∣ 20160 := (Nat.pow_dvd_pow 3 h).trans hd
    norm_num at this
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    _ = 9 := by norm_num

end A8

section Center


theorem center_eq_bot_of_alt8
    {L : Type} [Group L] [Finite L] (hS : SectionFourHyp L)
    (hL : IsQuasisimple L) (hZ3 : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 8)) : Subgroup.center L = ⊥ := by
  by_contra hne
  have h3 : 3 ∣ Nat.card (Subgroup.center L) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hZ3
    have h1 : 1 < Nat.card (Subgroup.center L) :=
      (Subgroup.one_lt_card_iff_ne_bot (H := Subgroup.center L)).2 hne
    rw [hn] at h1 ⊢
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at h1
    exact dvd_pow_self 3 hn0
  have hN : Nat.card (L ⧸ Subgroup.center L) = 20160 := (Nat.card_congr e.toEquiv).trans card_alt8
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_fin (n := 6) (by norm_num)]
    decide
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_fin (n := 7) (by norm_num)]
    decide
  rcases diag_item43_holds L hS hL h3 with
    hI | hSix | hSeven | hG2 | hU43 | hM22' | hJ3' | hMcL' | hON'
  · exact not_isType429_of_alternating_eight (Fintype.card_fin 8) e (Or.inl hI)
  · obtain ⟨φ⟩ := hSix
    have := hN.symm.trans ((Nat.card_congr φ.toEquiv).trans hA6)
    norm_num at this
  · obtain ⟨φ⟩ := hSeven
    have := hN.symm.trans ((Nat.card_congr φ.toEquiv).trans hA7)
    norm_num at this
  · exact CFSG.RankThree.PartTwo.Sec4.Item426.not_five_dvd_card_of_G2_three hG2
      (by rw [hN]; norm_num)
  · obtain ⟨φ⟩ := hU43
    have := hN.symm.trans ((Nat.card_congr φ.toEquiv).trans CFSG.PGLModel.card_projSU_four_three)
    norm_num at this
  · obtain ⟨φ⟩ := hM22'
    have := hN.symm.trans
      ((Nat.card_congr φ.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM22)
    norm_num at this
  · obtain ⟨φ⟩ := hJ3'
    have := hN.symm.trans ((Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.J3.card_J3)
    norm_num at this
  · obtain ⟨φ⟩ := hMcL'
    have := hN.symm.trans ((Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.McL.card_McL)
    norm_num at this
  · obtain ⟨φ⟩ := hON'
    have := hN.symm.trans ((Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.ON.card_ON)
    norm_num at this

end Center

section Row


theorem rowOf427_alt8
    : RowOf427 (alternatingGroup (Fin 8)) := by
  refine rowOf427_of_e9Move ?_ rankTwo_alt8 (fun S _ _ ⟨e⟩ => e9Move_alt8.of_mulEquiv e)
    (by rw [card_alt8]; norm_num)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_alt8 hSL hL hZ3 e'

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
