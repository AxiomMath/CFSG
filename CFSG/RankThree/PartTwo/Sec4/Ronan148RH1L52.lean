module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A8
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL52

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec4.Res417Four
  (a5 b5 r5 E9 card_E9 rs5_spec gl5EquivProjSL factorization_card_GL5 a5_mem b5_mem rN5)

section GL5

theorem gl5_facts : a5 ^ 3 = 1 ∧ b5 ^ 3 = 1 ∧ a5 * b5 = b5 * a5 ∧ a5 ≠ 1 ∧ b5 ≠ 1 ∧
    b5 ≠ a5 ∧ b5 ≠ a5⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem gl5_e9 : CFSG.Assembly.IsElemAbelian 3 E9 ∧ Nat.card E9 = 9 := by
  obtain ⟨ha3, hb3, hab, ha1, hb1, hba, hbai⟩ := gl5_facts
  exact e9_of_commute ha3 ha1 hb3 hab (not_mem_zpowers_of_ne ha3 hb1 hba hbai)

theorem mem_E9_gl5 {x : GL (Fin 5) (ZMod 2)} (hx : x ∈ E9) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ x = a5 ^ i * b5 ^ j := by
  obtain ⟨ha3, hb3, hab, -, -, -, -⟩ := gl5_facts
  have hc : ∀ u ∈ Subgroup.zpowers a5, ∀ v ∈ Subgroup.zpowers b5, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute a5 b5 from hab).zpow_zpow i j).eq
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).2
  have hx' : x ∈ ((Subgroup.zpowers a5 ⊔ Subgroup.zpowers b5 : Subgroup _) : Set _) := hx
  rw [hset] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx'
  have hpow : ∀ (c : GL (Fin 5) (ZMod 2)), c ^ 3 = 1 → ∀ w ∈ Subgroup.zpowers c,
      ∃ k : ℕ, k < 3 ∧ w = c ^ k := by
    intro c hc3 w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨(k % 3).toNat, by omega, ?_⟩
    have h1 : c ^ k = c ^ (k % 3) := zpow_eq_zpow_emod' k hc3
    rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
  obtain ⟨i, hi, rfl⟩ := hpow a5 ha3 u hu
  obtain ⟨j, hj, rfl⟩ := hpow b5 hb3 v hv
  exact ⟨i, j, hi, hj, rfl⟩

theorem gl5_move (s : GL (Fin 5) (ZMod 2)) (hs : s ∈ E9) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (E9 : Set (GL (Fin 5) (ZMod 2))),
      n ∉ Subgroup.normalizer
        ((Subgroup.zpowers s : Subgroup (GL (Fin 5) (ZMod 2))) : Set (GL (Fin 5) (ZMod 2))) := by
  obtain ⟨i, j, hi, hj, rfl⟩ := mem_E9_gl5 hs
  have key : ∀ t : GL (Fin 5) (ZMod 2), t ^ 3 = 1 →
      r5 * t * r5⁻¹ ≠ 1 → r5 * t * r5⁻¹ ≠ t → r5 * t * r5⁻¹ ≠ t⁻¹ →
      r5 ∉ Subgroup.normalizer
        ((Subgroup.zpowers t : Subgroup (GL (Fin 5) (ZMod 2))) : Set (GL (Fin 5) (ZMod 2))) :=
    fun t ht h1 h2 h3 => not_mem_normalizer_of_conj (not_mem_zpowers_of_ne ht h1 h2 h3)
  refine ⟨r5, rN5.2, ?_⟩
  interval_cases i <;> interval_cases j
  · exact absurd (by decide +kernel) hs1
  all_goals refine key _ ?_ ?_ ?_ ?_ <;> decide +kernel

theorem e9Move_gl5 : E9Move (GL (Fin 5) (ZMod 2)) :=
  e9Move_of_sylow factorization_card_GL5 gl5_e9.2 gl5_move

theorem rankTwo_gl5 : RankTwoData (GL (Fin 5) (ZMod 2)) := by
  haveI : Finite (projSL 5 (GaloisField 2 1)) := Finite.of_equiv _ gl5EquivProjSL.toEquiv
  refine ⟨cubeInner_of_mulEquiv gl5EquivProjSL (cubeInner_of_not_three_dvd_card_outer
    (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num))),
    fun E hE => ?_, ⟨E9, gl5_e9⟩⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 _ g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hd : 3 ^ k ∣ Nat.card (GL (Fin 5) (ZMod 2)) := hk ▸ Subgroup.card_subgroup_dvd_card E
  rw [hk]
  have : k ≤ 2 := by
    by_contra h
    push Not at h
    exact RonanK432.not_27_dvd_card_gl5 ((Nat.pow_dvd_pow 3 h).trans hd)
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    _ = 9 := by norm_num

theorem card_gl5 : Nat.card (GL (Fin 5) (ZMod 2)) = 9999360 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem l52_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 9999360 →
      9999360 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 9999360 →
      9999360 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 10) (by norm_num) (by decide +kernel)

end GL5

section Row


theorem rowOf427_l52
    : RowOf427 (projSL 5 (GaloisField 2 1)) := by
  haveI : Finite (projSL 5 (GaloisField 2 1)) := Finite.of_equiv _ gl5EquivProjSL.toEquiv
  have hcard : Nat.card (projSL 5 (GaloisField 2 1)) = 9999360 := by
    rw [← Nat.card_congr gl5EquivProjSL.toEquiv, card_gl5]
  refine rowOf427_of_e9Move ?_ (RankTwoData.of_mulEquiv gl5EquivProjSL.symm rankTwo_gl5)
    (fun S _ _ ⟨e⟩ => e9Move_gl5.of_mulEquiv (e.trans gl5EquivProjSL.symm))
    (by rw [hcard]; norm_num)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
    l52_orderChecks.1 l52_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
