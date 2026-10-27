module

public import CFSG.Quasithin.H13.KG14726Alt
public import CFSG.Quasithin.H13.KG14726Lie
public import CFSG.Quasithin.H13.KG14726C27
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.RankThree.PartOne.S15K.LinAutRank

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup Equiv
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_mulAut_alternatingGroup_six_dvd :
    Nat.card (MulAut (alternatingGroup (Fin 6))) ∣ 1440 := by
  have hle := CFSG.LargeExtraspecial.S12Tri.card_mulAut_alternatingGroup_six_le
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6
    (by norm_num)
  have h720 : 720 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    have h1 := card_subgroup_dvd_card (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  obtain ⟨k, hk⟩ := h720
  have : Finite (MulAut (alternatingGroup (Fin 6))) :=
    Finite.of_injective _ MulEquiv.toEquiv_injective
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
  rw [hk] at hle hpos ⊢
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl <;> norm_num

theorem card_mulAut_dvd_of_quotientCenter_alternatingGroup_six
    {X : Type*} [Group X] [Group.IsPerfect X] (e : X ⧸ center X ≃* alternatingGroup (Fin 6)) :
    Nat.card (MulAut X) ∣ 1440 := by
  have h := card_mulAut_dvd_of_perfect (X := X)
  rw [card_mulAut_congr e] at h
  exact h.trans card_mulAut_alternatingGroup_six_dvd

theorem card_specialLinear_two {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem card_mulAut_dvd_of_mulEquiv_sl2_four {X : Type} [Group X] (hqs : CFSG.IsQuasisimple X)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Nat.card (MulAut X) ∣ 120 := by
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) (show Nat.card F = 2 ^ 2 by rw [hF]; norm_num)
  have hc : center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rw [← scalars_eq_center, scalars_two_eq_bot]
  have hcX : center X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hex : e x ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hx) z]
    rw [hc, mem_bot] at hex
    rw [mem_bot]
    exact e.injective (by rw [hex, map_one])
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) :=
    nontrivial_specialLinearGroup le_rfl F
  have : Nontrivial X := e.symm.injective.nontrivial
  have : IsSimpleGroup X := by
    have hs : IsSimpleGroup (X ⧸ center X) := hqs.2.1
    exact IsSimpleGroup.isSimpleGroup_of_surjective
      (quotientCenterEquivSelf hcX).toMonoidHom (quotientCenterEquivSelf hcX).surjective
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv, card_specialLinear_two, hF]
    norm_num
  obtain ⟨e₅⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    hcard
  rw [card_mulAut_congr e₅, card_mulAut_alternatingGroup (by norm_num) (by norm_num)]
  decide

section LinearAut

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem card_mulAut_projectiveSL_dvd' (hn : 3 ≤ n) {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card (MulAut (projectiveSL n K)) ∣ 2 * f * Nat.card (GL (Fin n) K) := by
  set E := semilinearAutGroup n K with hE
  set D := (conjAut n K).range with hD
  set Φ := (fieldAut n K).range with hΦ
  have hDn : D.Normal := CFSG.RankThree.PartOne.S15K.conjAut_range_normal hn
  have hEidx : E.index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨dualAut n K, fun b => ?_⟩
    have hb : b ∈ standardAutGroup n K := by
      rw [(automorphism_generation (K := K) hn).1]
      exact mem_top b
    rcases mem_or_mul_dualAut_mem hb with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hEsup : E = Φ ⊔ D := by
    rw [hE, semilinearAutGroup, Subgroup.closure_union, linearAutGroup_eq_range,
      Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq, sup_comm]
  have hEDidx : D.relIndex E ∣ f := by
    rw [hEsup, Subgroup.relIndex_sup_right]
    refine (Subgroup.relIndex_dvd_card D Φ).trans ?_
    refine (Subgroup.card_range_dvd (fieldAut n K)).trans ?_
    rw [(card_ringAut_and_isCyclic Nat.prime_two K hK).1]
  have hDE : D ≤ E := by
    rw [hD, ← linearAutGroup_eq_range]
    exact linearAutGroup_le_semilinearAutGroup
  have hEcard : Nat.card E = D.relIndex E * Nat.card D := by
    rw [← Subgroup.relIndex_mul_card D E, inf_eq_left.2 hDE]
  have hDcard : Nat.card D ∣ Nat.card (GL (Fin n) K) := Subgroup.card_range_dvd _
  have hAut : Nat.card (MulAut (projectiveSL n K)) = E.index * (D.relIndex E * Nat.card D) := by
    rw [← hEcard, mul_comm, Subgroup.card_mul_index]
  rw [hAut, mul_assoc]
  exact Nat.mul_dvd_mul hEidx (Nat.mul_dvd_mul hEDidx hDcard)

end LinearAut

theorem card_GL_dvd_of_card_two {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) : Nat.card (GL (Fin n) K) ∣ 9999360 := by
  classical
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK]
  rcases hn with rfl | rfl | rfl <;> decide

theorem card_mulAut_dvd_of_quotientCenter_projectiveSL_card_two {X : Type*} [Group X]
    [Group.IsPerfect X] {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : X ⧸ center X ≃* projectiveSL n K) :
    Nat.card (MulAut X) ∣ 2 * 9999360 := by
  have h := card_mulAut_dvd_of_perfect (X := X)
  rw [card_mulAut_congr e] at h
  refine h.trans ((card_mulAut_projectiveSL_dvd' (n := n) (f := 1) (by omega)
    (by rw [hK]; norm_num)).trans ?_)
  rw [mul_one]
  exact Nat.mul_dvd_mul_left 2 (card_GL_dvd_of_card_two hn hK)

end CFSG.Quasithin.H13.KG14726

end
