module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6 RecipeFieldE6

namespace TableBExc.E6Three

section Two

variable {K : Type} [Field K]

theorem eq_one_of_card_two (hK : Nat.card K = 2) (u : Kˣ) : u = 1 := by
  have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim u 1

theorem ringEquiv_eq_refl_of_card_two (hK : Nat.card K = 2) (σ : K ≃+* K) :
    σ = RingEquiv.refl K := by
  ext x
  by_cases hx : x = 0
  · rw [hx, map_zero]
    rfl
  · have h1 := eq_one_of_card_two hK (Units.mk0 x hx)
    have hx1 : x = 1 := by simpa using congrArg Units.val h1
    rw [hx1, map_one]
    rfl

end Two

section Aut

variable {K : Type} [Field K] [Finite K]

omit
  [Finite K] in
theorem recipeID_subset_inn_E6_two (hK : Nat.card K = 2) :
    RecipeID .E6 K ⊆
      Set.range (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)) :=
  idImage_subset_inn_of_top .E6 K (eq_top_iff.mpr fun a _ => by
    rw [show a = 1 from funext fun i => eq_one_of_card_two hK (a i)]
    exact one_mem _)

theorem isElemAbelian_le_inn_of_card_two (hK : Nat.card K = 2)
    {Eh : Subgroup (MulAut (RecipeGroup .E6 K))} (hEh : IsElemAbelian 3 Eh) :
    (Eh : Set (MulAut (RecipeGroup .E6 K))) ⊆
      Set.range (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)) := by
  obtain ⟨Ψ, hker⟩ := exists_quot_E6 K
  intro e he
  refine recipeID_subset_inn_E6_two hK ((hker e).1 (Prod.ext ?_ ?_))
  · rw [ringEquiv_eq_refl_of_card_two hK (Ψ e).1]
    rfl
  · have hsq : ∀ y : Multiplicative (ZMod (exactE TwistTag.E6.tag)), y ^ 2 = 1 := by
      have h0 : ∀ z : ZMod 2, z + z = 0 := by decide
      intro y
      rw [pow_two]
      exact congrArg Multiplicative.ofAdd (h0 (Multiplicative.toAdd y))
    refine eq_one_of_sq_of_pow_odd (p := 3) (by decide) (hsq _) ?_
    rw [← Prod.pow_snd, ← map_pow, hEh.2 e he, map_one, Prod.snd_one]

end Aut

local instance tableBExcE6ThreeTwoNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def wordE6Nine : List (Fin Tag.E6.rank) := [0, 1, 2, 3, 1, 4, 3, 5]

theorem wordE6Nine_pow_nine : (coxeterSystem .E6).wordProd wordE6Nine ^ 9 = 1 := by
  refine ext_single fun j => ?_
  rw [one_smul, ← wordProd_replicate, wordProd_smul]
  revert j
  decide +kernel

theorem wordE6Nine_pow_three_ne : (coxeterSystem .E6).wordProd wordE6Nine ^ 3 ≠ 1 := by
  intro h
  have h1 := congrArg (fun w : WeylGroup .E6 => w • (Pi.single (0 : Fin Tag.E6.rank) 1 :
    Fin Tag.E6.rank → ℤ)) h
  simp only [one_smul] at h1
  rw [← wordProd_replicate, wordProd_smul] at h1
  revert h1
  decide +kernel

theorem orderOf_wordE6Nine : orderOf ((coxeterSystem .E6).wordProd wordE6Nine) = 9 :=
  orderOf_eq_prime_pow (p := 3) (n := 1) wordE6Nine_pow_three_ne (by
    rw [show 3 ^ (1 + 1) = 9 by norm_num]
    exact wordE6Nine_pow_nine)

section C

variable {K : Type} [Field K] [Finite K]

theorem exists_pow_nine_ne_E6 : ∃ y : adjointGroup .E6 K, y ^ 9 = 1 ∧ y ^ 3 ≠ 1 := by
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  set x := nWord .E6 K wordE6Nine with hx
  set m : monomialSubgroup .E6 K := ⟨_, coe_nWord_mem_monomialSubgroup wordE6Nine⟩ with hm
  have hρ : weylQuotientHom .E6 K m = (coxeterSystem .E6).wordProd wordE6Nine :=
    weylQuotientHom_nWord _
  have hdvd : 9 ∣ orderOf m := by
    rw [← orderOf_wordE6Nine, ← hρ]
    exact orderOf_map_dvd _ _
  have hox : orderOf x = orderOf m := by
    rw [← Subgroup.orderOf_coe x, ← Subgroup.orderOf_coe m]
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < orderOf x := orderOf_pos x
  refine ⟨x ^ k, ?_, fun h => ?_⟩
  · rw [← pow_mul, mul_comm, ← hk, ← hox, pow_orderOf_eq_one]
  · have h1 := orderOf_dvd_of_pow_eq_one (show x ^ (k * 3) = 1 by rw [pow_mul]; exact h)
    rw [hox, hk] at h1
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [hox, hk, h0] at hpos
        omega
      · exact h0
    have := Nat.le_of_dvd (by omega) h1
    omega

omit [Finite K]
  in
theorem card_torusGroup_E6_two (hK : Nat.card K = 2) : Nat.card (torusGroup .E6 K) = 1 := by
  have h : torusGroup .E6 K = ⊥ := by
    rw [eq_bot_iff, torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    show torusElt Tag.E6 K i t ∈ (⊥ : Subgroup (ModGL Tag.E6 K))
    rw [show t = 1 from eq_one_of_card_two hK t, torusElt_one]
    exact one_mem _
  rw [h, Subgroup.card_bot]

theorem not_pow_seven_dvd_E6_two (hK : Nat.card K = 2) :
    ¬ 3 ^ 7 ∣ Nat.card (adjointGroup .E6 K) := by
  rw [card_adjointGroup_E6_eq, card_torusGroup_E6_two hK, hK, one_mul]
  simp only [prodE6, CFSG.Timmesfeld.ExceptionalOrders.geomSum, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num

theorem card_le_of_isElemAbelian_E6_two (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup .E6 K)} (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  have := Fact.mk Nat.prime_three
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  have h7 := not_pow_seven_dvd_E6_two hK
  have hE3 := TableB.isPGroup_of_isElemAbelian hE
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
  by_contra hlt
  push Not at hlt
  have hk6 : 6 ≤ k := by
    rw [hk] at hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
    omega
  obtain ⟨P, hEP⟩ := hE3.exists_le_sylow
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hj6 : j ≤ 6 := by
    by_contra h
    push Not at h
    apply h7
    have h1 : 3 ^ 7 ∣ Nat.card (P : Subgroup (adjointGroup .E6 K)) := hj ▸ pow_dvd_pow 3 h
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)
  have hEP' : E = P := Subgroup.eq_of_le_of_card_ge hEP (by
    rw [hj, hk]
    exact Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨y, hy9, hy3⟩ := exists_pow_nine_ne_E6 (K := K)
  have hy : IsPGroup 3 (Subgroup.zpowers y) := by
    rintro ⟨z, hz⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show ((3 ^ 2 : ℕ) : ℤ) = ((9 : ℕ) : ℤ) by
      norm_num, zpow_natCast, hy9, one_zpow]
  obtain ⟨Q, hyQ⟩ := hy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .E6 K) P Q
  have hyg : y ∈ ((g • P : Sylow 3 (adjointGroup .E6 K)) : Subgroup (adjointGroup .E6 K)) := by
    rw [hg]
    exact hyQ (Subgroup.mem_zpowers y)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyg
  rw [← hEP'] at hyg
  have h3 := hE.2 _ hyg
  rw [MulAut.smul_def, ← map_pow, MulEquiv.map_eq_one_iff] at h3
  exact hy3 h3


theorem card_le_of_isElemAbelian_aut_E6_two (hK : Nat.card K = 2)
    {Eh : Subgroup (MulAut (RecipeGroup .E6 K))} (hEh : IsElemAbelian 3 Eh) :
    Nat.card Eh ≤ 3 ^ 5 := by
  have := finite_recipeGroup .E6 K
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn (center_recipeGroup_eq_bot .E6 K)
    (isElemAbelian_le_inn_of_card_two hK hEh) hEh
  have h := card_le_of_isElemAbelian_E6_two hK
    (TableB.isElemAbelian_map hA (recipeEquiv .E6 K).toMonoidHom)
  rwa [Subgroup.card_map_of_injective (recipeEquiv .E6 K).injective, hAc] at h

theorem ggBstarBound_E6_two (hK : Nat.card K = 2) :
    GGBstarBound 3 4 (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  intro Eb Eh _ _ hr _ _ hEh hcard
  exfalso
  have h1 := card_le_of_isElemAbelian_aut_E6_two hK hEh
  have : 3 ^ 2 * 3 ^ 4 ≤ 3 ^ 5 := (Nat.mul_le_mul_left _ hr).trans (hcard.trans h1)
  norm_num at this

end C

end TableBExc.E6Three

end CFSG.StandardType
