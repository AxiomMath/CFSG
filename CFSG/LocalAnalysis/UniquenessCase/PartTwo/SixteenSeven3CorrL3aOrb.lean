module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.LargeExtraspecial.ConjCountTwoPow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16c167_invariant_eq_bot_or_card {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) (hcard : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)}
    (hL : IsPOnePlusTwo 3 ↥L) (U : Subgroup W) (hU : ∀ ℓ ∈ L, ∀ u ∈ U, ℓ u ∈ U)
    (hfix : ∀ ℓ : ↥L, ℓ ∈ Subgroup.center ↥L → ℓ ≠ 1 →
      ∀ u ∈ U, (ℓ : MulAut W) u = u → u = 1) :
    U = ⊥ ∨ Nat.card U = 2 ^ 6 := by
  classical
  haveI hExt : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hLcard : Nat.card ↥L = 27 := by
    rw [hL.2.1]
    norm_num
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 :=
    CFSG.IsExtraspecial.center_order_p 3 ↥L
  have hminFac : (Nat.card ↥L).minFac = 3 := by
    rw [hLcard]
    have hle : (27 : ℕ).minFac ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) (by norm_num)
    have hge : 2 ≤ (27 : ℕ).minFac := (Nat.minFac_prime (by norm_num)).two_le
    have hne2 : (27 : ℕ).minFac ≠ 2 := by
      intro h
      have hd : 2 ∣ 27 := h ▸ Nat.minFac_dvd 27
      norm_num at hd
    omega
  have hnormal_aux : ∀ S : Subgroup ↥L, 3 < Nat.card S → Nat.card S ∣ 27 → S.Normal := by
    intro S hgt hdvd
    obtain ⟨k, hk, hkS⟩ :=
      (Nat.dvd_prime_pow (p := 3) (m := 3) (i := Nat.card S) Nat.prime_three).1
        (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact hdvd)
    have hk2 : 1 < k := by
      by_contra h
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · have hkS' : Nat.card S = 1 := by rw [hkS]; norm_num
        omega
      · have hkS' : Nat.card S = 3 := by rw [hkS]; norm_num
        omega
    have hk23 : k = 2 ∨ k = 3 := by omega
    have hmul := Subgroup.card_mul_index S
    rw [hLcard] at hmul
    rcases hk23 with rfl | rfl
    · have hcardS : Nat.card S = 9 := by norm_num at hkS; exact hkS
      rw [hcardS] at hmul
      have hidx : S.index = 3 := by omega
      exact Subgroup.normal_of_index_eq_minFac_card (hminFac.symm ▸ hidx)
    · have hcardS : Nat.card S = 27 := by norm_num at hkS; exact hkS
      rw [hcardS] at hmul
      have hidx : S.index = 1 := by omega
      exact Subgroup.normal_of_index_eq_one hidx
  have hstep1 : ∀ S : Subgroup ↥L, S ⊓ Subgroup.center ↥L = ⊥ → Nat.card S ≤ 3 := by
    intro S hS
    by_contra hle
    have hgt : 3 < Nat.card S := not_le.1 hle
    have hdvd : Nat.card S ∣ 27 := by
      simpa [hLcard] using Subgroup.card_subgroup_dvd_card S
    have hnormal : S.Normal := hnormal_aux S hgt hdvd
    haveI : S.Normal := hnormal
    have hcomm : _root_.commutator ↥L ≤ Subgroup.center ↥L := by
      haveI : IsElementaryAbelian 3 (↥L ⧸ Subgroup.center ↥L) :=
        CFSG.IsExtraspecial.quotient_elementary_abelian 3 ↥L
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    rw [_root_.commutator_def] at hcomm
    have hleZ : ⁅S, (⊤ : Subgroup ↥L)⁆ ≤ Subgroup.center ↥L :=
      (Subgroup.commutator_mono le_top le_top).trans hcomm
    have hleS : ⁅S, (⊤ : Subgroup ↥L)⁆ ≤ S :=
      Subgroup.commutator_le_left S (⊤ : Subgroup ↥L)
    have hbot : ⁅S, (⊤ : Subgroup ↥L)⁆ = ⊥ := by
      apply le_bot_iff.mp
      rw [← hS]
      exact le_inf hleS hleZ
    have hSZ : S ≤ Subgroup.center ↥L :=
      (Subgroup.commutator_top_right_eq_bot_iff_le_center (H := S)).mp hbot
    have hSbot : S = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxinf : x ∈ S ⊓ Subgroup.center ↥L := ⟨hx, hSZ hx⟩
      rw [hS] at hxinf
      simpa using hxinf
    have hcardS : Nat.card S = 1 := by rw [hSbot, Subgroup.card_bot]
    omega
  let X := {u : W // u ∈ U ∧ u ≠ 1}
  let act : ↥L → X → X := fun ℓ x =>
    ⟨(ℓ : MulAut W) x.1, hU (ℓ : MulAut W) ℓ.2 x.1 x.2.1, by
      intro h
      apply x.2.2
      have h1 : (ℓ : MulAut W) 1 = 1 := map_one _
      exact (ℓ : MulAut W).injective (h.trans h1.symm)⟩
  letI : MulAction ↥L X :=
    { smul := act
      one_smul := fun x => by
        apply Subtype.ext
        change (act 1 x).1 = x.1
        rfl
      mul_smul := fun ℓ m x => by
        apply Subtype.ext
        change (act (ℓ * m) x).1 = (act ℓ (act m x)).1
        rfl }
  have horbit : ∀ x : X, 9 ∣ (MulAction.orbit ↥L x).ncard := by
    intro x
    have hstab_le : Nat.card (MulAction.stabilizer ↥L x) ≤ 3 := by
      apply hstep1
      rw [eq_bot_iff]
      intro ℓ hℓ
      rw [Subgroup.mem_bot]
      by_contra hne
      have hfixℓ : (ℓ : MulAut W) x.1 = x.1 := by
        have hsm := (MulAction.mem_stabilizer_iff).mp hℓ.1
        have hval := congrArg Subtype.val hsm
        change (act ℓ x).1 = x.1 at hval
        exact hval
      exact x.2.2 (hfix ℓ hℓ.2 hne x.1 x.2.1 hfixℓ)
    have hdvd : Nat.card (MulAction.stabilizer ↥L x) ∣ 27 := by
      simpa [hLcard] using
        Subgroup.card_subgroup_dvd_card (MulAction.stabilizer ↥L x)
    obtain ⟨k, hk, hkS⟩ :=
      (Nat.dvd_prime_pow (p := 3) (m := 3)
        (i := Nat.card (MulAction.stabilizer ↥L x)) Nat.prime_three).1
        (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact hdvd)
    have hcard13 : Nat.card (MulAction.stabilizer ↥L x) = 1 ∨
        Nat.card (MulAction.stabilizer ↥L x) = 3 := by
      have hle : 3 ^ k ≤ 3 := by
        calc 3 ^ k = Nat.card (MulAction.stabilizer ↥L x) := hkS.symm
          _ ≤ 3 := hstab_le
      have hk01 : k = 0 ∨ k = 1 := by
        by_contra h
        have hk2 : 2 ≤ k := by omega
        have h9 : 9 ≤ 3 ^ k := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        omega
      rcases hk01 with rfl | rfl
      · left
        simpa using hkS
      · right
        norm_num at hkS ⊢
        exact hkS
    have hidx : (MulAction.stabilizer ↥L x).index = (MulAction.orbit ↥L x).ncard :=
      MulAction.index_stabilizer ↥L x
    have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥L x)
    rw [hLcard] at hmul
    rcases hcard13 with h1 | h3
    · have hidx27 : (MulAction.stabilizer ↥L x).index = 27 := by
        rw [h1] at hmul
        omega
      rw [← hidx, hidx27]
      norm_num
    · have hidx9 : (MulAction.stabilizer ↥L x).index = 9 := by
        rw [h3] at hmul
        omega
      rw [← hidx, hidx9]
  have hdvd9 : 9 ∣ Nat.card X :=
    CFSG.LargeExtraspecial.dvd_natCard_of_forall_dvd_ncard_orbit (H := ↥L) (n := 9) horbit
  have hXcard : Nat.card X = Nat.card U - 1 := by
    have h1 : (1 : W) ∈ (U : Set W) := U.one_mem
    have hset : Nat.card X = ((U : Set W) \ {1}).ncard := by
      rw [← Nat.card_coe_set_eq ((U : Set W) \ {1})]
      rfl
    rw [hset, Set.ncard_sdiff_singleton_of_mem h1]
    simpa using congrArg (fun n => n - 1) (Nat.card_coe_set_eq (U : Set W)).symm
  have hdvd9U : 9 ∣ Nat.card U - 1 := by
    rw [← hXcard]
    exact hdvd9
  have hdvdU : Nat.card U ∣ 2 ^ 6 := by
    simpa [hcard] using Subgroup.card_subgroup_dvd_card U
  obtain ⟨r, hr, hUr⟩ :=
    (Nat.dvd_prime_pow (p := 2) (m := 6) (i := Nat.card U) Nat.prime_two).1 hdvdU
  have hr6 : r ≤ 6 := by
    have hle : 2 ^ r ≤ 2 ^ 6 := by
      apply Nat.le_of_dvd (by positivity)
      simpa [hUr] using hdvdU
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  rw [hUr] at hdvd9U
  have hr0or6 : r = 0 ∨ r = 6 := by
    interval_cases r
    · left; rfl
    · exact absurd hdvd9U (by norm_num)
    · exact absurd hdvd9U (by norm_num)
    · exact absurd hdvd9U (by norm_num)
    · exact absurd hdvd9U (by norm_num)
    · exact absurd hdvd9U (by norm_num)
    · right; rfl
  rcases hr0or6 with rfl | rfl
  · left
    apply Subgroup.eq_bot_of_card_eq
    simpa [hUr]
  · right
    simpa [hUr]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
