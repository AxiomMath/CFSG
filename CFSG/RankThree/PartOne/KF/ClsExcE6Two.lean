module

public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
public import CFSG.RankThree.PartOne.KF.ClsLiftS3
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6Local

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.CentralCover CFSG.RankThree.PartTwo.Census.Exceptional
open scoped MatrixGroups

theorem CentralThree.exists_involution_lift {G H : Type*} [Group G] [Group H] {π : G →* H}
    (hC : CentralThree π) (hπ : Function.Surjective π) {t : H} (ht : t ^ 2 = 1) :
    ∃ g : G, π g = t ∧ g ^ 2 = 1 :=
  hC.exists_involution_lift_of_mem_range (hπ t) ht

section SL2

variable {K : Type*} [Field K]

theorem sl2Weyl_mul_self (h2 : (2 : K) = 0) : sl2Weyl K * sl2Weyl K = 1 := by
  have h : (-1 : K) = 1 := by linear_combination (-1 : K) * h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Weyl, Matrix.mul_apply, Fin.sum_univ_two, h]

theorem sl2Weyl_mul_three_mul_weyl (h2 : (2 : K) = 0) :
    sl2Weyl K * sl2Three K * sl2Weyl K = sl2Three K * sl2Three K := by
  have h : (-1 : K) = 1 := by linear_combination (-1 : K) * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Three, coe_sl2Weyl, coe_sl2Upper, Matrix.mul_apply, Fin.sum_univ_two, h]
  linear_combination (-1 : K) * h2

theorem sl2Weyl_conj_three (h2 : (2 : K) = 0) :
    sl2Weyl K * sl2Three K * (sl2Weyl K)⁻¹ = (sl2Three K)⁻¹ := by
  have hs : (sl2Weyl K)⁻¹ = sl2Weyl K := inv_eq_of_mul_eq_one_right (sl2Weyl_mul_self h2)
  have hw : (sl2Three K)⁻¹ = sl2Three K * sl2Three K :=
    inv_eq_of_mul_eq_one_right (by
      have h3 := sl2Three_pow_three K
      rw [pow_succ, pow_two] at h3
      rw [← mul_assoc]
      exact h3)
  rw [hs, hw, sl2Weyl_mul_three_mul_weyl h2]

end SL2

theorem four_le_localRank_three_of_lift {G Y : Type} [Group G] [Finite G] [Group Y] {π : G →* Y}
    (hπ : Function.Surjective π) (hC : CentralThree π) {z₀ : G} (hz₀ : π z₀ = 1) (hz₀1 : z₀ ≠ 1)
    {K : Type} [Field K] (hK : ringChar K = 2) (φ : Fin 4 → SL(2, K) →* Y)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A) : 4 ≤ localRank 3 G := by
  have : CharP K 2 := ringChar.of_eq hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hw3 : sl2Three K ^ 3 = 1 := sl2Three_pow_three K
  have hv2 : sl2Upper (1 : K) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (sl2Upper (1 : K))
    rwa [orderOf_sl2Upper_one hK] at this
  have hs2 : sl2Weyl K ^ 2 = 1 := by
    rw [pow_two]
    exact sl2Weyl_mul_self h2
  have hv1 : sl2Upper (1 : K) ≠ 1 := by
    intro h
    have := orderOf_sl2Upper_one hK
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hwv : sl2Three K * sl2Upper (1 : K) ≠ sl2Upper (1 : K) * sl2Three K :=
    sl2Three_not_commute K
  choose ls hlsπ hls2 using fun i : Fin 4 => hC.exists_involution_lift hπ
    (t := φ i (sl2Weyl K)) (by rw [← map_pow, hs2, map_one])
  choose lv hlvπ hlv2 using fun i : Fin 4 => hC.exists_involution_lift hπ
    (t := φ i (sl2Upper 1)) (by rw [← map_pow, hv2, map_one])
  choose lw hlwπ using fun i : Fin 4 => hπ (φ i (sl2Three K))
  have hinv : ∀ i, π (ls i) * π (lw i) * (π (ls i))⁻¹ = (π (lw i))⁻¹ := fun i => by
    simp only [hlsπ, hlwπ, ← map_inv, ← map_mul, sl2Weyl_conj_three h2]
  have hw3' : ∀ i, lw i ^ 3 = 1 := fun i => hC.pow_three_eq_one (s := ls i)
    (by rw [hlwπ, ← map_pow, hw3, map_one]) (hinv i)
  have hwc : ∀ i j : Fin 4, i ≠ j → lw i * lw j = lw j * lw i := by
    intro i j hij
    refine hC.commute_of_inv (s := ls i) ?_ (hinv i) ?_
    · rw [hlwπ, hlwπ]
      exact hcomm i j hij _ _
    · refine (hC.commute_of_sq (x := lw j) (y := ls i) ?_ (hls2 i)).symm
      rw [hlwπ, hlsπ]
      exact hcomm j i (Ne.symm hij) _ _
  have hyc : ∀ i j : Fin 4, i ≠ j → lw j * lv i = lv i * lw j := by
    intro i j hij
    refine hC.commute_of_sq (x := lw j) (y := lv i) ?_ (hlv2 i)
    rw [hlwπ, hlvπ]
    exact hcomm j i (Ne.symm hij) _ _
  have hne : ∀ i : Fin 3, i.castSucc ≠ 3 := fun i h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have hlv1 : lv 3 ≠ 1 := by
    intro h
    apply hv1
    apply hφ 3
    rw [map_one, ← hlvπ, h, map_one]
  have h4 := card_add_one_le_localRank_three (ι := Fin 3) (fun i => lw i.castSucc) z₀
    (fun i => lv i.castSucc)
    (fun i j => by
      by_cases h : i = j
      · subst h
        exact Commute.refl _
      · exact hwc _ _ (fun h' => h (Fin.castSucc_injective _ h')))
    (fun i => hC.central z₀ hz₀ _) (fun i => hw3' _) (hC.exp_three z₀ hz₀) hz₀1
    (fun i j hij => (hyc i.castSucc j.castSucc
      (fun h' => hij (Fin.castSucc_injective _ h'))).symm)
    (fun i => hC.central z₀ hz₀ _)
    (fun i h => by
      have h' := congrArg π (show lv i.castSucc * lw i.castSucc = lw i.castSucc * lv i.castSucc
        from h)
      rw [map_mul, map_mul, hlvπ, hlwπ, ← map_mul, ← map_mul] at h'
      exact hwv (hφ _ h').symm)
    (u := lv 3) (orderOf_eq_prime (hlv2 3) hlv1)
    (fun i => hyc 3 i.castSucc (fun h => hne i h.symm)) (hC.central z₀ hz₀ _).symm
  simpa using h4

theorem ringChar_eq_two_of_card_eq_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ringChar K = 2 := by
  have : Fintype K := Fintype.ofFinite K
  have h : (2 : ℕ) • (1 : K) = 0 := by
    have := card_nsmul_eq_zero (G := K) (x := 1)
    rwa [← Nat.card_eq_fintype_card, hK] at this
  refine CharP.ringChar_of_prime_eq_zero Nat.prime_two ?_
  rwa [nsmul_one] at h

theorem four_le_localRank_three_of_commuting_sl2_two {L : Type} [Group L] [Finite L]
    (hZ12 : Nat.card (Subgroup.center L) ∣ 12) (hZ3 : 3 ∣ Nat.card (Subgroup.center L))
    {Y : Type} [Group Y] (ε : L ⧸ Subgroup.center L ≃* Y) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (φ : Fin 4 → SL(2, K) →* Y) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A) : 4 ≤ localRank 3 L := by
  let N : Subgroup L :=
    { carrier := {n | ∃ z ∈ Subgroup.center L, n = z ^ 3}
      one_mem' := ⟨1, one_mem _, (one_pow 3).symm⟩
      mul_mem' := by
        rintro _ _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩
        refine ⟨z₁ * z₂, mul_mem hz₁ hz₂, ?_⟩
        have hc : Commute z₁ z₂ := Subgroup.mem_center_iff.1 hz₂ z₁
        exact (hc.mul_pow 3).symm
      inv_mem' := by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨z⁻¹, inv_mem hz, (inv_pow z 3).symm⟩ }
  have hNmem : ∀ n ∈ N, ∃ z ∈ Subgroup.center L, n = z ^ 3 := fun n hn => hn
  have hNZ : ∀ n ∈ N, n ∈ Subgroup.center L := by
    intro n hn
    obtain ⟨z, hz, rfl⟩ := hNmem n hn
    exact (Subgroup.center L).pow_mem hz 3
  have hz12 : ∀ z ∈ Subgroup.center L, z ^ 12 = 1 := by
    intro z hz
    have h1 : orderOf (⟨z, hz⟩ : Subgroup.center L) ∣ Nat.card (Subgroup.center L) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans hZ12)
  have hN4 : ∀ n ∈ N, n ^ 4 = 1 := by
    intro n hn
    obtain ⟨z, hz, rfl⟩ := hNmem n hn
    rw [← pow_mul]
    exact hz12 z hz
  have hNn : N.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hNZ n hn) g
    rwa [this, mul_inv_cancel_right]⟩
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have h4 : (x : L) ^ 4 = 1 := hN4 x x.2
    have := orderOf_dvd_of_pow_eq_one h4
    rw [Subgroup.orderOf_coe, hx] at this
    omega
  let ψ : L →* Y := ε.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψ : ∀ l, ψ l = 1 → l ∈ Subgroup.center L := fun l hl => by
    have : QuotientGroup.mk' (Subgroup.center L) l = 1 := ε.injective (by rw [map_one]; exact hl)
    exact (QuotientGroup.eq_one_iff l).1 this
  let π : L ⧸ N →* Y := QuotientGroup.lift N ψ (fun n hn => by
    have h1 : QuotientGroup.mk' (Subgroup.center L) n = 1 :=
      (QuotientGroup.eq_one_iff n).2 (hNZ n hn)
    rw [MonoidHom.mem_ker]
    simp only [ψ, MonoidHom.comp_apply, h1, map_one])
  have hπmk : ∀ l, π (QuotientGroup.mk l) = ψ l := fun l => QuotientGroup.lift_mk _ _ l
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨q, hq⟩ := ε.surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk l, by rw [hπmk]; exact hq⟩
  have hC : CentralThree π := by
    constructor
    · intro z hz g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      rw [hπmk] at hz
      have := Subgroup.mem_center_iff.1 (hψ l hz) g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
    · intro z hz
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
      rw [hπmk] at hz
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨l, hψ l hz, rfl⟩
  obtain ⟨z₁, hz₁⟩ := exists_prime_orderOf_dvd_card' 3 hZ3
  have hz₁o : orderOf (z₁ : L) = 3 := by rw [Subgroup.orderOf_coe]; exact hz₁
  have hz₁3 : (z₁ : L) ^ 3 = 1 := by
    rw [← hz₁o]
    exact pow_orderOf_eq_one (z₁ : L)
  have hz₁1 : (QuotientGroup.mk (z₁ : L) : L ⧸ N) ≠ 1 := by
    intro h
    have h4 := hN4 _ ((QuotientGroup.eq_one_iff _).1 h)
    have h5 : (z₁ : L) = 1 := by
      calc (z₁ : L) = (z₁ : L) ^ 4 * ((z₁ : L) ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4, hz₁3]; simp
    rw [h5, orderOf_one] at hz₁o
    omega
  have hz₀ : π (QuotientGroup.mk (z₁ : L)) = 1 := by
    rw [hπmk]
    simp only [ψ, MonoidHom.comp_apply]
    have : QuotientGroup.mk' (Subgroup.center L) (z₁ : L) = 1 :=
      (QuotientGroup.eq_one_iff _).2 z₁.2
    rw [this, map_one]
  have h4 := four_le_localRank_three_of_lift hπsurj hC hz₀ hz₁1
    (ringChar_eq_two_of_card_eq_two hK) φ hφ hcomm
  exact h4.trans (CFSG.RankThree.Classical2.localRank_quotient_le Nat.prime_three (by norm_num) N
    hN3)

end CFSG.RankThree.PartOne.KFU
