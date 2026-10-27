module

public import CFSG.Quasithin.EmptyFaithful.LRed3Four
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.B42ListF

open CFSG.Assembly.LowTwoRank

section Center

variable {X : Type} [Group X] [Finite X]

theorem odd_orderOf_of_mem_center (hO2 : CFSG.pCore 2 X = ⊥) {x : X}
    (hx : x ∈ Subgroup.center X) : Odd (orderOf x) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨m, hm⟩ := hev
  have hpos : 0 < orderOf x := orderOf_pos x
  set y := x ^ (orderOf x / 2) with hy
  have hy2 : orderOf y = 2 := by
    rw [hy, orderOf_pow_orderOf_div hpos.ne' (by omega)]
  have hyc : y ∈ Subgroup.center X := Subgroup.pow_mem _ hx _
  have hnorm : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have h1 := Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hyc k) g
    have h2 : g * y ^ k * g⁻¹ = y ^ k := by rw [h1, mul_inv_cancel_right]
    rw [h2]
    exact hn
  have hp : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2]; simp)
  have hle : Subgroup.zpowers y ≤ CFSG.pCore 2 X := le_sSup ⟨hnorm, hp⟩
  rw [hO2] at hle
  have hy1 : y ∈ (⊥ : Subgroup X) := hle (Subgroup.mem_zpowers y)
  rw [Subgroup.mem_bot] at hy1
  rw [hy1, orderOf_one] at hy2
  omega

theorem odd_card_center (hO2 : CFSG.pCore 2 X = ⊥) : Odd (Nat.card (Subgroup.center X)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) 2
    (even_iff_two_dvd.1 hev)
  have := odd_orderOf_of_mem_center hO2 z.2
  rw [Subgroup.orderOf_coe, hz] at this
  exact absurd this (by decide)

omit [Finite X] in
theorem center_eq_bot_of_isPGroup (hO2 : CFSG.pCore 2 X = ⊥)
    (h : IsPGroup 2 ↥(Subgroup.center X)) : Subgroup.center X = ⊥ := by
  have hle : Subgroup.center X ≤ CFSG.pCore 2 X := le_sSup ⟨inferInstance, h⟩
  rw [hO2] at hle
  exact le_bot_iff.1 hle

noncomputable def quotEquivOfCenterEqBot (h : Subgroup.center X = ⊥) :
    X ⧸ Subgroup.center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

end Center

section Covers

variable {X Y : Type} [Group X] [Group Y]

theorem two_le_two_pow_four {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem isPSL2_of_equiv {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : X ≃* StatedProj (StatedSL 2 K)) : IsPSL 2 2 n X := by
  have h4 := two_le_two_pow_four hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  · intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    exact absurd (h2 ▸ h4) (by norm_num)
  · intro h
    have h2 : 2 ^ n = 3 := congrArg Prod.snd h
    exact absurd (h2 ▸ h4) (by norm_num)

theorem isPSL2_of_cover [Finite X] (hX : CFSG.IsQuasisimple X) (hO2 : CFSG.pCore 2 X = ⊥)
    (hY : CFSG.IsQuasisimple Y) (cq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : Y ≃* StatedSL 2 K) : IsPSL 2 2 n X := by
  have h4 : 4 ≤ Nat.card K := hK ▸ two_le_two_pow_four hn
  obtain ⟨eY⟩ := lred3_cq_stated hY (StatedSL 2 K)
    (lred3_simple_statedProj_sl le_rfl (Or.inr h4)) e.symm.toMonoidHom e.symm.surjective
  have e' : X ⧸ Subgroup.center X ≃* StatedProj (StatedSL 2 K) := cq.trans eY
  have : Group.IsPerfect X := hX.1
  have hZ := center_eq_bot_of_isPGroup hO2
    (isPGroup_two_of_mulEquiv_stated_psl_two_even (Subgroup.center X) le_rfl hn hK e')
  exact isPSL_congr (quotEquivOfCenterEqBot hZ) (isPSL2_of_equiv hn hK e')

theorem isPSp4_of_equiv {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : X ≃* StatedProj (StatedSp 2 K)) : IsPSp4 2 n X := by
  have h4 := two_le_two_pow_four hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  intro h
  have h2 : 2 ^ n = 2 := congrArg Prod.snd h
  exact absurd (h2 ▸ h4) (by norm_num)

theorem isPSp4_of_cover
    [Finite X] (hX : CFSG.IsQuasisimple X)
    (hO2 : CFSG.pCore 2 X = ⊥) (hY : CFSG.IsQuasisimple Y)
    (cq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : Y ≃* StatedSp 2 K) :
    IsPSp4 2 n X := by
  have h4 := two_le_two_pow_four hn
  obtain ⟨eY⟩ := lred3_cq_stated hY (StatedSp 2 K)
    (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr (hK ▸ h4)))) e.symm.toMonoidHom e.symm.surjective
  have hP : IsPSp4 2 n (X ⧸ Subgroup.center X) := isPSp4_of_equiv hn hK (cq.trans eY)
  have hZ : Subgroup.center X = ⊥ :=
    (CFSG.SectionRank.EvenCover.even_symplectic_odd_cover_catalog_step hX
      (odd_card_center hO2) hP).1
  exact isPSp4_congr (quotEquivOfCenterEqBot hZ) hP

theorem isG2_of_cover
    [Finite X]
    (hG2 : FactG2Cayley) (hX : CFSG.IsQuasisimple X) (hO2 : CFSG.pCore 2 X = ⊥)
    (cq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : Y ≃* ↥(CFSG.Open.quasithinG2 K)) :
    IsG2 2 n X := by
  have hG : IsG2 2 n (Y ⧸ Subgroup.center Y) :=
    IsG2.of_mulEquiv (QuotientGroup.congr (Subgroup.center Y)
      (Subgroup.center ↥(CFSG.Open.quasithinG2 K)) e (Subgroup.map_center_eq e)).symm
      (hG2 K n hn hK)
  have hG' : IsG2 2 n (X ⧸ Subgroup.center X) := IsG2.of_mulEquiv cq.symm hG
  have : Group.IsPerfect X := hX.1
  have hker := CFSG.SectionRank.g2_even_perfect_odd_cover_trivial hG'
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (by rw [QuotientGroup.ker_mk']; exact odd_card_center hO2)
  rw [QuotientGroup.ker_mk'] at hker
  exact IsG2.of_mulEquiv (quotEquivOfCenterEqBot hker) hG'

end Covers

end CFSG.Quasithin.B42ListF
