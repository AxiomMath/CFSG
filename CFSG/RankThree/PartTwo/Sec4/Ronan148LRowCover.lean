module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LD4In
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSU)

section Lift

theorem isElemAbelian_of_mulEquiv {A B : Type*} [Group A] [Group B] {H : Subgroup A}
    {K : Subgroup B} (e : H ≃* K) (hK : CFSG.Assembly.IsElemAbelian 3 K) :
    CFSG.Assembly.IsElemAbelian 3 H := by
  refine ⟨⟨⟨fun a b => e.injective ?_⟩⟩, fun x hx => ?_⟩
  · rw [map_mul, map_mul]
    exact hK.1.is_comm.comm (e a) (e b)
  · have h := hK.2 _ (e ⟨x, hx⟩).2
    have h' : e (⟨x, hx⟩ ^ 3) = 1 := by
      rw [map_pow]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h
    rw [map_eq_one_iff e e.injective] at h'
    exact congrArg Subtype.val h'

variable {S : Type*} [Group S] [Finite S]

theorem exists_ne_one_pow_three_of_card {E : Subgroup S} (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hE9 : Nat.card E = 9) : ∃ k ∈ E, k ≠ 1 ∧ k ^ 3 = 1 := by
  haveI : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE9]
    norm_num
  obtain ⟨k, hk⟩ := exists_ne (1 : E)
  exact ⟨k, k.2, fun h => hk (Subtype.ext h), hE3 k k.2⟩

theorem exists_e9_of_cover {Y : Subgroup S} {m : ℕ} (hmo : Odd m) (hm1 : 1 < m)
    (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) :
    ∃ E : Subgroup S, E ≤ Y ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 3 = 1) ∧
      Nat.card E = 9 ∧ ∀ z ∈ E, (∀ k ∈ Y, z * k = k * z) → z = 1 := by
  obtain ⟨E₀, hE₀, hE₀9⟩ := exists_e9_projSU hmo
  have hp3 : IsPGroup 3 E₀ := IsPGroup.of_card (n := 2) (by rw [hE₀9]; norm_num)
  obtain ⟨T, -, ⟨eT⟩⟩ := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3
    Nat.prime_three π hπ (Nat.Coprime.symm hker) E₀ hp3
  have hTab : CFSG.Assembly.IsElemAbelian 3 T := isElemAbelian_of_mulEquiv eT hE₀
  have hT9 : Nat.card T = 9 := by rw [Nat.card_congr eT.toEquiv, hE₀9]
  refine ⟨T.map Y.subtype, Subgroup.map_subtype_le T, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h : a * b = b * a := congrArg Subtype.val (hTab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact congrArg Subtype.val h
  · rintro _ ⟨a, ha, rfl⟩
    have h : a ^ 3 = 1 := hTab.2 a ha
    exact congrArg Subtype.val h
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hT9]
  · rintro _ ⟨a, ha, rfl⟩ hcent
    have hca : ∀ g : Y, a * g = g * a := fun g => Subtype.ext (hcent g g.2)
    have hz : π a ∈ Subgroup.center (projSU 3 2 m) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := hπ g
      rw [← map_mul, ← map_mul, hca g']
    rw [center_projSU_eq_bot hmo hm1, Subgroup.mem_bot] at hz
    have hak : a ∈ π.ker := hz
    have h3 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (hTab.2 a ha)
    have hk : orderOf a ∣ Nat.card π.ker := by
      rw [← Subgroup.orderOf_mk a hak]
      exact orderOf_dvd_natCard _
    have h1 : orderOf a ∣ Nat.gcd (Nat.card π.ker) 3 := Nat.dvd_gcd hk h3
    rw [Nat.Coprime.gcd_eq_one hker, Nat.dvd_one, orderOf_eq_one_iff] at h1
    rw [h1]
    rfl

end Lift

section Orders

theorem padicValNat_card_projSU {m : ℕ} (hm : 1 ≤ m) :
    padicValNat 2 (Nat.card (projSU 3 2 m)) = 3 * m := by
  rw [KFacts.card_projSU_three_two hm]
  exact KFacts.padicValNat_ordTwistedA_two hm

theorem one_lt_card_projSU {m : ℕ} (hm : 1 ≤ m) : 1 < Nat.card (projSU 3 2 m) := by
  have h := padicValNat_card_projSU hm
  by_contra hle
  have h01 : Nat.card (projSU 3 2 m) = 0 ∨ Nat.card (projSU 3 2 m) = 1 := by omega
  rcases h01 with h0 | h0
  · rw [h0, padicValNat.zero] at h
    omega
  · rw [h0, padicValNat.one] at h
    omega

theorem padicValNat_ordG2_two_pow {n : ℕ} (hn : 1 ≤ n) :
    padicValNat 2 (CFSG.Open.ordG2 (2 ^ n)) = 6 * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Odd ((2 ^ n) ^ 6 - 1) := CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)
  have h2 : Odd ((2 ^ n) ^ 2 - 1) := CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)
  have hodd := h1.mul h2
  rw [CFSG.Open.ordG2, mul_assoc, padicValNat.mul (by positivity) hodd.pos.ne',
    padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero, ← pow_mul,
    padicValNat.prime_pow, mul_comm]

theorem card_eq_of_isSimpleGroup_surj {Y Q : Type*} [Group Y] [Group Q] [IsSimpleGroup Y]
    (π : Y →* Q) (hπ : Function.Surjective π) (hQ : 1 < Nat.card Q) :
    Nat.card Y = Nat.card Q := by
  haveI : π.ker.Normal := MonoidHom.normal_ker π
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact Nat.card_congr (Equiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp h, hπ⟩)
  · exfalso
    have h1 : ∀ z : Q, z = 1 := by
      intro z
      obtain ⟨y, rfl⟩ := hπ z
      have : y ∈ π.ker := by rw [h]; exact Subgroup.mem_top y
      exact this
    have : Nat.card Q = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [h1 a, h1 b]⟩, ⟨1⟩⟩
    omega

end Orders

section G2


theorem isSimpleGroup_adjointGroup_of_isPerfect (τ : Tag) (k : Type) [Field k] [Finite k]
    (hperf : Group.IsPerfect (adjointGroup τ k)) : IsSimpleGroup (adjointGroup τ k) := by
  have hnc := (opposite_simple_root_noncommutativity τ k).2.2.1
  have : Nontrivial (adjointGroup τ k) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ : Subgroup.center (adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  refine IsSimpleGroup.mk fun M hM => ?_
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    have hnot : ¬ M ≤ Subgroup.center (adjointGroup τ k) := by
      rw [hZ]
      exact fun h => hbot (le_bot_iff.1 h)
    have hsolv := (noncentral_normal_solvable_quotient τ k M hnot).2.1
    by_contra htop
    have : Nontrivial (adjointGroup τ k ⧸ M) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact htop
    exact Group.IsPerfect.not_isSolvable _ hsolv

theorem false_of_g2_cover {k : Type} [Field k] [Finite k] {n : ℕ} (hk : Nat.card k = 2 ^ n)
    (hn : 1 ≤ n) {G : Type*} [Group G] {C Y : Subgroup G} (eC : C ≃* adjointGroup Tag.G2 k)
    (hYC : Y ≤ C) [Group.IsPerfect Y] (hsub : (Y.subgroupOf C).IsSubnormal) {m : ℕ}
    (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardC : Nat.card C = CFSG.Open.ordG2 (2 ^ n) := by
    rw [Nat.card_congr eC.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
  have hU := padicValNat_card_projSU (by omega : 1 ≤ m)
  have hU1 := one_lt_card_projSU (by omega : 1 ≤ m)
  have hdU : Nat.card (projSU 3 2 m) ∣ Nat.card Y := Subgroup.card_dvd_of_surjective hπ
  have hdY : Nat.card Y ∣ Nat.card C := Subgroup.card_dvd_of_le hYC
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  ·
    have h := hdU.trans hdY
    rw [hcardC] at h
    have h2 : 2 ^ (3 * m) ∣ Nat.card (projSU 3 2 m) := hU ▸ pow_padicValNat_dvd
    have hm3 : 3 ≤ m := by
      obtain ⟨j, rfl⟩ := hmo
      omega
    have h512 : 2 ^ 9 ∣ 2 ^ (3 * m) := pow_dvd_pow 2 (by omega)
    have := (h512.trans h2).trans h
    norm_num [CFSG.Open.ordG2] at this
  ·
    have hk3 : 3 ≤ Nat.card k := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    haveI : IsSimpleGroup (adjointGroup .G2 k) := isSimpleGroup_adjointGroup_of_isPerfect .G2 k
      (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card k hk3)
    haveI hCs : IsSimpleGroup C := eC.isSimpleGroup
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hCs hsub with h | h
    ·
      have hY1 : Y = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have : (⟨y, hYC hy⟩ : C) ∈ Y.subgroupOf C := hy
        rw [h, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val this
      rw [hY1, Subgroup.card_bot] at hdU
      have := Nat.le_of_dvd (by norm_num) hdU
      omega
    ·
      have hYeq : Y = C := by
        refine le_antisymm hYC fun y hy => ?_
        have : (⟨y, hy⟩ : C) ∈ Y.subgroupOf C := by
          rw [h]
          exact Subgroup.mem_top _
        exact this
      have eY : Y ≃* C := MulEquiv.subgroupCongr hYeq
      haveI : IsSimpleGroup Y := eY.isSimpleGroup
      have hcY := card_eq_of_isSimpleGroup_surj π hπ hU1
      have hv := padicValNat_ordG2_two_pow hn
      rw [← hcardC, ← Nat.card_congr eY.toEquiv, hcY, hU] at hv
      obtain ⟨j, rfl⟩ := hmo
      omega

end G2

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
