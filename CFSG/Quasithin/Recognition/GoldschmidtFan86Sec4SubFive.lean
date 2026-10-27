module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Five

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan41_2_sub (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) (hac : a ≠ c)
    {L : Subgroup G} (hL : L ∈ LamSet Γ G a b c) (h5 : valence Γ a = 5) {M : Subgroup G}
    (hM : M ≤ L ⊓ MulAction.stabilizer G a)
    (htr : ∀ u v, Γ.Adj a u → Γ.Adj a v → ∃ h ∈ M, h • u = v) :
    ∃ x ∈ M, orderOf x = 5 ∧
      ∀ g ∈ L ⊓ MulAction.stabilizer G a, g * x * g⁻¹ ∈ Subgroup.zpowers x := by
  obtain ⟨x₅, hx₅L, hx₅o, hx₅n⟩ := fan41_2 F hab hac hL h5
  obtain ⟨hfinL, -, hcardL, hP⟩ := lamSet_setup F hab hL
  have hfinGa : Finite ↥(MulAction.stabilizer G a) := F.loc_finite a
  have hMGa : M ≤ MulAction.stabilizer G a := hM.trans inf_le_right
  have hfinM : Finite ↥M := Finite.of_injective (Subgroup.inclusion hMGa)
    (Subgroup.inclusion_injective _)
  have hdvd : 5 ∣ Nat.card ↥M := by
    have := F.card_eq_valence_mul hab hMGa htr
    rw [h5] at this
    rw [this]
    exact dvd_mul_right _ _
  have h5p : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 5 hdvd
  let yK : ↥(L ⊓ MulAction.stabilizer G a) := ⟨(y : G), hM y.2⟩
  let xK : ↥(L ⊓ MulAction.stabilizer G a) := ⟨x₅, hx₅L⟩
  have hyK : orderOf yK = 5 := by
    have h1 : orderOf (y : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
    have h2 : orderOf ((yK : ↥(L ⊓ MulAction.stabilizer G a)) : G) = orderOf yK :=
      Subgroup.orderOf_coe yK
    rw [← h2]
    exact h1
  have hxK : orderOf xK = 5 := by
    have h2 : orderOf ((xK : ↥(L ⊓ MulAction.stabilizer G a)) : G) = orderOf xK :=
      Subgroup.orderOf_coe xK
    rw [← h2]
    exact hx₅o
  have hnorm : (Subgroup.zpowers xK).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hconj : g * xK * g⁻¹ ∈ Subgroup.zpowers xK := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hx₅n g g.2)
      exact Subgroup.mem_zpowers_iff.2 ⟨i, Subtype.ext (by simpa using hi)⟩
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hconj j
  have hfinR : Finite ↥(L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  have hcard : Nat.card ↥(L ⊓ MulAction.stabilizer G a) = 5 * 2 ^ k := by rw [hcardL, h5, hk]
  have hxcard : Nat.card ↥(Subgroup.zpowers xK) = 5 := by rw [Nat.card_zpowers, hxK]
  have hzeq : Subgroup.zpowers yK = Subgroup.zpowers xK :=
    zpowers_eq_of_normal (by norm_num) (by norm_num) hyK hcard hnorm hxcard
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hzeq ▸ Subgroup.mem_zpowers xK)
  refine ⟨x₅, ?_, hx₅o, hx₅n⟩
  have : (y : G) ^ j = x₅ := by simpa using congrArg Subtype.val hj
  rw [← this]
  exact M.zpow_mem y.2 j

theorem five_props (F : FanTree Γ G) (v : V) {K : Subgroup G} {x : G}
    (hx : x ∈ MulAction.stabilizer G v) (ho : orderOf x = 5)
    (hnorm : ∀ g ∈ K, g * x * g⁻¹ ∈ Subgroup.zpowers x) :
    (∀ u w, Γ.Adj v u → Γ.Adj v w → ∃ k ∈ Subgroup.zpowers x, k • v = v ∧ k • u = w) ∧
      ∀ k ∈ K ⊓ nbrStab Γ G v, x * k = k * x := by
  constructor
  · intro u w hu hw
    have hZ : Subgroup.zpowers x ≤ MulAction.stabilizer G v := Subgroup.zpowers_le.2 hx
    rcases F.fixes_or_trans v hZ with ⟨w₀, hw₀, hfix⟩ | htr
    · exfalso
      have hxw : x • w₀ = w₀ := hfix x (Subgroup.mem_zpowers x)
      obtain ⟨j, hj⟩ := F.edge_two v w₀ hw₀ ⟨x, hx, MulAction.mem_stabilizer_iff.2 hxw⟩
      have h1 : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [ho] at h2
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h2) (by norm_num)
    · obtain ⟨k, hk, hkx⟩ := htr u w hu hw
      exact ⟨k, hk, MulAction.mem_stabilizer_iff.1 (hZ hk), hkx⟩
  · intro k hk
    have h1 : k * x * k⁻¹ ∈ Subgroup.zpowers x := hnorm k hk.1
    have hc1 : x * k * x⁻¹ * k⁻¹ ∈ Subgroup.zpowers x := by
      have h2 := (Subgroup.zpowers x).inv_mem h1
      have h3 := (Subgroup.zpowers x).mul_mem (Subgroup.mem_zpowers x) h2
      have e : x * k * x⁻¹ * k⁻¹ = x * (k * x * k⁻¹)⁻¹ := by group
      rw [e]
      exact h3
    have hc2 : x * k * x⁻¹ * k⁻¹ ∈ nbrStab Γ G v :=
      (nbrStab Γ G v).mul_mem (nbrStab_conj_mem F (MulAction.mem_stabilizer_iff.1 hx) hk.2)
        ((nbrStab Γ G v).inv_mem hk.2)
    obtain ⟨n, hn⟩ := F.nbrStab_isPGroup v ⟨_, hc2⟩
    have hn' : (x * k * x⁻¹ * k⁻¹) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hd1 : orderOf (x * k * x⁻¹ * k⁻¹) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have hd2 : orderOf (x * k * x⁻¹ * k⁻¹) ∣ 5 := ho ▸ orderOf_dvd_of_mem_zpowers hc1
    have hcop : Nat.Coprime 5 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    have hd3 := Nat.dvd_gcd hd2 hd1
    rw [hcop.gcd_eq_one] at hd3
    have hc : x * k * x⁻¹ * k⁻¹ = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd3)
    exact commutatorElement_eq_one_iff_mul_comm.1 hc

end CFSG.Quasithin.Fan86
