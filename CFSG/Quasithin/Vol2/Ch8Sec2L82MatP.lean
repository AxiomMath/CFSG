module

public import CFSG.Quasithin.Background.HLUBase

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.LU

theorem pCore_le_ker_of_simple_mat {G S : Type*} [Group G] [Group S] [Finite G] (f : G →* S)
    (hf : Function.Surjective f) [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a) :
    CFSG.pCore 2 G ≤ f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite S := Finite.of_surjective f hf
  have hN : ((CFSG.pCore 2 G).map f).Normal := CFSG.pCore_normal.map f hf
  rcases hN.eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff _).1 h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hp : IsPGroup 2 S := by
      have h1 : IsPGroup 2 ((CFSG.pCore 2 G).map f) := CFSG.pCore_isPGroup.map f
      rw [h] at h1
      exact h1.of_equiv Subgroup.topEquiv
    have : Nontrivial S := ⟨⟨a * b, b * a, hab⟩⟩
    have hZ : Subgroup.center S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 hp.center_nontrivial
    rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h2 | h2
    · exact hZ h2
    · exact hab ((Subgroup.mem_center_iff.1 (h2 ▸ Subgroup.mem_top b)) a)

theorem pCoreOf_le_centSub {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
    {U : Subgroup V} (hP : P ≤ stabSub U) [IsSimpleGroup ↥(autSub P U)]
    (hnc : ∃ a b : ↥(autSub P U), a * b ≠ b * a) : pCoreOf 2 P ≤ centSub U := by
  have : Finite (MulAut V) := finite_mulAut_z (V := V)
  rintro _ ⟨y, hy, rfl⟩
  have hker : y ∈ (resP hP).ker := pCore_le_ker_of_simple_mat (resP hP) (resP_surjective hP) hnc hy
  intro u hu
  have h1 := congrArg (fun φ : ↥(autSub P U) => (((φ : MulAut ↥U) ⟨u, hu⟩ : ↥U) : V))
    (MonoidHom.mem_ker.1 hker)
  exact h1

theorem mem_of_pow_two_of_index_three {C : Type*} [Group C] (K : Subgroup C) [K.Normal]
    (hK : K.index = 3) {y : C} {k : ℕ} (hy : y ^ (2 ^ k) = 1) : y ∈ K := by
  have h3 : y ^ 3 ∈ K := hK ▸ K.pow_index_mem y
  have hcop : IsCoprime (3 : ℤ) (2 ^ k) := by
    have : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  obtain ⟨a, b, hab⟩ := hcop
  have e : y = (y ^ 3) ^ a * (y ^ (2 ^ k)) ^ b := by
    rw [← zpow_natCast y 3, ← zpow_mul, ← zpow_natCast y (2 ^ k), ← zpow_mul, ← zpow_add]
    push_cast
    have h1 : (3 : ℤ) * a + 2 ^ k * b = 1 := by linarith [hab]
    rw [h1, zpow_one]
  rw [e, hy, one_zpow, mul_one]
  exact K.zpow_mem h3 a

theorem pCoreOf_le_of_index_three {V : Type} [CommGroup V] [Finite V] {P K : Subgroup (MulAut V)}
    {U : Subgroup V} (hP : P ≤ stabSub U) [IsSimpleGroup ↥(autSub P U)]
    (hnc : ∃ a b : ↥(autSub P U), a * b ≠ b * a) (hKP : K ≤ P)
    (hKn : P ≤ Subgroup.normalizer (K : Set (MulAut V))) (hKC : K ≤ centSub U)
    (hCK : Nat.card ↥(P ⊓ centSub U) = 3 * Nat.card ↥K) : pCoreOf 2 P ≤ K := by
  have : Finite (MulAut V) := finite_mulAut_z (V := V)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hxC : x ∈ centSub U := pCoreOf_le_centSub hP hnc hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hKC' : K ≤ P ⊓ centSub U := le_inf hKP hKC
  set C := P ⊓ centSub U with hC
  let y' : ↥C := ⟨(y : MulAut V), y.2, hxC⟩
  have hK' : (K.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC').2
      (inf_le_left.trans hKn)
  have hidx : (K.subgroupOf C).index = 3 := by
    have h1 := Subgroup.index_mul_card (K.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC').toEquiv, hCK] at h1
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥P))) ⟨y, hy⟩
  rw [Subgroup.orderOf_mk] at hk
  have hyk : y' ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    show ((y : MulAut V)) ^ (2 ^ k) = 1
    have : (y : MulAut V) ^ (orderOf y) = 1 := by
      have := pow_orderOf_eq_one y
      exact congrArg Subtype.val this
    rwa [hk] at this
  have hmem := mem_of_pow_two_of_index_three (K.subgroupOf C) hidx hyk
  exact Subgroup.mem_subgroupOf.1 hmem

end CFSG.Quasithin.H13.Mat
