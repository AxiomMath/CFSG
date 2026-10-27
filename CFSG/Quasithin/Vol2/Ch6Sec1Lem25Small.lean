module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Rank

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

@[expose] def SmallGroup625Fact : Prop :=
  (∀ (S : Type) [Group S], IsSporadic .J2 S → ∃ E : Subgroup S, IsElemAbelianOfRank 3 2 ↥E) ∧
  (∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → Odd (Nat.card (Subgroup.center X)) →
    IsSporadic .J2 (X ⧸ Subgroup.center X) → Subgroup.center X = ⊥) ∧
  (∀ (S : Type) [Group S], Is3D4 2 1 S → ∃ E : Subgroup S, IsElemAbelianOfRank 7 2 ↥E) ∧
  (∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → Odd (Nat.card (Subgroup.center X)) →
    Is3D4 2 1 (X ⧸ Subgroup.center X) → Subgroup.center X = ⊥)

variable {G : Type} [Group G] [Finite G]

theorem odd_card_center_KQ625 (K : Subgroup G) : Odd (Nat.card (Subgroup.center (KQ K))) := by
  classical
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center (KQ K)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set N := CFSG.pCore 2 ↥K with hN
  have hz2 : orderOf (z : KQ K) = 2 := by rw [Subgroup.orderOf_coe, hz]
  set Z₂ : Subgroup (KQ K) := Subgroup.zpowers (z : KQ K) with hZ₂
  have hZc : Z₂ ≤ Subgroup.center (KQ K) := Subgroup.zpowers_le.mpr z.2
  have hZn : Z₂.Normal := Subgroup.normal_of_le_center hZc
  have hZ2 : IsPGroup 2 Z₂ := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; rfl)
  set P : Subgroup ↥K := Z₂.comap (QuotientGroup.mk' N) with hP
  have hPn : P.Normal := hZn.comap _
  have hP2 : IsPGroup 2 P := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := hZ2 ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hPN : P ≤ N := le_sSup ⟨hPn, hP2⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective N (z : KQ K)
  have hkP : k ∈ P := by
    show QuotientGroup.mk' N k ∈ Z₂
    rw [hk]
    exact Subgroup.mem_zpowers _
  have h1 : (z : KQ K) = 1 := by
    rw [← hk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hPN hkP
  rw [h1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

theorem center_KQ_of_J2 (kf3 : SmallGroup625Fact) (hJ : IsSporadic .J2 (KBar K)) :
    Subgroup.center (KQ K) = ⊥ :=
  kf3.2.1 (KQ K) d.quasi.1 (odd_card_center_KQ625 K) hJ

theorem center_KQ_of_3D4 (kf3 : SmallGroup625Fact) (hD : Is3D4 2 1 (KBar K)) :
    Subgroup.center (KQ K) = ⊥ :=
  kf3.2.2.2 (KQ K) d.quasi.1 (odd_card_center_KQ625 K) hD

theorem center_KQ_of_L2 (hL2 : L2MultiplierFact) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : IsPSL 2 p 1 (KBar K)) : Subgroup.center (KQ K) = ⊥ :=
  center_KQ_eq_bot_of_card_le_two (hL2 p hp hp5 (KQ K) d.quasi.1 (Subgroup.center (KQ K))
    le_rfl hK)

include hI in
theorem false_of_J2 (kf3 : SmallGroup625Fact) {x : G} (hx : x ∈ DL) (hxr : orderOf x = 3)
    (hinn : phiK K ⟨x, d.DL_le_NK hI hx⟩ ∈ innAut (KBar K)) (hJ : IsSporadic .J2 (KBar K)) :
    False := by
  obtain ⟨E, hE⟩ := kf3.1 (KBar K) hJ
  exact d.false_of_inner_rank_two hI hx Nat.prime_three (by norm_num) hxr hinn
    (d.center_KQ_of_J2 kf3 hJ) hE

include hI in
theorem false_of_3D4 (kf3 : SmallGroup625Fact) {x : G} (hx : x ∈ DL) (hxr : orderOf x = 7)
    (hinn : phiK K ⟨x, d.DL_le_NK hI hx⟩ ∈ innAut (KBar K)) (hD : Is3D4 2 1 (KBar K)) :
    False := by
  obtain ⟨E, hE⟩ := kf3.2.2.1 (KBar K) hD
  exact d.false_of_inner_rank_two hI hx (by norm_num) (by norm_num) hxr hinn
    (d.center_KQ_of_3D4 kf3 hD) hE

end Dat625

end CFSG.Quasithin.H13
