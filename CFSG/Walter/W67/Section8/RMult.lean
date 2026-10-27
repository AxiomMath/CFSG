module

public import CFSG.Walter.W67.Section8.Lemma82
public import CFSG.Walter.W67.JR.ThreeMult

public section

namespace CFSG.Walter.W67

namespace RMult3

variable {G : Type} [Group G] [Finite G] (Z : Subgroup G) (hZc : Z ≤ Subgroup.center G)

@[expose] noncomputable def m : ℕ := Nat.card Z / 3 ^ (Nat.card Z).factorization 3

@[expose] def N : Subgroup G where
  carrier := {x | x ∈ Z ∧ x ^ m Z = 1}
  one_mem' := ⟨Z.one_mem, one_pow _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Z.mul_mem ha hb, ?_⟩
    have hcomm : Commute a b := (Subgroup.mem_center_iff.mp (hZc ha) b).symm
    rw [hcomm.mul_pow, ha', hb', one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨Z.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩

omit [Finite G] in
include hZc in
theorem N_le : N Z hZc ≤ Z := fun _ h => h.1

omit [Finite G] in
include hZc in
theorem N_normal : (N Z hZc).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hc : g * n = n * g := (Subgroup.mem_center_iff.mp (hZc hn.1) g)
  rw [hc, mul_inv_cancel_right]
  exact hn

theorem card_pos : 0 < Nat.card Z := Nat.card_pos

omit [Finite G] in
theorem pow_mem_N {z : G} (hz : z ∈ Z) :
    z ^ (3 ^ (Nat.card Z).factorization 3) ∈ N Z hZc := by
  refine ⟨Z.pow_mem hz _, ?_⟩
  rw [← pow_mul, m, Nat.mul_div_cancel' (Nat.ordProj_dvd _ _)]
  have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
  exact congrArg Subtype.val this

include hZc in
theorem three_not_dvd
    {L : Type} [Group L] [Finite L] (hL : JRGroup L) (hq5 : hL.q ≠ 5)
    (hq3 : 3 < hL.q) [Z.Normal] (hperf : commutator G = ⊤) (e : (G ⧸ Z) ≃* L) :
    ¬ 3 ∣ Nat.card Z := by
  have : (N Z hZc).Normal := N_normal Z hZc
  set π := QuotientGroup.mk' (N Z hZc) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Z' := Z.map π with hZ'
  have : Z'.Normal := Subgroup.Normal.map inferInstance π hπs
  have hZ'c : Z' ≤ Subgroup.center (G ⧸ N Z hZc) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := hπs y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hZc hz) y)]
  have hZ'3 : IsPGroup 3 Z' := by
    rintro ⟨_, z, hz, rfl⟩
    refine ⟨(Nat.card Z).factorization 3, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, MonoidHom.mem_ker.mp ?_]
    rw [hπ, QuotientGroup.ker_mk']
    exact pow_mem_N Z hZc hz
  have hperf' : commutator (G ⧸ N Z hZc) = ⊤ := by
    have htop : (⊤ : Subgroup G).map π = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπs]
    calc commutator (G ⧸ N Z hZc) = ⁅(⊤ : Subgroup (G ⧸ N Z hZc)), ⊤⁆ := commutator_def _
      _ = ⁅(⊤ : Subgroup G).map π, (⊤ : Subgroup G).map π⁆ := by rw [htop]
      _ = (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G).map π :=
          (Subgroup.map_commutator _ _ _).symm
      _ = (commutator G).map π := by rw [commutator_def]
      _ = ⊤ := by rw [hperf, htop]
  have hiso : Nonempty ((G ⧸ N Z hZc) ⧸ Z' ≃* L) :=
    ⟨(QuotientGroup.quotientQuotientEquivQuotient (N Z hZc) Z (N_le Z hZc)).trans e⟩
  have hbot := rGroup_threeMultiplier L hL hq5 hq3 (G ⧸ N Z hZc) Z' hZ'c hZ'3 hperf' hiso
  have hall : ∀ z ∈ Z, z ^ m Z = 1 := by
    intro z hz
    have hmem : π z ∈ Z' := ⟨z, hz, rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmem.2
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 h3
  have h1 : (z : G) ^ m Z = 1 := hall z z.2
  have h2 : 3 ∣ m Z := by
    rw [← hz, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one h1
  have hcop := Nat.coprime_ordCompl Nat.prime_three (card_pos Z).ne'
  exact Nat.prime_three.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h2)

end RMult3

open RMult3 in
theorem rMult_of_of₃
    (h82 : S_lemma_8_2) (h83 : S_prop_8_3) : S_rMult_of := by
  intro hR L _ _ hL hq5 hq3 E _ _ Z _ hZc hZo hperf ⟨e⟩
  have h3 := three_not_dvd Z hZc hL hq5 hq3 hperf e
  by_contra hZ
  obtain ⟨h1, h2, -, h4, -⟩ := hR L hL hq5
  obtain ⟨hII, hE⟩ := h82 E hL hq3 ⟨h1, h2, h4⟩ Z hZc hZo hZ hperf e
  exact hZ (hE ▸ h83 E hII (hE ▸ h3))

theorem rMult_of_of₃'
    (hM : S_psl2_three_oddMultiplier) (h43ab : S_prop_4_3_ab)
    (h83 : S_prop_8_3) : S_rMult_of :=
  rMult_of_of₃ (lemma_8_2_of hM h43ab) h83

end CFSG.Walter.W67
