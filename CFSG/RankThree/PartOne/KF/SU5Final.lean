module

public import CFSG.RankThree.PartOne.KF.SU5Frattini
public import CFSG.RankThree.PartOne.S12.Sec12Two

public section

namespace CFSG.RankThree.PartOne.KFSU5

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem three_lt_evenRank_of_outer_element {A K L : Subgroup G} {e : G}
    (hA : IsElementaryAbelian 5 A) (hAcard : Nat.card A = 5 ^ 3) (hAL : A ≤ L) (hKL : K ≤ L)
    (hKA : K ⊓ A = ⊥) (hKc : K ≤ Subgroup.centralizer (A : Set G))
    (hec : e ∈ Subgroup.centralizer (A : Set G)) (heK : e ∈ Subgroup.normalizer (K : Set G))
    (he5 : e ^ 5 = 1) (heL : e ∉ L) (hK2 : 2 ∣ Nat.card K) : 3 < evenRank G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set M : Subgroup G := K ⊔ Subgroup.zpowers e with hM
  have hKM : K ≤ M := le_sup_left
  have heM : e ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hzK : Subgroup.zpowers e ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr heK
  have hMnorm : M ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hzK
  have : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMnorm
  obtain ⟨S'⟩ := (inferInstance : Nonempty (Sylow 2 ↥(K.subgroupOf M)))
  have heMK : (⟨e, heM⟩ : ↥M) ∉ K.subgroupOf M := fun h =>
    heL (hKL (Subgroup.mem_subgroupOf.mp h))
  have he5M : (⟨e, heM⟩ : ↥M) ^ 5 = 1 := Subtype.ext he5
  obtain ⟨x, hx5, hxN⟩ :=
    exists_orderOf_eq_normalizer_sylow_of_pow (K.subgroupOf M) S' he5M heMK
  have hNcard : 2 ∣ Nat.card ↥(K.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
    exact hK2
  have hS'ne : (S' : Subgroup ↥(K.subgroupOf M)) ≠ ⊥ := by
    intro hbot
    have h1 := Sylow.card_eq_multiplicity S'
    rw [hbot, Subgroup.card_bot] at h1
    have h2 : 0 < (Nat.card ↥(K.subgroupOf M)).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.card_pos).ne' hNcard
    have h3 : 2 ^ 1 ≤ 2 ^ (Nat.card ↥(K.subgroupOf M)).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) h2
    omega
  set U : Subgroup ↥M := (S' : Subgroup ↥(K.subgroupOf M)).map (K.subgroupOf M).subtype with hU
  have hUne : U ≠ ⊥ := fun h =>
    hS'ne ((Subgroup.map_eq_bot_iff_of_injective _ (K.subgroupOf M).subtype_injective).mp h)
  have hU2 : IsPGroup 2 U := S'.isPGroup'.map _
  have hxp : x ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx5] at this
  have hrank : 1 ≤ localRank 5 ↥M := by
    have hloc : IsTwoLocal (Subgroup.normalizer (U : Set ↥M)) := ⟨U, hUne, hU2, rfl⟩
    have h1 : 1 ≤ CFSG.Assembly.pRank 5 (Subgroup.normalizer (U : Set ↥M)) :=
      CFSG.SectionRank.le_pRank Nat.prime_five.one_lt (E := Subgroup.zpowers x) (k := 1)
        (Subgroup.zpowers_le.mpr hxN)
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 5 _).mp
          (IsElementaryAbelian.zpowers_of_pow_eq_one hxp))
        (by rw [Nat.card_zpowers, hx5, pow_one])
    exact h1.trans (Sec12Two.pRank_le_localRank_of_isTwoLocal Nat.prime_five hloc)
  have hMc : M ≤ Subgroup.centralizer (A : Set G) :=
    sup_le hKc (Subgroup.zpowers_le.mpr hec)
  have hPM : A ≤ Subgroup.centralizer (M : Set G) := fun a ha m hm =>
    (Subgroup.mem_centralizer_iff.mp (hMc hm) a ha).symm
  have hdisj : A ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haA, haM⟩
    have hM' : (M : Set G) = (Subgroup.zpowers e : Set G) * (K : Set G) := by
      rw [hM, sup_comm]
      exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzK
    obtain ⟨y, hy, k, hk, hyk⟩ := (hM' ▸ haM : a ∈ (Subgroup.zpowers e : Set G) * (K : Set G))
    have hyk : y * k = a := hyk
    have hyL : y ∈ L ⊓ Subgroup.zpowers e := by
      refine ⟨?_, hy⟩
      have : y = a * k⁻¹ := by rw [← hyk]; group
      rw [this]
      exact L.mul_mem (hAL haA) (L.inv_mem (hKL hk))
    have hy1 : y = 1 := by
      rw [Sec12Two.inf_zpowers_eq_bot Nat.prime_five he5 heL] at hyL
      exact Subgroup.mem_bot.mp hyL
    have hak : a = k := by rw [← hyk, hy1, one_mul]
    have haKA : a ∈ K ⊓ A := ⟨hak ▸ hk, haA⟩
    rw [hKA] at haKA
    exact haKA
  have hAel : CFSG.Assembly.IsElemAbelian 5 A := by
    have := hA
    exact ⟨inferInstance, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have := Sec12Two.localRank_add_le_evenRank Nat.prime_five (by norm_num) (by omega) hAel hPM
    hdisj hAcard
  omega

end CFSG.RankThree.PartOne.KFSU5
