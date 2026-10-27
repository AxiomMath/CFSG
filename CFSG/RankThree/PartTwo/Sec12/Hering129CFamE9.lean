module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam0
import CFSG.RankThree.PartTwo.Sec12.Hering129CRed1
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129C

section Datum

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb}

theorem census_a_comm_c (hD : Census129 c a I X f) : a * c = c * a :=
  Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hD.a_mem)

theorem census_a_pow_three (hD : Census129 c a I X f) : a ^ 3 = 1 := by
  have := pow_orderOf_eq_one a
  rwa [hD.orderOf_a] at this

theorem census_a_ne_one (hD : Census129 c a I X f) : a ≠ 1 := fun h => by
  have := hD.orderOf_a
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem census_abar_isElemAbelian (hD : Census129 c a I X f) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers c) :=
  isElemAbelian_zpowers_sup_three (census_a_pow_three hD) (c_pow_three hD) (census_a_comm_c hD)

theorem census_card_abar (hD : Census129 c a I X f) :
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers c) = 9 :=
  Proof128.card_zpowers_sup_eq_nine (census_abar_isElemAbelian hD) (x := c) (y := a)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) (c_ne_one hD) (census_a_ne_one hD)
    hD.a_not_mem

theorem census_center_eq_bot (hD : Census129 c a I X f)
    (h3 : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1 → z = 1) : Subgroup.center Q = ⊥ := by
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (isPGroup_center_of_theta_eq_bot hD.theta_eq_bot).exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
  have hdvd : 3 ∣ Nat.card (Subgroup.center Q) := by
    rw [hn]
    exact dvd_pow_self 3 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hz3 : (z : Q) ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 := h3 z z.2 hz3
  have : z = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

variable {H : Type} [Group H]

theorem census_maximal_E9 (hD : Census129 c a I X f) (hZ : Subgroup.center Q = ⊥) (e : Q ≃* H) :
    CFSG.Assembly.IsElemAbelian 3 ((Subgroup.zpowers a ⊔ Subgroup.zpowers c).map e.toMonoidHom) ∧
      Nat.card ↥((Subgroup.zpowers a ⊔ Subgroup.zpowers c).map e.toMonoidHom) = 9 ∧
      ∀ x : H, x ^ 3 = 1 →
        (∀ d ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers c).map e.toMonoidHom, x * d = d * x) →
          x ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers c).map e.toMonoidHom := by
  refine ⟨CFSG.Open.IsElemAbelian.map (census_abar_isElemAbelian hD) _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, census_card_abar hD]
  · intro x hx3 hxd
    set y : Q := e.symm x with hy
    have hy3 : y ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, hy, MulEquiv.apply_symm_apply, hx3, map_one]
    have hyc : y ∈ Subgroup.centralizer
        ((Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      apply e.injective
      rw [map_mul, map_mul, hy, MulEquiv.apply_symm_apply]
      exact (hxd (e u) ⟨u, hu, rfl⟩).symm
    have hyX := hD.beta y hyc hy3
    have hyA : y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
      have := hD.X_le hyX
      rwa [hZ, sup_bot_eq] at this
    exact ⟨y, hyA, by rw [hy]; exact MulEquiv.apply_symm_apply e x⟩

theorem census_gamma_map (hD : Census129 c a I X f) (e : Q ≃* H) :
    Subgroup.normalizer
        (((Subgroup.zpowers a ⊔ Subgroup.zpowers c).map e.toMonoidHom : Subgroup H) : Set H) ≤
      Subgroup.normalizer (Subgroup.zpowers (e c) : Set H) := by
  intro x hx
  have hx' : e.symm x ∈ Subgroup.normalizer
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup Q) : Set Q) := by
    rw [← Subgroup.map_equiv_normalizer_eq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : e.symm x = y := by
      rw [← hyx]
      exact e.symm_apply_apply y
    rwa [this]
  have h2 := hD.gamma hx'
  have h3 : x ∈ (Subgroup.normalizer (Subgroup.zpowers c : Set Q)).map e.toMonoidHom :=
    ⟨e.symm x, h2, by simp⟩
  rwa [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers] at h3

end Datum

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
