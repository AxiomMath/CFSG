module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Dickson
import CFSG.RankThree.PartTwo.Sec18.Item189StepL16SL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open Subgroup Matrix MatrixGroups

theorem exists_involution_inverting_of_orderOf_three {F : Type} [Field F] [CharP F 2]
    {z : SL(2, F)} (hz : orderOf z = 3) :
    ∃ w : SL(2, F), w * w = 1 ∧ w * z * w⁻¹ = z⁻¹ := by
  have hz3 : z ^ 3 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    norm_num at hz
  exact CFSG.RankThree.PartTwo.Sec18.exists_involution_inv_sl2_189 hz3 hz1

private theorem ksl2e_exists_zpowers_eq_of_card_three {H : Type*} [Group H] [Finite H]
    (O : Subgroup H) (hO : Nat.card O = 3) :
    ∃ θ : H, orderOf θ = 3 ∧ O = zpowers θ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO1 : O ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hO
    omega
  obtain ⟨θ, hθ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hO1
  have hθ1' : (θ : H) ≠ 1 := fun h => hθ1 (Subtype.ext h)
  have hord : orderOf (θ : H) = 3 := by
    rw [Subgroup.orderOf_coe]
    have h1 : orderOf θ ∣ 3 := hO ▸ orderOf_dvd_natCard θ
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hθ1
    · exact h
  refine ⟨θ, hord, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr θ.2) ?_
  rw [hO, Nat.card_zpowers, hord]

theorem normalizer_sup_eq_top_of_sl2_even {F : Type} [Field F] [Fintype F] {m : ℕ}
    (hF : Fintype.card F = 2 ^ m) (hm : 0 < m) {z : SL(2, F)} (hz : orderOf z = 3)
    {T : Subgroup SL(2, F)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    normalizer ((zpowers z : Subgroup SL(2, F)) : Set SL(2, F)) ⊔ T = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) hF
  set N : Subgroup SL(2, F) :=
    Subgroup.normalizer ((zpowers z : Subgroup SL(2, F)) : Set SL(2, F)) with hN
  rcases CFSG.QuasithinUnique.Lin2.dicksonLite hF hm hT (le_sup_right : T ≤ N ⊔ T) with
    htop | hnorm
  · exact htop
  · exfalso
    obtain ⟨w, hww, hwz⟩ := exists_involution_inverting_of_orderOf_three hz
    have hwN : w ∈ N := by
      rw [hN, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change Subgroup.zpowers ((MulAut.conj w) z) = Subgroup.zpowers z
      rw [MulAut.conj_apply, hwz, Subgroup.zpowers_inv]
    have hw_norm : w ∈ Subgroup.normalizer (T : Set SL(2, F)) :=
      hnorm (Subgroup.mem_sup_left hwN)
    have hTidx : ¬ 2 ∣ T.index := by
      have h : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
      intro hd
      exact hT.2.2 (h ▸ hd)
    let Q : Sylow 2 SL(2, F) := hT.2.1.toSylow hTidx
    have hQT : (Q : Subgroup SL(2, F)) = T := IsPGroup.toSylow_coe hT.2.1 hTidx
    have hwpg : IsPGroup 2 (zpowers w) := by
      apply IsPGroup.of_card_dvd_pow (n := 1)
      rw [Nat.card_zpowers]
      simpa using orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hww)
    have hwT : w ∈ T := by
      have hQset : (Q : Set SL(2, F)) = (T : Set SL(2, F)) :=
        congrArg (fun S : Subgroup SL(2, F) => (S : Set SL(2, F))) hQT
      have hmem : w ∈ zpowers w ⊓ Subgroup.normalizer (Q : Set SL(2, F)) :=
        ⟨Subgroup.mem_zpowers w, by rwa [hQset]⟩
      rw [IsPGroup.inf_normalizer_sylow hwpg Q] at hmem
      exact hQT ▸ hmem.2
    have hzN : z ∈ N := by
      rw [hN]
      exact Subgroup.le_normalizer (Subgroup.mem_zpowers z)
    have hz_norm : z ∈ Subgroup.normalizer (T : Set SL(2, F)) :=
      hnorm (Subgroup.mem_sup_left hzN)
    have hzw : z * w⁻¹ * z⁻¹ ∈ T :=
      ((Subgroup.mem_normalizer_iff.mp hz_norm) w⁻¹).mp (T.inv_mem hwT)
    have hz3 : z ^ 3 = 1 := by rw [← hz, pow_orderOf_eq_one]
    have hzz : z⁻¹ * z⁻¹ = z := by
      have hzsq : z * z = z⁻¹ := by
        rw [← mul_eq_one_iff_eq_inv]
        simpa [pow_succ, pow_two, mul_assoc] using hz3
      calc z⁻¹ * z⁻¹ = (z * z)⁻¹ := (mul_inv_rev z z).symm
        _ = (z⁻¹)⁻¹ := by rw [hzsq]
        _ = z := inv_inv z
    have heq : w * (z * w⁻¹ * z⁻¹) = z := by
      calc w * (z * w⁻¹ * z⁻¹) = w * z * w⁻¹ * z⁻¹ := by group
        _ = z⁻¹ * z⁻¹ := by rw [hwz]
        _ = z := hzz
    have hzT : z ∈ T := heq ▸ T.mul_mem hwT hzw
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hT.2.1 : ∃ n, Nat.card T = 2 ^ n)
    have h3dvd : 3 ∣ Nat.card T := by
      have := Subgroup.orderOf_dvd_natCard T hzT
      rwa [hz] at this
    rw [hk] at h3dvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)

theorem normalizer_sup_sylow_two_eq_top {J : Type} [Group J] [Finite J] {F : Type} [Field F]
    [Fintype F] {m : ℕ} (hF : Fintype.card F = 2 ^ m) (hm : 0 < m) (e : J ≃* SL(2, F))
    (h3 : 3 ∣ Nat.card J) (h9 : ¬ 9 ∣ Nat.card J) (Z : Sylow 3 J) (T : Sylow 2 J) :
    normalizer ((Z : Subgroup J) : Set J) ⊔ (T : Subgroup J) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJpos : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have hfac_pos : 0 < Nat.factorization (Nat.card J) 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three hJpos h3
  have hfac_le_one : Nat.factorization (Nat.card J) 3 ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ Nat.factorization (Nat.card J) 3 := by omega
    exact h9 (by
      have := (Nat.prime_three.pow_dvd_iff_le_factorization hJpos).mpr h2
      simpa using this)
  have hfac : Nat.factorization (Nat.card J) 3 = 1 := le_antisymm hfac_le_one hfac_pos
  have hZcard : Nat.card (Z : Subgroup J) = 3 := by
    rw [Sylow.card_eq_multiplicity Z, hfac, pow_one]
  obtain ⟨x, hxord, hZx⟩ := ksl2e_exists_zpowers_eq_of_card_three (Z : Subgroup J) hZcard
  let z : SL(2, F) := e x
  have hzord : orderOf z = 3 := by
    rw [show z = e x from rfl, MulEquiv.orderOf_eq, hxord]
  let T' : Subgroup SL(2, F) := (T : Subgroup J).map e.toMonoidHom
  have hT' : CFSG.QuasithinUnique.IsSylowTwoOf T' ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact (T.isPGroup').map e.toMonoidHom
    · have h1 : (T'.subgroupOf ⊤).index = (T : Subgroup J).index := by
        change T'.relIndex ⊤ = (T : Subgroup J).index
        rw [Subgroup.relIndex_top_right]
        exact Subgroup.index_map_of_bijective e.bijective (T : Subgroup J)
      rw [h1]
      exact T.not_dvd_index
  have hmain := normalizer_sup_eq_top_of_sl2_even hF hm hzord hT'
  have hZmap : (Z : Subgroup J).map e.toMonoidHom = zpowers z := by
    rw [hZx, MonoidHom.map_zpowers]
    rfl
  have hmap : (Subgroup.normalizer ((Z : Subgroup J) : Set J) ⊔ (T : Subgroup J)).map
      e.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, Subgroup.map_equiv_normalizer_eq (Z : Subgroup J) e, hZmap]
    exact hmain
  refine le_antisymm le_top ?_
  refine (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp ?_
  rw [hmap]
  exact le_of_eq (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
