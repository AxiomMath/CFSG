module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Vol2.Ch1Quotient
public import CFSG.Quasithin.Background.A4Four
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.Quasithin.QA24

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sylow_two_of_top {Q : Type} [Group Q] {P : Subgroup Q} (h : IsSylowTwoOf P ⊤) :
    ∃ S : Sylow 2 Q, (S : Subgroup Q) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ P.index := by
    have h1 : (P.subgroupOf ⊤).index = P.index := Subgroup.relIndex_top_right P
    rw [← h1]
    exact h.2.2
  exact ⟨h.2.1.toSylow hidx, rfl⟩

theorem exists_threeElement_normalizer_of_isL2Quot_two
    {T K1 : Subgroup G} (hsyl : IsSylowTwoOf (T ⊓ K1) K1) (hK : IsL2Quot 2 (OTwoQuot K1)) :
    ∃ y : G, y ∈ K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) ∧ orderOf y = 3 := by
  obtain ⟨e⟩ := hK
  have hBT : BenderType (OTwoQuot K1) 2 1 1 := BenderType.linear 2 le_rfl e
  set π : ↥K1 →* OTwoQuot K1 := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hP0 : IsSylowTwoOf ((T ⊓ K1).subgroupOf K1) ⊤ := isSylowTwoOf_top_subgroupOf hsyl
  obtain ⟨Q, hQ⟩ := exists_sylow_two_of_top (isSylowTwoOf_top_map_of_surjective hP0 π hπs)
  obtain ⟨t, hcore⟩ := hBT.exists_benderCore Q
  have hcard : Nat.card ↥(cartan (Q : Subgroup (OTwoQuot K1)) t) = 3 := by
    rw [hcore.card_cartan]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(cartan (Q : Subgroup (OTwoQuot K1)) t))
    3 (by rw [hcard])
  have hcb : (c : OTwoQuot K1) ∈ borel (Q : Subgroup (OTwoQuot K1)) := by
    have : (c : OTwoQuot K1) ∈ (Q : Subgroup (OTwoQuot K1)) ⊔ cartan (Q : Subgroup _) t :=
      Subgroup.mem_sup_right c.2
    rwa [hcore.sup_eq] at this
  have hcN : (c : OTwoQuot K1) ∈ Subgroup.normalizer ((Q : Subgroup (OTwoQuot K1)) : Set _) := hcb
  have hc3 : orderOf (c : OTwoQuot K1) = 3 := by rw [Subgroup.orderOf_coe]; exact hc
  obtain ⟨k, hk⟩ := hπs (c : OTwoQuot K1)
  have hOle : pCoreOf 2 K1 ≤ T ⊓ K1 := B6.pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hkN : (k : G) ∈ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) := by
    refine CFSG.RankThree.PartOne.mem_normalizer_of_conj_subset fun x hx => ?_
    have hxK : x ∈ K1 := hx.2
    have hxP : (⟨x, hxK⟩ : ↥K1) ∈ (T ⊓ K1).subgroupOf K1 := hx
    have h1 : π (k * ⟨x, hxK⟩ * k⁻¹) ∈ (Q : Subgroup (OTwoQuot K1)) := by
      rw [map_mul, map_mul, map_inv, hk]
      exact (Subgroup.mem_normalizer_iff.mp hcN _).mp (hQ ▸ Subgroup.mem_map_of_mem π hxP)
    rw [hQ] at h1
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp h1
    have h2 : (x'⁻¹ * (k * ⟨x, hxK⟩ * k⁻¹) : ↥K1) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel]
    rw [hπ, QuotientGroup.ker_mk'] at h2
    have h3 : (((x'⁻¹ * (k * ⟨x, hxK⟩ * k⁻¹) : ↥K1)) : G) ∈ T ⊓ K1 :=
      hOle (Subgroup.mem_map_of_mem K1.subtype h2)
    have h4 : (x' : G) ∈ T ⊓ K1 := hx'
    have h5 : (k : G) * x * (k : G)⁻¹ = (x' : G) * (((x'⁻¹ * (k * ⟨x, hxK⟩ * k⁻¹) : ↥K1)) : G) := by
      simp [mul_assoc]
    rw [h5]
    exact (T ⊓ K1).mul_mem h4 h3
  have hk3 : 3 ∣ orderOf (k : G) := by
    have h := orderOf_map_dvd π k
    rw [hk, hc3] at h
    rwa [Subgroup.orderOf_coe]
  exact ⟨(k : G) ^ (orderOf (k : G) / 3), ⟨Subgroup.pow_mem _ k.2 _, Subgroup.pow_mem _ hkN _⟩,
    orderOf_pow_orderOf_div (orderOf_pos _).ne' hk3⟩

end CFSG.Quasithin.QA24
