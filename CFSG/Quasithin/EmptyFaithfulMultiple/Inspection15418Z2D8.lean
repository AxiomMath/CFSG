module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Component
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace Insp15418

theorem mem_of_odd_of_index_two {Γ : Type*} [Group Γ] {M : Subgroup Γ} (hM : M.index = 2)
    {y : Γ} (hy : Odd (orderOf y)) : y ∈ M := by
  obtain ⟨m, hm⟩ := hy
  have e : y = (y ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e]
  exact M.pow_mem (Subgroup.sq_mem_of_index_two hM y) _

end Insp15418

namespace InspectionData15418

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ S T Z : Subgroup G}
  (d : InspectionData15418 I G₁ G₂ S T Z)
include d

theorem isComponent_map_mk {K : Subgroup ↥I} (hK : CFSG.IsComponent K) :
    CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) := by
  refine ⟨CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
    (φ := (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)).subgroupMap K) hK.1
    ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)).subgroupMap_surjective K) ?_,
    hK.2.map (QuotientGroup.mk'_surjective _)⟩
  by_contra h
  push Not at h
  have hle : K ≤ CFSG.pPrimeCore 3 ↥I := fun k hk => by
    have := congrArg Subtype.val (h ⟨k, hk⟩)
    exact (QuotientGroup.eq_one_iff k).mp this
  have hKK : ⁅K, K⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hle).trans
      (d.commutator_pPrimeCore_eq_bot hK).le)
  rw [Subgroup.isPerfect_iff.mp hK.1.1] at hKK
  exact (Subgroup.nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial hK.1) hKK

theorem mem_of_mk_mem {K : Subgroup ↥I} (hK : CFSG.IsComponent K) {g : ↥I} (hg3 : g ^ 3 = 1)
    (hg : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) g ∈
      K.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) : g ∈ K := by
  obtain ⟨k, hk, hkg⟩ := hg
  set n := k⁻¹ * g with hn
  have hnO : n ∈ CFSG.pPrimeCore 3 ↥I := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) (k⁻¹ * g) = 1
    rw [map_mul, map_inv, hkg, inv_mul_cancel]
  have hkn : Commute k n := by
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (d.commutator_pPrimeCore_eq_bot hK)
      hk
    exact (Subgroup.mem_centralizer_iff.mp hc n hnO).symm
  have hgkn : g = k * n := by rw [hn, mul_inv_cancel_left]
  have hcop3 : Nat.Coprime 3 (orderOf n) := by
    have h1 : orderOf n ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥I) := by
      have := orderOf_dvd_natCard (⟨n, hnO⟩ : ↥(CFSG.pPrimeCore 3 ↥I))
      rwa [Subgroup.orderOf_mk] at this
    exact (CFSG.pPrimeCore_coprime_card (p := 3)).coprime_dvd_right h1
  have hcop : Nat.Coprime (orderOf n) (orderOf g) :=
    hcop3.symm.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hg3)
  have hpow : g ^ orderOf n = k ^ orderOf n := by
    rw [hgkn, hkn.mul_pow, pow_orderOf_eq_one, mul_one]
  have hmem := A4.mem_zpowers_pow_of_coprime hcop
  rw [hpow] at hmem
  exact (Subgroup.zpowers_le.mpr (K.pow_mem hk _)) hmem

theorem oTwoUpper_le_of_index_two {K : Subgroup ↥I} (hK : CFSG.IsComponent K)
    (hidx : (K.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))).index = 2) :
    oTwoUpper G₁ ≤ K.map I.subtype := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro g ⟨hg, ho⟩
  set g' : ↥I := ⟨g, d.G₁_le hg⟩
  have ho' : Odd (orderOf g') := by rwa [Subgroup.orderOf_mk]
  have h3 : orderOf g' ∣ 3 :=
    F6.orderOf_dvd_three_of_odd d.triple.subgroupOf (show g' ∈ G₁.subgroupOf I from hg) ho'
  have hg3 : g' ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
  have hodd : Odd (orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) g')) :=
    ho'.of_dvd_nat (orderOf_map_dvd _ g')
  exact ⟨g', d.mem_of_mk_mem hK hg3 (Insp15418.mem_of_odd_of_index_two hidx hodd), rfl⟩

theorem normal_of_index_two {K : Subgroup ↥I} (hK : CFSG.IsComponent K)
    (hidx : (K.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))).index = 2) : K.Normal := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  have hN : (K.map π).Normal := Subgroup.normal_of_index_eq_two hidx
  refine Subgroup.normal_iff_map_conj_eq.mpr fun g => ?_
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK
  have hmap : K'.map π = K.map π := by
    have e : π.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (π g)).toMonoidHom.comp π := by
      ext x
      simp [MulAut.conj_apply]
    rw [hK', Subgroup.map_map, e, ← Subgroup.map_map]
    exact Subgroup.Normal.map_conj_eq (H := K.map π) (π g)
  have heq : K' = K := by
    rcases CFSG.LocalCores.distinct_components_commute hK'c hK with h | h
    · exact h
    · exfalso
      have hc : ⁅K'.map π, K.map π⁆ = ⊥ := by rw [← Subgroup.map_commutator, h, Subgroup.map_bot]
      have hKc := d.isComponent_map_mk hK
      rw [hmap, Subgroup.isPerfect_iff.mp hKc.1.1] at hc
      exact (Subgroup.nontrivial_iff_ne_bot _).mp
        (CFSG.LocalCores.isQuasisimple_nontrivial hKc.1) hc
  exact heq

end InspectionData15418

end CFSG.Quasithin.EmptyFaithfulMultiple
