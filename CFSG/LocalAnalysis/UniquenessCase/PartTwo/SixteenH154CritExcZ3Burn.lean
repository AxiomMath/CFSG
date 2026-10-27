module

public import CFSG.Quasithin.Background.A1bBasic

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_not_dvd_of_central_sylow {H : Type*} [Group H] [Finite H] {J S : Subgroup H}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : IsSylowIn p S J)
    (hScen : ∀ s ∈ S, ∀ j ∈ J, s * j = j * s)
    (hJgen : ∃ X : Set H, (∀ g ∈ X, g ^ 2 = 1) ∧ J = closure X) : ¬ p ∣ Nat.card ↥J := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Sy : Sylow p ↥J := hS.toSylow
  have hSy_coe : (Sy : Subgroup ↥J) = S.subgroupOf J := IsSylowIn.coe_toSylow hS
  have hSy_centIn : (Sy : Subgroup ↥J) ≤
      centerIn (G := ↥J) (Subgroup.normalizer (Sy : Subgroup ↥J)) := by
    intro x hx
    rw [centerIn, Subgroup.mem_inf]
    refine ⟨Subgroup.le_normalizer hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    have hxS : (x : H) ∈ S := by
      have hx' : x ∈ S.subgroupOf J := by rwa [← hSy_coe]
      exact Subgroup.mem_subgroupOf.mp hx'
    apply Subtype.ext
    simpa using (hScen (x : H) hxS (y : H) y.property).symm
  obtain ⟨K, hKnorm, hKcop, hKquot⟩ :=
    CFSG.hasNormalPComplement_of_sylow_le_center_normalizer (G := ↥J) p Sy hSy_centIn
  haveI : K.Normal := hKnorm
  obtain ⟨X, hXinv, hJX⟩ := hJgen
  have hXK : X ⊆ K.map J.subtype := by
    intro g hg
    have hgJ : g ∈ J := by
      rw [hJX]
      exact Subgroup.subset_closure hg
    let gJ : ↥J := ⟨g, hgJ⟩
    have hg2 : gJ ^ 2 = 1 := by
      apply Subtype.ext
      simpa [gJ] using hXinv g hg
    have hq2 : (QuotientGroup.mk' K gJ) ^ 2 = 1 := by
      rw [← map_pow, hg2, map_one]
    have hord2 : orderOf (QuotientGroup.mk' K gJ) ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
    obtain ⟨k, hordp⟩ := (isPGroup_iff_orderOf_dvd_pow.mp hKquot) (QuotientGroup.mk' K gJ)
    have hpdvd2 : ¬ p ∣ 2 :=
      fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    have hcop : Nat.Coprime 2 (p ^ k) := Nat.Prime.coprime_pow_of_not_dvd hp hpdvd2
    have hq1 : QuotientGroup.mk' K gJ = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord2 hordp)
    have hgK : gJ ∈ K := by
      rw [← QuotientGroup.eq_one_iff gJ]
      simpa using hq1
    exact ⟨gJ, hgK, rfl⟩
  have hJK : J ≤ K.map J.subtype := by
    intro x hx
    rw [hJX] at hx
    rw [Subgroup.mem_closure] at hx
    exact hx _ hXK
  have hKJ : K.map J.subtype = J :=
    le_antisymm (Subgroup.map_subtype_le (H := J) K) hJK
  have hcard : Nat.card ↥J = Nat.card K := by
    rw [← Subgroup.card_subtype J K, hKJ]
  have hcopJ : Nat.Coprime p (Nat.card ↥J) := by
    rw [hcard]
    exact hKcop
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcopJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
