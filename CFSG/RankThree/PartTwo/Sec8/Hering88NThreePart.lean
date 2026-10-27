module

public import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

theorem factorization_card_range_of_not_dvd {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hker : ¬ 3 ∣ Nat.card f.ker) :
    (Nat.card f.range).factorization 3 = (Nat.card A).factorization 3 := by
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hA : Nat.card A = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  rw [hA, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hker, add_zero]

variable {G : Type} [Group G] [Finite G]

theorem factorization_card_imageModTheta {Y M : Subgroup G} (hMY : M ≤ Y) :
    (Nat.card (imageModTheta Y M)).factorization 3 = (Nat.card M).factorization 3 := by
  set f : ↥(M.subgroupOf Y) →* Y ⧸ aschbacherSolvableCore 3 Y :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)).comp (M.subgroupOf Y).subtype with hf
  have hrange : f.range = imageModTheta Y M := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    have hle : f.ker.map (M.subgroupOf Y).subtype ≤ aschbacherSolvableCore 3 Y := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hdvd : Nat.card f.ker ∣ Nat.card (aschbacherSolvableCore 3 Y) := by
      rw [← Subgroup.card_map_of_injective (M.subgroupOf Y).subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact fun h => KFacts.not_three_dvd_card_aschbacherSolvableCore Y (h.trans hdvd)
  have hMcard : Nat.card (M.subgroupOf Y) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMY).toEquiv
  rw [← hrange, factorization_card_range_of_not_dvd f hker, hMcard]

theorem factorization_card_inf_of_card_eq_two_mul {Q : Type*} [Group Q] [Finite Q]
    {H N C : Subgroup Q} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hcard : Nat.card H = 2 * Nat.card N) (hCH : C ≤ H) :
    (Nat.card ↥(N ⊓ C)).factorization 3 = (Nat.card C).factorization 3 := by
  set f : ↥(C.subgroupOf H) →* H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (C.subgroupOf H).subtype with hf
  have hquot : Nat.card (H ⧸ N.subgroupOf H) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, hcard] at h
    have hpos : 0 < Nat.card N := Nat.card_pos
    nlinarith
  have hrange : ¬ 3 ∣ Nat.card f.range := by
    intro h3
    have h := (h3.trans (Subgroup.card_subgroup_dvd_card f.range))
    rw [hquot] at h
    omega
  have hker : Nat.card f.ker = Nat.card ↥(N ⊓ C) := by
    have hmemN : ∀ x : f.ker, (((x : C.subgroupOf H) : H) : Q) ∈ N := fun x =>
      (QuotientGroup.eq_one_iff ((x : C.subgroupOf H) : H)).mp x.2
    have hmemK : ∀ y : ↥(N ⊓ C), f ⟨⟨y, hCH (Subgroup.mem_inf.mp y.2).2⟩,
        (Subgroup.mem_inf.mp y.2).2⟩ = 1 := fun y =>
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_inf.mp y.2).1
    exact Nat.card_congr
      { toFun := fun x => ⟨((x : C.subgroupOf H) : H),
          Subgroup.mem_inf.mpr ⟨hmemN x, (x : C.subgroupOf H).2⟩⟩
        invFun := fun y => ⟨⟨⟨y, hCH (Subgroup.mem_inf.mp y.2).2⟩, (Subgroup.mem_inf.mp y.2).2⟩,
          hmemK y⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hC : Nat.card (C.subgroupOf H) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hA : Nat.card (C.subgroupOf H) = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  rw [← hC, hA, hker, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hrange, zero_add]

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
