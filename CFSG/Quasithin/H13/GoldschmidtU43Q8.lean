module

public import CFSG.Quasithin.H13.A6Q8Q8

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

@[expose] def cc : QuaternionGroup 2 × QuaternionGroup 2 :=
  (QuaternionGroup.a 2, QuaternionGroup.a 2)

theorem cc_mem_center : cc ∈ Subgroup.center (QuaternionGroup 2 × QuaternionGroup 2) := by
  rw [Subgroup.mem_center_iff]
  intro g
  refine Prod.ext ?_ ?_
  · exact ((a2_central.1 g.1).symm)
  · exact ((a2_central.1 g.2).symm)

theorem cc_mul_cc : cc * cc = 1 := by
  refine Prod.ext ?_ ?_
  · exact a2_mul_a2
  · exact a2_mul_a2

theorem cc_ne_one : cc ≠ 1 := by
  intro h
  exact a2_central.2 (congrArg Prod.fst h)

theorem orderOf_cc : orderOf cc = 2 := by
  refine orderOf_eq_prime ?_ cc_ne_one
  rw [pow_two]
  exact cc_mul_cc

theorem normalClosure_cc :
    Subgroup.normalClosure {cc} = Subgroup.zpowers cc := by
  have hn : (Subgroup.zpowers cc).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hg : g * cc * g⁻¹ = cc := by
      rw [(Subgroup.mem_center_iff.mp cc_mem_center g)]
      group
    rw [← conj_zpow, hg]
    exact Subgroup.zpow_mem_zpowers cc k
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (by simp)
  · exact (Subgroup.zpowers_le).2 (Subgroup.subset_normalClosure rfl)

theorem mem_normalClosure_cc {x : QuaternionGroup 2 × QuaternionGroup 2} :
    x ∈ Subgroup.normalClosure {cc} ↔ x = 1 ∨ x = cc := by
  rw [normalClosure_cc, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      obtain ⟨m, rfl⟩ := Int.dvd_of_emod_eq_zero h
      rw [zpow_mul, zpow_two, ← pow_two, show cc ^ 2 = 1 from by rw [pow_two]; exact cc_mul_cc]
      simp
    · right
      have : k = 2 * (k / 2) + 1 := by omega
      rw [this, zpow_add, zpow_mul, zpow_one, zpow_two, ← pow_two,
        show cc ^ 2 = 1 from by rw [pow_two]; exact cc_mul_cc]
      simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem card_q8Q8 : Nat.card Q8Q8 = 32 := by
  have hN : Nat.card (Subgroup.normalClosure {cc} :
      Subgroup (QuaternionGroup 2 × QuaternionGroup 2)) = 2 := by
    rw [normalClosure_cc, Nat.card_zpowers, orderOf_cc]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.normalClosure {cc} : Subgroup (QuaternionGroup 2 × QuaternionGroup 2))
  rw [hN, card_q8_prod] at h
  have h2 : Nat.card Q8Q8 = Nat.card ((QuaternionGroup 2 × QuaternionGroup 2) ⧸
      (Subgroup.normalClosure {cc} : Subgroup (QuaternionGroup 2 × QuaternionGroup 2))) := rfl
  omega

theorem isQ8Sq_q8Q8 : IsQ8Sq Q8Q8 := by
  let N : Subgroup (QuaternionGroup 2 × QuaternionGroup 2) := Subgroup.normalClosure {cc}
  let π : QuaternionGroup 2 × QuaternionGroup 2 →* Q8Q8 := QuotientGroup.mk' N
  have hπ : ∀ x, π x = 1 ↔ x = 1 ∨ x = cc := fun x => by
    rw [show π x = (QuotientGroup.mk x : Q8Q8) from rfl, QuotientGroup.eq_one_iff]
    exact mem_normalClosure_cc
  let fA : QuaternionGroup 2 →* Q8Q8 := π.comp (MonoidHom.inl _ _)
  let fB : QuaternionGroup 2 →* Q8Q8 := π.comp (MonoidHom.inr _ _)
  have hfA : Function.Injective fA := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rcases (hπ (x, 1)).1 hx with h | h
    · exact congrArg Prod.fst h
    · exact absurd (congrArg Prod.snd h) (by simpa [cc] using a2_central.2.symm)
  have hfB : Function.Injective fB := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rcases (hπ (1, x)).1 hx with h | h
    · exact congrArg Prod.snd h
    · exact absurd (congrArg Prod.fst h) (by simpa [cc] using a2_central.2.symm)
  refine ⟨card_q8Q8, fA.range, fB.range, ⟨?_, ?_⟩,
    ⟨(MonoidHom.ofInjective hfA).symm⟩, ⟨(MonoidHom.ofInjective hfB).symm⟩⟩
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    simp only [fA, fB, MonoidHom.comp_apply, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_ <;> simp
  · rw [eq_top_iff]
    intro p _
    obtain ⟨⟨x, y⟩, rfl⟩ := QuotientGroup.mk'_surjective N p
    have : π (x, y) = fA x * fB y := by
      simp only [fA, fB, MonoidHom.comp_apply, ← map_mul]
      congr 1
      refine Prod.ext ?_ ?_ <;> simp
    show π (x, y) ∈ _
    rw [this]
    exact Subgroup.mul_mem_sup ⟨x, rfl⟩ ⟨y, rfl⟩

end CFSG.Quasithin.H13.U43
