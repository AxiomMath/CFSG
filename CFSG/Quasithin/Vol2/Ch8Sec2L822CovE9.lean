module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem exists_commuting_three_cv {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hLq : CFSG.Quasithin.IsHat (↥L ⧸ CFSG.pCore 2 ↥L) (alternatingGroup (Fin 6))) :
    ∃ a b : G, a ∈ L ∧ b ∈ L ∧ a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧
      b ∉ Subgroup.zpowers a := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNL : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := kzThreeRank2OfAlt6OrHat_kz3 (Or.inr hLq)
  have hXYcomm : ∀ u ∈ ({x, y} : Set (↥L ⧸ CFSG.pCore 2 ↥L)),
      ∀ v ∈ ({x, y} : Set (↥L ⧸ CFSG.pCore 2 ↥L)), u * v = v * u := by
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl
  have hXYexp : ∀ u ∈ ({x, y} : Set (↥L ⧸ CFSG.pCore 2 ↥L)), u ^ 3 = 1 := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hx3
    · exact hy3
  obtain ⟨-, hAcomm, hAexp⟩ := kzClosureCommExp_kz3 hXYcomm hXYexp
  set A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.closure ({x, y} : Set _) with hA
  have hAp : IsPGroup 3 A := fun u => ⟨1, by
    apply Subtype.ext
    simpa using hAexp u.1 u.2⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hAp
  obtain ⟨S, -, hSinf, hSmap⟩ :=
    kzLiftPowThree_kz3 (CFSG.pCore 2 ↥L) CFSG.pCore_isPGroup A m hm
  have hSmem : ∀ s ∈ S, (QuotientGroup.mk s : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ A := by
    intro s hs
    rw [← hSmap]
    exact Subgroup.mem_map_of_mem _ hs
  have hSexp : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    have h3 : (QuotientGroup.mk (s ^ 3) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hAexp _ (hSmem s hs)
    have hmem : s ^ 3 ∈ S := S.pow_mem hs 3
    have hmem2 : s ^ 3 ∈ S ⊓ CFSG.pCore 2 ↥L :=
      ⟨hmem, (QuotientGroup.eq_one_iff _).mp h3⟩
    rw [hSinf, Subgroup.mem_bot] at hmem2
    exact hmem2
  have hSabel : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    have hc := hAcomm _ (hSmem s hs) _ (hSmem t ht)
    have h1 : (QuotientGroup.mk (s * t) : ↥L ⧸ CFSG.pCore 2 ↥L) = QuotientGroup.mk (t * s) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hc
    have h2 : (s * t)⁻¹ * (t * s) ∈ S ⊓ CFSG.pCore 2 ↥L := by
      refine ⟨S.mul_mem (S.inv_mem (S.mul_mem hs ht)) (S.mul_mem ht hs), ?_⟩
      exact (QuotientGroup.eq).mp h1
    rw [hSinf, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.mp h2
  have hxA : x ∈ A := Subgroup.subset_closure (by simp)
  have hyA : y ∈ A := Subgroup.subset_closure (by simp)
  rw [← hSmap] at hxA hyA
  obtain ⟨a₁, ha₁S, ha₁⟩ := Subgroup.mem_map.mp hxA
  obtain ⟨b₁, hb₁S, hb₁⟩ := Subgroup.mem_map.mp hyA
  refine ⟨(a₁ : G), (b₁ : G), a₁.2, b₁.2, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val (hSabel _ ha₁S _ hb₁S)
    simpa using this
  · have := congrArg Subtype.val (hSexp _ ha₁S)
    simpa using this
  · have := congrArg Subtype.val (hSexp _ hb₁S)
    simpa using this
  · intro h
    have ha : a₁ = 1 := Subtype.ext (by simpa using h)
    rw [ha, map_one] at ha₁
    exact hx1 ha₁.symm
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hk' : a₁ ^ k = b₁ := Subtype.ext (by simpa using hk)
    apply hyx
    rw [← hb₁, ← ha₁, ← hk', map_zpow]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

end CFSG.Quasithin.H13
