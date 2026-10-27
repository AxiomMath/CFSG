module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43e

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem K_decomp (hK : IsTypeLnq 2 2 2 K) :
    ∀ x ∈ K, ∃ k ∈ ⁅K, K⁆, ∃ z ∈ K, (∀ g ∈ K, g * z = z * g) ∧ x = k * z := by
  obtain ⟨e5⟩ := CFSG.ComponentClassification.RankTwoClassical.nonempty_equiv_a5_of_psl hK
  have h5 : commutator (alternatingGroup (Fin 5)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hQ : commutator (↥K ⧸ Subgroup.center ↥K) = ⊤ := by
    have hsurj : Function.Surjective (e5.symm.toMonoidHom) := e5.symm.surjective
    have hmap : (commutator (alternatingGroup (Fin 5))).map e5.symm.toMonoidHom =
        commutator (↥K ⧸ Subgroup.center ↥K) := by
      rw [commutator, commutator, Subgroup.map_commutator,
        Subgroup.map_top, MonoidHom.range_eq_top.2 hsurj]
    rw [← hmap, h5, Subgroup.map_top, MonoidHom.range_eq_top.2 hsurj]
  have hmk : (commutator ↥K).map (QuotientGroup.mk' (Subgroup.center ↥K)) = ⊤ := by
    have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥K)) :=
      QuotientGroup.mk'_surjective _
    have : (commutator ↥K).map (QuotientGroup.mk' (Subgroup.center ↥K)) =
        commutator (↥K ⧸ Subgroup.center ↥K) := by
      rw [commutator, commutator, Subgroup.map_commutator,
        Subgroup.map_top, MonoidHom.range_eq_top.2 hsurj]
    rw [this, hQ]
  intro x hx
  have hxq : QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hx⟩ ∈
      (commutator ↥K).map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [hmk]; trivial
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 hxq
  have hz : k⁻¹ * ⟨x, hx⟩ ∈ Subgroup.center ↥K := by
    have := (QuotientGroup.eq (a := k) (b := ⟨x, hx⟩)).1 hkx
    exact this
  refine ⟨(k : G), ?_, ((k⁻¹ * ⟨x, hx⟩ : ↥K) : G), (k⁻¹ * ⟨x, hx⟩ : ↥K).2, ?_, ?_⟩
  · rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map_of_mem _ hk
  · intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  · simp

theorem b₂_mem_commutator (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) : b₂ ∈ ⁅K, K⁆ := by
  obtain ⟨k, hk, z, hzK, hzc, hb⟩ := K_decomp h.hK.2.1 b₂ h.hK.1
  have hz2 : z ^ 2 = 1 := by
    have := Z_K_sq hA h ⟨z, hzK⟩ (Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hzc g g.2))
    exact this
  have hcomm_le : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
    mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hkK : k ∈ K := hcomm_le hk
  have hkz : Commute k z := hzc k hkK
  have hb3 : b₂ ^ 3 = 1 := pow3_of_mem h (mem_b₂ h)
  have e4 : b₂ ^ 4 = b₂ := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hb3, one_mul]
  have hz4 : z ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hz2, one_pow]
  have : b₂ = k ^ 4 := by
    calc b₂ = b₂ ^ 4 := e4.symm
      _ = (k * z) ^ 4 := by rw [← hb]
      _ = k ^ 4 * z ^ 4 := hkz.mul_pow 4
      _ = k ^ 4 := by rw [hz4, mul_one]
  rw [this]
  exact pow_mem hk 4

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
