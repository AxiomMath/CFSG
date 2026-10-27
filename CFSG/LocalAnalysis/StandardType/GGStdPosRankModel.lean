module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPos_statedModel_psl {G : Type} [Group G] {m f : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f) (hadm : StatedLieAdmissible .PSL (m + 1) 2 f)
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :
    StatedClassicalModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) .PSL (m + 1) 2 f := by
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
    refine CFSG.LinearGroups.special_linear_isPerfect hadm.2.2.1 ?_
    rcases Nat.lt_or_ge m 2 with hm | hm
    · right
      obtain rfl : m = 1 := by have := hadm.2.2.1; omega
      have h4 : 4 ≤ 2 ^ f := by
        rcases Nat.lt_or_ge f 2 with hf | hf
        · obtain rfl : f = 1 := by have := hadm.2.1; omega
          exact absurd (by simp) hadm.2.2.2.1
        · calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      have := Fintype.ofFinite F
      have h4F : 4 ≤ (Finset.univ : Finset F).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
        exact h4
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4F
      exact ⟨s, hs⟩
    · left
      omega
  have hZ : Subgroup.center ↥ψ.range =
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)).map ψ.rangeRestrict := by
    ext l
    obtain ⟨u, rfl⟩ := ψ.rangeRestrict_surjective l
    constructor
    · intro hu
      exact ⟨u, InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf.commutator_eq_top ψ hker
        hu, rfl⟩
    · rintro ⟨v, hv, hvu⟩
      rw [← hvu, Subgroup.mem_center_iff]
      intro l'
      obtain ⟨w, rfl⟩ := ψ.rangeRestrict_surjective l'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hv w]
  exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
    (CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective ψ.rangeRestrict
      ψ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker) hZ)
    (SpecialLinear.statedClassicalModel_center_quotient m F hadm hF)

end CFSG.StandardType

end
