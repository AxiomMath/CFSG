module

public import CFSG.Quasithin.Vol2.Ch11SecGFacts2
public import CFSG.Quasithin.Vol2.Ch11SecO6E
public import CFSG.Quasithin.Vol2.Ch11SecAKE12
public import CFSG.Quasithin.Vol2.Ch11SecAKE14

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]


theorem false_of_list2 {X : Type} [Group X] [Finite X] {n : ℕ} (hl : List11_1_1Two X n)
    (hp2 : p ≠ 2) {φ : X →* SL(2, ZMod p)} (hφ : Function.Surjective φ) : False := by
  have hs : IsSimpleGroup X → False := fun h => false_of_simple hp2 hφ
  rcases hl with ⟨K, _, _, -, ⟨e⟩⟩ | h | h | h | h | h | ⟨-, h⟩
  · let e' : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
      e.trans (specialLinearGroupEquivStatedSL 3 K).symm
    refine false_of_quasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl)) ?_ hp2 hφ
    have hc : Nat.card (Subgroup.center X) =
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) := by
      rw [← Subgroup.map_center_eq e', Subgroup.card_map_of_injective e'.injective]
    rw [hc]
    exact SecA.C10KH.card_center_sl3_dvd K
  · exact hs (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 n h).2
  · exact hs (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp
      X 2 2 n h)
  · exact hs (CFSG.LieType.Simplicity.fam_g2_simplicity X 2 n h).2
  · exact hs (CFSG.LieType.Simplicity.fam_2f4_simplicity X 2 n h).2
  · exact hs (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 n h).2
  · exact hs (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 (n / 3) h).2


theorem shape_of_lists {X : Type} [Group X] [Finite X] {n : ℕ}
    (hl : List11_1_1Two X n ∨ (n = 2 ∧ List11_1_1Three X)) (hp2 : p ≠ 2)
    {φ : X →* SL(2, ZMod p)} (hφ : Function.Surjective φ) :
    A36Case4 X ∨ ∃ q : ℕ, q.Prime ∧ (q % 5 = 1 ∨ q % 5 = 4) ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧
      CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
      IsElemAbelianOfRank q 2 ↥(CFSG.fittingSubgroup X) ∧
      NaturalSL2Action q X (CFSG.fittingSubgroup X) := by
  have hqs : CFSG.IsQuasisimple X → Nat.card (Subgroup.center X) ∣ 3 → False :=
    fun hq hZ => false_of_quasisimple hq hZ hp2 hφ
  rcases hl with h | ⟨-, h⟩
  · exact (false_of_list2 h hp2 hφ).elim
  obtain ⟨h1, h2⟩ := SecA.factList3Table_holds
  have k1 := fun h => hqs (h1 X h).1 (h1 X h).2.1
  have k2 := fun h => hqs (h2 X h).1 (by rw [(h2 X h).2.1, Subgroup.card_bot]; exact one_dvd 3)
  rcases h with h | h | ⟨q, hq, hq5, -, h⟩ | h | ⟨s, h | h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact (k1 (Or.inl h)).elim
  · exact (k1 (by simp only [h, true_or, or_true])).elim
  · have h11 : 11 ≤ q := by
      by_contra hlt
      have hq2 := hq.two_le
      have hlt' : q < 11 := by omega
      interval_cases q <;> first | omega | exact absurd hq (by norm_num)
    exact (k2 (Or.inl ⟨q, hq, h11, h⟩)).elim
  · exact (k2 (by simp only [h, true_or, or_true])).elim
  · cases s
    · exact (k1 (by simp only [h, true_or, or_true])).elim
    · exact (k2 (by simp only [h, true_or, or_true])).elim
  · cases s
    · exact (k1 (by simp only [h, or_true])).elim
    · exact (k2 (by simp only [h, true_or, or_true])).elim
  · exact (k1 (by simp only [h, true_or, or_true])).elim
  · exact (k1 (by simp only [h, true_or, or_true])).elim
  · exact (k1 (by simp only [h, true_or, or_true])).elim
  · exact (k2 (by simp only [h, or_true])).elim
  · exact (k1 (by simp only [h, true_or, or_true])).elim
  · exact (k1 (by simp only [h, true_or, or_true])).elim
  · exact (k1 (by simp only [h, true_or, or_true])).elim
  · exact (k1 (by simp only [h, true_or, or_true])).elim
  · exact Or.inl h
  · exact Or.inr h

end CFSG.Quasithin.Vol2.Ch11.O6

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint


theorem factCase1Shape_holds : FactCase1Shape := by
  rintro X _ _ hl ⟨p, hp, hp5, φ, hφ, -⟩
  have : Fact p.Prime := ⟨hp⟩
  exact O6.shape_of_lists (n := 2) (hl.imp_right fun h => ⟨rfl, h⟩) (by omega) hφ

end CFSG.Quasithin.Vol2.Ch11.SecG
