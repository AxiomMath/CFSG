module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Orders
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Basic

public section

namespace CFSG.RankThree.SubgroupLists

open CFSG.BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

theorem orderOf_dvd_of_not_commute {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F)) (hH : ¬ p ∣ Nat.card H)
    {x y : H} (hx : 2 < orderOf x) (hy : 2 < orderOf y) (hxy : x * y ≠ y * x) (z : H) :
    orderOf z ∣ 2 ∨ orderOf z ∣ 3 ∨ orderOf z ∣ 4 ∨ orderOf z ∣ 5 := by
  rcases CFSG.Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part hF H hH with
    ⟨_, _, _, hcyc⟩ | ⟨_, _, _, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
  · exfalso
    apply hxy
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    rw [← ha, ← hb, ← zpow_add, ← zpow_add, add_comm]
  · exact absurd (commute_of_equiv_dihedral e hx hy) hxy
  · rcases orderOf_dvd_of_equiv_alternating_four e z with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases orderOf_dvd_of_equiv_perm_four e z with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases orderOf_dvd_of_equiv_alternating_five e z with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

theorem commute_of_six_le_orderOf {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F)) (hH : ¬ p ∣ Nat.card H)
    {w : H} (hw : 6 ≤ orderOf w) {x y : H} (hx : 2 < orderOf x) (hy : 2 < orderOf y) :
    x * y = y * x := by
  by_contra hxy
  have hw0 : 0 < orderOf w := orderOf_pos w
  rcases orderOf_dvd_of_not_commute hF H hH hx hy hxy w with h | h | h | h <;>
    · have := Nat.le_of_dvd (by norm_num) h
      omega

end CFSG.RankThree.SubgroupLists
