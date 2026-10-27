module

public import CFSG.RankThree.PartTwo.Sec17.Item1723ProofHJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

section Claims


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G}

theorem Sec17Y1.claim1719W_of_j2 (h1715 : Item1715) (h : Sec17Y1 G A c L Y₀ Y₁ S p P)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
      w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
        w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨w, hwm, hwnA, hw3⟩ := h.toSec17Std.exists_w h415 h1715 hJ
  obtain ⟨hwA, hwL⟩ := Subgroup.mem_inf.mp hwm
  obtain ⟨-, hne⟩ := h.orbit_of_j2 hJ hwA hwL hwnA hw3
  refine ⟨w, Subgroup.mem_inf.mpr ⟨hwA, h.le_y0 hwL⟩,
    le_normalizer_inf (Subgroup.zpowers_le.mpr hwA)
      (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hwL)) (Subgroup.mem_zpowers w),
    fun hwS => hne ?_⟩
  have hSL : S ⊓ L = (S ⊓ Y₀) ⊓ L := by
    rw [inf_assoc, inf_eq_right.mpr h.le_y0]
  rw [hSL, Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective,
    Late.map_conj_eq_of_mem_normalizer hwS,
    Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hwL)]

end Claims

end CFSG.RankThree.PartTwo.Sec17
