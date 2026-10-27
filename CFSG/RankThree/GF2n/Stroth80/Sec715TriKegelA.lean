module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriKegel
public import CFSG.LieType.D4Small.SmallIrrep

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small CFSG.LieType.D4Small.D4Datum

private theorem nfType_of_isWtClass {N : ℕ} {j : ℕ} {C : Finset (Fin 4 → ZMod N)}
    (h : IsWtClass N j C) : NFType j C := by
  rcases h with hnat | ⟨b₀, e, h2b, he, hC⟩
  · left
    intro a
    simpa only [IsNatWt, IsVWt] using hnat a
  · right
    refine ⟨b₀, e, h2b, he, fun a => ?_⟩
    rw [hC a]
    simp only [IsSpinWt, IsSWt, negCount]
    rw [Nat.mod_eq_of_lt he]

theorem smallNF_holds : SmallNFStatement := by
  intro G _ K _ _ _ D hK X _ _ _ ρ hirr hnt hdim
  obtain ⟨j, C, b, hj, hC, hNF⟩ :=
    exists_isNormalForm (D := D) (ρ := ρ) hK hirr hnt hdim
  refine ⟨j, C, b, hj, nfType_of_isWtClass hC, ?_⟩
  exact ⟨fun a ha => (hNF.mem a ha).1, fun a ha => (hNF.mem a ha).2,
    hNF.span_eq, hNF.act⟩

end CFSG.RankThree.GF2n.Stroth80.Tri
